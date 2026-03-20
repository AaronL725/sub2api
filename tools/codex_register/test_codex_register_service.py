import unittest
from pathlib import Path
from unittest import mock

from tools.codex_register import codex_register_service as service


class _FakeCursor:
    def __init__(self, rows):
        self._rows = rows
        self.queries = []

    def execute(self, sql, params=None):
        self.queries.append((sql, params))

    def fetchall(self):
        return self._rows


class _FakeConn:
    def __init__(self, cursor):
        self._cursor = cursor

    def cursor(self):
        return self._cursor

    def close(self):
        return None


class CodexRegisterServiceTests(unittest.TestCase):
    def test_classify_signup_page_type_supports_password_registration_flow(self):
        self.assertEqual(service.classify_signup_page_type("create_account_password"), "password_registration")
        self.assertEqual(service.classify_signup_page_type("password"), "password_registration")
        self.assertEqual(service.classify_signup_page_type("email_otp_verification"), "existing_account")

    def test_generate_registration_password_has_minimum_complexity(self):
        password = service.generate_registration_password(12)

        self.assertGreaterEqual(len(password), 12)
        self.assertRegex(password, r"[a-z]")
        self.assertRegex(password, r"[A-Z]")
        self.assertRegex(password, r"\d")
        self.assertRegex(password, r"[!@#$%^&*]")

    def test_extract_failure_summary_prefers_actionable_openai_error(self):
        stdout = "\n".join(
            [
                "2026-03-16 06:49:53,544 [WARNING] Attempt 1 failed: RuntimeError: Send OTP failed: 401 Passwordless signup is unavailable.",
                "2026-03-16 06:49:53,545 [INFO] Retry #2...",
            ]
        )

        self.assertEqual(
            service._extract_failure_summary(stdout, ""),
            "Attempt 1 failed: RuntimeError: Send OTP failed: 401 Passwordless signup is unavailable.",
        )

    def test_build_model_mapping_contains_supported_defaults(self):
        self.assertEqual(
            service.build_model_mapping(),
            {
                "claude-haiku*": "gpt-5.3-codex-spark",
                "claude-sonnet*": "gpt-5.4",
                "claude-opus*": "gpt-5.4",
                "gpt-5": "gpt-5",
                "gpt-5.1": "gpt-5.1",
                "gpt-5.1-codex": "gpt-5.1-codex",
                "gpt-5.1-codex-max": "gpt-5.1-codex-max",
                "gpt-5.1-codex-mini": "gpt-5.1-codex-mini",
                "gpt-5.2": "gpt-5.2",
                "gpt-5.2-codex": "gpt-5.2-codex",
                "gpt-5.3-codex": "gpt-5.3-codex",
                "gpt-5.3-codex-spark": "gpt-5.3-codex-spark",
                "gpt-5.4": "gpt-5.4",
            },
        )

    def test_build_model_mapping_can_be_overridden_by_env(self):
        custom_mapping = '{"claude-haiku*":"spark-max","claude-sonnet*":"gpt-5.4"}'

        with mock.patch.dict("os.environ", {"CODEX_MODEL_MAPPING_JSON": custom_mapping}, clear=False):
            self.assertEqual(
                service.build_model_mapping(),
                {
                    "claude-haiku*": "spark-max",
                    "claude-sonnet*": "gpt-5.4",
                },
            )

    def test_normalize_extra_ignores_transient_timestamp(self):
        before = {
            "codex_auto_register": True,
            "codex_auto_register_updated_at": "2026-03-07T10:00:00Z",
            "codex_auth_file": "a.json",
        }
        after = {
            "codex_auto_register": True,
            "codex_auto_register_updated_at": "2026-03-07T10:01:00Z",
            "codex_auth_file": "a.json",
        }

        self.assertEqual(
            service.normalize_extra_for_compare(before),
            service.normalize_extra_for_compare(after),
        )

    def test_archive_processed_file_moves_json_out_of_active_directory(self):
        source = Path("tokens/token.json")
        processed_dir = Path("tokens/processed")

        with mock.patch.object(Path, "mkdir") as mkdir, mock.patch.object(Path, "exists", autospec=True) as exists, mock.patch.object(
            service.shutil, "move"
        ) as move:
            exists.side_effect = lambda candidate: candidate == source
            archived = service.archive_processed_file(source, processed_dir)

        mkdir.assert_called_once_with(parents=True, exist_ok=True)
        move.assert_called_once_with(str(source), str(processed_dir / source.name))
        self.assertEqual(archived, processed_dir / source.name)

    def test_should_update_account_returns_false_for_timestamp_only_change(self):
        current_credentials = {"email": "a@example.com", "access_token": "same"}
        next_credentials = {"email": "a@example.com", "access_token": "same"}
        current_extra = {
            "codex_auto_register": True,
            "codex_auto_register_updated_at": "2026-03-07T10:00:00Z",
        }
        next_extra = {
            "codex_auto_register": True,
            "codex_auto_register_updated_at": "2026-03-07T10:01:00Z",
        }

        self.assertFalse(
            service.should_update_account(
                current_credentials,
                next_credentials,
                current_extra,
                next_extra,
            )
        )

    def test_build_credentials_preserves_new_openai_auth_fields(self):
        credentials = service.build_credentials(
            {"email": "old@example.com"},
            {
                "email": "new@example.com",
                "account_id": "acct_123",
                "access_token": "at",
                "refresh_token": "rt",
                "id_token": "id",
                "client_id": "client_123",
                "workspace_id": "ws_123",
                "session_token": "sess_123",
                "registration_mode": "login",
                "expired": "2026-03-20T12:00:00Z",
            },
        )

        self.assertEqual(credentials["email"], "new@example.com")
        self.assertEqual(credentials["account_id"], "acct_123")
        self.assertEqual(credentials["chatgpt_account_id"], "acct_123")
        self.assertEqual(credentials["client_id"], "client_123")
        self.assertEqual(credentials["organization_id"], "ws_123")
        self.assertEqual(credentials["workspace_id"], "ws_123")
        self.assertEqual(credentials["session_token"], "sess_123")
        self.assertEqual(credentials["codex_register_source"], "login")
        self.assertEqual(credentials["expires_at"], "2026-03-20T12:00:00Z")
        self.assertEqual(credentials["source"], "codex-auto-register")

    def test_build_extra_records_registration_flow_metadata(self):
        extra = service.build_extra(
            {},
            {
                "workspace_id": "ws_456",
                "registration_mode": "register",
            },
        )

        self.assertTrue(extra["codex_auto_register"])
        self.assertEqual(extra["codex_auto_register_flow"], "register")
        self.assertEqual(extra["codex_auto_register_workspace_id"], "ws_456")

    def test_compute_group_binding_changes_returns_add_remove_sets(self):
        to_add, to_remove = service.compute_group_binding_changes(
            current_group_ids={1, 2},
            next_group_ids={2, 3},
        )

        self.assertEqual(to_add, {3})
        self.assertEqual(to_remove, {1})

    def test_proxy_url_from_proxies_prefers_https(self):
        self.assertEqual(
            service._proxy_url_from_proxies({"http": "http://a", "https": "http://b"}),
            "http://b",
        )

    def test_build_tempmail_service_reads_env_overrides(self):
        with mock.patch.dict(
            "os.environ",
            {
                "CODEX_TEMPMAIL_BASE_URL": "https://tm.example/v2",
                "CODEX_TEMPMAIL_TIMEOUT": "45",
                "CODEX_TEMPMAIL_MAX_RETRIES": "6",
            },
            clear=False,
        ):
            tempmail = service._build_tempmail_service({"https": "http://proxy:7890"})

        self.assertEqual(tempmail.base_url, "https://tm.example/v2")
        self.assertEqual(tempmail.timeout, 45)
        self.assertEqual(tempmail.max_retries, 6)
        self.assertEqual(tempmail.proxy_url, "http://proxy:7890")

    def test_bind_groups_updates_by_diff_without_wholesale_delete(self):
        cur = _FakeCursor(rows=[(1, 1), (2, 5)])

        service.bind_groups(cur, account_id=42, group_ids=[2, 3])

        sqls = [sql for sql, _params in cur.queries]
        self.assertIn("SELECT group_id, priority FROM account_groups WHERE account_id = %s", sqls)
        self.assertIn("DELETE FROM account_groups WHERE account_id = %s AND group_id = %s", sqls)
        self.assertIn(
            "INSERT INTO account_groups (account_id, group_id, priority, created_at) VALUES (%s, %s, %s, NOW()) "
            "ON CONFLICT (account_id, group_id) DO UPDATE SET priority = EXCLUDED.priority",
            sqls,
        )
        self.assertIn(
            "UPDATE account_groups SET priority = %s WHERE account_id = %s AND group_id = %s",
            sqls,
        )
        self.assertNotIn("DELETE FROM account_groups WHERE account_id = %s", sqls)

    def test_upsert_account_skips_meaningless_update(self):
        existing = (
            9,
            "codex-a@example.com",
            {
                "email": "a@example.com",
                "access_token": "same",
                "refresh_token": "",
                "id_token": "",
                "source": "codex-auto-register",
                "model_mapping": service.build_model_mapping(),
            },
            {
                "codex_auto_register": True,
                "codex_auto_register_model_mapping": service.build_model_mapping(),
                "codex_auto_register_updated_at": "2026-03-07T10:00:00Z",
            },
        )
        cur = mock.Mock()

        with mock.patch.object(service, "get_existing_account", return_value=existing), mock.patch.object(
            service, "parse_group_ids", return_value=[1]
        ), mock.patch.object(service, "bind_groups") as bind_groups:
            action = service.upsert_account(cur, {"email": "a@example.com", "access_token": "same"})

        self.assertEqual(action, "skipped")
        bind_groups.assert_called_once_with(cur, 9, [1])
        executed_sql = "\n".join(call.args[0] for call in cur.execute.call_args_list)
        self.assertNotIn("UPDATE accounts SET credentials", executed_sql)

    def test_run_one_cycle_archives_successful_file_and_leaves_failed_file(self):
        tokens_dir = Path("tokens")
        good = tokens_dir / "good.json"
        bad = tokens_dir / "bad.json"

        cur = mock.Mock()
        conn = _FakeConn(cur)

        with mock.patch.object(service, "create_db_connection", return_value=conn), mock.patch.object(
            service,
            "run_codex_once",
            return_value=[
                (good, [{"email": "ok@example.com"}]),
                (bad, [{"email": "fail@example.com"}]),
            ],
        ), mock.patch.object(service, "upsert_account", side_effect=["skipped", RuntimeError("boom")]), mock.patch.object(
            service,
            "archive_processed_file",
            side_effect=lambda source, processed_dir: processed_dir / source.name,
        ) as archive_processed_file:
            service.run_one_cycle(tokens_dir)

        archived_sources = [call.args[0] for call in archive_processed_file.call_args_list]
        self.assertEqual(archived_sources, [good])


if __name__ == "__main__":
    unittest.main()
