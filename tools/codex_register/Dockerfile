FROM python:3.10-slim

ENV PYTHONUNBUFFERED=1 \
    PIP_NO_CACHE_DIR=1

WORKDIR /app
RUN apt-get update \
	&& apt-get install -y --no-install-recommends build-essential curl ca-certificates \
	&& rm -rf /var/lib/apt/lists/*

COPY sub2api/tools/codex_register /app/codex-auto-register-main

RUN pip install --upgrade pip \
    && pip install curl_cffi psycopg2-binary

WORKDIR /app/codex-auto-register-main

CMD ["python", "codex_register_service.py"]
