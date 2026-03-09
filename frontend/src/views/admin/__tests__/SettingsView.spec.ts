import { describe, it, expect, vi, beforeEach } from 'vitest'
import { mount, flushPromises } from '@vue/test-utils'

import SettingsView from '../SettingsView.vue'

const showError = vi.fn()
const showSuccess = vi.fn()
const fetchPublicSettings = vi.fn()
const fetchAdminSettings = vi.fn()

const getSettings = vi.fn()
const updateSettings = vi.fn()
const getAdminApiKey = vi.fn()
const getStreamTimeoutSettings = vi.fn()
const getAllGroups = vi.fn()
const mockRoute = {
  query: {} as Record<string, unknown>
}

vi.mock('@/api', () => ({
  adminAPI: {
    settings: {
      getSettings: (...args: unknown[]) => getSettings(...args),
      updateSettings: (...args: unknown[]) => updateSettings(...args),
      getAdminApiKey: (...args: unknown[]) => getAdminApiKey(...args),
      getStreamTimeoutSettings: (...args: unknown[]) => getStreamTimeoutSettings(...args)
    },
    groups: {
      getAll: (...args: unknown[]) => getAllGroups(...args)
    }
  }
}))

vi.mock('@/stores', () => ({
  useAppStore: () => ({
    showError,
    showSuccess,
    fetchPublicSettings
  })
}))

vi.mock('@/stores/adminSettings', () => ({
  useAdminSettingsStore: () => ({
    fetch: fetchAdminSettings
  })
}))

vi.mock('@/composables/useClipboard', () => ({
  useClipboard: () => ({
    copyToClipboard: vi.fn()
  })
}))

vi.mock('vue-i18n', async (importOriginal) => {
  const actual = await importOriginal<typeof import('vue-i18n')>()
  return {
    ...actual,
    useI18n: () => ({
      t: (key: string) => key
    }),
    createI18n: actual.createI18n
  }
})

vi.mock('@/components/layout/AppLayout.vue', () => ({
  default: { template: '<div><slot /></div>' }
}))
vi.mock('@/components/icons/Icon.vue', () => ({
  default: { template: '<span />' }
}))
vi.mock('@/components/common/Select.vue', () => ({
  default: {
    inheritAttrs: true,
    props: {
      modelValue: {
        type: [String, Number, Boolean, Object, Array, null],
        default: null
      },
      options: {
        type: Array,
        default: () => []
      }
    },
    emits: ['update:modelValue'],
    methods: {
      onChange(event: Event) {
        const rawValue = (event.target as HTMLSelectElement).value
        const matched = (this.options as Array<{ value: unknown }>).find(
          (option) => String(option.value) === rawValue
        )
        this.$emit('update:modelValue', matched ? matched.value : rawValue)
      }
    },
    template: `
      <select :class="$attrs.class" :value="modelValue ?? ''" @change="onChange">
        <option v-for="option in options" :key="String(option.value)" :value="option.value">
          {{ option.label }}
        </option>
      </select>
    `
  }
}))
vi.mock('@/components/common/GroupBadge.vue', () => ({
  default: { template: '<span><slot /></span>' }
}))
vi.mock('@/components/common/GroupOptionItem.vue', () => ({
  default: { template: '<span />' }
}))
vi.mock('@/components/common/Toggle.vue', () => ({
  default: {
    props: {
      modelValue: {
        type: Boolean,
        default: false
      },
      disabled: {
        type: Boolean,
        default: false
      }
    },
    emits: ['update:modelValue'],
    methods: {
      onChange(event: Event) {
        this.$emit('update:modelValue', (event.target as HTMLInputElement).checked)
      }
    },
    template: '<input type="checkbox" :checked="modelValue" :disabled="disabled" @change="onChange" />'
  }
}))
vi.mock('@/components/common/ImageUpload.vue', () => ({
  default: {
    props: {
      modelValue: {
        type: String,
        default: ''
      }
    },
    emits: ['update:modelValue'],
    methods: {
      onInput(event: Event) {
        this.$emit('update:modelValue', (event.target as HTMLInputElement).value)
      }
    },
    template: '<input type="text" :value="modelValue" @input="onInput" />'
  }
}))

vi.mock('vue-router', () => ({
  useRoute: () => mockRoute
}))

function buildSettingsResponse() {
  return {
    registration_enabled: true,
    email_verify_enabled: false,
    registration_email_suffix_whitelist: [],
    promo_code_enabled: true,
    password_reset_enabled: false,
    invitation_code_enabled: false,
    totp_enabled: false,
    totp_encryption_key_configured: false,
    default_balance: 0,
    default_concurrency: 1,
    default_subscriptions: [],
    site_name: 'Sub2API',
    site_logo: '',
    site_subtitle: '',
    api_base_url: '',
    contact_info: '',
    doc_url: '',
    home_content: '',
    hide_ccs_import_button: false,
    purchase_subscription_enabled: false,
    purchase_subscription_url: '',
    sora_client_enabled: false,
    custom_menu_items: [],
    smtp_host: '',
    smtp_port: 587,
    smtp_username: '',
    smtp_password_configured: false,
    smtp_from_email: '',
    smtp_from_name: '',
    smtp_use_tls: true,
    turnstile_enabled: false,
    turnstile_site_key: '',
    turnstile_secret_key_configured: false,
    linuxdo_connect_enabled: false,
    linuxdo_connect_client_id: '',
    linuxdo_connect_client_secret_configured: false,
    linuxdo_connect_redirect_url: '',
    enable_model_fallback: false,
    fallback_model_anthropic: 'claude-3-5-sonnet-20241022',
    fallback_model_openai: 'gpt-4o',
    fallback_model_gemini: 'gemini-2.5-pro',
    fallback_model_antigravity: 'gemini-2.5-pro',
    enable_identity_patch: true,
    identity_patch_prompt: '',
    ops_monitoring_enabled: true,
    ops_realtime_monitoring_enabled: true,
    ops_query_mode_default: 'auto',
    ops_metrics_interval_seconds: 60,
    min_claude_code_version: '',
    allow_ungrouped_key_scheduling: false
  }
}

describe('SettingsView', () => {
  beforeEach(() => {
    vi.clearAllMocks()
    mockRoute.query = {}
    getSettings.mockResolvedValue(buildSettingsResponse())
    getAdminApiKey.mockResolvedValue({ exists: false, masked_key: '' })
    getStreamTimeoutSettings.mockResolvedValue({
      enabled: true,
      action: 'temp_unsched',
      temp_unsched_minutes: 5,
      threshold_count: 3,
      threshold_window_minutes: 10
    })
    getAllGroups.mockResolvedValue([
      { id: 1, name: 'Group 1', description: null, platform: 'openai', subscription_type: 'subscription', rate_multiplier: 1, status: 'active' },
      { id: 2, name: 'Group 2', description: null, platform: 'openai', subscription_type: 'subscription', rate_multiplier: 1, status: 'active' }
    ])
    updateSettings.mockResolvedValue(buildSettingsResponse())
  })

  it('re-enables save after duplicate default subscription validation fails', async () => {
    const wrapper = mount(SettingsView, {
      global: {
        stubs: {}
      }
    })

    await flushPromises()
    await flushPromises()

    const addButton = wrapper
      .findAll('button')
      .find((button) => button.text().includes('admin.settings.defaults.addDefaultSubscription'))

    expect(addButton).toBeTruthy()

    await addButton?.trigger('click')
    await addButton?.trigger('click')
    await flushPromises()

    const subscriptionSelects = wrapper.findAll('select.default-sub-group-select')
    expect(subscriptionSelects).toHaveLength(2)

    await subscriptionSelects[1].setValue('1')
    await wrapper.find('form').trigger('submit')
    await flushPromises()

    expect(showError).toHaveBeenCalledWith('admin.settings.defaults.defaultSubscriptionsDuplicate')
    expect(updateSettings).not.toHaveBeenCalled()
    expect(wrapper.find('button[type="submit"]').attributes('disabled')).toBeUndefined()
  })

  it('still submits when a hidden tab contains an invalid constrained input', async () => {
    const wrapper = mount(SettingsView)

    await flushPromises()
    await flushPromises()

    const versionInput = wrapper.find(
      'input[placeholder="admin.settings.claudeCode.minVersionPlaceholder"]'
    )
    expect(versionInput.exists()).toBe(true)

    await versionInput.setValue('invalid-version')
    ;(wrapper.find('form').element as HTMLFormElement).requestSubmit()
    await flushPromises()

    expect(updateSettings).toHaveBeenCalledTimes(1)
  })

  it('initializes gateway tab from query without rendering codex content', async () => {
    mockRoute.query = { tab: 'gateway' }

    const wrapper = mount(SettingsView)

    await flushPromises()
    await flushPromises()

    const gatewayTabButton = wrapper
      .findAll('button')
      .find((button) => button.text().includes('admin.settings.tabs.gateway'))

    expect(gatewayTabButton).toBeTruthy()
    expect(gatewayTabButton?.classes()).toContain('settings-tab-active')
    expect(wrapper.find('[data-testid="codex-card"]').exists()).toBe(false)
    expect(wrapper.find('[data-testid="codex-error"]').exists()).toBe(false)
  })
})
