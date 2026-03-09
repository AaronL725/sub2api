import { mount } from '@vue/test-utils'
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'
import AppSidebar from '../AppSidebar.vue'

const mockToggleSidebar = vi.fn()
const mockSetMobileOpen = vi.fn()
const mockAdminFetch = vi.fn()
const mockLocalStorage = {
  getItem: vi.fn(() => null),
  setItem: vi.fn(),
  removeItem: vi.fn(),
  clear: vi.fn(),
}
const mockMatchMedia = vi.fn(() => ({
  matches: false,
  addEventListener: vi.fn(),
  removeEventListener: vi.fn(),
}))

const originalLocalStorage = globalThis.localStorage
const originalMatchMedia = window.matchMedia

const createAppStoreMock = () => ({
  sidebarCollapsed: false,
  mobileOpen: false,
  siteName: 'Test Site',
  siteLogo: 'https://example.com/custom-logo.png',
  publicSettingsLoaded: true,
  cachedPublicSettings: {
    sora_client_enabled: false,
    purchase_subscription_enabled: false,
    custom_menu_items: [],
  },
  toggleSidebar: mockToggleSidebar,
  setMobileOpen: mockSetMobileOpen,
})

let appStoreMock = createAppStoreMock()

const authStoreMock = {
  isAdmin: false,
  isSimpleMode: false,
}

const adminSettingsStoreMock = {
  customMenuItems: [],
  opsMonitoringEnabled: false,
  fetch: mockAdminFetch,
}

const onboardingStoreMock = {
  isCurrentStep: vi.fn(() => false),
  nextStep: vi.fn(),
}

const mountOptions = {
  global: {
    stubs: {
      RouterLink: true,
      'router-link': true,
    },
  },
}

vi.mock('@/stores', () => ({
  useAppStore: () => appStoreMock,
  useAuthStore: () => authStoreMock,
  useAdminSettingsStore: () => adminSettingsStoreMock,
  useOnboardingStore: () => onboardingStoreMock,
}))

vi.mock('vue-router', () => ({
  useRoute: () => ({ path: '/dashboard' }),
}))

vi.mock('vue-i18n', () => ({
  useI18n: () => ({
    t: (key: string) => key,
  }),
}))

describe('AppSidebar brand block', () => {
  beforeEach(() => {
    vi.clearAllMocks()
    appStoreMock = createAppStoreMock()
    authStoreMock.isAdmin = false
    authStoreMock.isSimpleMode = false
    mockLocalStorage.getItem.mockReturnValue(null)
    Object.defineProperty(globalThis, 'localStorage', {
      value: mockLocalStorage,
      configurable: true,
    })
    Object.defineProperty(window, 'matchMedia', {
      value: mockMatchMedia,
      configurable: true,
    })
  })

  afterEach(() => {
    if (originalLocalStorage === undefined) {
      delete (globalThis as Partial<GlobalThis>).localStorage
    } else {
      Object.defineProperty(globalThis, 'localStorage', {
        value: originalLocalStorage,
        configurable: true,
      })
    }

    if (originalMatchMedia === undefined) {
      delete (window as Partial<Window>).matchMedia
    } else {
      Object.defineProperty(window, 'matchMedia', {
        value: originalMatchMedia,
        configurable: true,
      })
    }
  })

  it('renders logo and site name when settings are loaded', () => {
    const wrapper = mount(AppSidebar, mountOptions)

    const header = wrapper.find('.sidebar-header')
    const brandName = header.find('span.text-lg.font-bold')
    const logo = header.find('img')

    expect(brandName.text()).toBe('Test Site')
    expect(logo.attributes('src')).toBe('https://example.com/custom-logo.png')
  })

  it('does not render version UI or update controls in the brand area', () => {
    const wrapper = mount(AppSidebar, mountOptions)

    const header = wrapper.find('.sidebar-header')
    const brandColumn = header.find('div.flex.flex-col')
    expect(brandColumn.exists()).toBe(true)
    expect(brandColumn.findAll('button')).toHaveLength(0)
    expect(brandColumn.findAll('svg')).toHaveLength(0)
    expect(wrapper.html()).not.toContain('version.')
  })

  it('shows the Codex Register navigation item between accounts and announcements for admins', () => {
    authStoreMock.isAdmin = true

    const wrapper = mount(AppSidebar, mountOptions)
    const html = wrapper.html()

    expect(html).toContain('/admin/accounts')
    expect(html).toContain('/admin/codex-register')
    expect(html).toContain('/admin/announcements')
    expect(html.indexOf('/admin/accounts')).toBeLessThan(html.indexOf('/admin/codex-register'))
    expect(html.indexOf('/admin/codex-register')).toBeLessThan(html.indexOf('/admin/announcements'))
  })
})