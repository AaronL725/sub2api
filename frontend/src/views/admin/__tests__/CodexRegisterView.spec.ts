import { describe, expect, it, vi } from 'vitest'
import { mount } from '@vue/test-utils'

import CodexRegisterView from '../CodexRegisterView.vue'

vi.mock('vue-i18n', () => ({
  useI18n: () => ({
    t: (key: string) => key
  })
}))

vi.mock('@/components/layout/AppLayout.vue', () => ({
  default: { template: '<div><slot /></div>' }
}))

vi.mock('@/views/admin/settings/components/CodexRegistrationCard.vue', () => ({
  default: {
    props: {
      active: {
        type: Boolean,
        default: false
      }
    },
    template: `<div data-testid="codex-card" :data-active="active ? 'true' : 'false'" />`
  }
}))

describe('CodexRegisterView', () => {
  it('renders the standalone admin codex page shell and card', () => {
    const wrapper = mount(CodexRegisterView)

    expect(wrapper.text()).toContain('admin.codexRegister.title')
    expect(wrapper.text()).toContain('admin.codexRegister.heroDescription')
    expect(wrapper.find('[data-testid="codex-card"]').exists()).toBe(true)
    expect(wrapper.find('[data-testid="codex-card"]').attributes('data-active')).toBe('true')
  })
})
