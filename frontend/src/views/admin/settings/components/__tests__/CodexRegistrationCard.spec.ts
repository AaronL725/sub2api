import { flushPromises, mount } from '@vue/test-utils'
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'

import CodexRegistrationCard from '../CodexRegistrationCard.vue'

const StatCardStub = {
  props: ['title', 'value'],
  template: '<div>{{ title }} {{ value }}</div>'
}

const codexApiMocks = vi.hoisted(() => ({
  getStatus: vi.fn(),
  getLogs: vi.fn(),
  enable: vi.fn(),
  disable: vi.fn(),
  runOnce: vi.fn()
}))

vi.mock('@/api/admin', () => ({
  adminAPI: {
    codex: codexApiMocks
  }
}))

vi.mock('vue-i18n', async (importOriginal) => {
  const actual = await importOriginal<typeof import('vue-i18n')>()

  const messages: Record<string, string> = {
    'common.loading': '加载中...',
    'common.unknown': '未知',
    'common.refresh': '刷新',
    'admin.codexRegister.badge.adminConsole': '后台控制台',
    'admin.codexRegister.badge.running': '运行中',
    'admin.codexRegister.badge.stopped': '已停止',
    'admin.codexRegister.badge.attention': '需关注',
    'admin.codexRegister.badge.healthy': '暂无错误',
    'admin.codexRegister.actions.start': '开启',
    'admin.codexRegister.actions.stop': '关闭',
    'admin.codexRegister.actions.runOnce': '手动执行一次',
    'admin.codexRegister.actions.refreshing': '刷新中…',
    'admin.codexRegister.summary.totalCreated': '累计生成账号数',
    'admin.codexRegister.summary.lastSuccess': '最近成功时间',
    'admin.codexRegister.summary.proxy': '是否配置代理',
    'admin.codexRegister.summary.sleepRange': '休眠区间（秒）',
    'admin.codexRegister.summary.proxyConfigured': '已配置',
    'admin.codexRegister.summary.proxyMissing': '未配置',
    'admin.codexRegister.summary.rangeValue': 'range',
    'admin.codexRegister.summary.rangeValueWithUnit': 'range with unit',
    'admin.codexRegister.panels.statusTitle': '当前状态',
    'admin.codexRegister.panels.statusDescription': 'status description',
    'admin.codexRegister.panels.serviceStatus': '服务状态',
    'admin.codexRegister.panels.serviceEnabled': '当前状态：已开启自动注册',
    'admin.codexRegister.panels.serviceDisabled': '当前状态：已关闭自动注册',
    'admin.codexRegister.panels.proxyConfig': '代理配置',
    'admin.codexRegister.panels.proxyConfiguredDetail': '已配置代理，容器可按当前出口执行注册',
    'admin.codexRegister.panels.proxyMissingDetail': '未配置代理，请确认网络出口要求',
    'admin.codexRegister.panels.lastSuccessTitle': '最近成功时间',
    'admin.codexRegister.panels.lastSuccessEmpty': '暂无成功记录',
    'admin.codexRegister.panels.sleepRangeTitle': '休眠区间',
    'admin.codexRegister.panels.errorTitle': '最近错误日志',
    'admin.codexRegister.panels.noErrors': '最近没有错误输出，服务状态看起来正常。',
    'admin.codexRegister.panels.eventsTitle': '最近事件',
    'admin.codexRegister.panels.eventsDescription': 'events description',
    'admin.codexRegister.panels.emptyEvents': '暂无事件'
  }

  return {
    ...actual,
    useI18n: () => ({
      t: (key: string, params?: Record<string, unknown>) => {
        if (key === 'admin.codexRegister.panels.polling' && params) {
          return `自动轮询：${params.seconds} 秒`
        }
        if (key === 'admin.codexRegister.panels.eventCount' && params) {
          return `${params.count} 条记录`
        }
        if (key === 'admin.codexRegister.summary.rangeValue' && params) {
          return `${params.min} - ${params.max}`
        }
        if (key === 'admin.codexRegister.summary.rangeValueWithUnit' && params) {
          return `${params.min} - ${params.max} 秒`
        }
        return messages[key] ?? key
      }
    })
  }
})

describe('CodexRegistrationCard', () => {
  beforeEach(() => {
    vi.useFakeTimers()
    vi.clearAllMocks()

    codexApiMocks.getStatus.mockResolvedValue({
      enabled: true,
      sleep_min: 12,
      sleep_max: 34,
      total_created: 18,
      last_success: '2026-03-06 10:00:00',
      last_error: 'sample failure',
      proxy: true
    })

    codexApiMocks.getLogs.mockResolvedValue([
      {
        level: 'info',
        time: '2026-03-06 10:00:01',
        message: 'run completed'
      }
    ])
  })

  afterEach(() => {
    vi.clearAllTimers()
    vi.useRealTimers()
  })

  it('renders operational status, summary, and logs', async () => {
    const clearIntervalSpy = vi.spyOn(window, 'clearInterval')

    const wrapper = mount(CodexRegistrationCard, {
      props: {
        active: true
      },
      global: {
        stubs: {
          StatCard: StatCardStub
        }
      }
    })

    await flushPromises()

    expect(codexApiMocks.getStatus).toHaveBeenCalledTimes(1)
    expect(codexApiMocks.getLogs).toHaveBeenCalledTimes(1)

    const cardText = wrapper.text()

    expect(cardText).toContain('当前状态')
    expect(cardText).toContain('手动执行一次')
    expect(cardText).toContain('12 - 34 秒')
    expect(cardText).toContain('18')
    expect(cardText).toContain('最近成功时间')
    expect(cardText).toContain('是否配置代理')
    expect(cardText).toContain('休眠区间（秒）')
    expect(cardText).toContain('最近错误日志')
    expect(cardText).toContain('最近事件')
    expect(cardText).toContain('run completed')

    wrapper.unmount()
    expect(clearIntervalSpy).toHaveBeenCalled()
    clearIntervalSpy.mockRestore()
  })

  it('polls only when active and stops when deactivated', async () => {
    const setIntervalSpy = vi.spyOn(window, 'setInterval')
    const clearIntervalSpy = vi.spyOn(window, 'clearInterval')

    const wrapper = mount(CodexRegistrationCard, {
      props: {
        active: false
      },
      global: {
        stubs: {
          StatCard: StatCardStub
        }
      }
    })

    await flushPromises()

    expect(codexApiMocks.getStatus).not.toHaveBeenCalled()
    expect(codexApiMocks.getLogs).not.toHaveBeenCalled()
    expect(setIntervalSpy).not.toHaveBeenCalled()

    await wrapper.setProps({ active: true })
    await flushPromises()

    expect(codexApiMocks.getStatus).toHaveBeenCalledTimes(1)
    expect(codexApiMocks.getLogs).toHaveBeenCalledTimes(1)
    expect(setIntervalSpy).toHaveBeenCalledTimes(1)

    vi.advanceTimersByTime(10000)
    await flushPromises()

    expect(codexApiMocks.getStatus).toHaveBeenCalledTimes(2)
    expect(codexApiMocks.getLogs).toHaveBeenCalledTimes(2)

    await wrapper.setProps({ active: false })
    await flushPromises()

    expect(clearIntervalSpy).toHaveBeenCalled()

    vi.advanceTimersByTime(10000)
    await flushPromises()

    expect(codexApiMocks.getStatus).toHaveBeenCalledTimes(2)
    expect(codexApiMocks.getLogs).toHaveBeenCalledTimes(2)

    setIntervalSpy.mockRestore()
    clearIntervalSpy.mockRestore()
  })

  it('shows error details when initial requests fail', async () => {
    codexApiMocks.getStatus.mockRejectedValueOnce(new Error('status failed'))
    codexApiMocks.getLogs.mockRejectedValueOnce(new Error('logs failed'))

    const wrapper = mount(CodexRegistrationCard, {
      props: {
        active: true
      },
      global: {
        stubs: {
          StatCard: StatCardStub
        }
      }
    })

    await flushPromises()

    const cardText = wrapper.text()

    expect(cardText).toContain('logs failed')
    expect(cardText).toContain('未知')
    expect(cardText).toContain('暂无事件')
    expect(cardText).not.toContain('当前状态：已关闭自动注册')
    expect(cardText).not.toContain('已配置代理，容器可按当前出口执行注册')
  })
})
