<template>
  <div
    :class="[
      'card overflow-hidden transition-shadow duration-200',
      active ? 'shadow-2xl ring-1 ring-primary-500/40' : 'shadow-sm'
    ]"
  >
    <div class="card-body space-y-6">
      <div class="flex flex-col gap-4 border-b border-gray-100 pb-6 dark:border-dark-700 xl:flex-row xl:items-start xl:justify-between">
        <div class="space-y-3">
          <div class="flex flex-wrap items-center gap-3">
            <span
              :class="[
                'inline-flex items-center rounded-full border px-3 py-1 text-xs font-medium',
                status?.enabled
                  ? 'border-emerald-200 bg-emerald-50 text-emerald-700 dark:border-emerald-900/60 dark:bg-emerald-900/20 dark:text-emerald-300'
                  : 'border-gray-200 bg-gray-100 text-gray-600 dark:border-dark-600 dark:bg-dark-700 dark:text-gray-300'
              ]"
            >
              {{ statusBadgeLabel }}
            </span>
            <span class="inline-flex items-center rounded-full border border-primary-200 bg-primary-50 px-3 py-1 text-xs font-medium text-primary-700 dark:border-primary-900/60 dark:bg-primary-900/20 dark:text-primary-300">
              {{ t('admin.codexRegister.badge.adminConsole') }}
            </span>
            <span class="inline-flex items-center rounded-full border border-gray-200 bg-gray-50 px-3 py-1 text-xs font-medium text-gray-500 dark:border-dark-600 dark:bg-dark-700 dark:text-gray-300">
              {{ t('admin.codexRegister.panels.polling', { seconds: 10 }) }}
            </span>
          </div>
          <div class="space-y-1">
            <p class="text-sm font-medium text-gray-700 dark:text-gray-200">
              {{ serviceStatusLabel }}
            </p>
            <p class="text-sm text-gray-500 dark:text-gray-400">
              {{ proxyDetailLabel }}
            </p>
          </div>
        </div>

        <div class="flex flex-wrap items-center gap-2 xl:justify-end">
          <button
            type="button"
            class="btn btn-secondary btn-sm"
            :disabled="refreshing || loading"
            @click="refreshAll"
          >
            {{ refreshing ? t('admin.codexRegister.actions.refreshing') : t('common.refresh') }}
          </button>
          <button
            type="button"
            class="btn btn-primary btn-sm"
            :disabled="loading || status?.enabled"
            @click="toggleEnabled(true)"
          >
            {{ t('admin.codexRegister.actions.start') }}
          </button>
          <button
            type="button"
            class="btn btn-secondary btn-sm"
            :disabled="loading || !status?.enabled"
            @click="toggleEnabled(false)"
          >
            {{ t('admin.codexRegister.actions.stop') }}
          </button>
          <button
            type="button"
            class="btn btn-secondary btn-sm"
            :disabled="loading"
            @click="runOnce"
          >
            {{ t('admin.codexRegister.actions.runOnce') }}
          </button>
        </div>
      </div>

      <div class="grid grid-cols-1 gap-4 sm:grid-cols-2 xl:grid-cols-4">
        <StatCard :title="t('admin.codexRegister.summary.totalCreated')" :value="status?.total_created ?? 0" :icon="AccountsIcon" icon-variant="primary" />
        <StatCard :title="t('admin.codexRegister.summary.lastSuccess')" :value="lastSuccessLabel" :icon="ClockIcon" icon-variant="success" />
        <StatCard :title="t('admin.codexRegister.summary.proxy')" :value="proxySummaryLabel" :icon="NetworkIcon" icon-variant="warning" />
        <StatCard :title="t('admin.codexRegister.summary.sleepRange')" :value="sleepRangeSummaryLabel" :icon="PulseIcon" icon-variant="danger" />
      </div>

      <p v-if="error" class="rounded-xl border border-red-200 bg-red-50 px-4 py-3 text-sm text-red-700 dark:border-red-900/60 dark:bg-red-900/20 dark:text-red-300">
        {{ error }}
      </p>

      <div class="grid gap-6 xl:grid-cols-[minmax(0,1.05fr)_minmax(0,0.95fr)]">
        <section class="rounded-2xl border border-gray-200 bg-gray-50/60 dark:border-dark-700 dark:bg-dark-900/20">
          <div class="border-b border-gray-200 px-6 py-4 dark:border-dark-700">
            <h2 class="text-base font-semibold text-gray-900 dark:text-white">{{ t('admin.codexRegister.panels.statusTitle') }}</h2>
            <p class="mt-1 text-sm text-gray-500 dark:text-gray-400">
              {{ t('admin.codexRegister.panels.statusDescription') }}
            </p>
          </div>
          <div class="space-y-4 p-6">
            <div class="grid gap-3 sm:grid-cols-2">
              <div class="rounded-xl border border-gray-200 bg-white p-4 dark:border-dark-700 dark:bg-dark-900/40">
                <p class="text-xs font-medium uppercase tracking-[0.18em] text-gray-400 dark:text-dark-400">{{ t('admin.codexRegister.panels.serviceStatus') }}</p>
                <p class="mt-2 text-sm font-medium text-gray-900 dark:text-white">
                  {{ serviceStatusLabel }}
                </p>
              </div>
              <div class="rounded-xl border border-gray-200 bg-white p-4 dark:border-dark-700 dark:bg-dark-900/40">
                <p class="text-xs font-medium uppercase tracking-[0.18em] text-gray-400 dark:text-dark-400">{{ t('admin.codexRegister.panels.proxyConfig') }}</p>
                <p class="mt-2 text-sm font-medium text-gray-900 dark:text-white">
                  {{ proxyDetailLabel }}
                </p>
              </div>
              <div class="rounded-xl border border-gray-200 bg-white p-4 dark:border-dark-700 dark:bg-dark-900/40">
                <p class="text-xs font-medium uppercase tracking-[0.18em] text-gray-400 dark:text-dark-400">{{ t('admin.codexRegister.panels.lastSuccessTitle') }}</p>
                <p class="mt-2 text-sm font-medium text-gray-900 dark:text-white">
                  {{ lastSuccessLabel }}
                </p>
              </div>
              <div class="rounded-xl border border-gray-200 bg-white p-4 dark:border-dark-700 dark:bg-dark-900/40">
                <p class="text-xs font-medium uppercase tracking-[0.18em] text-gray-400 dark:text-dark-400">{{ t('admin.codexRegister.panels.sleepRangeTitle') }}</p>
                <p class="mt-2 text-sm font-medium text-gray-900 dark:text-white">
                  {{ sleepRangeDetailLabel }}
                </p>
              </div>
            </div>

            <div
              :class="[
                'rounded-xl border p-4',
                status?.last_error
                  ? 'border-red-200 bg-red-50 dark:border-red-900/60 dark:bg-red-900/20'
                  : 'border-emerald-200 bg-emerald-50 dark:border-emerald-900/60 dark:bg-emerald-900/10'
              ]"
            >
              <div class="flex items-center justify-between gap-3">
                <h3
                  :class="[
                    'text-sm font-semibold',
                    status?.last_error ? 'text-red-700 dark:text-red-300' : 'text-emerald-700 dark:text-emerald-300'
                  ]"
                >
                  {{ t('admin.codexRegister.panels.errorTitle') }}
                </h3>
                <span
                  :class="[
                    'text-xs',
                    status?.last_error ? 'text-red-500 dark:text-red-400' : 'text-emerald-500 dark:text-emerald-400'
                  ]"
                >
                  {{ errorStateLabel }}
                </span>
              </div>
              <pre
                v-if="status?.last_error"
                class="mt-3 max-h-56 overflow-auto whitespace-pre-wrap rounded-lg border border-red-200/80 bg-white/70 p-3 text-[11px] leading-snug text-red-800 dark:border-red-900/60 dark:bg-dark-950/60 dark:text-red-200"
              >{{ status.last_error }}</pre>
              <p v-else class="mt-3 text-sm text-emerald-700 dark:text-emerald-300">
                {{ t('admin.codexRegister.panels.noErrors') }}
              </p>
            </div>
          </div>
        </section>

        <section class="rounded-2xl border border-gray-200 bg-gray-50/60 dark:border-dark-700 dark:bg-dark-900/20">
          <div class="flex items-center justify-between gap-3 border-b border-gray-200 px-6 py-4 dark:border-dark-700">
            <div>
              <h2 class="text-base font-semibold text-gray-900 dark:text-white">{{ t('admin.codexRegister.panels.eventsTitle') }}</h2>
              <p class="mt-1 text-sm text-gray-500 dark:text-gray-400">{{ t('admin.codexRegister.panels.eventsDescription') }}</p>
            </div>
            <span class="rounded-full border border-gray-200 bg-white px-3 py-1 text-xs font-medium text-gray-500 dark:border-dark-600 dark:bg-dark-800 dark:text-gray-300">
              {{ t('admin.codexRegister.panels.eventCount', { count: logs.length }) }}
            </span>
          </div>

          <div class="p-6">
            <div
              v-if="logs.length === 0"
              class="rounded-xl border border-dashed border-gray-200 px-6 py-10 text-center text-sm text-gray-500 dark:border-dark-700 dark:text-gray-400"
            >
              {{ t('admin.codexRegister.panels.emptyEvents') }}
            </div>
            <div
              v-else
              class="max-h-[28rem] overflow-auto rounded-xl border border-gray-200 bg-white dark:border-dark-700 dark:bg-dark-900/40"
            >
              <div
                v-for="(log, idx) in logs"
                :key="`${log.time}-${log.level}-${log.message}-${idx}`"
                class="border-b border-gray-100 px-4 py-3 last:border-b-0 dark:border-dark-800"
              >
                <div class="flex items-center justify-between gap-3 text-[11px]">
                  <span
                    :class="[
                      'inline-flex items-center rounded-full px-2 py-0.5 font-semibold uppercase tracking-wide',
                      log.level === 'error'
                        ? 'bg-red-100 text-red-700 dark:bg-red-900/40 dark:text-red-300'
                        : log.level === 'warn'
                          ? 'bg-amber-100 text-amber-700 dark:bg-amber-900/40 dark:text-amber-300'
                          : 'bg-gray-100 text-gray-600 dark:bg-dark-700 dark:text-gray-300'
                    ]"
                  >
                    {{ log.level }}
                  </span>
                  <span class="text-gray-400 dark:text-gray-500">{{ log.time }}</span>
                </div>
                <p class="mt-2 whitespace-pre-wrap break-words text-xs leading-6 text-gray-700 dark:text-gray-200">
                  {{ log.message }}
                </p>
              </div>
            </div>
          </div>
        </section>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, h, onUnmounted, ref, watch } from 'vue'
import { useI18n } from 'vue-i18n'
import { adminAPI } from '@/api/admin'
import type { CodexLogEntry, CodexStatus } from '@/api/admin/codex'
import StatCard from '@/components/common/StatCard.vue'

const props = defineProps({
  active: {
    type: Boolean,
    default: false
  }
})

const { t } = useI18n()

const status = ref<CodexStatus | null>(null)
const loading = ref(false)
const error = ref<string | null>(null)
const logs = ref<CodexLogEntry[]>([])
const refreshing = ref(false)
let timer: number | undefined
const POLL_INTERVAL = 10000

const statusBadgeLabel = computed(() => {
  if (status.value) {
    return status.value.enabled ? t('admin.codexRegister.badge.running') : t('admin.codexRegister.badge.stopped')
  }

  return error.value ? t('common.unknown') : t('common.loading')
})

const serviceStatusLabel = computed(() => {
  if (status.value) {
    return status.value.enabled ? t('admin.codexRegister.panels.serviceEnabled') : t('admin.codexRegister.panels.serviceDisabled')
  }

  return error.value ? t('common.unknown') : t('common.loading')
})

const proxySummaryLabel = computed(() => {
  if (status.value) {
    return status.value.proxy ? t('admin.codexRegister.summary.proxyConfigured') : t('admin.codexRegister.summary.proxyMissing')
  }

  return error.value ? t('common.unknown') : t('common.loading')
})

const proxyDetailLabel = computed(() => {
  if (status.value) {
    return status.value.proxy ? t('admin.codexRegister.panels.proxyConfiguredDetail') : t('admin.codexRegister.panels.proxyMissingDetail')
  }

  return error.value ? t('common.unknown') : t('common.loading')
})

const lastSuccessLabel = computed(() => {
  if (status.value) {
    return status.value.last_success || t('admin.codexRegister.panels.lastSuccessEmpty')
  }

  return error.value ? t('common.unknown') : t('common.loading')
})

const sleepRangeSummaryLabel = computed(() => {
  if (status.value) {
    return t('admin.codexRegister.summary.rangeValue', { min: status.value.sleep_min, max: status.value.sleep_max })
  }

  return error.value ? t('common.unknown') : t('common.loading')
})

const sleepRangeDetailLabel = computed(() => {
  if (status.value) {
    return t('admin.codexRegister.summary.rangeValueWithUnit', { min: status.value.sleep_min, max: status.value.sleep_max })
  }

  return error.value ? t('common.unknown') : t('common.loading')
})

const errorStateLabel = computed(() => {
  if (!status.value) {
    return error.value ? t('common.unknown') : t('common.loading')
  }

  return status.value.last_error ? t('admin.codexRegister.badge.attention') : t('admin.codexRegister.badge.healthy')
})

const AccountsIcon = {
  render: () => h('svg', { fill: 'none', viewBox: '0 0 24 24', stroke: 'currentColor', 'stroke-width': '1.8' }, [
    h('path', { 'stroke-linecap': 'round', 'stroke-linejoin': 'round', d: 'M17 20a4 4 0 00-8 0m8 0H7m10 0h3m-3 0a4 4 0 00-8 0m0-8a4 4 0 118 0 4 4 0 01-8 0zm8 0a4 4 0 11-8 0 4 4 0 018 0z' })
  ])
}

const ClockIcon = {
  render: () => h('svg', { fill: 'none', viewBox: '0 0 24 24', stroke: 'currentColor', 'stroke-width': '1.8' }, [
    h('path', { 'stroke-linecap': 'round', 'stroke-linejoin': 'round', d: 'M12 6v6l4 2m5-2a9 9 0 11-18 0 9 9 0 0118 0z' })
  ])
}

const NetworkIcon = {
  render: () => h('svg', { fill: 'none', viewBox: '0 0 24 24', stroke: 'currentColor', 'stroke-width': '1.8' }, [
    h('path', { 'stroke-linecap': 'round', 'stroke-linejoin': 'round', d: 'M7 17a4 4 0 010-8m10 8a4 4 0 000-8M8 12h8M12 7v10' })
  ])
}

const PulseIcon = {
  render: () => h('svg', { fill: 'none', viewBox: '0 0 24 24', stroke: 'currentColor', 'stroke-width': '1.8' }, [
    h('path', { 'stroke-linecap': 'round', 'stroke-linejoin': 'round', d: 'M3 12h4l3-7 4 14 3-7h4' })
  ])
}

function getErrorMessage(error: unknown): string {
  if (error && typeof error === 'object' && 'message' in error) {
    const message = error.message
    if (typeof message === 'string' && message) {
      return message
    }
  }

  return error instanceof Error ? error.message : String(error)
}

async function fetchStatus() {
  try {
    const data = await adminAPI.codex.getStatus()
    status.value = data
    error.value = null
  } catch (errorValue) {
    status.value = null
    error.value = getErrorMessage(errorValue)
  }
}

async function fetchLogs() {
  try {
    const data = await adminAPI.codex.getLogs()
    logs.value = data
  } catch (errorValue) {
    logs.value = []
    error.value = getErrorMessage(errorValue)
  }
}

async function refreshAll() {
  if (refreshing.value) return
  refreshing.value = true
  try {
    await Promise.all([fetchStatus(), fetchLogs()])
  } finally {
    refreshing.value = false
  }
}

async function toggleEnabled(value: boolean) {
  if (loading.value) return
  loading.value = true
  try {
    const data = value ? await adminAPI.codex.enable() : await adminAPI.codex.disable()
    status.value = data
    error.value = null
  } catch (errorValue) {
    error.value = getErrorMessage(errorValue)
  } finally {
    loading.value = false
  }
  await fetchLogs()
}

async function runOnce() {
  if (loading.value) return
  loading.value = true
  try {
    const data = await adminAPI.codex.runOnce()
    status.value = data
    error.value = null
  } catch (errorValue) {
    error.value = getErrorMessage(errorValue)
  } finally {
    loading.value = false
  }
  await fetchLogs()
}

function startPolling() {
  if (timer !== undefined) return
  void refreshAll()
  timer = window.setInterval(() => {
    if (loading.value || refreshing.value) {
      return
    }
    void refreshAll()
  }, POLL_INTERVAL)
}

function stopPolling() {
  if (timer !== undefined) {
    window.clearInterval(timer)
    timer = undefined
  }
}

watch(
  () => props.active,
  (isActive) => {
    if (isActive) {
      startPolling()
    } else {
      stopPolling()
    }
  },
  { immediate: true }
)

onUnmounted(() => {
  stopPolling()
})

defineExpose({
  StatCard,
  AccountsIcon,
  ClockIcon,
  NetworkIcon,
  PulseIcon,
  statusBadgeLabel,
  serviceStatusLabel,
  proxySummaryLabel,
  proxyDetailLabel,
  lastSuccessLabel,
  sleepRangeSummaryLabel,
  sleepRangeDetailLabel,
  errorStateLabel,
  toggleEnabled,
  runOnce
})
</script>
