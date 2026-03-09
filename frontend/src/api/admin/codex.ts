import { apiClient } from '@/api/client'

export interface CodexStatus {
  enabled: boolean
  sleep_min: number
  sleep_max: number
  total_created: number
  last_success: string | null
  last_error: string | null
  proxy: boolean
}

export interface CodexLogEntry {
  time: string
  level: string
  message: string
}

export async function getStatus(): Promise<CodexStatus> {
  const res = await apiClient.get<CodexStatus>('/admin/codex/status')
  return res.data
}

export async function getLogs(): Promise<CodexLogEntry[]> {
  const res = await apiClient.get<{ logs: CodexLogEntry[] }>('/admin/codex/logs')
  return res.data?.logs ?? []
}

export async function enable(): Promise<CodexStatus> {
  const res = await apiClient.post<CodexStatus>('/admin/codex/enable')
  return res.data
}

export async function disable(): Promise<CodexStatus> {
  const res = await apiClient.post<CodexStatus>('/admin/codex/disable')
  return res.data
}

export async function runOnce(): Promise<CodexStatus> {
  const res = await apiClient.post<CodexStatus>('/admin/codex/run-once')
  return res.data
}

export default {
  getStatus,
  getLogs,
  enable,
  disable,
  runOnce
}
