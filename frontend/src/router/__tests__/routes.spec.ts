import { afterAll, beforeAll, describe, expect, it } from 'vitest'
import type { RouteRecordRaw } from 'vue-router'

let routes: RouteRecordRaw[] = []
const originalLocalStorage = globalThis.localStorage
let localStorageStubbed = false

beforeAll(async () => {
  if (typeof globalThis.localStorage === 'undefined' || typeof globalThis.localStorage.getItem !== 'function') {
    const fakeLocalStorage: Storage = {
      length: 0,
      clear() {},
      getItem() {
        return null
      },
      key() {
        return null
      },
      removeItem() {},
      setItem() {}
    }

    Object.defineProperty(globalThis, 'localStorage', {
      value: fakeLocalStorage,
      configurable: true
    })
    localStorageStubbed = true
  }

  const routerModule = await import('@/router')
  routes = routerModule.routes
})

afterAll(() => {
  if (!localStorageStubbed) {
    return
  }

  if (originalLocalStorage === undefined) {
    delete (globalThis as Partial<GlobalThis>).localStorage
  } else {
    Object.defineProperty(globalThis, 'localStorage', {
      value: originalLocalStorage,
      configurable: true
    })
  }
})

describe('router table', () => {
  it('registers the Codex register route as a standalone admin page', () => {
    const codexRoute = routes.find((route) => route.path === '/admin/codex-register')
    expect(codexRoute).toBeDefined()

    expect(codexRoute?.redirect).toBeUndefined()
    expect(codexRoute?.component).toBeDefined()
    expect(codexRoute?.meta?.titleKey).toBe('admin.codexRegister.title')
  })
})
