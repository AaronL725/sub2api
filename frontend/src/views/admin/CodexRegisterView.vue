<template>
  <AppLayout>
    <div class="mx-auto max-w-6xl space-y-6">
      <section class="space-y-2">
        <h1 class="text-2xl font-semibold text-gray-900 dark:text-white">
          {{ t('admin.codexRegister.title') }}
        </h1>
        <p class="text-sm text-gray-500 dark:text-gray-400">
          {{ t('admin.codexRegister.heroDescription') }}
        </p>
      </section>

      <CodexRegistrationCard :active="true" />
    </div>
  </AppLayout>
</template>

<script setup lang="ts">
import { useI18n } from 'vue-i18n'
import AppLayout from '@/components/layout/AppLayout.vue'
import CodexRegistrationCard from '@/views/admin/settings/components/CodexRegistrationCard.vue'

const { t } = useI18n()
</script>
