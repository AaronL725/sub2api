package service

import (
	"encoding/json"
	"strconv"
)

const (
	defaultPoolModeRetryCount = 3
	maxPoolModeRetryCount     = 10
)

// GetPoolModeRetryCount returns the configured pool mode retry count from
// the account's credentials. Returns defaultPoolModeRetryCount when pool_mode
// is not enabled or pool_mode_retry_count is not set. Values are clamped to
// [0, maxPoolModeRetryCount].
func (a *Account) GetPoolModeRetryCount() int {
	if a == nil || a.Credentials == nil {
		return defaultPoolModeRetryCount
	}
	pm, ok := a.Credentials["pool_mode"]
	if !ok {
		return defaultPoolModeRetryCount
	}
	if enabled, isBool := pm.(bool); isBool && !enabled {
		return defaultPoolModeRetryCount
	}

	raw, ok := a.Credentials["pool_mode_retry_count"]
	if !ok || raw == nil {
		return defaultPoolModeRetryCount
	}

	var count int
	parsed := false
	switch v := raw.(type) {
	case float64:
		count = int(v)
		parsed = true
	case int:
		count = v
		parsed = true
	case int64:
		count = int(v)
		parsed = true
	case json.Number:
		if i, err := v.Int64(); err == nil {
			count = int(i)
			parsed = true
		}
	case string:
		if i, err := strconv.Atoi(v); err == nil {
			count = i
			parsed = true
		}
	}

	if !parsed {
		return defaultPoolModeRetryCount
	}
	if count < 0 {
		return 0
	}
	if count > maxPoolModeRetryCount {
		return maxPoolModeRetryCount
	}
	return count
}
