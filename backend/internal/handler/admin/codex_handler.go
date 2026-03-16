package admin

import (
	"encoding/json"
	"net/http"
	"os"
	"time"

	"github.com/Wei-Shaw/sub2api/internal/pkg/response"

	"github.com/gin-gonic/gin"
)

type CodexHandler struct {
}

func NewCodexHandler() *CodexHandler {
	return &CodexHandler{}
}

func (h *CodexHandler) baseURL() string {
	if v := os.Getenv("CODEX_REGISTER_BASE_URL"); v != "" {
		return v
	}
	return "http://codex-register:5000"
}

func (h *CodexHandler) proxyGet(c *gin.Context, path string) {
	client := &http.Client{Timeout: 5 * time.Second}
	req, err := http.NewRequestWithContext(c.Request.Context(), http.MethodGet, h.baseURL()+path, nil)
	if err != nil {
		response.Error(c, http.StatusInternalServerError, err.Error())
		return
	}
	resp, err := client.Do(req)
	if err != nil {
		response.Error(c, http.StatusBadGateway, err.Error())
		return
	}
	defer func() { _ = resp.Body.Close() }()
	var body any
	if err := json.NewDecoder(resp.Body).Decode(&body); err != nil {
		response.Error(c, http.StatusBadGateway, err.Error())
		return
	}
	c.JSON(resp.StatusCode, body)
}

func (h *CodexHandler) proxyPost(c *gin.Context, path string) {
	client := &http.Client{Timeout: 10 * time.Second}
	req, err := http.NewRequestWithContext(c.Request.Context(), http.MethodPost, h.baseURL()+path, nil)
	if err != nil {
		response.Error(c, http.StatusInternalServerError, err.Error())
		return
	}
	resp, err := client.Do(req)
	if err != nil {
		response.Error(c, http.StatusBadGateway, err.Error())
		return
	}
	defer func() { _ = resp.Body.Close() }()
	var body any
	if err := json.NewDecoder(resp.Body).Decode(&body); err != nil {
		response.Error(c, http.StatusBadGateway, err.Error())
		return
	}
	c.JSON(resp.StatusCode, body)
}

func (h *CodexHandler) GetStatus(c *gin.Context) {
	h.proxyGet(c, "/status")
}

func (h *CodexHandler) GetLogs(c *gin.Context) {
	h.proxyGet(c, "/logs")
}

func (h *CodexHandler) Enable(c *gin.Context) {
	h.proxyPost(c, "/enable")
}

func (h *CodexHandler) Disable(c *gin.Context) {
	h.proxyPost(c, "/disable")
}

func (h *CodexHandler) RunOnce(c *gin.Context) {
	h.proxyPost(c, "/run-once")
}
