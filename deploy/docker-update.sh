#!/usr/bin/env bash
set -euo pipefail

# 使用你自己的仓库 + docker-compose.local.yml 更新服务：
# 1. 从 origin/main 拉取最新代码（假设已包含 upstream 合并 + 你的改动）
# 2. docker-compose pull 最新镜像
# 3. docker-compose up -d 重新拉起服务

REPO_BRANCH=${REPO_BRANCH:-main}
COMPOSE_FILE=${COMPOSE_FILE:-docker-compose.local.yml}
COMPOSE_CMD=${COMPOSE_CMD:-docker-compose}  # 如使用新版 docker，可设为 "docker compose"

REPO_ROOT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

echo "[1/3] 切换到仓库根目录并拉取 origin/$REPO_BRANCH..."
cd "$REPO_ROOT_DIR"

git fetch origin
git checkout "$REPO_BRANCH"
git pull --ff-only origin "$REPO_BRANCH"

echo "[2/3] 进入 deploy 目录，拉取最新镜像 ($COMPOSE_FILE)..."
cd "$REPO_ROOT_DIR/deploy"

"$COMPOSE_CMD" -f "$COMPOSE_FILE" pull

echo "[3/3] 使用 $COMPOSE_CMD -f $COMPOSE_FILE up -d 重新拉起服务..."
"$COMPOSE_CMD" -f "$COMPOSE_FILE" up -d

echo
echo "✅ Docker 更新完成：当前代码来自 origin/$REPO_BRANCH（已包含合并后的 upstream + 你的改动）。"
