# sim8 — 8-bit CPU Simulator

Версия архитектуры: **v3** (см. `spec/spec.md` → Version History).

- **v0** — оригинальный [Schweigi/assembler-simulator](https://github.com/Schweigi/assembler-simulator): JS/AngularJS, 256 байт памяти, без спецификации.
- **v1** — 64 KB (256 страниц × 256 байт), регистр DP, формальная спецификация + TLA+ верификация, cost model, FAULT state machine, Python-реализация + MCP.
- **v2** — IEEE 754 FPU coprocessor (float32/float16/bfloat16/OFP8), 35 FP-опкодов, FPM-кодирование, FPCR/FPSR, sticky exceptions (no traps), 7 кодов ошибок.
- **v3** — текущая: async Vector Unit (VU) coprocessor, 21 VU-опкод, VFM-кодирование, 7 форматов (5 FP + UINT8/INT8), 9 кодов ошибок.

Проект **spec-driven**: поведение симулятора должно соответствовать `spec/`, а изменения — подтверждаться тестами (TLA+ и/или Python).

Каноническая конфигурация Claude Code для репозитория лежит в `.claude/`:

- `.claude/rules/` — модульные правила по темам (загружаются автоматически)
- `.claude/agents/` — субагенты с отдельными промптами/ограничениями (каждый под свою роль)
- `.claude/settings.local.json` — локальные/машинозависимые настройки

## Структура репозитория

- `spec/` — спецификация (ISA, opcodes, faults, memory, uarch, tests)
- `formal/tla/` — TLA+ модель + тесты TLC
- `pysim8/` — Python-реализация: ассемблер, симулятор, дизассемблер, TUI
- `mcp/` — MCP-сервер (fastmcp) для интеграции с Claude Code / Claude Desktop
- `assembler-simulator/` — старый веб-симулятор (v0, справочно)

## Быстрые команды

### TLA+ / Formal

```bash
cd formal/tla

export JAVA_HOME=/opt/homebrew/opt/openjdk   # brew install openjdk

make test
make test-full
make test_basic
make clean
```

### Python (pysim8)

```bash
cd pysim8
uv run pytest                          # тесты
uv run ruff check src/                 # линтер
uv run ruff format src/                # автоформат
uv run mypy src/                       # проверка типов
uv run pysim8-asm prog.asm             # ассемблер → prog.bin
uv run pysim8 prog.bin                 # TUI-симулятор (space/n/q)
uv run pysim8 --headless prog.bin      # headless: вывод I/O + state + FPU
uv run pysim8 --paused prog.bin        # TUI, старт на паузе
uv run pysim8-disasm prog.bin          # дизассемблер
```

Архитектура по умолчанию: `--arch 2` (FPU). Симулятор принимает только `.bin`.

### Web (sim8-web)

```bash
cd web
npm test                               # vitest
npm run build                          # esbuild → dist/sim.bundle.js
npm run lint                           # eslint + stylelint + htmlhint
npm run format                         # prettier (JS/CSS/HTML)
npm run format:check                   # проверка без записи
```

**ВАЖНО:** после любых изменений в `web/lib/` или `web/src/` необходимо пересобрать bundle командой `npm run build` (из `web/`).

### MCP-сервер

```bash
cd mcp
uv sync                    # установить зависимости
uv run pytest              # тесты сервера

# Запуск
uv run fastmcp run src/sim8_mcp/server.py:mcp

# Отладка (веб-интерфейс)
uv run fastmcp dev src/sim8_mcp/server.py:mcp
```

Подключение к Claude Code (из корня репозитория):

```bash
claude mcp add sim8 -- uv run --directory ./mcp fastmcp run src/sim8_mcp/server.py:mcp
```

MCP предоставляет 7 инструментов: `assemble_source`, `run_program`, `run_binary`, `disassemble`, `get_spec`, `search_spec`, `describe_instr`. Подробнее: `mcp/README.md`.

## Sentrux (структурное здоровье кода)

Любые изменения в проекте должны проходить проверку через Sentrux — в дополнение к formatter и linter.

**Обязательный порядок:**

1. `session_start` — зафиксировать baseline перед началом работы.
2. Внести изменения, прогнать тесты/линтер/форматтер.
3. `session_end` — сравнить с baseline: quality signal не должен деградировать.

Если `session_end` показывает деградацию — разобраться в причинах (`health`, `dsm`) и исправить до коммита.

**Доступные инструменты Sentrux:**

- `scan` — первичное сканирование директории
- `session_start` / `session_end` — замер до/после изменений
- `health` — quality signal (0–1) с разбивкой по причинам (modularity, acyclicity, depth, equality, redundancy)
- `dsm` — матрица зависимостей (кластеры, циклы, инверсии)
- `check_rules` — проверка архитектурных ограничений (`.sentrux/rules.toml`)
- `test_gaps` — файлы без тестового покрытия
- `git_stats` — churn, hotspots, bus factor

## Как работать (вкратце)

- Сначала зафиксировать требование в терминах перехода состояния (pre/step/post/fault).
- Затем синхронизировать: `spec/` → `formal/` → реализация → тесты.
- Всегда давать способ верификации: `make test` (в `formal/tla/`) и/или `uv run pytest` (в `pysim8/`).
- Всегда проверять структурное здоровье через Sentrux (`session_start` → изменения → `session_end`).

Подробные правила разбиты по темам в `.claude/rules/`.

## Локальные переопределения

Для приватных предпочтений, которые не должны попадать в git, использовать `CLAUDE.local.md`.

Примечание: держим **ровно один** project memory файл (этот), чтобы Claude не загружал дублирующиеся инструкции.
