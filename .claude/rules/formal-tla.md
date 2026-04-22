# Formal / TLA+

## Что проверяется

TLA+ модель в `formal/tla/` является исполняемой спецификацией. При изменении семантики CPU/ISA важно держать её в синхронизации со `spec/`.

## Команды

```bash
cd formal/tla

# Все тесты (кратко)
make test

# Все тесты (подробно)
make test-full

# Одиночный тест
make test_basic
make test_adversarial

# Очистка артефактов TLC
make clean
```

## Структура

- `formal/tla/cpu_base.tla` — базовые определения/константы/хелперы
- `formal/tla/cpu_core.tla` — машина состояний CPU (IDLE → RUNNING → HALTED/FAULT)
- `formal/tla/cpu_ops_*.tla` — семантика операций (ALU/stack/jump/mem/bit/...)
- `formal/tla/tests/` — тест-спеки и конфиги

## Требования окружения

- Java (OpenJDK)
- `tla2tools.jar` в `formal/tla/`
