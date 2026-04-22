# General coding rules

## Development philosophy

- Keep changes minimal and task-focused.
- Prefer clarity over cleverness.
- Fix root causes, not symptoms.
- Always provide a way to verify (tests/commands).

## Practices

- Use early returns to avoid deep nesting.
- Use descriptive names.
- Avoid duplication (DRY), but don’t over-abstract.
- Keep core logic clean; push I/O and integration to the edges.

## Linter / static analysis

- **Never suppress a check** (`eslint-disable`, `# noqa`, `@ts-ignore`, knip `exclude`, etc.) to make a warning go away.
  Fix the underlying issue instead. If a rule genuinely doesn’t apply, document *why* before touching config.
- Lint config changes (`.eslintrc`, `knip.json`, `pyproject.toml`, etc.) require the same justification as code changes.

## Naming conventions (project-wide)

- Use `instr` everywhere — never the abbreviation `insn`.
- Instruction definition class/type: `InstrDef` (not `InsnDef`, not `OpDef`).
- Instance field: `_instr_def` (Python) / `_instrDef` (JS).
- Tests: use `@pytest.mark.parametrize` with `pytest.param(..., id=...)` for table-driven cases.

## Git hygiene

- Never mention `co-authored-by` or similar commit metadata in messages/PR text.
