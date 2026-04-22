# Python rules

## Package management

- ONLY use `uv`, NEVER `pip`.
- Install: `uv add package`
- Run tools/tests: `uv run <tool>`
- Upgrade: `uv add --dev package --upgrade-package package`
- FORBIDDEN: `uv pip install`, `@latest` syntax

## Code quality

- Type hints required for all code
- Public APIs must have docstrings
- Keep functions small and focused
- Follow existing patterns
- Line length: 88 chars

## Testing

- `uv run pytest`
- Bug fixes require regression tests
- New features require tests and edge cases
