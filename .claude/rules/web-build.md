# Web (sim8-web) rules

## Build

After ANY modification to files in `web/lib/`, `web/src/`, or `web/css/`:

1. Run tests: `cd web && npm test`
2. Run linter: `cd web && npm run lint`
3. Rebuild bundle: `cd web && npm run build`

The bundle (`web/dist/sim.bundle.js`) is what gets served. Without rebuild, changes are invisible in the browser.

## Structure

- `web/lib/` — pure logic (ISA, assembler, CPU core, FP), no DOM
- `web/src/` — UI layer (DOM, CodeMirror, X6 wires, layout)
- `web/css/` — stylesheets (`sim.css`, `tailwind.input.css`)
- `web/tests/` — vitest unit tests (cover `lib/` only)
- `web/e2e/` — Playwright end-to-end tests
- `web/index.html`, `web/css/sim.css` — copied to `dist/` by build
- `web/dist/` — build output (deployed via GitHub Actions)

## Lint

```bash
npm run lint          # all: eslint + stylelint + htmlhint + depcruise + knip
npm run lint:arch     # dependency-cruiser: enforces lib/ → no src/ imports, no cycles
npm run lint:unused   # knip: unused exports, files, dependencies
```

**Architecture rules** (`.dependency-cruiser.js`):
- `lib/` must not import from `src/` — error
- Circular dependencies — error

## Stack

- Vanilla JS (ES modules), no framework
- esbuild bundles `src/sim.js` → IIFE `dist/sim.bundle.js`
- vitest for unit tests, Playwright for e2e
- CDN: DaisyUI, TailwindCSS, CodeMirror, @antv/x6, JetBrains Mono
