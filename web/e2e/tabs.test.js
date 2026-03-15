import { test, expect } from "@playwright/test";

// ── Helpers ──────────────────────────────────────────────────────

async function clearAndReload(page) {
    await page.goto("/");
    await page.evaluate(() => localStorage.clear());
    await page.reload();
}

async function getTabNames(page) {
    return page.locator("#tab-bar .tab-btn").evaluateAll((tabs) => tabs.map((t) => t.dataset.file));
}

async function getActiveTabName(page) {
    return page.locator("#tab-bar .tab-btn.active").getAttribute("data-file");
}

async function getEditorText(page) {
    return page.locator(".cm-content").innerText();
}

async function setEditorText(page, text) {
    const editor = page.locator(".cm-content");
    await editor.click();
    await page.keyboard.press("ControlOrMeta+A");
    await page.keyboard.type(text);
}

/**
 * Add a new tab via + button, then confirm with given name via inline input.
 * The tab appears with a default name; we clear and type our desired name, then press Enter.
 */
async function addTab(page, name) {
    await page.locator("#tab-bar .tab-add").click();
    // Inline input appears focused with default name selected
    const input = page.locator("#tab-bar .tab-name-input");
    await expect(input).toBeVisible();
    await input.fill(name);
    await input.press("Enter");
    // Wait for the tab to appear
    await expect(page.locator(`#tab-bar .tab-btn[data-file="${name}"]`)).toBeVisible();
}

// ── Initial state ─────────────────────────────────────────────────

test.describe("tabs — initial state", () => {
    test.beforeEach(async ({ page }) => {
        await clearAndReload(page);
    });

    test("single tab main.asm exists on load", async ({ page }) => {
        const tabs = await getTabNames(page);
        expect(tabs).toContain("main.asm");
        expect(tabs).toHaveLength(1);
    });

    test("main.asm is active on load", async ({ page }) => {
        const active = await getActiveTabName(page);
        expect(active).toBe("main.asm");
    });

    test("editor has content on load", async ({ page }) => {
        const text = await getEditorText(page);
        expect(text.trim()).not.toBe("");
    });
});

// ── Add and switch ────────────────────────────────────────────────

test.describe("tabs — add and switch", () => {
    test.beforeEach(async ({ page }) => {
        await clearAndReload(page);
    });

    test("add new tab via + button with inline name", async ({ page }) => {
        await addTab(page, "lib/io.asm");
        const tabs = await getTabNames(page);
        expect(tabs).toContain("lib/io.asm");
    });

    test("default name shown in inline input on add", async ({ page }) => {
        await page.locator("#tab-bar .tab-add").click();
        const input = page.locator("#tab-bar .tab-name-input");
        await expect(input).toBeVisible();
        const val = await input.inputValue();
        expect(val).toMatch(/New File \d+\.asm/);
        await input.press("Escape"); // cancel
    });

    test("Escape cancels new tab creation", async ({ page }) => {
        const before = await getTabNames(page);
        await page.locator("#tab-bar .tab-add").click();
        await page.locator("#tab-bar .tab-name-input").press("Escape");
        const after = await getTabNames(page);
        expect(after).toHaveLength(before.length);
    });

    test("switching tabs preserves content", async ({ page }) => {
        await addTab(page, "lib/io.asm");

        await setEditorText(page, "print: RET");

        await page.locator('#tab-bar .tab-btn[data-file="main.asm"]').click();
        await page.locator('#tab-bar .tab-btn[data-file="lib/io.asm"]').click();

        const text = await getEditorText(page);
        expect(text).toContain("print: RET");
    });

    test("double-click renames existing non-main tab", async ({ page }) => {
        await addTab(page, "utils.asm");
        await page.locator('#tab-bar .tab-btn[data-file="utils.asm"]').dblclick();
        const input = page.locator("#tab-bar .tab-name-input");
        await expect(input).toBeVisible();
        await input.fill("helpers.asm");
        await input.press("Enter");
        const tabs = await getTabNames(page);
        expect(tabs).toContain("helpers.asm");
        expect(tabs).not.toContain("utils.asm");
    });

    test("main.asm has no close button", async ({ page }) => {
        const closeBtn = page.locator('#tab-bar .tab-btn[data-file="main.asm"] .tab-close');
        await expect(closeBtn).toHaveCount(0);
    });
});

// ── Close ─────────────────────────────────────────────────────────

test.describe("tabs — close", () => {
    test.beforeEach(async ({ page }) => {
        await clearAndReload(page);
        await addTab(page, "lib/io.asm");
    });

    test("close non-main tab removes it", async ({ page }) => {
        await page.locator('#tab-bar .tab-btn[data-file="lib/io.asm"] .tab-close').click();
        const tabs = await getTabNames(page);
        expect(tabs).not.toContain("lib/io.asm");
        expect(tabs).toContain("main.asm");
    });

    test("after closing active tab, another tab becomes active", async ({ page }) => {
        await page.locator('#tab-bar .tab-btn[data-file="lib/io.asm"]').click();
        await page.locator('#tab-bar .tab-btn[data-file="lib/io.asm"] .tab-close').click();
        const active = await getActiveTabName(page);
        expect(active).toBe("main.asm");
    });
});

// ── Assembly with @include ────────────────────────────────────────

test.describe("tabs — assembly with @include", () => {
    test.beforeEach(async ({ page }) => {
        await clearAndReload(page);
    });

    test("assemble with @include resolves virtual file", async ({ page }) => {
        await addTab(page, "lib/print.asm");
        await setEditorText(page, "print: RET");

        await page.locator('#tab-bar .tab-btn[data-file="main.asm"]').click();
        await setEditorText(page, 'JMP start\nstart: CALL print\nHLT\n@include "lib/print.asm"');

        await page.locator("#btn-assemble").click();

        await expect(page.locator("#asm-error")).toBeHidden();
    });

    test("assemble with missing @include shows error", async ({ page }) => {
        await setEditorText(page, '@include "missing.asm"');
        await page.locator("#btn-assemble").click();

        const errEl = page.locator("#asm-error");
        await expect(errEl).toBeVisible();
        await expect(errEl).toContainText("file not found");
    });
});

// ── Persistence ───────────────────────────────────────────────────

test.describe("tabs — persistence", () => {
    test("tabs survive page reload", async ({ page }) => {
        await clearAndReload(page);
        await addTab(page, "lib/io.asm");

        await page.reload();

        const tabs = await getTabNames(page);
        expect(tabs).toContain("lib/io.asm");
        expect(tabs).toContain("main.asm");
    });
});
