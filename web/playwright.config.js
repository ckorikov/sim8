import { defineConfig, devices } from "@playwright/test";

export default defineConfig({
    testDir: "./e2e",
    timeout: 30_000,
    use: {
        baseURL: "http://localhost:4173",
        headless: true,
    },
    projects: [{ name: "chromium", use: { ...devices["Desktop Chrome"] } }],
    webServer: {
        command: "npx serve dist -p 4173 -s --no-clipboard",
        port: 4173,
        reuseExistingServer: true,
        timeout: 15_000,
    },
});
