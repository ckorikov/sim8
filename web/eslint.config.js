import js from "@eslint/js";

export default [
    js.configs.recommended,
    {
        languageOptions: {
            ecmaVersion: 2022,
            sourceType: "module",
            globals: {
                // Browser
                console: "readonly",
                document: "readonly",
                window: "readonly",
                performance: "readonly",
                URL: "readonly",
                URLSearchParams: "readonly",
                fetch: "readonly",
                setTimeout: "readonly",
                clearTimeout: "readonly",
                requestAnimationFrame: "readonly",
                getComputedStyle: "readonly",
                localStorage: "readonly",
                TextDecoder: "readonly",
                TextEncoder: "readonly",
                CSS: "readonly",
                // CDN libs
                X6: "readonly",
            },
        },
        rules: {
            "no-unused-vars": ["error", { argsIgnorePattern: "^_" }],
            "no-undef": "error",
        },
    },
    {
        files: ["tests/**/*.js"],
        languageOptions: {
            globals: {
                describe: "readonly",
                it: "readonly",
                test: "readonly",
                expect: "readonly",
                beforeEach: "readonly",
                afterEach: "readonly",
                beforeAll: "readonly",
                afterAll: "readonly",
            },
        },
    },
];
