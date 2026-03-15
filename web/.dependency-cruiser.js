/** @type {import('dependency-cruiser').IConfiguration} */
export default {
    forbidden: [
        {
            name: "lib-no-src",
            comment: "lib/ is pure logic — must not import from src/ (UI layer)",
            severity: "error",
            from: { path: "^lib/" },
            to: { path: "^src/" },
        },
        {
            name: "no-circular",
            comment: "Circular dependencies are forbidden",
            severity: "error",
            from: {},
            to: { circular: true },
        },
        {
            name: "no-orphans",
            comment: "Every file must be reachable from an entry point",
            severity: "warn",
            from: { orphan: true, pathNot: ["\\.test\\.js$"] },
            to: {},
        },
    ],
    options: {
        doNotFollow: { path: "node_modules" },
        tsPreCompilationDeps: false,
        reporterOptions: {
            text: { highlightFocused: true },
        },
    },
};
