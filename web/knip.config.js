/** @type {import('knip').KnipConfig} */
export default {
    // CSS files are used by the build script and index.html, not via JS imports
    ignoreExportsUsedInFile: true,
    ignore: ["css/**"],
    ignoreDependencies: ["puppeteer-core"],
};
