/**
 * Shared UI state: which register markers are visible.
 * Toggled by clicking register labels in CPU/VU blocks.
 */

const hidden = new Set();
const listeners = [];

export function onToggle(cb) {
    listeners.push(cb);
}

function toggle(name) {
    if (hidden.has(name)) hidden.delete(name);
    else hidden.add(name);
    for (const cb of listeners) cb();
}

export function isHidden(name) {
    return hidden.has(name);
}

/** Attach click-to-toggle on .ri-l labels inside a block element. */
export function bindToggleClicks(blockId) {
    document.getElementById(blockId).addEventListener("click", (e) => {
        const label = e.target.closest(".ri-l");
        if (!label) return;
        toggle(label.textContent.trim());
    });
}
