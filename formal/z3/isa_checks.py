"""ISA.json data consistency checks (D1–D17)."""

from __future__ import annotations

from typing import Any

from harness import check

# ── ISA constants (mirrors pysim8/src/pysim8/constants.py) ────────────────────

FP_FMT_MAX_POS = {0: 0, 1: 1, 2: 1, 3: 3, 4: 3, 5: 7, 6: 7}
FP_FMT_WIDTH = {0: 32, 1: 16, 2: 16, 3: 8, 4: 8, 5: 4, 6: 4}
VU_FMT_ELEM_SIZE = {0: 4, 1: 2, 2: 2, 3: 1, 4: 1, 5: 1, 6: 1}

_OP_BYTES = {"fp_imm16": 2}

_KNOWN_OPERAND_TYPES = frozenset(
    {
        "reg",
        "reg_arith",
        "reg_gpr",
        "reg_stack",
        "imm",
        "mem",
        "regaddr",
        "fp_reg",
        "fp_imm8",
        "fp_imm16",
    }
)

# Sync VU instruction -> expected operand list (spec/vector.md)
_VU_SYNC_OPERANDS: dict[str, list[str]] = {
    "VFCLR": [],
    "VWAIT": [],
    "VFSTAT": ["imm"],
    "VSET_GPR": ["imm", "imm"],
    "VSET_MEM": ["imm", "imm"],
    "VSET_MEMI": ["imm", "imm"],
    "VSET_IMM16": ["imm", "fp_imm16"],
}


def _encode_fpm(r: dict[str, int]) -> int:
    return (r["phys"] << 6) | (r["pos"] << 3) | r["fmt"]


def _isize(i: dict[str, Any]) -> int:
    return 1 + sum(_OP_BYTES.get(op, 1) for op in i["operands"])


def verify(isa: dict[str, Any]) -> None:
    print("ISA.json data consistency")

    core = isa["instructions"]
    fp = isa["instructions_fp"]
    vu = isa["instructions_vu"]

    all_opcodes = [i["opcode"] for i in core + fp + vu]

    # D1 — opcode uniqueness
    check(
        len(set(all_opcodes)) == len(all_opcodes),
        f"D1: all {len(all_opcodes)} opcodes are unique",
    )

    # D2 — opcode ranges
    core_ops = [i["opcode"] for i in core]
    fp_ops = [i["opcode"] for i in fp]
    vu_ops = [i["opcode"] for i in vu]
    check(
        max(core_ops) <= 127 and min(core_ops) == 0,
        f"D2: core opcodes in 0-127 (got {min(core_ops)}-{max(core_ops)})",
    )
    check(
        min(fp_ops) == 128 and max(fp_ops) <= 162,
        f"D2: FP opcodes in 128-162 (got {min(fp_ops)}-{max(fp_ops)})",
    )
    check(
        min(vu_ops) == 163 and max(vu_ops) <= 183,
        f"D2: VU opcodes in 163-183 (got {min(vu_ops)}-{max(vu_ops)})",
    )
    check(min(fp_ops) > max(core_ops), "D2: no overlap between core and FP ranges")
    check(min(vu_ops) > max(fp_ops), "D2: no overlap between FP and VU ranges")

    # D3 — VU format codes
    vu_fmt_codes = [f["code"] for f in isa["vu_formats"]]
    check(vu_fmt_codes == list(range(7)), "D3: VU format codes are 0-6 in order")

    # D4 — VU mode codes
    vu_mode_codes = [m["code"] for m in isa["vu_modes"]]
    check(vu_mode_codes == list(range(4)), "D4: VU mode codes are 0-3 in order")

    # D5 — VU condition codes
    vu_cond_codes = [c["code"] for c in isa["vu_conditions"]]
    check(vu_cond_codes == list(range(6)), "D5: VU condition codes are 0-5 in order")

    # D6 — FP register FPM bytes are distinct
    reg_bytes = [_encode_fpm(r) for r in isa["fp_registers"]]
    check(
        len(set(reg_bytes)) == len(reg_bytes),
        f"D6: {len(isa['fp_registers'])} named FP registers have distinct FPM bytes",
    )

    # D7 — FP register (pos, fmt) validity per FP_FMT_MAX_POS
    invalid_regs = [
        r["name"] for r in isa["fp_registers"] if r["fmt"] in FP_FMT_MAX_POS and r["pos"] > FP_FMT_MAX_POS[r["fmt"]]
    ]
    check(
        len(invalid_regs) == 0,
        f"D7: all FP register positions valid for their format (violations: {invalid_regs})",
    )

    # D8 — FP format widths match constants
    mismatches = [
        f"{f['suffix']}(code={f['code']}): isa.json={f['width']}, constants={FP_FMT_WIDTH[f['code']]}"
        for f in isa["fp_formats"]
        if f["code"] in FP_FMT_WIDTH and f["width"] != FP_FMT_WIDTH[f["code"]]
    ]
    check(len(mismatches) == 0, f"D8: FP format widths match constants ({mismatches})")

    # D9 — VU elem_size matches constants
    mismatches = [
        f"{f['suffix']}(code={f['code']}): isa.json={f['elem_size']}, constants={VU_FMT_ELEM_SIZE[f['code']]}"
        for f in isa["vu_formats"]
        if f["code"] in VU_FMT_ELEM_SIZE and f["elem_size"] != VU_FMT_ELEM_SIZE[f["code"]]
    ]
    check(len(mismatches) == 0, f"D9: VU elem_size values match constants ({mismatches})")

    # D10 — instruction size in [1,4]
    size_errors = [f"{i['op']}: size={_isize(i)}" for i in core + fp + vu if not (1 <= _isize(i) <= 4)]
    check(len(size_errors) == 0, f"D10: all instruction sizes in [1,4] ({size_errors})")

    # D11 — exactly 7 sync VU instructions
    sync_ops = {i["op"] for i in vu if i.get("sync", False)}
    check(
        len(sync_ops) == 7,
        f"D11: exactly 7 sync VU instructions; got {len(sync_ops)}: {sync_ops}",
    )

    # D12 — FP format metadata consistency
    fp_fmt_codes = [f["code"] for f in isa["fp_formats"]]
    check(fp_fmt_codes == list(range(7)), "D12: FP format codes are 0-6 in order")
    fp_fmt_max_pos_mismatches = [
        f"{f['suffix']}(code={f['code']}): isa.json={f['max_pos']}, constants={FP_FMT_MAX_POS[f['code']]}"
        for f in isa["fp_formats"]
        if f["code"] in FP_FMT_MAX_POS and f["max_pos"] != FP_FMT_MAX_POS[f["code"]]
    ]
    check(
        len(fp_fmt_max_pos_mismatches) == 0,
        f"D12: FP format max_pos matches constants ({fp_fmt_max_pos_mismatches})",
    )

    # D13 — since field
    bad_since_core = [i["op"] for i in core if i.get("since") != 1]
    bad_since_fp = [i["op"] for i in fp if i.get("since") != 2]
    bad_since_vu = [i["op"] for i in vu if i.get("since") != 3]
    check(
        len(bad_since_core) == 0,
        f"D13: all core instructions have since=1 (violations: {bad_since_core})",
    )
    check(
        len(bad_since_fp) == 0,
        f"D13: all FP instructions have since=2 (violations: {bad_since_fp})",
    )
    check(
        len(bad_since_vu) == 0,
        f"D13: all VU instructions have since=3 (violations: {bad_since_vu})",
    )

    # D14 — all operand types from the known set
    unknown_ops: list[str] = []
    for i in core + fp + vu:
        for op in i["operands"]:
            if op not in _KNOWN_OPERAND_TYPES:
                unknown_ops.append(f"{i['op']}.{op}")
    check(
        len(unknown_ops) == 0,
        f"D14: all operand types from known set (unknown: {unknown_ops})",
    )

    # D15 — all instruction costs >= 0
    neg_costs = [f"{i['op']}(cost={i['cost']})" for i in core + fp + vu if i["cost"] < 0]
    check(len(neg_costs) == 0, f"D15: all costs ≥ 0 ({neg_costs})")

    # D16 — VU operand structure
    bad_vcmp = [i["op"] for i in vu if i["op"] == "VCMP" and i["operands"] != ["imm", "imm", "imm"]]
    check(
        len(bad_vcmp) == 0,
        f"D16: VCMP has exactly 3 imm operands (violations: {bad_vcmp})",
    )
    bad_async = [
        i["op"] for i in vu if not i.get("sync", False) and i["op"] != "VCMP" and i["operands"] != ["imm", "imm"]
    ]
    check(
        len(bad_async) == 0,
        f"D16: async non-VCMP VU ops have exactly 2 imm operands (violations: {bad_async})",
    )
    bad_sync = [
        f"{i['op']}: got {i['operands']}, expected {_VU_SYNC_OPERANDS[i['op']]}"
        for i in vu
        if i.get("sync", False) and i["operands"] != _VU_SYNC_OPERANDS.get(i["op"])
    ]
    check(
        len(bad_sync) == 0,
        f"D16: sync VU operand structure correct (violations: {bad_sync})",
    )

    # D17 — mnemonic aliases resolve to existing mnemonics
    all_mnemonics = {i["mnemonic"] for i in core + fp + vu}
    bad_aliases = [
        f"{alias}→{target}" for alias, target in isa["mnemonic_aliases"].items() if target not in all_mnemonics
    ]
    check(
        len(bad_aliases) == 0,
        f"D17: all alias targets are known mnemonics (broken: {bad_aliases})",
    )
    print()
