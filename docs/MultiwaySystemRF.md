# MultiwaySystem RF Compatibility

## Overview

The `MultiwaySystem` object provides compatibility with the Wolfram Language `ResourceFunction["MultiwaySystem"]` (RF). This document covers the standalone API, RF-compatible properties, and behavioral differences.

## Standalone API

The 4-argument pattern matches the RF interface:

```wolfram
(* 4-arg: property query *)
MultiwaySystem[rules, init, n, "Property"]

(* 3-arg: defaults to AllStatesList *)
MultiwaySystem[rules, init, n]
```

Both forms automatically enable `"DeduplicateSlices" -> True` to match RF behavior.

## RF-Compatible Properties

| Property | Description |
|----------|-------------|
| `"AllStatesList"` | Sorted, deduplicated states per step |
| `"StatesCountsList"` | Count of unique states per step |
| `"CausalInvariantQ"` | Confluence check via branch pair resolution |
| `"BranchPairsList"` | Sorted, deduplicated branch pairs |
| `"CanonicalBranchPairsList"` | Branch pairs from LHS overlaps (distinct rules required) |
| `"AllEventsList"` | Events with `{rule, LHS, {prefix, suffix}}` format |
| `"StatesGraph"` | States evolution graph |
| `"BranchialGraph"` | Branchial connection graph |

## DeduplicateSlices

The RF's `"AllStatesList"` deduplicates successor states within each evolution step. Our implementation does this via the `"DeduplicateSlices"` option:

- **Standalone API** (3/4-arg): Enabled automatically
- **Object API** (`ms["Property", n]`): Requires `MultiwaySystem[rules, init, "DeduplicateSlices" -> True]`
- **Raw Multi**: Requires `Multi[expr, rules, "DeduplicateSlices" -> True]`

## CausalInvariantQ Semantics

Checks if the system is **confluent** — whether all branch pairs resolve (converge) within the evolution steps:

1. Compute `BranchPairResolutionsList` up to step `n`
2. Find pairs unresolved at step `Ceiling[n/2]`
3. Check if ALL such pairs are resolved by step `n`
4. If no unresolved pairs exist → `True`

## CanonicalBranchPairsList

Generates branch pairs from LHS overlaps:
1. Compute suffix-prefix overlaps between all LHS strings
2. Include each LHS itself (may have multiple applicable rules)
3. **Filter**: Keep only strings where ≥2 *different* rules can apply
4. For each overlap string, apply all applicable rules to get branch pairs

> **Important**: Same-rule position-branching (e.g., `"AA" -> "AB"` applied at positions 1 and 2 of `"AAA"`) does NOT count as a canonical branch pair. At least two distinct rules must apply.

## AllEventsList Format

Each event is a 3-element list: `{rule, LHS, {prefix, suffix}}`

- `rule`: The applied rule (e.g., `"A" -> "ABA"`)
- `LHS`: The left-hand side that was matched (e.g., `"A"`)
- `{prefix, suffix}`: The context around the match in the parent state

## Testing

```bash
# Run RF comparison tests
wolframscript -c 'TestReport["Tests/MultiwaySystemRF-Comparison.wlt"]'
```
