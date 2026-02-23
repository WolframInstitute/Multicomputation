# FromLinkedHypergraph Empty String Fix

## Problem

`FromLinkedHypergraph[{}, "String"]` returned unevaluated when given an empty linked hypergraph (produced by deletion rules like `"AA" -> ""`).

### Root Cause

Pattern matching order in `LinkedHypergraph.m`:

```wolfram
(* Line 259: matches {} via {_List...} with zero items → Select → {} *)
FromLinkedHypergraph[hg : {_List...}, ...] := FromLinkedHypergraph[Select[hg, Length[#] > 1 &], ...]

(* Line 261: {} does NOT match {{_, _, ___} ...} — needs 3+ element sublists *)
FromLinkedHypergraph[hg : {{_, _, ___} ...}, ...] := Switch[...]
```

The `{}` output fell through both definitions — `{_List...}` matched but recursed back to `{}`, which then didn't match `{{_, _, ___}...}`.

### Fix

Added a base case BEFORE the `{_List...}` filter:

```wolfram
FromLinkedHypergraph[{}, type : _String | None : "Graph", opts : OptionsPattern[]] := Switch[type,
    "String", "",
    "List", {},
    "Expression" | "ConstructExpression" | "HoldExpression", Null,
    _, {}
]
```

### Impact

This fixes multi-step evolution of systems with deletion rules. Without the fix, states produced by deletion rules (e.g., `"AA" -> ""`) would produce garbage `DisplayForm[...]` error objects instead of empty strings, corrupting all subsequent steps.

### Affected Systems

Any rule system where a rule can delete all characters, e.g.:
- `{"AA" -> "", "BA" -> "ABB", "BB" -> "A"}` starting from `"BBA"`
- Any rule with empty RHS
