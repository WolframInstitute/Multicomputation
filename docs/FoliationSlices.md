# FoliationSlices Property

## Overview

`"FoliationSlices"` (formerly `"Foliations"`) computes layer-by-layer evolution of a `Multi` object, returning the set of new states produced at each step along with cumulative state counts.

## Usage

```wolfram
multi["FoliationSlices", steps]
multi["FoliationSlices", steps, level]
multi["FoliationSlices", steps, level, f]
```

### Arguments

| Argument | Default | Description |
|----------|---------|-------------|
| `steps` | 1 | Number of evolution steps |
| `level` | 2 | Pattern match depth level |
| `f` | `Identity` | Optional transformation applied to each output state |

### Return Value

`{foliationList, countsAssociation}` where:
- `foliationList` — NestList of `{holdMulti, eventOutputs}` pairs (one per step)
- `countsAssociation` — cumulative `Counts` of all states seen across steps

## DeduplicateSlices Option

When `"DeduplicateSlices" -> True` is set in the Multi's `ExtraOptions`, successor states within each step are flattened and deduplicated before counting. This prevents the same state from being counted multiple times when reachable from different parent states.

### Default Behavior (DeduplicateSlices -> False)

Each parent state's successors are kept as separate groups. If state `X` is reachable from parents `A` and `B`, it appears in both groups and may be counted twice.

### Deduplicated Behavior (DeduplicateSlices -> True)

All successor states from all parents are merged into a single flat list and deduplicated. State `X` appears only once regardless of how many parents produce it.

### Setting the Option

The option flows through the standard options pipeline:

```wolfram
(* Via MultiwaySystem — forwarded through Method sub-options *)
MultiwaySystem[rules, init, "DeduplicateSlices" -> True]

(* Via Multi constructor — goes to ExtraOptions automatically *)
Multi[expr, rules, "DeduplicateSlices" -> True]

(* Enabled automatically in RF standalone API *)
MultiwaySystem[rules, init, n, "AllStatesList"]  (* DeduplicateSlices -> True *)
```

### Option Flow

```
MultiwaySystem[rules, init, "DeduplicateSlices" -> True]
  → MultiwaySystem constructor (MultiwaySystem.m)
    → FilterRules[{opts}, Except[Method]] merged into methodOpts
      → StringMulti[init, rules, methodOpts] (LinkedHypergraph.m)
        → Multi[..., opts, ...] (Multi.m)
          → ExtraOptions: {"DeduplicateSlices" -> True}
            → FoliationSlices reads: "DeduplicateSlices" /. multi["ExtraOptions"]
```

## Related Properties

- `"HoldFoliationSlices"` — same as `"FoliationSlices"` but with held expressions
- `"AllStatesList"` — uses FoliationSlices internally (in RF mode)
- `"StatesCountsList"` — derived from FoliationSlices state counts

## Migration from Foliations

The property was renamed from `"Foliations"` to `"FoliationSlices"`. Update any code using the old name:

```diff
-multi["Foliations", n]
+multi["FoliationSlices", n]
```
