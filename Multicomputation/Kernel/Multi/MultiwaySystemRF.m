Package["Wolfram`Multicomputation`"]

PackageImport["Wolfram`MulticomputationInit`"]

PackageScope["MultiwaySystemProp"]

(* ============================================================================
   MultiwaySystemRF: ResourceFunction-compatible properties for MultiwaySystem
   
   Adds MultiwaySystemProp definitions for RF-style properties:
     "AllStatesList", "StatesCountsList", "CausalInvariantQ",
     "BranchPairsList", "CanonicalBranchPairsList",
     "TotalCausalInvariantQ", "CanonicalKnuthBendixCompletion"
   
   Uses FoliationSlices with DeduplicateSlices to extract states
   from the existing Multi object.
   ============================================================================ *)


(* ---------- Internal helpers ---------- *)

(* Extract deduplicated states per step from FoliationSlices *)
rfFoliationStates[m_, n_Integer] := Module[{
    multi = m["Multi"], type = m["Type"],
    fols, statesPerStep
},
    fols = multi["FoliationSlices", n];
    statesPerStep = Table[
        Sort @ DeleteDuplicates[
            (If[type === "CA", Normal, Identity] @ FromLinkedHypergraph[#, type]) & /@ ReleaseHold[fols[[1, i, 1]]]["Expression"]
        ],
        {i, Length[fols[[1]]]}
    ];
    statesPerStep
]


(* String successors for branch pair analysis *)
rfStringSuccessors[state_String, rules : {(_String -> _String) ..}] :=
    DeleteDuplicates[Catenate[StringReplaceList[state, #] & /@ rules]]

rfListSuccessors[state_List, rules : {(_List -> _List) ..}] :=
    DeleteDuplicates[Catenate[
        Function[rule,
            With[{positions = SequencePosition[state, First[rule]]},
                (Join[Take[state, First[#] - 1], Last[rule], Drop[state, Last[#]]]) & /@ positions
            ]
        ] /@ rules
    ]]


(* Get overlaps between left-hand sides for canonical branch pairs *)
rfGetOverlaps[lhsList : {__String}, rules_] := Module[{overlaps = {}, multiRuleQ},
    (* Suffix-prefix overlaps between all pairs *)
    Do[Do[Do[
        If[StringLength[lhs1] >= k && StringLength[lhs2] >= k &&
           StringTake[lhs1, -k] === StringTake[lhs2, k],
            AppendTo[overlaps, StringJoin[lhs1, StringDrop[lhs2, k]]]
        ], {k, 1, Min[StringLength[lhs1], StringLength[lhs2]] - 1}
    ], {lhs2, lhsList}], {lhs1, lhsList}];
    (* Also include each LHS itself — it may have multiple applicable rules *)
    overlaps = Join[overlaps, lhsList];
    (* Filter: keep only strings where at least 2 DIFFERENT rules can apply.
       Same-rule position-branching (e.g., AA->AB applied at pos 1 and 2 of AAA) 
       does NOT count as a canonical branch pair. *)
    multiRuleQ[s_] := Length[Select[rules, StringContainsQ[s, First[#]] &]] >= 2;
    DeleteDuplicates[Select[overlaps, multiRuleQ]]
]

rfCanonicalBranchPairsList[rules : {(_String -> _String) ..}, opts___] := Module[{
    lhsList = First /@ rules, overlaps, branchPairs,
    includeSelf = TrueQ[Lookup[{opts}, "IncludeSelfPairs", False]]
},
    overlaps = rfGetOverlaps[lhsList, rules];
    branchPairs = Catenate[
        Module[{results = DeleteDuplicates[StringReplaceList[#, rules]]},
            If[includeSelf, Tuples[results, 2], Select[Subsets[results, {2}], Apply[UnsameQ]]]
        ] & /@ overlaps
    ];
    Union[Sort /@ branchPairs]
]

rfConvergesQ[rules_, s1_String, s2_String, maxSteps_Integer] := Module[{
    states1 = {s1}, states2 = {s2}
},
    Do[
        states1 = DeleteDuplicates[Catenate[rfStringSuccessors[#, rules] & /@ states1]];
        states2 = DeleteDuplicates[Catenate[rfStringSuccessors[#, rules] & /@ states2]];
        If[Intersection[states1, states2] =!= {}, Return[True, Module]];
        If[states1 === {} || states2 === {}, Return[False, Module]],
        {maxSteps}
    ];
    False
]

(* Extract original rules from the Multi expression *)
rfExtractRules[m_] := Module[{multi = m["Multi"], type = m["Type"]},
    Switch[type,
        "String",
        Cases[multi["Rules"], HoldPattern[_ :> ApplyStringRules[_, rules_]] :> rules][[1]],
        _,
        $Failed
    ]
]


(* ============================================================================
   MultiwaySystemProp definitions
   ============================================================================ *)

(* AllStatesList *)
MultiwaySystemProp[m_, "AllStatesList", n : _Integer ? Positive : 1, opts___] :=
    rfFoliationStates[m, n]

(* StatesCountsList *)
MultiwaySystemProp[m_, "StatesCountsList", n : _Integer ? Positive : 1, opts___] :=
    Length /@ rfFoliationStates[m, n]

(* CausalInvariantQ — checks that all branch pairs unresolved at Ceiling[n/2] are resolved by step n *)
MultiwaySystemProp[m_, "CausalInvariantQ", n : _Integer ? Positive : 5, opts___] := Module[{
    unresolvedHalf, resolvedFull
},
    unresolvedHalf = Sort /@ MultiwaySystemProp[m, "BranchPairResolutionsList", Ceiling[n / 2], opts]["Unresolved"];
    resolvedFull = Sort /@ MultiwaySystemProp[m, "BranchPairResolutionsList", n, opts]["Resolved"];
    Length[Complement[unresolvedHalf, resolvedFull]] == 0
]

(* BranchPairsList *)
MultiwaySystemProp[m_, "BranchPairsList", n : _Integer ? Positive : 1, opts___] := Module[{
    rules = rfExtractRules[m], statesLists, fn,
    givePredecessors = TrueQ[Lookup[{opts}, "GivePredecessors", False]]
},
    If[rules === $Failed, Return[$Failed]];
    statesLists = rfFoliationStates[m, n];
    fn = Function[state, rfStringSuccessors[state, rules]];

    DeleteDuplicates[Sort /@ Catenate[
        Function[state, Module[{succs = fn[state]},
            If[Length[succs] >= 2,
                If[givePredecessors, (state -> #) & /@ Subsets[succs, {2}], Subsets[succs, {2}]],
                {}
            ]
        ]] /@ Catenate[Most[statesLists]]
    ]]
]

(* CanonicalBranchPairsList *)
MultiwaySystemProp[m_, "CanonicalBranchPairsList", opts___] := Module[{rules = rfExtractRules[m]},
    If[rules === $Failed || !MatchQ[rules, {(_String -> _String) ..}], Return[$Failed]];
    rfCanonicalBranchPairsList[rules, opts]
]

(* TotalCausalInvariantQ *)
MultiwaySystemProp[m_, "TotalCausalInvariantQ", n : _Integer ? Positive : 10, opts___] := Module[{
    rules = rfExtractRules[m], canonicalPairs
},
    If[rules === $Failed || !MatchQ[rules, {(_String -> _String) ..}], Return[$Failed]];
    canonicalPairs = rfCanonicalBranchPairsList[rules, opts];
    AllTrue[canonicalPairs, rfConvergesQ[rules, #[[1]], #[[2]], n] &]
]

(* CanonicalKnuthBendixCompletion *)
MultiwaySystemProp[m_, "CanonicalKnuthBendixCompletion", opts___] := Module[{
    rules = rfExtractRules[m], canonicalPairs
},
    If[rules === $Failed || !MatchQ[rules, {(_String -> _String) ..}], Return[$Failed]];
    canonicalPairs = rfCanonicalBranchPairsList[rules, opts];
    Catenate[{First[#] -> Last[#], Last[#] -> First[#]} & /@ canonicalPairs]
]

(* AllEventsList *)
MultiwaySystemProp[m_, "AllEventsList", n : _Integer ? Positive : 1, opts___] := Module[{
    rules = rfExtractRules[m], type = m["Type"],
    statesLists, eventFn, allEvents
},
    If[rules === $Failed, Return[$Failed]];
    statesLists = rfFoliationStates[m, n];

    eventFn = Switch[type,
        "String",
        Function[{state, rs},
            Catenate[Function[rule,
                {rule, First[rule], {StringTake[state, First[#] - 1], StringDrop[state, Last[#]]}} & /@
                    StringPosition[state, First[rule]]
            ] /@ rs]
        ],
        _,
        Return[$Failed]
    ];

    allEvents = Table[
        Catenate[eventFn[#, rules] & /@ statesLists[[step]]],
        {step, 1, Min[n, Length[statesLists] - 1]}
    ];
    allEvents
]

(* BranchPairResolutionsList *)
MultiwaySystemProp[m_, "BranchPairResolutionsList", n : _Integer ? Positive : 1, opts___] := Module[{
    rules = rfExtractRules[m],
    branchPairs, resolved, unresolved,
    giveResolvents = TrueQ[Lookup[{opts}, "GiveResolvents", False]]
},
    If[rules === $Failed || !MatchQ[rules, {(_String -> _String) ..}], Return[$Failed]];
    branchPairs = MultiwaySystemProp[m, "BranchPairsList", n, opts];
    If[FailureQ[branchPairs], Return[$Failed]];

    resolved = Select[branchPairs, rfConvergesQ[rules, #[[1]], #[[2]], n] &];
    unresolved = Complement[branchPairs, resolved];

    <|
        "Resolved" -> If[giveResolvents,
            (# -> rfGetResolvent[rules, #[[1]], #[[2]], n]) & /@ resolved,
            resolved
        ],
        "Unresolved" -> unresolved
    |>
]

rfGetResolvent[rules_, s1_String, s2_String, maxSteps_Integer] := Module[{
    states1 = {s1}, states2 = {s2}
},
    Do[
        states1 = DeleteDuplicates[Catenate[rfStringSuccessors[#, rules] & /@ states1]];
        states2 = DeleteDuplicates[Catenate[rfStringSuccessors[#, rules] & /@ states2]];
        With[{common = Intersection[states1, states2]},
            If[common =!= {}, Return[First[common], Module]]
        ],
        {maxSteps}
    ];
    Missing["NotResolved"]
]


(* ============================================================================
   Standalone RF API: MultiwaySystem[rules, init, n, prop, opts]
   
   Creates the MS object internally and dispatches to the property.
   Passes "DeduplicateSlices" -> True via Method sub-options so
   FoliationSlices deduplicates states per step (matching RF behavior).
   ============================================================================ *)

PackageExport["MultiwaySystem"]

(* 4-arg: MultiwaySystem[rules, init, n, "Property", opts...] *)
MultiwaySystem[rules_, init_, n_Integer, prop_String, opts : OptionsPattern[]] /;
    !MultiwaySystemQ[Unevaluated[MultiwaySystem[rules, init, n, prop, opts]]] :=
    Module[{ms = MultiwaySystem[rules, init, "DeduplicateSlices" -> True]},
        If[MultiwaySystemQ[ms],
            MultiwaySystemProp[ms, prop, n, opts],
            $Failed
        ]
    ]

(* 3-arg default: MultiwaySystem[rules, init, n] => AllStatesList *)
MultiwaySystem[rules_, init_, n_Integer] /;
    !MultiwaySystemQ[Unevaluated[MultiwaySystem[rules, init, n]]] :=
    Module[{ms = MultiwaySystem[rules, init, "DeduplicateSlices" -> True]},
        If[MultiwaySystemQ[ms],
            MultiwaySystemProp[ms, "AllStatesList", n],
            $Failed
        ]
    ]

(* 3-arg property: MultiwaySystem[rules, init, "Property", opts...] — no step count *)
MultiwaySystem[rules_, init_, prop_String, opts : OptionsPattern[]] /;
    !MultiwaySystemQ[Unevaluated[MultiwaySystem[rules, init, prop, opts]]] :=
    Module[{ms = MultiwaySystem[rules, init, "DeduplicateSlices" -> True]},
        If[MultiwaySystemQ[ms],
            MultiwaySystemProp[ms, prop, opts],
            $Failed
        ]
    ]

