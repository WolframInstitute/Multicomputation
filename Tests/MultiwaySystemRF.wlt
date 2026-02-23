BeginTestSection["MultiwaySystemRF"]

(* Setup *)
PacletDirectoryLoad[FileNameJoin[{DirectoryName[$TestFileName], "..", "Multicomputation"}]];
Needs["Wolfram`Multicomputation`"];


(* ===== AllStatesList ===== *)

VerificationTest[
    MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 2],
    {{_String}, {_String, _String}, {_String, _String, _String}},
    TestID -> "AllStatesList-3arg-default",
    SameTest -> MatchQ
]

VerificationTest[
    MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 2, "AllStatesList"],
    {{_String}, {_String, _String}, {_String, _String, _String}},
    TestID -> "AllStatesList-4arg",
    SameTest -> MatchQ
]

VerificationTest[
    MultiwaySystem[{"A" -> "AA"}, "A", 3],
    {{_String}, {_String}, {_String}, {_String}},
    TestID -> "AllStatesList-single-rule-deterministic",
    SameTest -> MatchQ
]

VerificationTest[
    MultiwaySystem[{"A" -> "AA"}, "A", 3, "AllStatesList"][[All, 1]],
    {"A", "AA", "AAA", "AAAA"},
    TestID -> "AllStatesList-single-rule-values"
]

VerificationTest[
    MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 2, "AllStatesList"][[1]],
    {"ABA"},
    TestID -> "AllStatesList-initial-state"
]


(* ===== StatesCountsList ===== *)

VerificationTest[
    MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 3, "StatesCountsList"],
    {1, 2, 3, 4},
    TestID -> "StatesCountsList-branching"
]

VerificationTest[
    MultiwaySystem[{"A" -> "AA"}, "A", 3, "StatesCountsList"],
    {1, 1, 1, 1},
    TestID -> "StatesCountsList-deterministic"
]


(* ===== CausalInvariantQ ===== *)

VerificationTest[
    MultiwaySystem[{"ABA" -> "ABBA"}, "ABA", 4, "CausalInvariantQ"],
    True,
    TestID -> "CausalInvariantQ-true-single-rule"
]

VerificationTest[
    MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 5, "CausalInvariantQ"],
    True,
    TestID -> "CausalInvariantQ-true-branching"
]


(* ===== BranchPairsList ===== *)

VerificationTest[
    MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 2, "BranchPairsList"],
    _List,
    TestID -> "BranchPairsList-returns-list",
    SameTest -> MatchQ
]

VerificationTest[
    Length[MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 2, "BranchPairsList"]] > 0,
    True,
    TestID -> "BranchPairsList-nonempty"
]


(* ===== CanonicalBranchPairsList ===== *)

VerificationTest[
    MultiwaySystem[{"A" -> "AB", "BA" -> "A"}, "ABA", "CanonicalBranchPairsList"],
    _List,
    TestID -> "CanonicalBranchPairsList-returns-list",
    SameTest -> MatchQ
]


(* ===== TotalCausalInvariantQ ===== *)

VerificationTest[
    MultiwaySystem[{"A" -> "AB", "B" -> "A"}, "A", "TotalCausalInvariantQ"],
    True,
    TestID -> "TotalCausalInvariantQ-true"
]


(* ===== AllEventsList ===== *)

VerificationTest[
    MatchQ[MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 1, "AllEventsList"], {{__List} ..}],
    True,
    TestID -> "AllEventsList-returns-nested-list"
]


(* ===== BranchPairResolutionsList ===== *)

VerificationTest[
    Module[{result = MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 3, "BranchPairResolutionsList"]},
        AssociationQ[result] && KeyExistsQ[result, "Resolved"] && KeyExistsQ[result, "Unresolved"]
    ],
    True,
    TestID -> "BranchPairResolutionsList-structure"
]


(* ===== CanonicalKnuthBendixCompletion ===== *)

VerificationTest[
    MultiwaySystem[{"A" -> "AB", "BA" -> "A"}, "ABA", "CanonicalKnuthBendixCompletion"],
    {(_String -> _String) ...},
    TestID -> "CanonicalKnuthBendixCompletion-returns-rules",
    SameTest -> MatchQ
]


(* ===== Graph properties ===== *)

VerificationTest[
    Quiet[Head[MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 2, "StatesGraph"]]],
    Graph,
    TestID -> "StatesGraph-returns-graph"
]

VerificationTest[
    Quiet[Head[MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 2, "EvolutionGraph"]]],
    Graph,
    TestID -> "EvolutionGraph-returns-graph"
]

VerificationTest[
    Quiet[Head[MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 2, "BranchialGraph"]]],
    Graph,
    TestID -> "BranchialGraph-returns-graph"
]

VerificationTest[
    Quiet[Head[MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 2, "CausalGraph"]]],
    Graph,
    TestID -> "CausalGraph-returns-graph"
]

VerificationTest[
    Quiet[Head[MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 2, "StatesGraphStructure"]]],
    Graph,
    TestID -> "StatesGraphStructure-returns-graph"
]


(* ===== Standalone API consistency ===== *)

VerificationTest[
    MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 2] ===
    MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 2, "AllStatesList"],
    True,
    TestID -> "3arg-equals-4arg-AllStatesList"
]


(* ==========================================================================
   CA (Cellular Automaton) — token-based multiway
   Note: our CA semantics differ from RF. We use token-based evolution
   where each cell neighborhood is tracked as a linked hypergraph token.
   Single-rule CAs are deterministic; multi-rule CAs branch.
   ========================================================================== *)

VerificationTest[
    MultiwaySystem[CellularAutomaton[30], SparseArray[{3 -> 1}, 5], 4, "StatesCountsList"],
    {1, 1, 1, 1, 1},
    TestID -> "CA-single-rule-deterministic"
]

VerificationTest[
    MultiwaySystem[CellularAutomaton[30], SparseArray[{3 -> 1}, 5], 3],
    {{{1}}, {{1, 1, 1}}, {{1, 1, 0, 0, 1}}, {{1, 1, 0, 1, 1, 1, 1}}},
    TestID -> "CA-single-rule-states"
]

VerificationTest[
    MultiwaySystem[{CellularAutomaton[30], CellularAutomaton[110]}, SparseArray[{3 -> 1}, 5], 3, "StatesCountsList"],
    {1, 2, 3, 6},
    TestID -> "CA-multi-rule-branching"
]

VerificationTest[
    MultiwaySystem[{CellularAutomaton[30], CellularAutomaton[110]}, SparseArray[{3 -> 1}, 5], 2],
    {{{1}}, {{1, 1}, {1, 1, 1}}, {{1, 1, 1}, {1, 1, 0, 1}, {1, 1, 0, 0, 1}}},
    TestID -> "CA-multi-rule-states"
]


EndTestSection[]
