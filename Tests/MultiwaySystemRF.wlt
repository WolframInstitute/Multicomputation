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
    ms = MultiwaySystem[{"A" -> "AB", "BA" -> "A"}, "ABA"];
    ms["CanonicalBranchPairsList"],
    _List,
    TestID -> "CanonicalBranchPairsList-returns-list",
    SameTest -> MatchQ
]


(* ===== TotalCausalInvariantQ ===== *)

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AB", "B" -> "A"}, "A"];
    ms["TotalCausalInvariantQ", 5],
    True,
    TestID -> "TotalCausalInvariantQ-true"
]


(* ===== AllEventsList ===== *)

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA"];
    events = ms["AllEventsList", 1];
    MatchQ[events, {{__List} ..}],
    True,
    TestID -> "AllEventsList-returns-nested-list"
]


(* ===== BranchPairResolutionsList ===== *)

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA"];
    result = ms["BranchPairResolutionsList", 3];
    AssociationQ[result] && KeyExistsQ[result, "Resolved"] && KeyExistsQ[result, "Unresolved"],
    True,
    TestID -> "BranchPairResolutionsList-structure"
]


(* ===== Graph properties (existing, should still work) ===== *)

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA"];
    Head[ms["StatesGraph", 2]],
    Graph,
    TestID -> "StatesGraph-returns-graph"
]

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA"];
    VertexCount[ms["StatesGraph", 2]],
    6,
    TestID -> "StatesGraph-vertex-count"
]

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA"];
    Head[ms["EvolutionGraph", 2]],
    Graph,
    TestID -> "EvolutionGraph-returns-graph"
]

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA"];
    Head[ms["BranchialGraph", 2]],
    Graph,
    TestID -> "BranchialGraph-returns-graph"
]

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA"];
    Quiet[Head[ms["CausalGraph", 2]]],
    Graph,
    TestID -> "CausalGraph-returns-graph"
]

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA"];
    Head[ms["StatesGraphStructure", 2]],
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


(* ===== CanonicalKnuthBendixCompletion ===== *)

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AB", "BA" -> "A"}, "ABA"];
    MatchQ[ms["CanonicalKnuthBendixCompletion"], {(_String -> _String) ...}],
    True,
    TestID -> "CanonicalKnuthBendixCompletion-returns-rules"
]


EndTestSection[]
