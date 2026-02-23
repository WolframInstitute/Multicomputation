BeginTestSection["MultiwaySystemRF-Comparison"]

(* =====================================================================
   Comparison tests: ResourceFunction["MultiwaySystem"] vs paclet
   
   Derived from the RF example notebook (MultiwaySystem.nb).
   Uses ms["Property", n] on our side to avoid standalone API conflicts.
   Uses TimeConstrained to prevent hangs from expensive RF computations.
   ===================================================================== *)

(* Setup *)
PacletDirectoryLoad[FileNameJoin[{DirectoryName[$TestFileName], "..", "Multicomputation"}]];
Needs["Wolfram`Multicomputation`"];
rf = ResourceFunction["MultiwaySystem"];


(* ==========================================================================
   AllStatesList — exact match
   ========================================================================== *)

VerificationTest[
    ms = MultiwaySystem[{"AA" -> "", "BA" -> "ABB", "BB" -> "A"}, "BBA", "DeduplicateSlices" -> True];
    ms["AllStatesList", 3],
    rf[{"AA" -> "", "BA" -> "ABB", "BB" -> "A"}, {"BBA"}, 3, "AllStatesList"],
    TestID -> "Compare-AllStatesList-3rule"
]

VerificationTest[
    ms = MultiwaySystem["A" -> "AA", "A"];
    ms["AllStatesList", 7],
    rf["A" -> "AA", "A", 7],
    TestID -> "Compare-AllStatesList-single-rule"
]

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA"];
    ms["AllStatesList", 3],
    rf[{"A" -> "AA", "B" -> "AB"}, {"ABA"}, 3, "AllStatesList"],
    TestID -> "Compare-AllStatesList-ABA"
]

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AB", "B" -> "A"}, "A"];
    ms["AllStatesList", 5],
    rf[{"A" -> "AB", "B" -> "A"}, "A", 5],
    TestID -> "Compare-AllStatesList-fibonacci"
]

VerificationTest[
    ms = MultiwaySystem[{"AA" -> "BAA", "BAA" -> "AB"}, "AAA"];
    ms["AllStatesList", 3],
    rf[{"AA" -> "BAA", "BAA" -> "AB"}, {"AAA"}, 3],
    TestID -> "Compare-AllStatesList-AA-BAA"
]


(* ==========================================================================
   StatesCountsList
   ========================================================================== *)

VerificationTest[
    ms = MultiwaySystem[{"AA" -> "", "BA" -> "ABB", "BB" -> "A"}, "BBA", "DeduplicateSlices" -> True];
    ms["StatesCountsList", 10],
    rf[{"AA" -> "", "BA" -> "ABB", "BB" -> "A"}, "BBA", 10, "StatesCountsList"],
    TestID -> "Compare-StatesCountsList-10step"
]

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA"];
    ms["StatesCountsList", 5],
    rf[{"A" -> "AA", "B" -> "AB"}, {"ABA"}, 5, "StatesCountsList"],
    TestID -> "Compare-StatesCountsList-ABA"
]


(* ==========================================================================
   CausalInvariantQ
   ========================================================================== *)

VerificationTest[
    ms = MultiwaySystem[{"TT" -> "F", "TF" -> "T", "FT" -> "T", "FF" -> "F"}, "TFTTFF"];
    ms["CausalInvariantQ", 10],
    rf[{"TT" -> "F", "TF" -> "T", "FT" -> "T", "FF" -> "F"}, "TFTTFF", 10, "CausalInvariantQ"],
    TestID -> "Compare-CausalInvariantQ-XOR"
]

VerificationTest[
    ms = MultiwaySystem[{"TT" -> "F", "TF" -> "T", "FT" -> "T", "FF" -> "T"}, "TFTTFF"];
    ms["CausalInvariantQ", 10],
    rf[{"TT" -> "F", "TF" -> "T", "FT" -> "T", "FF" -> "T"}, "TFTTFF", 10, "CausalInvariantQ"],
    TestID -> "Compare-CausalInvariantQ-NAND"
]

VerificationTest[
    ms = MultiwaySystem["BA" -> "AB", "BBBAAA"];
    ms["CausalInvariantQ", 10],
    rf["BA" -> "AB", "BBBAAA", 10, "CausalInvariantQ"],
    TestID -> "Compare-CausalInvariantQ-sorting"
]

VerificationTest[
    ms = MultiwaySystem[{"AAB" -> "ABBBAA"}, "AAABBB"];
    ms["CausalInvariantQ", 5],
    rf[{"AAB" -> "ABBBAA"}, "AAABBB", 5, "CausalInvariantQ"],
    TestID -> "Compare-CausalInvariantQ-single"
]

VerificationTest[
    ms = MultiwaySystem[{"A" -> "ABA", "AA" -> "B"}, "AABAA"];
    ms["CausalInvariantQ", 3],
    rf[{"A" -> "ABA", "AA" -> "B"}, "AABAA", 3, "CausalInvariantQ"],
    TestID -> "Compare-CausalInvariantQ-branching"
]


(* ==========================================================================
   CanonicalBranchPairsList
   ========================================================================== *)

VerificationTest[
    ms = MultiwaySystem[{"AA" -> "AB", "BAA" -> "BA"}, "ABA"];
    Sort[Sort /@ ms["CanonicalBranchPairsList"]],
    Sort[Sort /@ rf[{"AA" -> "AB", "BAA" -> "BA"}, "CanonicalBranchPairsList"]],
    TestID -> "Compare-CanonicalBranchPairsList-4pairs"
]

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA"];
    ms["CanonicalBranchPairsList"],
    rf[{"A" -> "AA", "B" -> "AB"}, "CanonicalBranchPairsList"],
    TestID -> "Compare-CanonicalBranchPairsList-empty"
]

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AB", "BA" -> "A"}, "ABA"];
    Sort[Sort /@ ms["CanonicalBranchPairsList"]],
    Sort[Sort /@ rf[{"A" -> "AB", "BA" -> "A"}, "CanonicalBranchPairsList"]],
    TestID -> "Compare-CanonicalBranchPairsList-overlap"
]

VerificationTest[
    ms = MultiwaySystem[{"AA" -> "AB", "BAA" -> "BA"}, "ABA"];
    Sort[Sort /@ ms["CanonicalBranchPairsList", "IncludeSelfPairs" -> True]],
    Sort[Sort /@ rf[{"AA" -> "AB", "BAA" -> "BA"}, "CanonicalBranchPairsList", "IncludeSelfPairs" -> True]],
    TestID -> "Compare-CanonicalBranchPairsList-self"
]


(* ==========================================================================
   BranchPairsList
   ========================================================================== *)

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AB", "B" -> "BA"}, "ABA"];
    Sort[Sort /@ ms["BranchPairsList", 2]],
    Sort[Sort /@ rf[{"A" -> "AB", "B" -> "BA"}, "ABA", 2, "BranchPairsList"]],
    TestID -> "Compare-BranchPairsList-AB-BA"
]

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA"];
    Sort[Sort /@ ms["BranchPairsList", 2]],
    Sort[Sort /@ rf[{"A" -> "AA", "B" -> "AB"}, {"ABA"}, 2, "BranchPairsList"]],
    TestID -> "Compare-BranchPairsList-basic"
]


(* ==========================================================================
   StatesGraph — vertex list comparison 
   ========================================================================== *)

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA"];
    Sort[VertexList[ms["StatesGraph", 3]]],
    Sort[VertexList[rf[{"A" -> "AA", "B" -> "AB"}, {"ABA"}, 3, "StatesGraph"]]],
    TestID -> "Compare-StatesGraph-vertices"
]

VerificationTest[
    ms = MultiwaySystem["BA" -> "AB", "BBBAAA"];
    Sort[VertexList[ms["StatesGraph", 5]]],
    Sort[VertexList[rf["BA" -> "AB", "BBBAAA", 5, "StatesGraph"]]],
    TestID -> "Compare-StatesGraph-sorting"
]


(* ==========================================================================
   BranchialGraph — sorted vertex lists
   ========================================================================== *)

VerificationTest[
    ms = MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA"];
    Sort[VertexList[ms["BranchialGraph", 2]]],
    Sort[VertexList[rf[{"A" -> "AA", "B" -> "AB"}, {"ABA"}, 2, "BranchialGraph"]]],
    TestID -> "Compare-BranchialGraph-vertices"
]


(* ==========================================================================
   AllEventsList
   ========================================================================== *)

VerificationTest[
    ms = MultiwaySystem[{"A" -> "ABA", "AA" -> "B"}, "ABA"];
    ms["AllEventsList", 3],
    rf[{"A" -> "ABA", "AA" -> "B"}, {"ABA"}, 3, "AllEventsList"],
    TestID -> "Compare-AllEventsList"
]


EndTestSection[]
