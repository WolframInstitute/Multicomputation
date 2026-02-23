BeginTestSection["MultiwaySystemRF-Comparison"]

(* =====================================================================
   Comparison tests: ResourceFunction["MultiwaySystem"] vs paclet
   
   Uses standalone API on our side:
     4-arg: MultiwaySystem[rules, init, n, "Property"]
     3-arg: MultiwaySystem[rules, init, n] (defaults to AllStatesList)
     3-arg: MultiwaySystem[rules, init, "Property"] (no step count)
   ===================================================================== *)

(* Setup *)
PacletDirectoryLoad[FileNameJoin[{DirectoryName[$TestFileName], "..", "Multicomputation"}]];
Needs["Wolfram`Multicomputation`"];
rf = ResourceFunction["MultiwaySystem"];


(* ==========================================================================
   AllStatesList — exact match
   ========================================================================== *)

VerificationTest[
    MultiwaySystem[{"AA" -> "", "BA" -> "ABB", "BB" -> "A"}, "BBA", 3],
    rf[{"AA" -> "", "BA" -> "ABB", "BB" -> "A"}, {"BBA"}, 3, "AllStatesList"],
    TestID -> "Compare-AllStatesList-3rule"
]

VerificationTest[
    MultiwaySystem["A" -> "AA", "A", 7],
    rf["A" -> "AA", "A", 7],
    TestID -> "Compare-AllStatesList-single-rule"
]

VerificationTest[
    MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 3],
    rf[{"A" -> "AA", "B" -> "AB"}, {"ABA"}, 3, "AllStatesList"],
    TestID -> "Compare-AllStatesList-ABA"
]

VerificationTest[
    MultiwaySystem[{"A" -> "AB", "B" -> "A"}, "A", 5],
    rf[{"A" -> "AB", "B" -> "A"}, "A", 5],
    TestID -> "Compare-AllStatesList-fibonacci"
]

VerificationTest[
    MultiwaySystem[{"AA" -> "BAA", "BAA" -> "AB"}, "AAA", 3],
    rf[{"AA" -> "BAA", "BAA" -> "AB"}, {"AAA"}, 3],
    TestID -> "Compare-AllStatesList-AA-BAA"
]


(* ==========================================================================
   StatesCountsList
   ========================================================================== *)

VerificationTest[
    MultiwaySystem[{"AA" -> "", "BA" -> "ABB", "BB" -> "A"}, "BBA", 10, "StatesCountsList"],
    rf[{"AA" -> "", "BA" -> "ABB", "BB" -> "A"}, "BBA", 10, "StatesCountsList"],
    TestID -> "Compare-StatesCountsList-10step"
]

VerificationTest[
    MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 5, "StatesCountsList"],
    rf[{"A" -> "AA", "B" -> "AB"}, {"ABA"}, 5, "StatesCountsList"],
    TestID -> "Compare-StatesCountsList-ABA"
]


(* ==========================================================================
   CausalInvariantQ
   ========================================================================== *)

VerificationTest[
    MultiwaySystem[{"TT" -> "F", "TF" -> "T", "FT" -> "T", "FF" -> "F"}, "TFTTFF", 10, "CausalInvariantQ"],
    rf[{"TT" -> "F", "TF" -> "T", "FT" -> "T", "FF" -> "F"}, "TFTTFF", 10, "CausalInvariantQ"],
    TestID -> "Compare-CausalInvariantQ-XOR"
]

VerificationTest[
    MultiwaySystem[{"TT" -> "F", "TF" -> "T", "FT" -> "T", "FF" -> "T"}, "TFTTFF", 10, "CausalInvariantQ"],
    rf[{"TT" -> "F", "TF" -> "T", "FT" -> "T", "FF" -> "T"}, "TFTTFF", 10, "CausalInvariantQ"],
    TestID -> "Compare-CausalInvariantQ-NAND"
]

VerificationTest[
    MultiwaySystem["BA" -> "AB", "BBBAAA", 10, "CausalInvariantQ"],
    rf["BA" -> "AB", "BBBAAA", 10, "CausalInvariantQ"],
    TestID -> "Compare-CausalInvariantQ-sorting"
]

VerificationTest[
    MultiwaySystem[{"AAB" -> "ABBBAA"}, "AAABBB", 5, "CausalInvariantQ"],
    rf[{"AAB" -> "ABBBAA"}, "AAABBB", 5, "CausalInvariantQ"],
    TestID -> "Compare-CausalInvariantQ-single"
]

VerificationTest[
    MultiwaySystem[{"A" -> "ABA", "AA" -> "B"}, "AABAA", 3, "CausalInvariantQ"],
    rf[{"A" -> "ABA", "AA" -> "B"}, "AABAA", 3, "CausalInvariantQ"],
    TestID -> "Compare-CausalInvariantQ-branching"
]


(* ==========================================================================
   CanonicalBranchPairsList
   ========================================================================== *)

VerificationTest[
    Sort[Sort /@ MultiwaySystem[{"AA" -> "AB", "BAA" -> "BA"}, "ABA", "CanonicalBranchPairsList"]],
    Sort[Sort /@ rf[{"AA" -> "AB", "BAA" -> "BA"}, "CanonicalBranchPairsList"]],
    TestID -> "Compare-CanonicalBranchPairsList-4pairs"
]

VerificationTest[
    MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", "CanonicalBranchPairsList"],
    rf[{"A" -> "AA", "B" -> "AB"}, "CanonicalBranchPairsList"],
    TestID -> "Compare-CanonicalBranchPairsList-empty"
]

VerificationTest[
    Sort[Sort /@ MultiwaySystem[{"A" -> "AB", "BA" -> "A"}, "ABA", "CanonicalBranchPairsList"]],
    Sort[Sort /@ rf[{"A" -> "AB", "BA" -> "A"}, "CanonicalBranchPairsList"]],
    TestID -> "Compare-CanonicalBranchPairsList-overlap"
]

VerificationTest[
    Sort[Sort /@ MultiwaySystem[{"AA" -> "AB", "BAA" -> "BA"}, "ABA", "CanonicalBranchPairsList", "IncludeSelfPairs" -> True]],
    Sort[Sort /@ rf[{"AA" -> "AB", "BAA" -> "BA"}, "CanonicalBranchPairsList", "IncludeSelfPairs" -> True]],
    TestID -> "Compare-CanonicalBranchPairsList-self"
]


(* ==========================================================================
   BranchPairsList
   ========================================================================== *)

VerificationTest[
    Sort[Sort /@ MultiwaySystem[{"A" -> "AB", "B" -> "BA"}, "ABA", 2, "BranchPairsList"]],
    Sort[Sort /@ rf[{"A" -> "AB", "B" -> "BA"}, "ABA", 2, "BranchPairsList"]],
    TestID -> "Compare-BranchPairsList-AB-BA"
]

VerificationTest[
    Sort[Sort /@ MultiwaySystem[{"A" -> "AA", "B" -> "AB"}, "ABA", 2, "BranchPairsList"]],
    Sort[Sort /@ rf[{"A" -> "AA", "B" -> "AB"}, {"ABA"}, 2, "BranchPairsList"]],
    TestID -> "Compare-BranchPairsList-basic"
]





(* ==========================================================================
   AllEventsList
   ========================================================================== *)

VerificationTest[
    MultiwaySystem[{"A" -> "ABA", "AA" -> "B"}, "ABA", 3, "AllEventsList"],
    rf[{"A" -> "ABA", "AA" -> "B"}, {"ABA"}, 3, "AllEventsList"],
    TestID -> "Compare-AllEventsList",
    SameTest -> (Sort[Sort /@ #1] === Sort[Sort /@ #2] &)
]


(* ==========================================================================
   Sorting system: BA -> AB (causal invariant bubble sort)
   ========================================================================== *)

VerificationTest[
    MultiwaySystem["BA" -> "AB", "BBBAAA", 5],
    rf["BA" -> "AB", "BBBAAA", 5],
    TestID -> "Compare-Sort-AllStatesList-5"
]

VerificationTest[
    MultiwaySystem["BA" -> "AB", "BBBAAA", 8, "StatesCountsList"],
    rf["BA" -> "AB", "BBBAAA", 8, "StatesCountsList"],
    TestID -> "Compare-Sort-StatesCountsList-8"
]

VerificationTest[
    MultiwaySystem["BA" -> "AB", "BBBAAA", 10, "CausalInvariantQ"],
    rf["BA" -> "AB", "BBBAAA", 10, "CausalInvariantQ"],
    TestID -> "Compare-Sort-CausalInvariantQ"
]


(* ==========================================================================
   XOR boolean: TT->F, TF->T, FT->T, FF->F
   ========================================================================== *)

VerificationTest[
    MultiwaySystem[{"TT" -> "F", "TF" -> "T", "FT" -> "T", "FF" -> "F"}, "TFTTFF", 4],
    rf[{"TT" -> "F", "TF" -> "T", "FT" -> "T", "FF" -> "F"}, "TFTTFF", 4],
    TestID -> "Compare-XOR-AllStatesList-4"
]

VerificationTest[
    MultiwaySystem[{"TT" -> "F", "TF" -> "T", "FT" -> "T", "FF" -> "F"}, "TFTTFF", 4, "StatesCountsList"],
    rf[{"TT" -> "F", "TF" -> "T", "FT" -> "T", "FF" -> "F"}, "TFTTFF", 4, "StatesCountsList"],
    TestID -> "Compare-XOR-StatesCountsList-4"
]


(* ==========================================================================
   Fibonacci: A->AB, B->A (deterministic, causal invariant)
   ========================================================================== *)

VerificationTest[
    MultiwaySystem[{"A" -> "AB", "B" -> "A"}, "A", 6],
    rf[{"A" -> "AB", "B" -> "A"}, "A", 6],
    TestID -> "Compare-Fib-AllStatesList-6"
]

VerificationTest[
    MultiwaySystem[{"A" -> "AB", "B" -> "A"}, "A", 6, "StatesCountsList"],
    rf[{"A" -> "AB", "B" -> "A"}, "A", 6, "StatesCountsList"],
    TestID -> "Compare-Fib-StatesCountsList-6"
]


(* ==========================================================================
   Growing: AA->BAA, BAA->AB
   ========================================================================== *)

VerificationTest[
    MultiwaySystem[{"AA" -> "BAA", "BAA" -> "AB"}, "AAA", 4],
    rf[{"AA" -> "BAA", "BAA" -> "AB"}, {"AAA"}, 4],
    TestID -> "Compare-Grow-AllStatesList-4"
]

VerificationTest[
    Sort[Sort /@ MultiwaySystem[{"AA" -> "BAA", "BAA" -> "AB"}, "AAA", 3, "BranchPairsList"]],
    Sort[Sort /@ rf[{"AA" -> "BAA", "BAA" -> "AB"}, {"AAA"}, 3, "BranchPairsList"]],
    TestID -> "Compare-Grow-BranchPairsList-3"
]


(* ==========================================================================
   NKS p209: A->ABA, AA->B
   ========================================================================== *)

VerificationTest[
    MultiwaySystem[{"A" -> "ABA", "AA" -> "B"}, "AABAA", 3],
    rf[{"A" -> "ABA", "AA" -> "B"}, "AABAA", 3],
    TestID -> "Compare-NKS-AllStatesList-3"
]

VerificationTest[
    MultiwaySystem[{"A" -> "ABA", "AA" -> "B"}, "AABAA", 3, "CausalInvariantQ"],
    rf[{"A" -> "ABA", "AA" -> "B"}, "AABAA", 3, "CausalInvariantQ"],
    TestID -> "Compare-NKS-CausalInvariantQ-3"
]


(* ==========================================================================
   Single expanding rule: AAB->ABBBAA (causal invariant, single rule)
   ========================================================================== *)

VerificationTest[
    MultiwaySystem[{"AAB" -> "ABBBAA"}, "AAABBB", 3],
    rf[{"AAB" -> "ABBBAA"}, "AAABBB", 3],
    TestID -> "Compare-Single-AllStatesList-3"
]

VerificationTest[
    MultiwaySystem[{"AAB" -> "ABBBAA"}, "AAABBB", 3, "CausalInvariantQ"],
    rf[{"AAB" -> "ABBBAA"}, "AAABBB", 3, "CausalInvariantQ"],
    TestID -> "Compare-Single-CausalInvariantQ-3"
]


(* ==========================================================================
   Converging: A->AB, BA->A
   ========================================================================== *)

VerificationTest[
    MultiwaySystem[{"A" -> "AB", "BA" -> "A"}, "ABA", 4],
    rf[{"A" -> "AB", "BA" -> "A"}, {"ABA"}, 4],
    TestID -> "Compare-Conv-AllStatesList-4"
]

VerificationTest[
    Sort[Sort /@ MultiwaySystem[{"A" -> "AB", "BA" -> "A"}, "ABA", 2, "BranchPairsList"]],
    Sort[Sort /@ rf[{"A" -> "AB", "BA" -> "A"}, {"ABA"}, 2, "BranchPairsList"]],
    TestID -> "Compare-Conv-BranchPairsList-2"
]


EndTestSection[]
