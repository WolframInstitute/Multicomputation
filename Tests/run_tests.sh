#!/bin/bash
# Run MultiwaySystemRF tests
# Usage: bash Tests/run_tests.sh

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

wolframscript -c "
PacletDirectoryLoad[\"$REPO_DIR/Multicomputation\"];
Needs[\"Wolfram\`Multicomputation\`\"];
report = TestReport[\"$SCRIPT_DIR/MultiwaySystemRF.wlt\"];
Print[\"Tests: \", report[\"TestsSucceededCount\"], \"/\", report[\"TestsSucceededCount\"] + report[\"TestsFailedCount\"], \" passed\"];
If[report[\"TestsFailedCount\"] > 0,
  Print[\"Failed:\"];
  Do[
    Print[\"  \", result[\"TestID\"], \": \", result[\"Outcome\"]],
    {result, Select[Values[report[\"TestResults\"]], #[\"Outcome\"] =!= \"Success\" &]}
  ]
];
Exit[If[report[\"AllTestsSucceeded\"], 0, 1]]
"
