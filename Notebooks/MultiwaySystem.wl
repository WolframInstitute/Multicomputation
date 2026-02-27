(* ::Package:: *)

(*From /Users/dreiss/Documents/WolframInstitute/MultiPacletVsResourceFunctions/ResourceComparisons/MultiwaySystem/MultiwaySystem-12-0-0-definition.nb*)



(* ::Section:: *)
(*PackageExported*)


(*PackageExported[MultiwaySystem];*)



(* ::Section:: *)
(*PackageScoped*)


(*PackageScoped[XXX];*)



(* ::Section:: *)
(*Usages*)


(* ::Section:: *)
(*Function Definitions*)


(* ::Input::Initialization:: *)
MultiwaySystem::usage = "MultiwaySystem[rules,init,n] generates the results of n steps in the evolution of the multiway system with the specified rules, starting from initial conditions init.
MultiwaySystem[rules,init,n,prop] gives the property prop for the specified multiway system evolution.
MultiwaySystem[rules->sel,init,n,\[Ellipsis]] uses the function sel to select which of the events obtained at each step to include in the evolution.";



Options[MultiwaySystem] = Join[{"IncludeStepNumber" -> False, "IncludeStateID" -> False, "IncludeInitializationEvents"
	 -> False, "IncludeEventInstances" -> False, "IncludeStateWeights" -> False, "IncludeStatePathWeights" -> False, "StateRenderingFunction"
	 -> Automatic, "EventRenderingFunction" -> Automatic, "MaxItems" -> Infinity, "GivePredecessors" -> False, "GiveResolvents"
	 -> False, "IncludeSelfPairs" -> False, "IncludeFullBranchialSpace" -> False, "LineThickness" -> 1, "VertexSizeMultiplier"
	 -> 1}, Options[Graph]];



MultiwaySystem[SubstitutionSystem[rules_], rest___] :=
	MultiwaySystem["SubstitutionSystem" -> rules, rest]

MultiwaySystem[SubstitutionSystem[rules_] -> eventSelectionFunction_, rest___] :=
	MultiwaySystem["SubstitutionSystem" -> rules -> eventSelectionFunction, rest]

MultiwaySystem[substitutionSystems : {__SubstitutionSystem}, rest___] :=
	MultiwaySystem["SubstitutionSystem" -> Catenate[First /@ substitutionSystems], rest]

MultiwaySystem[substitutionSystems : {__SubstitutionSystem} -> eventSelectionFunction_, rest___] :=
	MultiwaySystem["SubstitutionSystem" -> Catenate[First /@ substitutionSystems] -> eventSelectionFunction, rest]



MultiwaySystem[cellularAutomata : {__CellularAutomaton}, rest___] :=
	MultiwaySystem["CellularAutomaton" -> (First /@ cellularAutomata), rest]

MultiwaySystem[cellularAutomata : {__CellularAutomaton} -> eventSelectionFunction_, rest___] :=
	MultiwaySystem["CellularAutomaton" -> (First /@ cellularAutomata) -> eventSelectionFunction, rest]



getEventSelectionFunction["Sequential"] :=
	({First[#]}&)

getEventSelectionFunction["Random"] :=
	({RandomChoice[#]}&)

getEventSelectionFunction["MaxScan"] :=
	getStringMaxScan

getEventSelectionFunction[{"Random", eventCount_Integer}] :=
	(RandomChoice[#, eventCount]&)

getEventSelectionFunction[(function_Symbol | function_Function)] :=
	function



getStringMaxScan[allEventsList_List] :=
	Reap[
			NestWhile[
				Function[{eventsList},
					(
							Sow[#];
							Complement[eventsList, {#}, SameTest -> (IntervalIntersection @@ (Interval[StringLength[#[[3, 1]]] + 1 + {0, 
								StringLength[#[[1, 1]]] - 1}]& /@ {##}) =!= Interval[]&)]
						)& @ First @ SortBy[eventsList, {(-#&) @* StringLength @* Last @* Last, StringLength @* First @* Last, First}]
							
				],
				allEventsList,
				# =!= {}&
			]
		][[2, 1]] /; !AllTrue[allEventsList, Head[#] === Rule&]

getStringMaxScan[allEventsList_List] :=
	Reap[
			NestWhile[
				Function[{eventsList},
					(
							Sow[#];
							Complement[eventsList, {#}, SameTest -> (IntervalIntersection @@ (Interval[StringLength[#[[2, 3, 1]]] + 1 + {
								0, StringLength[#[[2, 1, 1]]] - 1}]& /@ {##}) =!= Interval[]&)]
						)& @ First @ SortBy[eventsList, {(-#&) @* StringLength @* Last @* Last @* Last, StringLength @* First @* Last 
							@* Last, First}]
				],
				allEventsList,
				# =!= {}&
			]
		][[2, 1]] /; AllTrue[allEventsList, Head[#] === Rule&]



MultiwaySystem[rules : {(_String -> _String)..}, initialConditions : {_String...}] :=
	Last[MultiwaySystem[rules, initialConditions, 1]]

MultiwaySystem[(rules : {(_String -> _String)..}) -> eventSelectionFunction_, initialConditions : {_String...}] :=
	Last[MultiwaySystem[rules -> eventSelectionFunction, initialConditions, 1]]

MultiwaySystem[rule : (_String -> _String), initialConditions : {_String...}] :=
	Last[MultiwaySystem[{rule}, initialConditions, 1]]

MultiwaySystem[(rule : (_String -> _String)) -> eventSelectionFunction_, initialConditions : {_String...}] :=
	Last[MultiwaySystem[{rule} -> eventSelectionFunction, initialConditions, 1]]

MultiwaySystem[rules : {(_String -> _String)..}, initialCondition_String] :=
	MultiwaySystem[rules, {initialCondition}]

MultiwaySystem[(rules : {(_String -> _String)..}) -> eventSelectionFunction_, initialCondition_String] :=
	MultiwaySystem[rules -> eventSelectionFunction, {initialCondition}]

MultiwaySystem[rule : (_String -> _String), initialCondition_String] :=
	MultiwaySystem[{rule}, {initialCondition}]

MultiwaySystem[(rule : (_String -> _String)) -> eventSelectionFunction_, initialCondition_String] :=
	MultiwaySystem[{rule} -> eventSelectionFunction, {initialCondition}]

MultiwaySystem[rules : {(_String -> _String)..}][initialConditions : {_String...}] :=
	MultiwaySystem[rules, initialConditions]

MultiwaySystem[(rules : {(_String -> _String)..}) -> eventSelectionFunction_][initialConditions : {_String...}] :=
	MultiwaySystem[rules -> eventSelectionFunction, initialConditions]

MultiwaySystem[rule : (_String -> _String)][initialConditions : {_String...}] :=
	MultiwaySystem[{rule}, initialConditions]

MultiwaySystem[(rule : (_String -> _String)) -> eventSelectionFunction_][initialConditions : {_String...}] :=
	MultiwaySystem[{rule} -> eventSelectionFunction, initialConditions]

MultiwaySystem[rules : {(_String -> _String)..}][initialCondition_String] :=
	MultiwaySystem[rules][{initialCondition}]

MultiwaySystem[(rules : {(_String -> _String)..}) -> eventSelectionFunction_][initialCondition_String] :=
	MultiwaySystem[rules -> eventSelectionFunction][{initialCondition}]

MultiwaySystem[rule : (_String -> _String)][initialCondition_String] :=
	MultiwaySystem[{rule}][{initialCondition}]

MultiwaySystem[(rule : (_String -> _String)) -> eventSelectionFunction_][initialCondition_String] :=
	MultiwaySystem[{rule} -> eventSelectionFunction][{initialCondition}]

MultiwaySystem[rules : {(_String -> _String)..}, initialConditions : {_String...}, stepCount_Integer, rest___] :=
	MultiwaySystem["SubstitutionSystem" -> rules, initialConditions, stepCount, rest]

MultiwaySystem[(rules : {(_String -> _String)..}) -> eventSelectionFunction_, initialConditions : {_String...}, stepCount_Integer,
	 rest___] :=
	MultiwaySystem["SubstitutionSystem" -> rules -> eventSelectionFunction, initialConditions, stepCount, rest]

MultiwaySystem[rule : (_String -> _String), initialConditions : {_String...}, stepCount_Integer, rest___] :=
	MultiwaySystem["SubstitutionSystem" -> {rule}, initialConditions, stepCount, rest]

MultiwaySystem[(rule : (_String -> _String)) -> eventSelectionFunction_, initialConditions : {_String...}, stepCount_Integer,
	 rest___] :=
	MultiwaySystem["SubstitutionSystem" -> {rule} -> eventSelectionFunction, initialConditions, stepCount, rest]

MultiwaySystem[rules : {(_String -> _String)..}, initialCondition_String, stepCount_Integer, rest___] :=
	MultiwaySystem["SubstitutionSystem" -> rules, {initialCondition}, stepCount, rest]

MultiwaySystem[(rules : {(_String -> _String)..}) -> eventSelectionFunction_, initialCondition_String, stepCount_Integer,
	 rest___] :=
	MultiwaySystem["SubstitutionSystem" -> rules -> eventSelectionFunction, {initialCondition}, stepCount, rest]

MultiwaySystem[rule : (_String -> _String), initialCondition_String, stepCount_Integer, rest___] :=
	MultiwaySystem["SubstitutionSystem" -> {rule}, {initialCondition}, stepCount, rest]

MultiwaySystem[(rule : (_String -> _String)) -> eventSelectionFunction_, initialCondition_String, stepCount_Integer,
	 rest___] :=
	MultiwaySystem["SubstitutionSystem" -> {rule} -> eventSelectionFunction, {initialCondition}, stepCount, rest]



MultiwaySystem[rules : {(_String -> _String)..}, "CanonicalBranchPairsList"] :=
	MultiwaySystem[rules, "CanonicalBranchPairsList", "IncludeSelfPairs" -> False]

MultiwaySystem[rules : {(_String -> _String)..}, "CanonicalBranchPairsList", options : OptionsPattern[]] :=
	Module[{leftHandSides, overlaps, branchPairs},
		leftHandSides = First[#]& /@ rules;
		overlaps = getOverlaps[leftHandSides];
		branchPairs =
			If[
				OptionValue["GivePredecessors"] === True,
				Catenate[Thread[#]& /@ (# -> If[
								OptionValue["IncludeSelfPairs"] === False,
								DeleteCases[{x_, x_}],
								Identity
							][Tuples[StringReplaceList[#, rules], 2]]& /@ overlaps)],
				Union[Sort[#]& /@ Catenate[(If[
							OptionValue["IncludeSelfPairs"] === True,
							Identity,
							DeleteCases[{x_, x_}]
						][Tuples[StringReplaceList[#, rules], 2]]& /@ overlaps)]]
			];
		branchPairs
	]

MultiwaySystem[rule : (_String -> _String), "CanonicalBranchPairsList"] :=
	MultiwaySystem[rule, "CanonicalBranchPairsList", "IncludeSelfPairs" -> False]

MultiwaySystem[rule : (_String -> _String), "CanonicalBranchPairsList", options : OptionsPattern[]] :=
	MultiwaySystem[{rule}, "CanonicalBranchPairsList", options]



MultiwaySystem[rules : {(_String -> _String)..}, stepCount_Integer, "CanonicalBranchPairResolutionsList"] :=
	MultiwaySystem[rules, stepCount, "CanonicalBranchPairResolutionsList", "IncludeSelfPairs" -> False]

MultiwaySystem[rules : {(_String -> _String)..}, stepCount_Integer, "CanonicalBranchPairResolutionsList", options : 
	OptionsPattern[]] :=
	Module[{canonicalBranchPairs, resolvedBranchPairs, unresolvedBranchPairs, resolvedBranchPairsWithResolvent},
		canonicalBranchPairs = MultiwaySystem[rules, "CanonicalBranchPairsList", options];
		resolvedBranchPairs = Select[canonicalBranchPairs, convergentCanonicalBranchPairQ[rules, #, stepCount]&];
		unresolvedBranchPairs = Complement[canonicalBranchPairs, resolvedBranchPairs];
		resolvedBranchPairsWithResolvent =
			If[
				OptionValue["GiveResolvents"] === True,
				# -> getCanonicalBranchPairResolvent[rules, #, stepCount]& /@ resolvedBranchPairs,
				resolvedBranchPairs
			];
		<|"Resolved" -> resolvedBranchPairsWithResolvent, "Unresolved" -> unresolvedBranchPairs|>
	]

MultiwaySystem[rule : (_String -> _String), stepCount_Integer, "CanonicalBranchPairResolutionsList"] :=
	MultiwaySystem[rule, stepCount, "CanonicalBranchPairResolutionsList", "IncludeSelfPairs" -> False]

MultiwaySystem[rule : (_String -> _String), stepCount_Integer, "CanonicalBranchPairResolutionsList", options : OptionsPattern[
	]] :=
	MultiwaySystem[{rule}, stepCount, "CanonicalBranchPairResolutionsList", options]



MultiwaySystem[rules : {(_String -> _String)..}, stepCount_Integer, "TotalCausalInvariantQ"] :=
	MultiwaySystem[rules, stepCount, "TotalCausalInvariantQ", "IncludeSelfPairs" -> False]

MultiwaySystem[rules : {(_String -> _String)..}, stepCount_Integer, "TotalCausalInvariantQ", options : OptionsPattern[
	]] :=
	Module[{unresolvedCanonicalBranchPairsList},
		unresolvedCanonicalBranchPairsList = MultiwaySystem[rules, stepCount, "CanonicalBranchPairResolutionsList", options
			]["Unresolved"];
		Length[unresolvedCanonicalBranchPairsList] == 0
	]

MultiwaySystem[rule : (_String -> _String), stepCount_Integer, "TotalCausalInvariantQ"] :=
	MultiwaySystem[rule, stepCount, "TotalCausalInvariantQ", "IncludeSelfPairs" -> False]

MultiwaySystem[rule : (_String -> _String), stepCount_Integer, "TotalCausalInvariantQ", options : OptionsPattern[]] :=
	MultiwaySystem[{rule}, stepCount, "TotalCausalInvariantQ", options]



MultiwaySystem[rules : {(_String -> _String)..}, "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[rules, "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem[rules : {(_String -> _String)..}, "CanonicalKnuthBendixCompletion", options : OptionsPattern[]] :=
	Module[{canonicalBranchPairsList},
		canonicalBranchPairsList = MultiwaySystem[rules, "CanonicalBranchPairsList"];
		Catenate[{First[#] -> Last[#], Last[#] -> First[#]}& /@ canonicalBranchPairsList]
	]

MultiwaySystem[rule : (_String -> _String), "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[rule, "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem[rule : (_String -> _String), "CanonicalKnuthBendixCompletion", options : OptionsPattern[]] :=
	MultiwaySystem[{rule}, "CanonicalKnuthBendixCompletion", options]



MultiwaySystem[rules : {(_String -> _String)..}, stepCount_Integer, "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[rules, stepCount, "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem[rules : {(_String -> _String)..}, stepCount_Integer, "CanonicalKnuthBendixCompletion", options : OptionsPattern[
	]] :=
	Module[{unresolvedCanonicalBranchPairsList},
		unresolvedCanonicalBranchPairsList = MultiwaySystem[rules, stepCount, "CanonicalBranchPairResolutionsList"]["Unresolved"
			];
		Catenate[{First[#] -> Last[#], Last[#] -> First[#]}& /@ unresolvedCanonicalBranchPairsList]
	]

MultiwaySystem[rule : (_String -> _String), stepCount_Integer, "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[rule, stepCount, "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem[rule : (_String -> _String), stepCount_Integer, "CanonicalKnuthBendixCompletion", options : OptionsPattern[
	]] :=
	MultiwaySystem[{rule}, stepCount, "CanonicalKnuthBendixCompletion", options]



(*
overlappingIntervalsQ[intervals_List]:=Catch[(Scan[If[#[[2,1]]\[LessEqual]#[[1,2]],Throw[True]]&,Partition[intervals,2,1]];False)]
*)



(*
getStringEventPositions[state_String,rules_List]:=Module[{lhsOccurrences,nonOverlappingOccurrences},
lhsOccurrences=Catenate[(Thread[Last[#]\[Rule]StringPosition[state,First[#],Overlaps\[Rule]All]])&/@rules];
nonOverlappingOccurrences=Select[Subsets[lhsOccurrences],!overlappingIntervalsQ[Sort[Last/@#]]&];
nonOverlappingOccurrences]
*)



(*
getStringEvolution[state_String,rules_List]:=Module[{generationList=#},
StringReplacePart[state,First/@generationList,Last/@generationList]]&/@getStringEventPositions[state,rules]
getStringEvolution[states_List,rules_List]:=getStringEvolution[#,rules]&/@states
*)



(*
getStringSpacelikePredecessorStates[states_List,rules_List]:=SortBy[(#[[1,1]]\[Rule]Sort[(Last/@#)])&/@GatherBy[Catenate[(Function[x,x\[Rule]#]/@getStringEvolution[#,rules])&/@states],First],First]
*)



(*
MultiwaySystem[rule:(_String\[Rule]_String),initialCondition_String,stepCount_Integer,"SpacelikeStatesList",options:OptionsPattern[]]:=MultiwaySystem[{rule},{initialCondition},stepCount,"SpacelikeStatesList",options]
MultiwaySystem[rule:(_String\[Rule]_String),initialConditions:{(_String)...},stepCount_Integer,"SpacelikeStatesList",options:OptionsPattern[]]:=MultiwaySystem[{rule},initialConditions,stepCount,"SpacelikeStatesList",options]
MultiwaySystem[rules:{(_String\[Rule]_String)..},initialCondition_String,stepCount_Integer,"SpacelikeStatesList",options:OptionsPattern[]]:=MultiwaySystem[rules,{initialCondition},stepCount,"SpacelikeStatesList",options]

MultiwaySystem[rules:{(_String\[Rule]_String)..},initialConditions:{(_String)...},stepCount_Integer,"SpacelikeStatesList",options:OptionsPattern[]]:=NestList[Union[Catenate[getStringEvolution[#,rules]&/@#]]&,initialConditions,stepCount]
*)



(*
MultiwaySystem[rule:(_String\[Rule]_String),initialCondition_String,stepCount_Integer,"SpacelikePredecessorRulesList",options:OptionsPattern[]]:=MultiwaySystem[{rule},{initialCondition},stepCount,"SpacelikePredecessorRulesList",options]
MultiwaySystem[rule:(_String\[Rule]_String),initialConditions:{(_String)...},stepCount_Integer,"SpacelikePredecessorRulesList",options:OptionsPattern[]]:=MultiwaySystem[{rule},initialConditions,stepCount,"SpacelikePredecessorRulesList",options]
MultiwaySystem[rules:{(_String\[Rule]_String)..},initialCondition_String,stepCount_Integer,"SpacelikePredecessorRulesList",options:OptionsPattern[]]:=MultiwaySystem[rules,{initialCondition},stepCount,"SpacelikePredecessorRulesList",options]

MultiwaySystem[rules:{(_String\[Rule]_String)..},initialConditions:{(_String)..},stepCount_Integer,"SpacelikePredecessorRulesList",options:OptionsPattern[]]:=NestList[getStringSpacelikePredecessorStates[First/@#,rules]&,(#\[Rule]{})&/@initialConditions,stepCount]
*)



(*
MultiwaySystem[rule:(_String\[Rule]_String),initialCondition_String,stepCount_Integer,"SpacelikeStatesGraph",options:OptionsPattern[]]:=MultiwaySystem[{rule},{initialCondition},stepCount,"SpacelikeStatesGraph",options]
MultiwaySystem[rule:(_String\[Rule]_String),initialConditions:{(_String)...},stepCount_Integer,"SpacelikeStatesGraph",options:OptionsPattern[]]:=MultiwaySystem[{rule},initialConditions,stepCount,"SpacelikeStatesGraph",options]
MultiwaySystem[rules:{(_String\[Rule]_String)..},initialCondition_String,stepCount_Integer,"SpacelikeStatesGraph",options:OptionsPattern[]]:=MultiwaySystem[rules,{initialCondition},stepCount,"SpacelikeStatesGraph",options]

MultiwaySystem[rules:{(_String\[Rule]_String)..},initialConditions:{(_String)...},stepCount_Integer,"SpacelikeStatesGraph",options:OptionsPattern[]]:=Graph[Catenate[Map[(Function[state,state\[Rule]First[#]]/@Last[#])&,Catenate[MultiwaySystem[rules,initialConditions,stepCount,"SpacelikePredecessorRulesList",options]]]],VertexShapeFunction\[Rule]getStateRenderingFunction["StringSubstitutionSystem",OptionValue["StateRenderingFunction"]],EdgeStyle\[Rule]Directive[{Hue[0.75,0,0.35],Dashing[None],AbsoluteThickness[OptionValue["LineThickness"]]}],VertexStyle\[Rule]Directive[Opacity[0.7],Hue[0.62,0.45,0.87]],PerformanceGoal\[Rule]getGraphQuality[{OptionValue["StateRenderingFunction"]}],FilterRules[{options},Options[Graph]]]
*)



(*
MultiwaySystem[rule:(_String\[Rule]_String),initialCondition_String,stepCount_Integer,"SpacelikeBranchPairsList",options:OptionsPattern[]]:=MultiwaySystem[{rule},{initialCondition},stepCount,"SpacelikeBranchPairsList",options]
MultiwaySystem[rule:(_String\[Rule]_String),initialConditions:{(_String)...},stepCount_Integer,"SpacelikeBranchPairsList",options:OptionsPattern[]]:=MultiwaySystem[{rule},initialConditions,stepCount,"SpacelikeBranchPairsList",options]
MultiwaySystem[rules:{(_String\[Rule]_String)..},initialCondition_String,stepCount_Integer,"SpacelikeBranchPairsList",options:OptionsPattern[]]:=MultiwaySystem[rules,{initialCondition},stepCount,"SpacelikeBranchPairsList",options]

MultiwaySystem[rules:{(_String\[Rule]_String)..},initialConditions:{(_String)..},stepCount_Integer,"SpacelikeBranchPairsList",options:OptionsPattern[]]:=Module[{branchPairsList,spacelikeStatesList,spacelikeBranchPairsList},
branchPairsList=MultiwaySystem[rules,initialConditions,stepCount,"BranchPairsList",options];
spacelikeStatesList=Catenate[MultiwaySystem[rules,initialConditions,stepCount,"SpacelikeStatesList",options]];
spacelikeBranchPairsList=Select[branchPairsList,SubsetQ[spacelikeStatesList,#]&];
<|"Spacelike"\[Rule]spacelikeBranchPairsList,"Branchlike"\[Rule]Complement[branchPairsList,spacelikeBranchPairsList]|>]
*)



(*
MultiwaySystem[rule:(_String\[Rule]_String),initialCondition_String,stepCount_Integer,"AnnotatedBranchialGraph",options:OptionsPattern[]]:=MultiwaySystem[{rule},{initialCondition},stepCount,"AnnotatedBranchialGraph",options]
MultiwaySystem[rule:(_String\[Rule]_String),initialConditions:{(_String)...},stepCount_Integer,"AnnotatedBranchialGraph",options:OptionsPattern[]]:=MultiwaySystem[{rule},initialConditions,stepCount,"AnnotatedBranchialGraph",options]
MultiwaySystem[rules:{(_String\[Rule]_String)..},initialCondition_String,stepCount_Integer,"AnnotatedBranchialGraph",options:OptionsPattern[]]:=MultiwaySystem[rules,{initialCondition},stepCount,"AnnotatedBranchialGraph",options]

MultiwaySystem[rules:{(_String\[Rule]_String)..},initialConditions:{(_String)...},stepCount_Integer,"AnnotatedBranchialGraph",options:OptionsPattern[]]:=Module[{spacelikeBranchPairsList,branchialGraph},
spacelikeBranchPairsList=MultiwaySystem[rules,initialConditions,stepCount,"SpacelikeBranchPairsList",options]["Spacelike"];
branchialGraph=MultiwaySystem[rules,initialConditions,stepCount,"BranchialGraph",options];
HighlightGraph[branchialGraph,Style[UndirectedEdge@@@spacelikeBranchPairsList,Orange]]]
*)



getStringStateEvolutionFunction[state_String, rules : {(_String -> _String)..}] :=
	StringReplaceList[state, rules]

getStringStateEvolutionFunction[states : {_String...}, rules : {(_String -> _String)..}] :=
	StringReplaceList[states, rules]

getStringStateEvolutionFunction[{stepNumber_Integer, stateID_Integer} -> state_String, rules : {(_String -> _String)
	..}] :=
	({stepNumber + 1, RandomInteger[10^10]} -> #)& /@ StringReplaceList[state, rules]

getStringStateEvolutionFunction[stepNumber_Integer -> state_String, rules : {(_String -> _String)..}] :=
	((stepNumber + 1) -> #)& /@ StringReplaceList[state, rules]

getStringStateEvolutionFunction[{Automatic, stateID_Integer} -> state_String, rules : {(_String -> _String)..}] :=
	({Automatic, RandomInteger[10^10]} -> #)& /@ StringReplaceList[state, rules]



getStringStateEquivalenceFunction[state1_String, state2_String] :=
	SameQ[state1, state2]

getStringStateEquivalenceFunction[state1_Rule, state2_Rule] :=
	SameQ[state1, state2]



getStringReplacementEvent[state_String, rule : (_String -> _String)] :=
	{rule, First[rule], {StringTake[state, First[#] - 1], StringDrop[state, Last[#]]}}& /@ StringPosition[state, First[
		rule]]

getStringReplacementEvent[states : {_String...}, rules : {(_String -> _String)..}] :=
	Catenate[
		Function[currentState,
				Catenate[getStringReplacementEvent[currentState, #]& /@ rules]
			] /@ states
	]

getStringReplacementEvent[{stepNumber_Integer, stateID_Integer} -> state_String, rule : (_String -> _String)] :=
	({stepNumber, {stateID, RandomInteger[10^10]}} -> {rule, First[rule], {StringTake[state, First[#] - 1], StringDrop[
		state, Last[#]]}})& /@ StringPosition[state, First[rule]]

getStringReplacementEvent[stepNumber_Integer -> state_String, rule : (_String -> _String)] :=
	(stepNumber -> {rule, First[rule], {StringTake[state, First[#] - 1], StringDrop[state, Last[#]]}})& /@ StringPosition[
		state, First[rule]]

getStringReplacementEvent[{Automatic, stateID_Integer} -> state_String, rule : (_String -> _String)] :=
	({Automatic, {stateID, RandomInteger[10^10]}} -> {rule, First[rule], {StringTake[state, First[#] - 1], StringDrop[state,
		 Last[#]]}})& /@ StringPosition[state, First[rule]]

getStringReplacementEvent[states : {_Rule...}, rules : {(_String -> _String)..}] :=
	Catenate[
		Function[currentState,
				Catenate[getStringReplacementEvent[currentState, #]& /@ rules]
			] /@ states
	]



getStringStateEventFunction[state_String, rules : {(_String -> _String)..}] :=
	getStringReplacementEvent[state, rules]

getStringStateEventFunction[states : {_String...}, rules : {(_String -> _String)..}] :=
	getStringReplacementEvent[states, rules]

getStringStateEventFunction[state_Rule, rules : {(_String -> _String)..}] :=
	getStringReplacementEvent[state, rules]

getStringStateEventFunction[states : {_Rule...}, rules : {(_String -> _String)..}] :=
	getStringReplacementEvent[states, rules]



getStringElementShifts[shiftedFragment_String, {input : {inputPrefix_String, inputSuffix_String}, output : {outputPrefix_String,
	 outputSuffix_String}}] :=
	Table[Rule @@ ({StringPart[shiftedFragment, position], {StringJoin[#1, StringTake[shiftedFragment,  ;; position - 1
		]], StringJoin[StringTake[shiftedFragment, position + 1 ;; ], #2]}}& @@@ {input, output}), {position, StringLength[shiftedFragment
		]}]

getStringElementShifts[{(input_String | input_Symbol) -> output_String, (input_String | input_Symbol), {prefix_String,
	 suffix_String}}] :=
	Join[getStringElementShifts[prefix, {{"", StringJoin[input, suffix]}, {"", StringJoin[output, suffix]}}], getStringElementShifts[
		suffix, {{StringJoin[prefix, input], ""}, {StringJoin[prefix, output], ""}}]]



getStringElements[{substring_String, {prefix_String, suffix_String}}] :=
	{StringPart[substring, #], {StringJoin[prefix, StringTake[substring,  ;; # - 1]], StringJoin[StringTake[substring, 
		# + 1 ;; ], suffix]}}& /@ Range[StringLength[substring]]



getStringEventDecompositionFunction[event : {(input_String | input_Symbol) -> output_String, (input_String | input_Symbol
	), {prefix_String, suffix_String}}] :=
	Join[{getStringElementShifts[event]}, getStringElements[{#, {prefix, suffix}}]& /@ {input, output}]



getStringEventApplicationFunction[{(input_String | input_Symbol) -> output_String, (input_String | input_Symbol), {prefix_String,
	 suffix_String}}] :=
	StringJoin[prefix, output, suffix]

getStringEventApplicationFunction[{stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer
	}} -> {(input_String | input_Symbol) -> output_String, (input_String | input_Symbol), {prefix_String, suffix_String}
	}] :=
	{stepNumber + 1, outputStateID} -> StringJoin[prefix, output, suffix]

getStringEventApplicationFunction[stepNumber_Integer -> {(input_String | input_Symbol) -> output_String, (input_String
	 | input_Symbol), {prefix_String, suffix_String}}] :=
	(stepNumber + 1) -> StringJoin[prefix, output, suffix]

getStringEventApplicationFunction[{Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}}
	 -> {(input_String | input_Symbol) -> output_String, (input_String | input_Symbol), {prefix_String, suffix_String}}] :=
	{Automatic, outputStateID} -> StringJoin[prefix, output, suffix]



MultiwaySystem["SubstitutionSystem" -> (rules : {(_String -> _String)..}), rest___] :=
	MultiwaySystem[<|"StateEvolutionFunction" -> (getStringStateEvolutionFunction[#, rules]&), "StateEquivalenceFunction"
		 -> getStringStateEquivalenceFunction, "StateEventFunction" -> (getStringStateEventFunction[#, rules]&), "EventDecompositionFunction"
		 -> getStringEventDecompositionFunction, "EventApplicationFunction" -> getStringEventApplicationFunction, "SystemType"
		 -> "StringSubstitutionSystem", "EventSelectionFunction" -> Identity|>, rest]

MultiwaySystem["SubstitutionSystem" -> (rules : {(_String -> _String)..}) -> eventSelectionFunction_, rest___] :=
	MultiwaySystem[<|"StateEvolutionFunction" -> (getStringStateEvolutionFunction[#, rules]&), "StateEquivalenceFunction"
		 -> getStringStateEquivalenceFunction, "StateEventFunction" -> (getStringStateEventFunction[#, rules]&), "EventDecompositionFunction"
		 -> getStringEventDecompositionFunction, "EventApplicationFunction" -> getStringEventApplicationFunction, "SystemType"
		 -> "StringSubstitutionSystem", "EventSelectionFunction" -> getEventSelectionFunction[eventSelectionFunction]|>, rest
		]



MultiwaySystem[rules : {(_List -> _List)..}, initialConditions : {_List...}] :=
	Last[MultiwaySystem[rules, initialConditions, 1]]

MultiwaySystem[(rules : {(_List -> _List)..}) -> eventSelectionFunction_, initialConditions : {_List...}] :=
	Last[MultiwaySystem[rules -> eventSelectionFunction, initialConditions, 1]]

MultiwaySystem[rule : (_List -> _List), initialConditions : {_List...}] :=
	Last[MultiwaySystem[{rule}, initialConditions, 1]]

MultiwaySystem[(rule : (_List -> _List)) -> eventSelectionFunction_, initialConditions : {_List...}] :=
	Last[MultiwaySystem[{rule} -> eventSelectionFunction, initialConditions, 1]]

MultiwaySystem[rules : {(_List -> _List)..}, initialCondition_List] :=
	MultiwaySystem[rules, {initialCondition}] /; Depth[initialCondition] == 2

MultiwaySystem[(rules : {(_List -> _List)..}) -> eventSelectionFunction_, initialCondition_List] :=
	MultiwaySystem[rules -> eventSelectionFunction, {initialCondition}] /; Depth[initialCondition] == 2

MultiwaySystem[rule : (_List -> _List), initialCondition_List] :=
	MultiwaySystem[{rule}, {initialCondition}] /; Depth[initialCondition] == 2

MultiwaySystem[(rule : (_List -> _List)) -> eventSelectionFunction_, initialCondition_List] :=
	MultiwaySystem[{rule} -> eventSelectionFunction, {initialCondition}] /; Depth[initialCondition] == 2

MultiwaySystem[rules : {(_List -> _List)..}][initialConditions : {_List...}] :=
	MultiwaySystem[rules, initialConditions]

MultiwaySystem[(rules : {(_List -> _List)..}) -> eventSelectionFunction_][initialConditions : {_List...}] :=
	MultiwaySystem[rules -> eventSelectionFunction, initialConditions]

MultiwaySystem[rule : (_List -> _List)][initialConditions : {_List...}] :=
	MultiwaySystem[{rule}, initialConditions]

MultiwaySystem[(rule : (_List -> _List)) -> eventSelectionFunction_][initialConditions : {_List...}] :=
	MultiwaySystem[{rule} -> eventSelectionFunction, initialConditions]

MultiwaySystem[rules : {(_List -> _List)..}][initialCondition_List] :=
	MultiwaySystem[rules][{initialCondition}] /; Depth[initialCondition] == 2

MultiwaySystem[(rules : {(_List -> _List)..}) -> eventSelectionFunction_][initialCondition_List] :=
	MultiwaySystem[rules -> eventSelectionFunction][{initialCondition}] /; Depth[initialCondition] == 2

MultiwaySystem[rule : (_List -> _List)][initialCondition_List] :=
	MultiwaySystem[{rule}][{initialCondition}] /; Depth[initialCondition] == 2

MultiwaySystem[(rule : (_List -> _List)) -> eventSelectionFunction_][initialCondition_List] :=
	MultiwaySystem[{rule} -> eventSelectionFunction][{initialCondition}] /; Depth[initialCondition] == 2

MultiwaySystem[rules : {(_List -> _List)..}, initialConditions : {_List...}, stepCount_Integer, rest___] :=
	MultiwaySystem["SubstitutionSystem" -> rules, initialConditions, stepCount, rest]

MultiwaySystem[(rules : {(_List -> _List)..}) -> eventSelectionFunction_, initialConditions : {_List...}, stepCount_Integer,
	 rest___] :=
	MultiwaySystem["SubstitutionSystem" -> rules -> eventSelectionFunction, initialConditions, stepCount, rest]

MultiwaySystem[rule : (_List -> _List), initialConditions : {_List...}, stepCount_Integer, rest___] :=
	MultiwaySystem["SubstitutionSystem" -> {rule}, initialConditions, stepCount, rest]

MultiwaySystem[(rule : (_List -> _List)) -> eventSelectionFunction_, initialConditions : {_List...}, stepCount_Integer,
	 rest___] :=
	MultiwaySystem["SubstitutionSystem" -> {rule} -> eventSelectionFunction, initialConditions, stepCount, rest]

MultiwaySystem[rules : {(_List -> _List)..}, initialCondition_List, stepCount_Integer, rest___] :=
	MultiwaySystem["SubstitutionSystem" -> rules, {initialCondition}, stepCount, rest] /; Depth[initialCondition] == 2

MultiwaySystem[(rules : {(_List -> _List)..}) -> eventSelectionFunction_, initialCondition_List, stepCount_Integer, 
	rest___] :=
	MultiwaySystem["SubstitutionSystem" -> rules -> eventSelectionFunction, {initialCondition}, stepCount, rest] /; Depth[
		initialCondition] == 2

MultiwaySystem[rule : (_List -> _List), initialCondition_List, stepCount_Integer, rest___] :=
	MultiwaySystem["SubstitutionSystem" -> {rule}, {initialCondition}, stepCount, rest] /; Depth[initialCondition] == 2

MultiwaySystem[(rule : (_List -> _List)) -> eventSelectionFunction_, initialCondition_List, stepCount_Integer, rest___
	] :=
	MultiwaySystem["SubstitutionSystem" -> {rule} -> eventSelectionFunction, {initialCondition}, stepCount, rest] /; Depth[
		initialCondition] == 2



MultiwaySystem[rules : {(_List -> _List)..}, "CanonicalBranchPairsList"] :=
	MultiwaySystem[rules, "CanonicalBranchPairsList", "IncludeSelfPairs" -> False]

MultiwaySystem[rules : {(_List -> _List)..}, "CanonicalBranchPairsList", options : OptionsPattern[]] :=
	Module[{leftHandSides, overlaps, branchPairs},
		leftHandSides = First[#]& /@ rules;
		overlaps = getOverlaps[leftHandSides];
		branchPairs =
			If[
				OptionValue["GivePredecessors"] === True,
				Module[{$list},
					Catenate[
							Thread[#]& /@
								(
									$list[#] ->
											If[
												OptionValue["IncludeSelfPairs"] === False,
												DeleteCases[{x_, x_}],
												Identity
											][
												Tuples[
													Module[{left, right},
														With[{prunedRules = ((Join[{left___}, #1, {right___}] -> Join[{left}, #2, {right}])& @@@ rules)},
															ReplaceList[#, prunedRules]
														]
													],
													2
												]
											]& /@ overlaps
								)
						] /. {$list[x_] :> x}
				],
				Union[
					Sort[#]& /@
						Catenate[
							(
								If[
										OptionValue["IncludeSelfPairs"] === True,
										Identity,
										DeleteCases[{x_, x_}]
									][
										Tuples[
											Module[{left, right},
												With[{prunedRules = ((Join[{left___}, #1, {right___}] -> Join[{left}, #2, {right}])& @@@ rules)},
													ReplaceList[#, prunedRules]
												]
											],
											2
										]
									]& /@ overlaps
							)
						]
				]
			];
		branchPairs
	]

MultiwaySystem[rule : (_List -> _List), "CanonicalBranchPairsList"] :=
	MultiwaySystem[rule, "CanonicalBranchPairsList", "IncludeSelfPairs" -> False]

MultiwaySystem[rule : (_List -> _List), "CanonicalBranchPairsList", options : OptionsPattern[]] :=
	MultiwaySystem[{rule}, "CanonicalBranchPairsList", options]



MultiwaySystem[rules : {(_List -> _List)..}, stepCount_Integer, "CanonicalBranchPairResolutionsList"] :=
	MultiwaySystem[rules, stepCount, "CanonicalBranchPairResolutionsList", "IncludeSelfPairs" -> False]

MultiwaySystem[rules : {(_List -> _List)..}, stepCount_Integer, "CanonicalBranchPairResolutionsList", options : OptionsPattern[
	]] :=
	Module[{canonicalBranchPairs, resolvedBranchPairs, unresolvedBranchPairs, resolvedBranchPairsWithResolvent},
		canonicalBranchPairs = MultiwaySystem[rules, "CanonicalBranchPairsList", options];
		resolvedBranchPairs = Select[canonicalBranchPairs, convergentCanonicalBranchPairQ[rules, #, stepCount]&];
		unresolvedBranchPairs = Complement[canonicalBranchPairs, resolvedBranchPairs];
		resolvedBranchPairsWithResolvent =
			If[
				OptionValue["GiveResolvents"] === True,
				# -> getCanonicalBranchPairResolvent[rules, #, stepCount]& /@ resolvedBranchPairs,
				resolvedBranchPairs
			];
		<|"Resolved" -> resolvedBranchPairsWithResolvent, "Unresolved" -> unresolvedBranchPairs|>
	]

MultiwaySystem[rule : (_List -> _List), stepCount_Integer, "CanonicalBranchPairResolutionsList"] :=
	MultiwaySystem[rule, stepCount, "CanonicalBranchPairResolutionsList", "IncludeSelfPairs" -> False]

MultiwaySystem[rule : (_List -> _List), stepCount_Integer, "CanonicalBranchPairResolutionsList", options : OptionsPattern[
	]] :=
	MultiwaySystem[{rule}, stepCount, "CanonicalBranchPairResolutionsList", options]



MultiwaySystem[rules : {(_List -> _List)..}, stepCount_Integer, "TotalCausalInvariantQ"] :=
	MultiwaySystem[rules, stepCount, "TotalCausalInvariantQ", "IncludeSelfPairs" -> False]

MultiwaySystem[rules : {(_List -> _List)..}, stepCount_Integer, "TotalCausalInvariantQ", options : OptionsPattern[]] :=
	Module[{unresolvedCanonicalBranchPairsList},
		unresolvedCanonicalBranchPairsList = MultiwaySystem[rules, stepCount, "CanonicalBranchPairResolutionsList", options
			]["Unresolved"];
		Length[unresolvedCanonicalBranchPairsList] == 0
	]

MultiwaySystem[rule : (_List -> _List), stepCount_Integer, "TotalCausalInvariantQ"] :=
	MultiwaySystem[rule, stepCount, "TotalCausalInvariantQ", "IncludeSelfPairs" -> False]

MultiwaySystem[rule : (_List -> _List), stepCount_Integer, "TotalCausalInvariantQ", options : OptionsPattern[]] :=
	MultiwaySystem[{rule}, stepCount, "TotalCausalInvariantQ", options]



MultiwaySystem[rules : {(_List -> _List)..}, "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[rules, "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem[rules : {(_List -> _List)..}, "CanonicalKnuthBendixCompletion", options : OptionsPattern[]] :=
	Module[{canonicalBranchPairsList},
		canonicalBranchPairsList = MultiwaySystem[rules, "CanonicalBranchPairsList"];
		Catenate[{First[#] -> Last[#], Last[#] -> First[#]}& /@ canonicalBranchPairsList]
	]

MultiwaySystem[rule : (_List -> _List), "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[rule, "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem[rule : (_List -> _List), "CanonicalKnuthBendixCompletion", options : OptionsPattern[]] :=
	MultiwaySystem[{rule}, "CanonicalKnuthBendixCompletion", options]



MultiwaySystem[rules : {(_List -> _List)..}, stepCount_Integer, "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[rules, stepCount, "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem[rules : {(_List -> _List)..}, stepCount_Integer, "CanonicalKnuthBendixCompletion", options : OptionsPattern[
	]] :=
	Module[{unresolvedCanonicalBranchPairsList},
		unresolvedCanonicalBranchPairsList = MultiwaySystem[rules, stepCount, "CanonicalBranchPairResolutionsList"]["Unresolved"
			];
		Catenate[{First[#] -> Last[#], Last[#] -> First[#]}& /@ unresolvedCanonicalBranchPairsList]
	]

MultiwaySystem[rule : (_List -> _List), stepCount_Integer, "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[rule, stepCount, "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem[rule : (_List -> _List), stepCount_Integer, "CanonicalKnuthBendixCompletion", options : OptionsPattern[
	]] :=
	MultiwaySystem[{rule}, stepCount, "CanonicalKnuthBendixCompletion", options]



getListStateEvolutionFunction[state_List, rules : {(_List -> _List)..}] :=
	Module[{left, right},
		With[{prunedRules = ((Join[{left___}, #1, {right___}] -> Join[{left}, #2, {right}])& @@@ rules)},
			ReplaceList[state, prunedRules]
		]
	]

getListStateEvolutionFunction[{stepNumber_Integer, stateID_Integer} -> state_List, rules : {(_List -> _List)..}] :=
	({stepNumber + 1, RandomInteger[10^10]} -> #)& /@
		Module[{left, right},
			With[{prunedRules = ((Join[{left___}, #1, {right___}] -> Join[{left}, #2, {right}])& @@@ rules)},
				ReplaceList[state, prunedRules]
			]
		]

getListStateEvolutionFunction[stepNumber_Integer -> state_List, rules : {(_List -> _List)..}] :=
	((stepNumber + 1) -> #)& /@
		Module[{left, right},
			With[{prunedRules = ((Join[{left___}, #1, {right___}] -> Join[{left}, #2, {right}])& @@@ rules)},
				ReplaceList[state, prunedRules]
			]
		]

getListStateEvolutionFunction[{Automatic, stateID_Integer} -> state_List, rules : {(_List -> _List)..}] :=
	({Automatic, RandomInteger[10^10]} -> #)& /@
		Module[{left, right},
			With[{prunedRules = ((Join[{left___}, #1, {right___}] -> Join[{left}, #2, {right}])& @@@ rules)},
				ReplaceList[state, prunedRules]
			]
		]



getListStateEquivalenceFunction[state1_List, state2_List] :=
	SameQ[state1, state2]

getListStateEquivalenceFunction[state1_Rule, state2_Rule] :=
	SameQ[state1, state2]



getListReplacementEvent[state_List, rule : (_List -> _List)] :=
	{rule, First[rule], {Take[state, First[#] - 1], Drop[state, Last[#]]}}& /@ SequencePosition[state, First[rule]] /; Depth[
		state] == 2

getListReplacementEvent[states : {_List...}, rules : {(_List -> _List)..}] :=
	Catenate[
			Function[currentState,
					Catenate[getListReplacementEvent[currentState, #]& /@ rules]
				] /@ states
		] /; Depth[states] > 2

getListReplacementEvent[{stepNumber_Integer, stateID_Integer} -> state_List, rule : (_List -> _List)] :=
	({stepNumber, {stateID, RandomInteger[10^10]}} -> {rule, First[rule], {Take[state, First[#] - 1], Drop[state, Last[
		#]]}})& /@ SequencePosition[state, First[rule]] /; Depth[state] == 2

getListReplacementEvent[stepNumber_Integer -> state_List, rule : (_List -> _List)] :=
	(stepNumber -> {rule, First[rule], {Take[state, First[#] - 1], Drop[state, Last[#]]}})& /@ SequencePosition[state, 
		First[rule]] /; Depth[state] == 2

getListReplacementEvent[{Automatic, stateID_Integer} -> state_List, rule : (_List -> _List)] :=
	({Automatic, {stateID, RandomInteger[10^10]}} -> {rule, First[rule], {Take[state, First[#] - 1], Drop[state, Last[#
		]]}})& /@ SequencePosition[state, First[rule]] /; Depth[state] == 2

getListReplacementEvent[states : {_Rule...}, rules : {(_List -> _List)..}] :=
	Catenate[
		Function[currentState,
				Catenate[getListReplacementEvent[currentState, #]& /@ rules]
			] /@ states
	]



getListStateEventFunction[state_List, rules : {(_List -> _List)..}] :=
	getListReplacementEvent[state, rules] /; Depth[state] == 2

getListStateEventFunction[states : {_List...}, rules : {(_List -> _List)..}] :=
	getListReplacementEvent[states, rules] /; Depth[states] > 2

getListStateEventFunction[state_Rule, rules : {(_List -> _List)..}] :=
	getListReplacementEvent[state, rules]

getListStateEventFunction[states : {_Rule...}, rules : {(_List -> _List)..}] :=
	getListReplacementEvent[states, rules]



getListElementShifts[shiftedFragment_List, {input : {inputPrefix_List, inputSuffix_List}, output : {outputPrefix_List,
	 outputSuffix_List}}] :=
	Table[Rule @@ ({Part[shiftedFragment, position], {Join[#1, Take[shiftedFragment,  ;; position - 1]], Join[Take[shiftedFragment,
		 position + 1 ;; ], #2]}}& @@@ {input, output}), {position, Length[shiftedFragment]}]

getListElementShifts[{(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List
	}}] :=
	Join[getListElementShifts[prefix, {{{}, Join[input, suffix]}, {{}, Join[output, suffix]}}], getListElementShifts[suffix,
		 {{Join[prefix, input], {}}, {Join[prefix, output], {}}}]]



getListElements[{sublist_List, {prefix_List, suffix_List}}] :=
	{Part[sublist, #], {Join[prefix, Take[sublist,  ;; # - 1]], Join[Take[sublist, # + 1 ;; ], suffix]}}& /@ Range[Length[
		sublist]]



getListEventDecompositionFunction[event : {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), 
	{prefix_List, suffix_List}}] :=
	Join[{getListElementShifts[event]}, getListElements[{#, {prefix, suffix}}]& /@ {input, output}]



getListEventApplicationFunction[{(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List,
	 suffix_List}}] :=
	Join[prefix, output, suffix]

getListEventApplicationFunction[{stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer
	}} -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}] :=
	{stepNumber + 1, outputStateID} -> Join[prefix, output, suffix]

getListEventApplicationFunction[stepNumber_Integer -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol
	), {prefix_List, suffix_List}}] :=
	(stepNumber + 1) -> Join[prefix, output, suffix]

getListEventApplicationFunction[{Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} ->
	 {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}] :=
	{Automatic, outputStateID} -> Join[prefix, output, suffix]



MultiwaySystem["SubstitutionSystem" -> (rules : {(_List -> _List)..}), rest___] :=
	MultiwaySystem[<|"StateEvolutionFunction" -> (getListStateEvolutionFunction[#, rules]&), "StateEquivalenceFunction"
		 -> getListStateEquivalenceFunction, "StateEventFunction" -> (getListStateEventFunction[#, rules]&), "EventDecompositionFunction"
		 -> getListEventDecompositionFunction, "EventApplicationFunction" -> getListEventApplicationFunction, "SystemType" ->
		 "ListSubstitutionSystem", "EventSelectionFunction" -> Identity|>, rest]

MultiwaySystem["SubstitutionSystem" -> (rules : {(_List -> _List)..}) -> eventSelectionFunction_, rest___] :=
	MultiwaySystem[<|"StateEvolutionFunction" -> (getListStateEvolutionFunction[#, rules]&), "StateEquivalenceFunction"
		 -> getListStateEquivalenceFunction, "StateEventFunction" -> (getListStateEventFunction[#, rules]&), "EventDecompositionFunction"
		 -> getListEventDecompositionFunction, "EventApplicationFunction" -> getListEventApplicationFunction, "SystemType" ->
		 "ListSubstitutionSystem", "EventSelectionFunction" -> getEventSelectionFunction[eventSelectionFunction]|>, rest]



MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}], initialConditions : {_List...}] :=
	Last[MultiwaySystem[MWWolframModel[rules], initialConditions, 1]] /; Depth[initialConditions] > 3

MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_, initialConditions : {_List...
	}] :=
	Last[MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction, initialConditions, 1]] /; Depth[initialConditions
		] > 3

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}], initialConditions : {_List...}] :=
	MultiwaySystem[MWWolframModel[rules], initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_, initialConditions : {_List
	...}] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction, initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}], initialConditions : {_List...}] :=
	MultiwaySystem[MWWolframModel[rules], initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_, initialConditions :
	 {_List...}] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction, initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}], initialConditions : {_List...}] :=
	MultiwaySystem[MWWolframModel[rules], initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}] -> eventSelectionFunction_, initialConditions
	 : {_List...}] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction, initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[MWWolframModel[rule : (_List -> _List)], initialConditions : {_List...}] :=
	Last[MultiwaySystem[MWWolframModel[{rule}], initialConditions, 1]] /; Depth[initialConditions] > 3

MultiwaySystem[MWWolframModel[rule : (_List -> _List)] -> eventSelectionFunction_, initialConditions : {_List...}] :=
	Last[MultiwaySystem[MWWolframModel[{rule}] -> eventSelectionFunction, initialConditions, 1]] /; Depth[initialConditions
		] > 3

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)], initialConditions : {_List...}] :=
	MultiwaySystem[MWWolframModel[rule], initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)] -> eventSelectionFunction_, initialConditions : {_List...
	}] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction, initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)], initialConditions : {_List...}] :=
	MultiwaySystem[MWWolframModel[rule], initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)] -> eventSelectionFunction_, initialConditions : {_List
	...}] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction, initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)], initialConditions : {_List...}] :=
	MultiwaySystem[MWWolframModel[rule], initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)] -> eventSelectionFunction_, initialConditions
	 : {_List...}] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction, initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}], initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rules], {initialCondition}] /; Depth[initialCondition] == 3

MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_, initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction, {initialCondition}] /; Depth[initialCondition] == 3

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}], initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rules], initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_, initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction, initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}], initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rules], initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_, initialCondition_List
	] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction, initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}], initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rules], initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}] -> eventSelectionFunction_, initialCondition_List
	] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction, initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[MWWolframModel[rule : (_List -> _List)], initialCondition_List] :=
	MultiwaySystem[MWWolframModel[{rule}], {initialCondition}] /; Depth[initialCondition] == 3

MultiwaySystem[MWWolframModel[rule : (_List -> _List)] -> eventSelectionFunction_, initialCondition_List] :=
	MultiwaySystem[MWWolframModel[{rule}] -> eventSelectionFunction, {initialCondition}] /; Depth[initialCondition] == 3

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)], initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rule], initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)] -> eventSelectionFunction_, initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction, initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)], initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rule], initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)] -> eventSelectionFunction_, initialCondition_List] :=
	MulitwaySystem[MWWolframModel[rule] -> eventSelectionFunction, initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)], initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rule], initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)] -> eventSelectionFunction_, initialCondition_List
	] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction, initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}]][initialConditions : {_List...}] :=
	MultiwaySystem[MWWolframModel[rules], initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_][initialConditions : {_List...
	}] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction, initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}]][initialConditions : {_List...}] :=
	MultiwaySystem[MWWolframModel[rules]][initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_][initialConditions : {_List
	...}] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction][initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}]][initialConditions : {_List...}] :=
	MultiwaySystem[MWWolframModel[rules]][initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_][initialConditions :
	 {_List...}] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction][initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}]][initialConditions : {_List...}] :=
	MultiwaySystem[MWWolframModel[rules]][initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}] -> eventSelectionFunction_][initialConditions
	 : {_List...}] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction][initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[MWWolframModel[rule : (_List -> _List)]][initialConditions : {_List...}] :=
	MultiwaySystem[MWWolframModel[{rule}], initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[MWWolframModel[rule : (_List -> _List)] -> eventSelectionFunction_][initialConditions : {_List...}] :=
	MultiwaySystem[MWWolframModel[{rule}] -> eventSelectionFunction, initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)]][initialConditions : {_List...}] :=
	MultiwaySystem[MWWolframModel[rule], initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)] -> eventSelectionFunction_][initialConditions : {_List...
	}] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction, initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)]][initialConditions : {_List...}] :=
	MultiwaySystem[MWWolframModel[rule], initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)] -> eventSelectionFunction_][initialConditions : {_List
	...}] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction, initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)]][initialConditions : {_List...}] :=
	MultiwaySystem[MWWolframModel[rule], initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)] -> eventSelectionFunction_][initialConditions
	 : {_List...}] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction, initialConditions] /; Depth[initialConditions] > 3

MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}]][initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rules]][{initialCondition}] /; Depth[initialCondition] == 3

MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_][initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction][{initialCondition}] /; Depth[initialCondition] == 3

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}]][initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rules]][initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_][initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction][initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}]][initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rules]][initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_][initialCondition_List
	] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction][initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}]][initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rules]][initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}] -> eventSelectionFunction_][initialCondition_List
	] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction][initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[MWWolframModel[rule : (_List -> _List)]][initialCondition_List] :=
	MultiwaySystem[MWWolframModel[{rule}]][{initialCondition}] /; Depth[initialCondition] == 3

MultiwaySystem[MWWolframModel[rule : (_List -> _List)] -> eventSelectionFunction_][initialCondition_List] :=
	MultiwaySystem[MWWolframModel[{rule}] -> eventSelectionFunction][{initialCondition}] /; Depth[initialCondition] == 3

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)]][initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rule]][initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)] -> eventSelectionFunction_][initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction][initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)]][initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rule]][initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)] -> eventSelectionFunction_][initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction][initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)]][initialCondition_List] :=
	MultiwaySystem[MWWolframModel[rule]][initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)] -> eventSelectionFunction_][initialCondition_List
	] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction][initialCondition] /; Depth[initialCondition] == 3

MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}], initialConditions : {_List...}, stepCount_Integer, rest___
	] :=
	MultiwaySystem["WolframModel" -> rules, initialConditions, stepCount, rest] /; Depth[initialConditions] > 3

MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_, initialConditions : {_List...
	}, stepCount_Integer, rest___] :=
	MultiwaySystem["WolframModel" -> rules -> eventSelectionFunction, initialConditions, stepCount, rest] /; Depth[initialConditions
		] > 3

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}], initialConditions : {_List...}, stepCount_Integer,
	 rest___] :=
	MultiwaySystem[MWWolframModel[rules], initialConditions, stepCount, rest] /; Depth[initialConditions] > 3

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_, initialConditions : {_List
	...}, stepCount_Integer, rest___] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction, initialConditions, stepCount, rest] /; Depth[initialConditions
		] > 3

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}], initialConditions : {_List...}, stepCount_Integer,
	 rest___] :=
	MultiwaySystem[MWWolframModel[rules], initialConditions, stepCount, rest] /; Depth[initialConditions] > 3

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_, initialConditions :
	 {_List...}, stepCount_Integer, rest___] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction, initialConditions, stepCount, rest] /; Depth[initialConditions
		] > 3

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}], initialConditions : {_List...}, stepCount_Integer,
	 rest___] :=
	MultiwaySystem[MWWolframModel[rules], initialConditions, stepCount, rest] /; Depth[initialConditions] > 3

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}] -> eventSelectionFunction_, initialConditions
	 : {_List...}, stepCount_Integer, rest___] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction, initialConditions, stepCount, rest] /; Depth[initialConditions
		] > 3

MultiwaySystem[MWWolframModel[rule : (_List -> _List)], initialConditions : {_List...}, stepCount_Integer, rest___] :=
	MultiwaySystem["WolframModel" -> {rule}, initialConditions, stepCount, rest] /; Depth[initialConditions] > 3

MultiwaySystem[MWWolframModel[rule : (_List -> _List)] -> eventSelectionFunction_, initialConditions : {_List...}, stepCount_Integer,
	 rest___] :=
	MultiwaySystem["WolframModel" -> {rule} -> eventSelectionFunction, initialConditions, stepCount, rest] /; Depth[initialConditions
		] > 3

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)], initialConditions : {_List...}, stepCount_Integer, rest___
	] :=
	MultiwaySystem[MWWolframModel[rule], initialConditions, stepCount, rest] /; Depth[initialConditions] > 3

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)] -> eventSelectionFunction_, initialConditions : {_List...
	}, stepCount_Integer, rest___] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction, initialConditions, stepCount, rest] /; Depth[initialConditions
		] > 3

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)], initialConditions : {_List...}, stepCount_Integer, 
	rest___] :=
	MultiwaySystem[MWWolframModel[rule], initialConditions, stepCount, rest] /; Depth[initialConditions] > 3

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)] -> eventSelectionFunction_, initialConditions : {_List
	...}, stepCount_Integer, rest___] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction, initialConditions, stepCount, rest] /; Depth[initialConditions
		] > 3

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)], initialConditions : {_List...}, stepCount_Integer,
	 rest___] :=
	MultiwaySystem[MWWolframModel[rule], initialConditions, stepCount, rest] /; Depth[initialConditions] > 3

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)] -> eventSelectionFunction_, initialConditions
	 : {_List...}, stepCount_Integer, rest___] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction, initialConditions, stepCount, rest] /; Depth[initialConditions
		] > 3

MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}], initialCondition_List, stepCount_Integer, rest___] :=
	MultiwaySystem["WolframModel" -> rules, {initialCondition}, stepCount, rest] /; Depth[initialCondition] == 3

MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_, initialCondition_List, stepCount_Integer,
	 rest___] :=
	MultiwaySystem["WolframModel" -> rules -> eventSelectionFunction, {initialCondition}, stepCount, rest] /; Depth[initialCondition
		] == 3

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}], initialCondition_List, stepCount_Integer, rest___] :=
	MultiwaySystem[MWWolframModel[rules], initialCondition, stepCount, rest] /; Depth[initialCondition] == 3

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_, initialCondition_List, 
	stepCount_Integer, rest___] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction, initialCondition, stepCount, rest] /; Depth[initialCondition
		] == 3

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}], initialCondition_List, stepCount_Integer, rest___
	] :=
	MultiwaySystem[MWWolframModel[rules], initialCondition, stepCount, rest] /; Depth[initialCondition] == 3

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}] -> eventSelectionFunction_, initialCondition_List,
	 stepCount_Integer, rest___] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction, initialCondition, stepCount, rest] /; Depth[initialCondition
		] == 3

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}], initialCondition_List, stepCount_Integer,
	 rest___] :=
	MultiwaySystem[MWWolframModel[rules], initialCondition, stepCount, rest] /; Depth[initialCondition] == 3

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}] -> eventSelectionFunction_, initialCondition_List,
	 stepCount_Integer, rest___] :=
	MultiwaySystem[MWWolframModel[rules] -> eventSelectionFunction, initialCondition, stepCount, rest] /; Depth[initialCondition
		] == 3

MultiwaySystem[MWWolframModel[rule : (_List -> _List)], initialCondition_List, stepCount_Integer, rest___] :=
	MultiwaySystem["WolframModel" -> {rule}, {initialCondition}, stepCount, rest] /; Depth[initialCondition] == 3

MultiwaySystem[MWWolframModel[rule : (_List -> _List)] -> eventSelectionFunction_, initialCondition_List, stepCount_Integer,
	 rest___] :=
	MultiwaySystem["WolframModel" - {rule} -> eventSelectionFunction, {initialCondition}, stepCount, rest] /; Depth[initialCondition
		] == 3

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)], initialCondition_List, stepCount_Integer, rest___] :=
	MultiwaySystem[MWWolframModel[rule], initialCondition, stepCount, rest] /; Depth[initialCondition] == 3

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)] -> eventSelectionFunction_, initialCondition_List, stepCount_Integer,
	 rest___] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction, initialCondition, stepCount, rest] /; Depth[initialCondition
		] == 3

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)], initialCondition_List, stepCount_Integer, rest___] :=
	MulitwaySystem[MWWolframModel[rule], initialCondition, stepCount, rest] /; Depth[initialCondition] == 3

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)] -> eventSelectionFunction_, initialCondition_List, stepCount_Integer,
	 rest___] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction, initialCondition, stepCount, rest] /; Depth[initialCondition
		] == 3

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)], initialCondition_List, stepCount_Integer, 
	rest___] :=
	MultiwaySystem[MWWolframModel[rule], initialCondition, stepCount, rest] /; Depth[initialCondition] == 3

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)] -> eventSelectionFunction_, initialCondition_List,
	 stepCount_Integer, rest___] :=
	MultiwaySystem[MWWolframModel[rule] -> eventSelectionFunction, initialCondition, stepCount, rest] /; Depth[initialCondition
		] == 3



MultiwaySystem["WolframModel" -> rules : {(_List -> _List)..}, "CanonicalBranchPairsList"] :=
	MultiwaySystem["WolframModel" -> rules, "CanonicalBranchPairsList", "IncludeSelfPairs" -> False]

MultiwaySystem["WolframModel" -> rules : {(_List -> _List)..}, "CanonicalBranchPairsList", options : OptionsPattern[
	]] :=
	Module[{leftHandSides, overlaps, branchPairs, branchPairsEmbedded},
		leftHandSides = First[#]& /@ rules;
		overlaps = getOverlaps[leftHandSides];
		branchPairs = Tuples[Last[MultiwaySystem["WolframModel" -> rules, overlaps, 1, "AllStatesList"]], 2];
		branchPairsEmbedded = Tuples[Last[MultiwaySystem["WolframModel" -> rules, overlaps, 2, "AllStatesList"]], 2];
		If[
			OptionValue["IncludeSelfPairs"] === False,
			DeleteCases[{x_, x_}],
			Identity
		][DeleteDuplicates[Join[branchPairs, branchPairsEmbedded]]]
	]

MultiwaySystem["WolframModel" -> rule : (_List -> _List), "CanonicalBranchPairsList"] :=
	MultiwaySystem["WolframModel" -> rule, "CanonicalBranchPairsList", "IncludeSelfPairs" -> False]

MultiwaySystem["WolframModel" -> rule : (_List -> _List), "CanonicalBranchPairsList", options : OptionsPattern[]] :=
	MultiwaySystem["WolframModel" -> {rule}, "CanonicalBranchPairsList", options]



MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}], "CanonicalBranchPairsList"] :=
	MultiwaySystem[MWWolframModel[rules], "CanonicalBranchPairsList", "IncludeSelfPairs" -> False]

MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}], "CanonicalBranchPairsList", options : OptionsPattern[]] :=
	Module[{leftHandSides, overlaps, branchPairs, branchPairsEmbedded},
		leftHandSides = First[#]& /@ rules;
		overlaps = getOverlaps[leftHandSides];
		branchPairs = Tuples[Last[MultiwaySystem[MWWolframModel[rules], overlaps, 1, "AllStatesList"]], 2];
		branchPairsEmbedded = Tuples[Last[MultiwaySystem[MWWolframModel[rules], overlaps, 2, "AllStatesList"]], 2];
		If[
			OptionValue["IncludeSelfPairs"] === False,
			DeleteCases[{x_, x_}],
			Identity
		][DeleteDuplicates[Join[branchPairs, branchPairsEmbedded]]]
	]

MultiwaySystem[MWWolframModel[rule : (_List -> _List)], "CanonicalBranchPairsList"] :=
	MultiwaySystem[MWWolframModel[rule], "CanonicalBranchPairsList", "IncludeSelfPairs" -> False]

MultiwaySystem[MWWolframModel[rule : (_List -> _List)], "CanonicalBranchPairsList", options : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[{rule}], "CanonicalBranchPairsList", options]

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}], "CanonicalBranchPairsList"] :=
	MultiwaySystem[MWWolframModel[rules], "CanonicalBranchPairsList"]

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}], "CanonicalBranchPairsList", options : OptionsPattern[
	]] :=
	MultiwaySystem[MWWolframModel[rules], "CanonicalBranchPairsList", options]

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)], "CanonicalBranchPairsList"] :=
	MultiwaySystem[MWWolframModel[rule], "CanonicalBranchPairsList"]

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)], "CanonicalBranchPairsList", options : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rule], "CanonicalBranchPairsList", options]

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}], "CanonicalBranchPairsList"] :=
	MultiwaySystem[MWWolframModel[rules], "CanonicalBranchPairsList"]

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}], "CanonicalBranchPairsList", options : OptionsPattern[
	]] :=
	MultiwaySystem[MWWolframModel[rules], "CanonicalBranchPairsList", options]

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)], "CanonicalBranchPairsList"] :=
	MultiwaySystem[MWWolframModel[rule], "CanonicalBranchPairsList"]

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)], "CanonicalBranchPairsList", options : OptionsPattern[
	]] :=
	MultiwaySystem[MWWolframModel[rule], "CanonicalBranchPairsList", options]

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}], "CanonicalBranchPairsList"] :=
	MultiwaySystem[MWWolframModel[rules], "CanonicalBranchPairsList"]

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}], "CanonicalBranchPairsList", options :
	 OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rules], "CanonicalBranchPairsList", options]

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)], "CanonicalBranchPairsList"] :=
	MultiwaySystem[MWWolframModel[rule], "CanonicalBranchPairsList"]

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)], "CanonicalBranchPairsList", options : OptionsPattern[
	]] :=
	MultiwaySystem[MWWolframModel[rule], "CanonicalBranchPairsList", options]



MultiwaySystem["WolframModel" -> rules : {(_List -> _List)..}, stepCount_Integer, "CanonicalBranchPairResolutionsList"
	] :=
	MultiwaySystem["WolframModel" -> rules, stepCount, "CanonicalBranchPairResolutionsList", "IncludeSelfPairs" -> False
		]

MultiwaySystem["WolframModel" -> rules : {(_List -> _List)..}, stepCount_Integer, "CanonicalBranchPairResolutionsList",
	 options : OptionsPattern[]] :=
	Module[{canonicalBranchPairs, resolvedBranchPairs, unresolvedBranchPairs, resolvedBranchPairsWithResolvent},
		canonicalBranchPairs = MultiwaySystem["WolframModel" -> rules, "CanonicalBranchPairsList", options];
		resolvedBranchPairs = Select[canonicalBranchPairs, convergentCanonicalBranchPairQ[rules, #, stepCount]&];
		unresolvedBranchPairs = Complement[canonicalBranchPairs, resolvedBranchPairs];
		resolvedBranchPairsWithResolvent =
			If[
				OptionValue["GiveResolvents"] === True,
				# -> getCanonicalBranchPairResolvent[rules, #, stepCount]& /@ resolvedBranchPairs,
				resolvedBranchPairs
			];
		<|"Resolved" -> resolvedBranchPairsWithResolvent, "Unresolved" -> unresolvedBranchPairs|>
	]

MultiwaySystem["WolframModel" -> rule : (_List -> _List), stepCount_Integer, "CanonicalBranchPairResolutionsList"] :=
	MultiwaySystem["WolframModel" -> rule, stepCount, "CanonicalBranchPairResolutionsList", "IncludeSelfPairs" -> False
		]

MultiwaySystem["WolframModel" -> rule : (_List -> _List), stepCount_Integer, "CanonicalBranchPairResolutionsList", options
	 : OptionsPattern[]] :=
	MultiwaySystem["WolframModel" -> {rule}, stepCount, "CanonicalBranchPairResolutionsList", options]



MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "CanonicalBranchPairResolutionsList"
	] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "CanonicalBranchPairResolutionsList", "IncludeSelfPairs" -> False]

MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "CanonicalBranchPairResolutionsList",
	 options : OptionsPattern[]] :=
	Module[{canonicalBranchPairs, resolvedBranchPairs, unresolvedBranchPairs, resolvedBranchPairsWithResolvent},
		canonicalBranchPairs = MultiwaySystem[MWWolframModel[rules], "CanonicalBranchPairsList", options];
		resolvedBranchPairs = Select[canonicalBranchPairs, convergentCanonicalBranchPairQ[rules, #, stepCount]&];
		unresolvedBranchPairs = Complement[canonicalBranchPairs, resolvedBranchPairs];
		resolvedBranchPairsWithResolvent =
			If[
				OptionValue["GiveResolvents"] === True,
				# -> getCanonicalBranchPairResolvent[rules, #, stepCount]& /@ resolvedBranchPairs,
				resolvedBranchPairs
			];
		<|"Resolved" -> resolvedBranchPairsWithResolvent, "Unresolved" -> unresolvedBranchPairs|>
	]

MultiwaySystem[MWWolframModel[rule : (_List -> _List)], stepCount_Integer, "CanonicalBranchPairResolutionsList"] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "CanonicalBranchPairResolutionsList", "IncludeSelfPairs" -> False]

MultiwaySystem[MWWolframModel[rule : (_List -> _List)], stepCount_Integer, "CanonicalBranchPairResolutionsList", options
	 : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[{rule}], stepCount, "CanonicalBranchPairResolutionsList", options]

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "CanonicalBranchPairResolutionsList"
	] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "CanonicalBranchPairResolutionsList"]

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "CanonicalBranchPairResolutionsList",
	 options : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "CanonicalBranchPairResolutionsList", options]

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)], stepCount_Integer, "CanonicalBranchPairResolutionsList"
	] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "CanonicalBranchPairResolutionsList"]

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)], stepCount_Integer, "CanonicalBranchPairResolutionsList",
	 options : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "CanonicalBranchPairResolutionsList", options]

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "CanonicalBranchPairResolutionsList"
	] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "CanonicalBranchPairResolutionsList"]

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "CanonicalBranchPairResolutionsList",
	 options : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "CanonicalBranchPairResolutionsList", options]

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)], stepCount_Integer, "CanonicalBranchPairResolutionsList"
	] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "CanonicalBranchPairResolutionsList"]

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)], stepCount_Integer, "CanonicalBranchPairResolutionsList",
	 options : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "CanonicalBranchPairResolutionsList", options]

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}], stepCount_Integer, "CanonicalBranchPairResolutionsList"
	] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "CanonicalBranchPairResolutionsList"]

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}], stepCount_Integer, "CanonicalBranchPairResolutionsList",
	 options : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "CanonicalBranchPairResolutionsList", options]

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)], stepCount_Integer, "CanonicalBranchPairResolutionsList"
	] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "CanonicalBranchPairResolutionsList"]

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)], stepCount_Integer, "CanonicalBranchPairResolutionsList",
	 options : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "CanonicalBranchPairResolutionsList", options]



MultiwaySystem["WolframModel" -> rules : {(_List -> _List)..}, stepCount_Integer, "TotalCausalInvariantQ"] :=
	MultiwaySystem["WolframModel" -> rules, stepCount, "TotalCausalInvariantQ", "IncludeSelfPairs" -> False]

MultiwaySystem["WolframModel" -> rules : {(_List -> _List)..}, stepCount_Integer, "TotalCausalInvariantQ", options :
	 OptionsPattern[]] :=
	Module[{unresolvedCanonicalBranchPairsList},
		unresolvedCanonicalBranchPairsList = MultiwaySystem["WolframModel" -> rules, stepCount, "TotalCausalInvariantQ", options
			]["Unresolved"];
		Length[unresolvedCanonicalBranchPairsList] == 0
	]

MultiwaySystem["WolframModel" -> rule : (_List -> _List), stepCount_Integer, "TotalCausalInvariantQ"] :=
	MultiwaySystem["WolframModel" -> rule, stepCount, "TotalCausalInvariantQ", "IncludeSelfPairs" -> False]

MultiwaySystem["WolframModel" -> rule : (_List -> _List), stepCount_Integer, "TotalCausalInvariantQ", options : OptionsPattern[
	]] :=
	MultiwaySystem["WolframModel" -> {rule}, stepCount, "TotalCausalInvariantQ", options]



MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "TotalCausalInvariantQ"] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "TotalCausalInvariantQ", "IncludeSelfPairs" -> False]

MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "TotalCausalInvariantQ", options : OptionsPattern[
	]] :=
	Module[{unresolvedCanonicalBranchPairsList},
		unresolvedCanonicalBranchPairsList = MultiwaySystem[MWWolframModel[rules], stepCount, "CanonicalBranchPairResolutionsList",
			 options]["Unresolved"];
		Length[unresolvedCanonicalBranchPairsList] == 0
	]

MultiwaySystem[MWWolframModel[rule : (_List -> _List)], stepCount_Integer, "TotalCausalInvariantQ"] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "TotalCausalInvariantQ", "IncludeSelfPairs" -> False]

MultiwaySystem[MWWolframModel[rule : (_List -> _List)], stepCount_Integer, "TotalCausalInvariantQ", options : OptionsPattern[
	]] :=
	MultiwaySystem[MWWolframModel[{rule}], stepCount, "TotalCausalInvariantQ", options]

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "TotalCausalInvariantQ"] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "TotalCausalInvariantQ"]

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "TotalCausalInvariantQ", options
	 : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "TotalCausalInvariantQ", options]

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)], stepCount_Integer, "TotalCausalInvariantQ"] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "TotalCausalInvariantQ"]

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)], stepCount_Integer, "TotalCausalInvariantQ", options : OptionsPattern[
	]] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "TotalCausalInvariantQ", options]

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "TotalCausalInvariantQ"] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "TotalCausalInvariantQ"]

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "TotalCausalInvariantQ", options
	 : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "TotalCausalInvariantQ", options]

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)], stepCount_Integer, "TotalCausalInvariantQ"] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "TotalCausalInvariantQ"]

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)], stepCount_Integer, "TotalCausalInvariantQ", options
	 : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "TotalCausalInvariantQ", options]

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}], stepCount_Integer, "TotalCausalInvariantQ"
	] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "TotalCausalInvariantQ"]

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}], stepCount_Integer, "TotalCausalInvariantQ",
	 options : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "TotalCausalInvariantQ", options]

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)], stepCount_Integer, "TotalCausalInvariantQ"
	] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "TotalCausalInvariantQ"]

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)], stepCount_Integer, "TotalCausalInvariantQ",
	 options : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "TotalCausalInvariantQ", options]



MultiwaySystem["WolframModel" -> rules : {(_List -> _List)..}, "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem["WolframModel" -> rules, "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem["WolframModel" -> rules : {(_List -> _List)..}, "CanonicalKnuthBendixCompletion", options : OptionsPattern[
	]] :=
	Module[{canonicalBranchPairsList},
		canonicalBranchPairsList = MultiwaySystem["WolframModel" -> rules, "CanonicalBranchPairsList"];
		Catenate[{First[#] -> Last[#], Last[#] -> First[#]}& /@ canonicalBranchPairsList]
	]

MultiwaySystem["WolframModel" -> rule_List, "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem["WolframModel" -> rule, "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem["WolframModel" -> rule_List, "CanonicalKnuthBendixCompletion", options:OptionsPattern] :=
	MultiwaySystem["WolframModel" -> {rule}, "CanonicalKnuthBendixCompletion", options]



MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}], "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[MWWolframModel[rules], "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}], "CanonicalKnuthBendixCompletion", options : OptionsPattern[
	]] :=
	Module[{canonicalBranchPairsList},
		canonicalBranchPairsList = MultiwaySystem[MWWolframModel[rules], "CanonicalBranchPairsList"];
		Catenate[{First[#] -> Last[#], Last[#] -> First[#]}& /@ canonicalBranchPairsList]
	]

MultiwaySystem[MWWolframModel[rule : (_List -> _List)], "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[MWWolframModel[rule], "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem[MWWolframModel[rule : (_List -> _List)], "CanonicalKnuthBendixCompletion", options : OptionsPattern[]
	] :=
	MultiwaySystem[MWWolframModel[{rule}], "CanonicalKnuthBendixCompletion", options]

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}], "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[MWWolframModel[rules], "CanonicalKnuthBendixCompletion"]

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}], "CanonicalKnuthBendixCompletion", options : OptionsPattern[
	]] :=
	MultiwaySystem[MWWolframModel[rules], "CanonicalKnuthBendixCompletion", options]

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)], "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[MWWolframModel[rule], "CanonicalKnuthBendixCompletion"]

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)], "CanonicalKnuthBendixCompletion", options : OptionsPattern[
	]] :=
	MultiwaySystem[MWWolframModel[rule], "CanonicalKnuthBendixCompletion", options]

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}], "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[MWWolframModel[rules], "CanonicalKnuthBendixCompletion"]

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}], "CanonicalKnuthBendixCompletion", options : OptionsPattern[
	]] :=
	MultiwaySystem[MWWolframModel[rules], "CanonicalKnuthBendixCompletion", options]

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)], "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[MWWolframModel[rule], "CanonicalKnuthBendixCompletion"]

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)], "CanonicalKnuthBendixCompletion", options : OptionsPattern[
	]] :=
	MultiwaySystem[MWWolframModel[rule], "CanonicalKnuthBendixCompletion", options]

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}], "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[MWWolframModel[rules], "CanonicalKnuthBendixCompletion"]

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}], "CanonicalKnuthBendixCompletion", options
	 : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rules], "CanonicalKnuthBendixCompletion", options]

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)], "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[MWWolframModel[rule], "CanonicalKnuthBendixCompletion"]

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)], "CanonicalKnuthBendixCompletion", options 
	: OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rule], "CanonicalKnuthBendixCompletion", options]



MultiwaySystem["WolframModel" -> rules : {(_List -> _List)..}, stepCount_Integer, "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem["WolframModel" -> rules, stepCount, "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem["WolframModel" -> rules : {(_List -> _List)..}, stepCount_Integer, "CanonicalKnuthBendixCompletion", 
	options : OptionsPattern[]] :=
	Module[{unresolvedCanonicalBranchPairsList},
		unresolvedCanonicalBranchPairsList = MultiwaySystem["WolframModel" -> rules, stepCount, "CanonicalBranchPairResolutionsList"
			]["Unresolved"];
		Catenate[{First[#] -> Last[#], Last[#] -> First[#]}& /@ unresolvedCanonicalBranchPairsList]
	]

MultiwaySystem["WolframModel" -> rule : (_List -> _List), stepCount_Integer, "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem["WolframModel" -> rule, stepCount, "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem["WolframModel" -> rule : (_List -> _List), stepCount_Integer, "CanonicalKnuthBendixCompletion", options
	 : OptionsPattern[]] :=
	MultiwaySystem["WolframModel" -> {rule}, stepCount, "CanonicalKnuthBendixCompletion", options]



MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem[MWWolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "CanonicalKnuthBendixCompletion", options
	 : OptionsPattern[]] :=
	Module[{unresolvedCanonicalBranchPairsList},
		unresolvedCanonicalBranchPairsList = MultiwaySystem[MWWolframModel[rules], stepCount, "CanonicalBranchPairResolutionsList"
			]["Unresolved"];
		Catenate[{First[#] -> Last[#], Last[#] -> First[#]}& /@ unresolvedCanonicalBranchPairsList]
	]

MultiwaySystem[MWWolframModel[rule : (_List -> _List)], stepCount_Integer, "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem[MWWolframModel[rule : (_List -> _List)], stepCount_Integer, "CanonicalKnuthBendixCompletion", options
	 : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[{rule}], stepCount, "CanonicalKnuthBendixCompletion", options]

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "CanonicalKnuthBendixCompletion"
	] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "CanonicalKnuthBendixCompletion"]

MultiwaySystem[Global`WolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "CanonicalKnuthBendixCompletion",
	 options : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "CanonicalKnuthBendixCompletion", options]

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)], stepCount_Integer, "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "CanonicalKnuthBendixCompletion"]

MultiwaySystem[Global`WolframModel[rule : (_List -> _List)], stepCount_Integer, "CanonicalKnuthBendixCompletion", options
	 : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "CanonicalKnuthBendixCompletion", options]

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "CanonicalKnuthBendixCompletion"
	] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "CanonicalKnuthBendixCompletion"]

MultiwaySystem[SetReplace`WolframModel[rules : {(_List -> _List)..}], stepCount_Integer, "CanonicalKnuthBendixCompletion",
	 options : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "CanonicalKnuthBendixCompletion", options]

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)], stepCount_Integer, "CanonicalKnuthBendixCompletion"
	] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "CanonicalKnuthBendixCompletion"]

MultiwaySystem[SetReplace`WolframModel[rule : (_List -> _List)], stepCount_Integer, "CanonicalKnuthBendixCompletion",
	 options : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "CanonicalKnuthBendixCompletion", options]

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}], stepCount_Integer, "CanonicalKnuthBendixCompletion"
	] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "CanonicalKnuthBendixCompletion"]

MultiwaySystem[ResourceFunction["WolframModel"][rules : {(_List -> _List)..}], stepCount_Integer, "CanonicalKnuthBendixCompletion",
	 options : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rules], stepCount, "CanonicalKnuthBendixCompletion", options]

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)], stepCount_Integer, "CanonicalKnuthBendixCompletion"
	] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "CanonicalKnuthBendixCompletion"]

MultiwaySystem[ResourceFunction["WolframModel"][rule : (_List -> _List)], stepCount_Integer, "CanonicalKnuthBendixCompletion",
	 options : OptionsPattern[]] :=
	MultiwaySystem[MWWolframModel[rule], stepCount, "CanonicalKnuthBendixCompletion", options]



getPatternRules[rule_Rule] :=
	Module[{leftSymbols, rightSymbols, symbols, newVertexNames, vertexPatterns, newLeft, leftVertices, rightVertices, rightOnlyVertices
		},
		{leftSymbols, rightSymbols} = Union[Cases[#, _?AtomQ, {0, 1}], Cases[#, _, {2}]]& /@ List @@ rule;
		symbols = Union[leftSymbols, rightSymbols];
		newVertexNames = ToHeldExpression /@ StringTemplate["v``"] /@ Range[Length[symbols]];
		vertexPatterns = Pattern[#, Blank[]]& /@ newVertexNames;
		newLeft = (First[rule] /. Thread[symbols -> vertexPatterns]);
		{leftVertices, rightVertices} = {leftSymbols, rightSymbols} /. Thread[symbols -> newVertexNames];
		rightOnlyVertices = Complement[rightVertices, leftVertices];
		With[{moduleVariables = rightOnlyVertices, moduleExpression = Last[rule] /. Thread[symbols -> newVertexNames]},
				If[
					moduleVariables =!= {},
					newLeft :>
						Module[moduleVariables,
							moduleExpression
						],
					newLeft :> moduleExpression
				]
			] /. Hold[expression_] :> expression
	]

getPatternRules[rules : {(_List -> _List)..}] :=
	getPatternRules[#]& /@ rules



getUnduplicatedHypergraphAlphabet[hypergraph_List] :=
	Module[{alphabet},
		alphabet = DeleteDuplicates[Flatten[hypergraph]];
		hypergraph /. Thread[alphabet -> Range[Length[alphabet]]]
	]



getMinimalHypergraphAlphabet[hypergraph_List] :=
	Module[{gatheredAlphabet, alphabet, alphabetLength, sequences},
		gatheredAlphabet = Gather[hypergraph];
		alphabetLength = Length[gatheredAlphabet];
		sequences = {#}& /@ Range[alphabetLength];
		alphabet = First /@ gatheredAlphabet;
		Do[
			sequences =
				Flatten[
					With[{growth = #, newElement = Complement[Range[alphabetLength], #]},
							Append[growth, #]& /@ newElement
						]& /@ First[SplitBy[SortBy[sequences, Length[Union[Flatten[alphabet[[#]]]]]&], Length[Union[Flatten[alphabet[[
							#]]]]]&]],
					1
				],
			{level, 1, alphabetLength - 1}
		];
		First[SplitBy[SortBy[Union[Flatten[gatheredAlphabet[[#]], 1]& /@ sequences], getUnduplicatedHypergraphAlphabet[#]&
			], getUnduplicatedHypergraphAlphabet[#]&]]
	]



getCanonicalHypergraph[hypergraph_List] :=
	First[getUnduplicatedHypergraphAlphabet[getMinimalHypergraphAlphabet[hypergraph]]] /; Depth[hypergraph] >= 3

getCanonicalHypergraph[{stepNumber_Integer, stateID_Integer} -> hypergraph_List] :=
	{stepNumber, stateID} -> getCanonicalHypergraph[hypergraph]

getCanonicalHypergraph[stepNumber_Integer -> hypergraph_List] :=
	stepNumber -> getCanonicalHypergraph[hypergraph]

getCanonicalHypergraph[{Automatic, stateID_Integer} -> hypergraph_List] :=
	{Automatic, stateID} -> getCanonicalHypergraph[hypergraph]

getCanonicalHypergraph[{}] :=
	{}

getCanonicalHypergraph[Null] :=
	Null



getCanonicalStatesList[statesList_List, "WolframModel"] :=
	Module[{generation = #},
			DeleteDuplicates[getCanonicalHypergraph[#]& /@ generation]
		]& /@ statesList

getCanonicalStatesList[statesList_List, Except["WolframModel"]] :=
	statesList



getCanonicalEvent[{(input_List | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List, suffix_List
	}}] :=
	{getCanonicalHypergraph[input] :> Evaluate[getCanonicalHypergraph[output]], getCanonicalHypergraph[input], {getCanonicalHypergraph[
		prefix], getCanonicalHypergraph[suffix]}}

getCanonicalEvent[{stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {(input_List
	 | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}] :=
	{stepNumber, {inputStateID, outputStateID}} -> getCanonicalEvent[{input :> output, input, {prefix, suffix}}]

getCanonicalEvent[stepNumber_Integer -> {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List,
	 suffix_List}}] :=
	stepNumber -> getCanonicalEvent[{input :> output, input, {prefix, suffix}}]

getCanonicalEvent[{Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {(input_List
	 | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}] :=
	{Automatic, {inputStateID, outputStateID}} -> getCanonicalEvent[{input :> output, input, {prefix, suffix}}]



getCanonicalEventsList[eventsList_List, "WolframModel"] :=
	Module[{generation = #},
			DeleteDuplicates[getCanonicalEvent[#]& /@ generation]
		]& /@ eventsList

getCanonicalEventsList[eventsList_List, Except["WolframModel"]] :=
	eventsList



getCanonicalPredecessorRulesList[predecessorRulesList_List, "WolframModel"] :=
	Module[{generation = #},
			ParallelMap[
				Module[{predecessorRule = #},
					getCanonicalHypergraph[First[predecessorRule]] -> DeleteDuplicates[getCanonicalHypergraph[#]& /@ Last[predecessorRule
						]]
				]&,
				generation
			]
		]& /@ predecessorRulesList

getCanonicalPredecessorRulesList[predecessorRulesList_List, Except["WolframModel"]] :=
	predecessorRulesList



getCanonicalCausalElement[$event[event_List, stepNumber_Integer]] :=
	$event[getCanonicalEvent[event], stepNumber]

getCanonicalCausalElement[$element[element_List, stepNumber_Integer]] :=
	$element[getCanonicalHypergraph[element], stepNumber]



getCanonicalCausalElementList[causalElementList_List, "WolframModel"] :=
	getCanonicalCausalElement[#]& /@ causalElementList

getCanonicalCausalElementList[causalElementList_List, Except["WolframModel"]] :=
	causalElementList



getCanonicalCausalEdgeList[causalEdgeList_List, "WolframModel"] :=
	DirectedEdge[getCanonicalCausalElement[First[#]], getCanonicalCausalElement[Last[#]]]& /@ causalEdgeList

getCanonicalCausalEdgeList[causalEdgeList_List, Except["WolframModel"]] :=
	causalEdgeList



validSubsetQ[state_, pattern_, positions_] :=
	MatchQ[state[[positions]], pattern]



getAllSubsetPositions[state_, pattern_] :=
	Select[validSubsetQ[state, pattern, #]&] @ Catenate[Permutations /@ SubsetPosition[state, pattern]]



getWolframModelStateEvolutionFunction[state_List, rules : {(_List :> (_List | _Module))..}] :=
	Catenate[
		Function[rule,
				Join[state[[#]] /. rule, state[[Complement[Range[Length[state]], #]]]]& /@ getAllSubsetPositions[state, First[rule
					]]
			] /@ rules
	]

getWolframModelStateEvolutionFunction[{stepNumber_Integer, stateID_Integer} -> state_List, rules : {(_List :> (_List
	 | _Module))..}] :=
	({stepNumber + 1, RandomInteger[10^10]} -> #)& /@
		Catenate[
			Function[rule,
					Join[state[[#]] /. rule, state[[Complement[Range[Length[state]], #]]]]& /@ getAllSubsetPositions[state, First[rule
						]]
				] /@ rules
		]

getWolframModelStateEvolutionFunction[stepNumber_Integer -> state_List, rules : {(_List :> (_List | _Module))..}] :=
	((stepNumber + 1) -> #)& /@
		Catenate[
			Function[rule,
					Join[state[[#]] /. rule, state[[Complement[Range[Length[state]], #]]]]& /@ getAllSubsetPositions[state, First[rule
						]]
				] /@ rules
		]

getWolframModelStateEvolutionFunction[{Automatic, stateID_Integer} -> state_List, rules : {(_List :> (_List | _Module
	))..}] :=
	({Automatic, RandomInteger[10^10]} -> #)& /@
		Catenate[
			Function[rule,
					Join[state[[#]] /. rule, state[[Complement[Range[Length[state]], #]]]]& /@ getAllSubsetPositions[state, First[rule
						]]
				] /@ rules
		]



getWolframModelStateEquivalenceFunction[state1_List, state2_List] :=
	(getCanonicalHypergraph[state1] === getCanonicalHypergraph[state2])

getWolframModelStateEquivalenceFunction[state1_Rule, state2_Rule] :=
	((First[state1] === First[state2]) && (getCanonicalHypergraph[state1] === getCanonicalHypergraph[state2]))



getWolframModelReplacementEvent[state_List, rule : (_List :> (_List | _Module))] :=
	Module[{instantiatedRule},
				instantiatedRule = (Part[state, #]) :> (Evaluate[Part[state, #] /. rule]);
				{instantiatedRule, First[instantiatedRule], {Part[state, Complement[Range[Length[state]], #]], {}}}
			]& /@ getAllSubsetPositions[state, First[rule]] /; Depth[state] == 3

getWolframModelReplacementEvent[state_List, rules : {(_List :> (_List | _Module))..}] :=
	getWolframModelReplacementEvent[{state}, rules] /; Depth[state] == 3

getWolframModelReplacementEvent[states_List, rules : {(_List :> (_List | _Module))..}] :=
	Catenate[
			Function[currentState,
					Catenate[getWolframModelReplacementEvent[currentState, #]& /@ rules]
				] /@ states
		] /; Depth[states] > 3

getWolframModelReplacementEvent[{stepNumber_Integer, stateID_Integer} -> state_List, rule : (_List :> (_List | _Module
	))] :=
	Module[{instantiatedRule},
				instantiatedRule = (Part[state, #]) :> (Evaluate[Part[state, #] /. rule]);
				({stepNumber, {stateID, RandomInteger[10^10]}} -> {instantiatedRule, First[instantiatedRule], {Part[state, Complement[
					Range[Length[state]], #]], {}}})
			]& /@ getAllSubsetPositions[state, First[rule]] /; Depth[state] == 3

getWolframModelReplacementEvent[stepNumber_Integer -> state_List, rule : (_List :> (_List | _Module))] :=
	Module[{instantiatedRule},
				instantiatedRule = (Part[state, #]) :> (Evaluate[Part[state, #] /. rule]);
				(stepNumber -> {instantiatedRule, First[instantiatedRule], {Part[state, Complement[Range[Length[state]], #]], {}
					}})
			]& /@ getAllSubsetPositions[state, First[rule]] /; Depth[state] == 3

getWolframModelReplacementEvent[{Automatic, stateID_Integer} -> state_List, rule : (_List :> (_List | _Module))] :=
	Module[{instantiatedRule},
				instantiatedRule = (Part[state, #]) :> (Evaluate[Part[state, #] /. rule]);
				({Automatic, {stateID, RandomInteger[10^10]}} -> {instantiatedRule, First[instantiatedRule], {Part[state, Complement[
					Range[Length[state]], #]], {}}})
			]& /@ getAllSubsetPositions[state, First[rule]] /; Depth[state] == 3

getWolframModelReplacementEvent[state_Rule, rules : {(_List :> (_List | _Module))..}] :=
	getWolframModelReplacementEvent[{state}, rules] /; Depth[state] == 3

getWolframModelReplacementEvent[states : {_Rule...}, rules : {(_List :> (_List | _Module))..}] :=
	Catenate[
		Function[currentState,
				Catenate[getWolframModelReplacementEvent[currentState, #]& /@ rules]
			] /@ states
	]



getWolframModelStateEventFunction[state_List, rules : {(_List :> (_List | _Module))..}] :=
	getWolframModelReplacementEvent[state, rules] /; Depth[state] == 3

getWolframModelStateEventFunction[states : {_List...}, rules : {(_List :> (_List | _Module))..}] :=
	getWolframModelReplacementEvent[states, rules] /; Depth[states] > 3

getWolframModelStateEventFunction[state_Rule, rules : {(_List :> (_List | _Module))..}] :=
	getWolframModelReplacementEvent[state, rules]

getWolframModelStateEventFunction[states : {_Rule...}, rules : {(_List :> (_List | _Module))..}] :=
	getWolframModelReplacementEvent[states, rules]



getWolframModelElementShifts[shiftedFragment_List, {input : {inputPrefix_List, inputSuffix_List}, output : {outputPrefix_List,
	 outputSuffix_List}}] :=
	Table[Rule @@ ({Part[shiftedFragment, position], {Sort[Join[Join[#1, Take[shiftedFragment,  ;; position - 1]], Join[
		Take[shiftedFragment, position + 1 ;; ], #2]]], {}}}& @@@ {input, output}), {position, Length[shiftedFragment]}]

getWolframModelElementShifts[{(input_List | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List,
	 suffix_List}}] :=
	Join[getWolframModelElementShifts[prefix, {{{}, Join[input, suffix]}, {{}, Join[output, suffix]}}], getWolframModelElementShifts[
		suffix, {{Join[prefix, input], {}}, {Join[prefix, output], {}}}]]



getWolframModelElements[{subHypergraph_List, {prefix_List, suffix_List}}] :=
	{Part[subHypergraph, #], {Sort[Join[Join[prefix, Take[subHypergraph,  ;; # - 1]], Join[Take[subHypergraph, # + 1 ;;
		 ], suffix]]], {}}}& /@ Range[Length[subHypergraph]]



getWolframModelEventDecompositionFunction[event : {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol
	), {prefix_List, suffix_List}}] :=
	Join[{getWolframModelElementShifts[event]}, getWolframModelElements[{#, {prefix, suffix}}]& /@ {input, output}]



getWolframModelEventApplicationFunction[{(input_List | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List,
	 suffix_List}}] :=
	Join[prefix, output, suffix]

getWolframModelEventApplicationFunction[{stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer
	}} -> {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}] :=
	{stepNumber + 1, outputStateID} -> Join[prefix, output, suffix]

getWolframModelEventApplicationFunction[stepNumber_Integer -> {(input_List | input_Symbol) :> output_List, (input_List
	 | input_Symbol), {prefix_List, suffix_List}}] :=
	(stepNumber + 1) -> Join[prefix, output, suffix]

getWolframModelEventApplicationFunction[{Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer
	}} -> {(input_List | input_symbol) :> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}] :=
	{Automatic, outputStateID} -> Join[prefix, output, suffix]



MultiwaySystem["WolframModel" -> (rules : {(_List -> _List)..}), rest___] :=
	MultiwaySystem[<|"StateEvolutionFunction" -> (getWolframModelStateEvolutionFunction[#, getPatternRules[rules]]&), "StateEquivalenceFunction"
		 -> getWolframModelStateEquivalenceFunction, "StateEventFunction" -> (getWolframModelStateEventFunction[#, getPatternRules[
		rules]]&), "EventDecompositionFunction" -> getWolframModelEventDecompositionFunction, "EventApplicationFunction" -> 
		getWolframModelEventApplicationFunction, "SystemType" -> "WolframModel", "EventSelectionFunction" -> Identity|>, rest
		]

MultiwaySystem["WolframModel" -> (rules : {(_List -> _List)..}) -> eventSelectionFunction_, rest___] :=
	MultiwaySystem[<|"StateEvolutionFunction" -> (getWolframModelStateEvolutionFunction[#, getPatternRules[rules]]&), "StateEquivalenceFunction"
		 -> getWolframModelStateEquivalenceFunction, "StateEventFunction" -> (getWolframModelStateEventFunction[#, getPatternRules[
		rules]]&), "EventDecompositionFunction" -> getWolframModelEventDecompositionFunction, "EventApplicationFunction" -> 
		getWolframModelEventApplicationFunction, "SystemType" -> "WolframModel", "EventSelectionFunction" -> getEventSelectionFunction[
		eventSelectionFunction]|>, rest]



MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}], initialConditions : {_List...}] :=
	Last[MultiwaySystem[CellularAutomaton[rules], initialConditions, 1]] /; Depth[initialConditions] > 2

MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}] -> eventSelectionFunction_, initialConditions : {_List...}] :=
	Last[MultiwaySystem[CellularAutomaton[rules] -> eventSelectionFunction, initialConditions, 1]] /; Depth[initialConditions
		] > 2

MultiwaySystem[CellularAutomaton[rule_Integer], initialConditions : {_List...}] :=
	Last[MultiwaySystem[CellularAutomaton[{rule}], initialConditions, 1]] /; Depth[initialConditions] > 2

MultiwaySystem[CellularAutomaton[rule_Integer] -> eventSelectionFunction_, initialConditions : {_List...}] :=
	Last[MultiwaySystem[CellularAutomaton[{rule}] -> eventSelectionFunction, initialConditions, 1]] /; Depth[initialConditions
		] > 2

MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}], initialCondition_List] :=
	MultiwaySystem[CellularAutomaton[rules], {initialCondition}] /; Depth[initialCondition] == 2

MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}] -> eventSelectionFunction_, initialCondition_List] :=
	MultiwaySystem[CellularAutomaton[rules] -> eventSelectionFunction, {initialCondition}] /; Depth[initialCondition] ==
		 2

MultiwaySystem[CellularAutomaton[rule_Integer], initialCondition_List] :=
	MultiwaySystem[CellularAutomaton[{rule}], {initialCondition}] /; Depth[initialCondition] == 2

MultiwaySystem[CellularAutomaton[rule_Integer] -> eventSelectionFunction_, initialCondition_List] :=
	MultiwaySystem[CellularAutomaton[{rule}] -> eventSelectionFunction, {initialCondition}] /; Depth[initialCondition] ==
		 2

MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}]][initialConditions : {_List...}] :=
	MultiwaySystem[CellularAutomaton[rules], initialConditions] /; Depth[initialConditions] > 2

MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}] -> eventSelectionFunction_][initialConditions : {_List...}] :=
	MultiwaySystem[CellularAutomaton[rules] -> eventSelectionFunction, initialConditions] /; Depth[initialConditions] >
		 2

MultiwaySystem[CellularAutomaton[rule_Integer]][initialConditions : {_List...}] :=
	MultiwaySystem[CellularAutomaton[{rule}], initialConditions] /; Depth[initialConditions] > 2

MultiwaySystem[CellularAutomaton[rule_Integer] -> eventSelectionFunction_][initialConditions : {_List...}] :=
	MultiwaySystem[CellularAutomaton[{rule}] -> eventSelectionFunction, initialConditions] /; Depth[initialConditions] >
		 2

MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}]][initialCondition_List] :=
	MultiwaySystem[CellularAutomaton[rules]][{initialCondition}] /; Depth[initialCondition] == 2

MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}] -> eventSelectionFunction_][initialCondition_List] :=
	MultiwaySystem[CellularAutomaton[rules] -> eventSelectionFunction][{initialCondition}] /; Depth[initialCondition] ==
		 2

MultiwaySystem[CellularAutomaton[rule_Integer]][initialCondition_List] :=
	MultiwaySystem[CellularAutomaton[{rule}]][{initialCondition}] /; Depth[initialCondition] == 2

MultiwaySystem[CellularAutomaton[rule_Integer] -> eventSelectionFunction_][initialCondition_List] :=
	MultiwaySystem[CellularAutomaton[{rule}] -> eventSelectionFunction][{initialCondition}] /; Depth[initialCondition] ==
		 2

MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}], initialConditions : {_List...}, stepCount_Integer, rest___
	] :=
	MultiwaySystem["CellularAutomaton" -> rules, initialConditions, stepCount, rest] /; Depth[initialConditions] > 2

MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}] -> eventSelectionFunction_, initialConditions : {_List...},
	 stepCount_Integer, rest___] :=
	MultiwaySystem["CellularAutomaton" -> rules -> eventSelectionFunction, initialConditions, stepCount, rest] /; Depth[
		initialConditions] > 2

MultiwaySystem[CellularAutomaton[rule_Integer], initialConditions : {_List...}, stepCount_Integer, rest___] :=
	MultiwaySystem["CellularAutomaton" -> {rule}, initialConditions, stepCount, rest] /; Depth[initialConditions] > 2

MultiwaySystem[CellularAutomaton[rule_Integer] -> eventSelectionFunction_, initialConditions : {_List...}, stepCount_Integer,
	 rest___] :=
	MultiwaySystem["CellularAutomaton" -> {rule} -> eventSelectionFunction, initialConditions, stepCount, rest] /; Depth[
		initialConditions] > 2

MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}], initialCondition_List, stepCount_Integer, rest___] :=
	MultiwaySystem["CellularAutomaton" -> rules, {initialCondition}, stepCount, rest] /; Depth[initialCondition] == 2

MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}] -> eventSelectionFunction_, initialCondition_List, stepCount_Integer,
	 rest___] :=
	MultiwaySystem["CellularAutomaton" -> rules -> eventSelectionFunction, {initialCondition}, stepCount, rest] /; Depth[
		initialCondition] == 2

MultiwaySystem[CellularAutomaton[rule_Integer], initialCondition_List, stepCount_Integer, rest___] :=
	MultiwaySystem["CellularAutomaton" -> {rule}, {initialCondition}, stepCount, rest] /; Depth[initialCondition] == 2

MultiwaySystem[CellularAutomaton[rule_Integer] -> eventSelectionFunction_, initialCondition_List, stepCount_Integer,
	 rest___] :=
	MultiwaySystem["CellularAutomaton" -> {rule} -> eventSelectionFunction, {initialCondition}, stepCount, rest] /; Depth[
		initialCondition] == 2



MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}], "CanonicalBranchPairsList"] :=
	MultiwaySystem[CellularAutomaton[rules], "CanonicalBranchPairsList", "IncludeSelfPairs" -> False]

MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}], "CanonicalBranchPairsList", options : OptionsPattern[]] :=
	Module[{leftHandSides, overlaps, branchPairs},
		leftHandSides = First[#]& /@ Catenate[getCellularAutomatonSubstitutionRules[rules]];
		overlaps = getOverlaps[leftHandSides];
		branchPairs =
			If[
				OptionValue["GivePredecessors"] === True,
				Module[{$state},
					Catenate[
							Thread[#]& /@
								(
									$state[#] ->
											If[
												OptionValue["IncludeSelfPairs"] === False,
												DeleteCases[{x_, x_}],
												Identity
											][
												Tuples[
													Module[{left, right},
														With[{prunedRules = ((Join[{left___}, #1, {right___}] -> Join[{left}, #2, {right}])& @@@ Catenate[getCellularAutomatonSubstitutionRules[
															rules]])},
															Drop[Drop[#, 1], -1]& /@
																ReplaceList[
																	With[{firstElement = First[#], lastElement = Last[#]},
																		Prepend[Append[#, firstElement], lastElement]
																	],
																	prunedRules
																]
														]
													],
													2
												]
											]& /@ overlaps
								)
						] /. {$state[x_] :> x}
				],
				Union[
					Sort[#]& /@
						Catenate[
							(
								If[
										OptionValue["IncludeSelfPairs"] === True,
										Identity,
										DeleteCases[{x_, x_}]
									][
										Tuples[
											Module[{left, right},
												With[{prunedRules = ((Join[{left___}, #1, {right___}] -> Join[{left}, #2, {right}])& @@@ Catenate[getCellularAutomatonSubstitutionRules[
													rules]])},
													Drop[Drop[#, 1], -1]& /@
														ReplaceList[
															With[{firstElement = First[#], lastElement = Last[#]},
																Prepend[Append[#, firstElement], lastElement]
															],
															prunedRules
														]
												]
											],
											2
										]
									]& /@ overlaps
							)
						]
				]
			];
		branchPairs
	]

MultiwaySystem[CellularAutomaton[rule_Integer], "CanonicalBranchPairsList"] :=
	MultiwaySystem[CellularAutomaton[rule], "CanonicalBranchPairsList", "IncludeSelfPairs" -> False]

MultiwaySystem[CellularAutomaton[rule_Integer], "CanonicalBranchPairsList", options : OptionsPattern[]] :=
	MultiwaySystem[CellularAutomaton[{rule}], "CanonicalBranchPairsList", options]



MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}], stepCount_Integer, "CanonicalBranchPairResolutionsList"] :=
	MultiwaySystem[CellularAutomaton[rules], stepCount, "CanonicalBranchPairResolutionsList", "IncludeSelfPairs" -> False
		]

MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}], stepCount_Integer, "CanonicalBranchPairResolutionsList", options
	 : OptionsPattern[]] :=
	Module[{canonicalBranchPairs, resolvedBranchPairs, unresolvedBranchPairs, resolvedBranchPairsWithResolvent},
		canonicalBranchPairs = MultiwaySystem[CellularAutomaton[rules], "CanonicalBranchPairsList", options];
		resolvedBranchPairs = Select[canonicalBranchPairs, convergentCanonicalBranchPairQ[First[getCellularAutomatonSubstitutionRules[
			rules]], #, stepCount]&];
		unresolvedBranchPairs = Complement[canonicalBranchPairs, resolvedBranchPairs];
		resolvedBranchPairsWithResolvent =
			If[
				OptionValue["GiveResolvents"] === True,
				# -> getCanonicalBranchPairResolvent[rules, #, stepCount]& /@ resolvedBranchPairs,
				resolvedBranchPairs
			];
		<|"Resolved" -> resolvedBranchPairsWithResolvent, "Unresolved" -> unresolvedBranchPairs|>
	]

MultiwaySystem[CellularAutomaton[rule_Integer], stepCount_Integer, "CanonicalBranchPairResolutionsList"] :=
	MultiwaySystem[CellularAutomaton[rule], stepCount, "CanonicalBranchPairResolutionsList", "IncludeSelfPairs" -> False
		]

MultiwaySystem[CellularAutomaton[rule_Integer], stepCount_Integer, "CanonicalBranchPairResolutionsList", options : OptionsPattern[
	]] :=
	MultiwaySystem[CellularAutomaton[{rule}], stepCount, "CanonicalBranchPairResolutionsList", options]



MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}], stepCount_Integer, "TotalCausalInvariantQ"] :=
	MultiwaySystem[CellularAutomaton[rules], stepCount, "TotalCausalInvariantQ", "IncludeSelfPairs" -> False]

MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}], stepCount_Integer, "TotalCausalInvariantQ", options : OptionsPattern[
	]] :=
	Module[{unresolvedCanonicalBranchPairsList},
		unresolvedCanonicalBranchPairsList = MultiwaySystem[CellularAutomaton[rules], stepCount, "CanonicalBranchPairResolutionsList",
			 options]["Unresolved"];
		Length[unresolvedCanonicalBranchPairsList] == 0
	]

MultiwaySystem[CellularAutomaton[rule_Integer], stepCount_Integer, "TotalCausalInvariantQ"] :=
	MultiwaySystem[CellularAutomaton[rule], stepCount, "TotalCausalInvariantQ", "IncludeSelfPairs" -> False]

MultiwaySystem[CellularAutomaton[rule_Integer], stepCount_Integer, "TotalCausalInvariantQ", options : OptionsPattern[
	]] :=
	MultiwaySystem[CellularAutomaton[{rule}], stepCount, "TotalCausalInvariantQ", options]



MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}], "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[CellularAutomaton[rules], "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}], "CanonicalKnuthBendixCompletion", options : OptionsPattern[
	]] :=
	Module[{canonicalBranchPairsList},
		canonicalBranchPairsList = MultiwaySystem[CellularAutomaton[rules], "CanonicalBranchPairsList"];
		Catenate[{First[#] -> Last[#], Last[#] -> First[#]}& /@ canonicalBranchPairsList]
	]

MultiwaySystem[CellularAutomaton[rule_Integer], "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[CellularAutomaton[rule], "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem[CellularAutomaton[rule_Integer], "CanonicalKnuthBendixCompletion", options : OptionsPattern[]] :=
	MultiwaySystem[CellularAutomaton[{rule}], "CanonicalKnuthBendixCompletion", options]



MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}], stepCount_Integer, "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[CellularAutomaton[rules], stepCount, "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem[CellularAutomaton[rules : {(_Integer)..}], stepCount_Integer, "CanonicalKnuthBendixCompletion", options
	 : OptionsPattern[]] :=
	Module[{unresolvedCanonicalBranchPairsList},
		unresolvedCanonicalBranchPairsList = MultiwaySystem[CellularAutomaton[rules], stepCount, "CanonicalBranchPairResolutionsList"
			]["Unresolved"];
		Catenate[{First[#] -> Last[#], Last[#] -> First[#]}& /@ unresolvedCanonicalBranchPairsList]
	]

MultiwaySystem[CellularAutomaton[rule_Integer], stepCount_Integer, "CanonicalKnuthBendixCompletion"] :=
	MultiwaySystem[CellularAutomaton[rule], stepCount, "CanonicalKnuthBendixCompletion", "IncludeSelfPairs" -> False]

MultiwaySystem[CellularAutomaton[rule_Integer], stepCount_Integer, "CanonicalKnuthBendixCompletion", options : OptionsPattern[
	]] :=
	MultiwaySystem[CellularAutomaton[{rule}], stepCount, "CanonicalKnuthBendixCompletion", options]



getCellularAutomatonSubstitutionRules[rules : {(_Integer)..}] :=
	Module[{ruleNumber = #},
			Thread[Tuples[{1, 0}, 3] -> MapIndexed[ReplacePart[#1, 2 -> First[IntegerDigits[ruleNumber, 2, 8][[#2]]]]&, Tuples[
				{1, 0}, 3]]]
		]& /@ rules



getCellularAutomatonStateEvolutionFunction[state_List, rules : {(_Integer)..}] :=
	Module[{left, right},
		With[{prunedRules = ((Join[{left___}, #1, {right___}] -> Join[{left}, #2, {right}])& @@@ Catenate[getCellularAutomatonSubstitutionRules[
			rules]])},
			Drop[Drop[#, 1], -1]& /@
				ReplaceList[
					With[{firstElement = First[state], lastElement = Last[state]},
						Prepend[Append[state, firstElement], lastElement]
					],
					prunedRules
				]
		]
	]

getCellularAutomatonStateEvolutionFunction[{stepNumber_Integer, stateID_Integer} -> state_List, rules : {(_Integer)..
	}] :=
	({stepNumber + 1, RandomInteger[10^10]} -> #)& /@
		Module[{left, right},
			With[{prunedRules = ((Join[{left___}, #1, {right___}] -> Join[{left}, #2, {right}])& @@@ Catenate[getCellularAutomatonSubstitutionRules[
				rules]])},
				Drop[Drop[#, 1], -1]& /@
					ReplaceList[
						With[{firstElement = First[state], lastElement = Last[state]},
							Prepend[Append[state, firstElement], lastElement]
						],
						prunedRules
					]
			]
		]

getCellularAutomatonStateEvolutionFunction[stepNumber_Integer -> state_List, rules : {(_Integer)..}] :=
	((stepNumber + 1) -> #)& /@
		Module[{left, right},
			With[{prunedRules = ((Join[{left___}, #1, {right___}] -> Join[{left}, #2, {right}])& @@@ Catenate[getCellularAutomatonSubstitutionRules[
				rules]])},
				Drop[Drop[#, 1], -1]& /@
					ReplaceList[
						With[{firstElement = First[state], lastElement = Last[state]},
							Prepend[Append[state, firstElement], lastElement]
						],
						prunedRules
					]
			]
		]

getCellularAutomatonStateEvolutionFunction[{Automatic, stateID_Integer} -> state_List, rules : {(_Integer)..}] :=
	({Automatic, RandomInteger[10^10]} -> #)& /@
		Module[{left, right},
			With[{prunedRules = ((Join[{left___}, #1, {right___}] -> Join[{left}, #2, {right}])& @@@ Catenate[getCellularAutomatonSubstitutionRules[
				rules]])},
				Drop[Drop[#, 1], -1]& /@
					ReplaceList[
						With[{firstElement = First[state], lastElement = Last[state]},
							Prepend[Append[state, firstElement], lastElement]
						],
						prunedRules
					]
			]
		]



getCellularAutomatonStateEquivalenceFunction[state1_List, state2_List] :=
	SameQ[state1, state2]

getCellularAutomatonStateEquivalenceFunction[state1_Rule, state2_Rule] :=
	SameQ[state1, state2]



getCellularAutomatonReplacementEvent[state_List, rule : (_List -> _List)] :=
	Module[{firstElement = First[state], lastElement = Last[state], paddedState},
			paddedState = Prepend[Append[state, firstElement], lastElement];
			{First[rule] -> (Last[rule])[[2]], First[rule], {Take[paddedState, First[#] - 1], Drop[paddedState, Last[#]]}}& /@
				 SequencePosition[paddedState, First[rule]]
		] /; Depth[state] == 2

getCellularAutomatonReplacementEvent[state_List, rules : {(_List -> _List)..}] :=
	getCellularAutomatonReplacementEvent[{state}, rules] /; Depth[state] == 2

getCellularAutomatonReplacementEvent[states : {_List...}, rules : {(_List -> _List)..}] :=
	Catenate[
			Function[currentState,
					Catenate[getCellularAutomatonReplacementEvent[currentState, #]& /@ rules]
				] /@ states
		] /; Depth[states] > 2

getCellularAutomatonReplacementEvent[state_List, rule : (_Integer)] :=
	getCellularAutomatonReplacementEvent[{state}, Catenate[getCellularAutomatonSubstitutionRules[{rule}]]] /; Depth[state
		] == 2

getCellularAutomatonReplacementEvent[state_List, rules : {(_Integer)..}] :=
	getCellularAutomatonReplacementEvent[{state}, rules] /; Depth[state] == 2

getCellularAutomatonReplacementEvent[states : {_List...}, rules : {(_Integer)..}] :=
	Catenate[
			Function[currentState,
					Catenate[getCellularAutomatonReplacementEvent[currentState, #]& /@ rules]
				] /@ states
		] /; Depth[states] > 2

getCellularAutomatonReplacementEvent[{stepNumber_Integer, stateID_Integer} -> state_List, rule : (_List -> _List)] :=
	Module[{firstElement = First[state], lastElement = Last[state], paddedState},
			paddedState = Prepend[Append[state, firstElement], lastElement];
			({stepNumber, {stateID, RandomInteger[10^10]}} -> {First[rule] -> (Last[rule])[[2]], First[rule], {Take[paddedState,
				 First[#] - 1], Drop[paddedState, Last[#]]}})& /@ SequencePosition[paddedState, First[rule]]
		] /; Depth[state] == 2

getCellularAutomatonReplacementEvent[stepNumber_Integer -> state_List, rule : (_List -> _List)] :=
	Module[{firstElement = First[state], lastElement = Last[state], paddedState},
			paddedState = Prepend[Append[state, firstElement], lastElement];
			(stepNumber -> {First[rule] -> (Last[rule])[[2]], First[rule], {Take[paddedState, First[#] - 1], Drop[paddedState,
				 Last[#]]}})& /@ SequencePosition[paddedState, First[rule]]
		] /; Depth[state] == 2

getCellularAutomatonReplacementEvent[{Automatic, stateID_Integer} -> state_List, rule : (_List -> _List)] :=
	Module[{firstElement = First[state], lastElement = Last[state], paddedState},
			paddedState = Prepend[Append[state, firstElement], lastElement];
			({Automatic, {stateID, RandomInteger[10^10]}} -> {First[rule] -> (Last[rule])[[2]], First[rule], {Take[paddedState,
				 First[#] - 1], Drop[paddedState, Last[#]]}})& /@ SequencePosition[paddedState, First[rule]]
		] /; Depth[state] == 2

getCellularAutomatonReplacementEvent[state_Rule, rules : {(_List -> _List)..}] :=
	getCellularAutomatonReplacementEvent[{state}, rules] /; Depth[state] == 2

getCellularAutomatonReplacementEvent[states : {_Rule...}, rules : {(_List -> _List)..}] :=
	Catenate[
		Function[currentState,
				Catenate[getCellularAutomatonReplacementEvent[currentState, #]& /@ rules]
			] /@ states
	]

getCellularAutomatonReplacementEvent[state_Rule, rule : (_Integer)] :=
	getCellularAutomatonReplacementEvent[{state}, Catenate[getCellularAutomatonSubstitutionRules[{rule}]]]

getCellularAutomatonReplacementEvent[state_Rule, rules : {(_Integer)..}] :=
	getCellularAutomatonReplacementEvent[{state}, rules]

getCellularAutomatonReplacementEvent[states : {_Rule...}, rules : {(_Integer)..}] :=
	Catenate[
		Function[currentState,
				Catenate[getCellularAutomatonReplacementEvent[currentState, #]& /@ rules]
			] /@ states
	]



getCellularAutomatonStateEventFunction[state_List, rules : {(_List -> _List)..}] :=
	getCellularAutomatonReplacementEvent[state, rules] /; Depth[state] == 2

getCellularAutomatonStateEventFunction[states : {_List...}, rules : {(_List -> _List)..}] :=
	getCellularAutomatonReplacementEvent[states, rules] /; Depth[states] > 2

getCellularAutomatonStateEventFunction[state_Rule, rules : {(_List -> _List)..}] :=
	getCellularAutomatonReplacementEvent[state, rules]

getCellularAutomatonStateEventFunction[states : {_Rule...}, rules : {(_List -> _List)..}] :=
	getCellularAutomatonReplacementEvent[states, rules]

getCellularAutomatonStateEventFunction[state_List, rules : {(_Integer)..}] :=
	getCellularAutomatonReplacementEvent[state, rules] /; Depth[state] == 2

getCellularAutomatonStateEventFunction[states : {_List...}, rules : {(_Integer)..}] :=
	getCellularAutomatonReplacementEvent[states, rules] /; Depth[states] > 2

getCellularAutomatonStateEventFunction[state_Rule, rules : {(_Integer)..}] :=
	getCellularAutomatonReplacementEvent[state, rules]

getCellularAutomatonStateEventFunction[states : {_Rule...}, rules : {(_Integer)..}] :=
	getCellularAutomatonReplacementEvent[states, rules]



getCellularAutomatonElementShifts[shiftedFragment_List, {input : {inputPrefix_List, inputSuffix_List}, output : {outputPrefix_List,
	 outputSuffix_List}}] :=
	Table[Rule @@ ({Part[shiftedFragment, position], {Join[#1, Take[shiftedFragment,  ;; position - 1]], Join[Take[shiftedFragment,
		 position + 1 ;; ], #2]}}& @@@ {input, output}), {position, Length[shiftedFragment]}]

getCellularAutomatonElementShifts[{(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol
	), {prefix_List, suffix_List}}] :=
	Join[getCellularAutomatonElementShifts[prefix, {{{}, Join[input, suffix]}, {{}, Join[{First[input], output, Last[input
		]}, suffix]}}], getCellularAutomatonElementShifts[suffix, {{Join[prefix, input], {}}, {Join[prefix, {First[input], output,
		 Last[input]}], {}}}]]



getCellularAutomatonElements[{sublist_List, {prefix_List, suffix_List}}] :=
	{Part[sublist, #], {Join[prefix, Take[sublist,  ;; # - 1]], Join[Take[sublist, # + 1 ;; ], suffix]}}& /@ Range[Length[
		sublist]]



getCellularAutomatonEventDecompositionFunction[event : {(input_List | input_Symbol) -> (output_Integer | output_Symbol
	), (input_List | input_Symbol), {prefix_List, suffix_List}}] :=
	Join[{getCellularAutomatonElementShifts[event]}, getCellularAutomatonElements[{#, {prefix, suffix}}]& /@ {input, {First[
		input], output, Last[input]}}]



getCellularAutomatonEventApplicationFunction[{input_List -> output_Integer, input_List, {prefix_List, suffix_List}}] :=
	Drop[Drop[Join[prefix, {First[input], output, Last[input]}, suffix], 1], -1]

getCellularAutomatonEventApplicationFunction[{input_Symbol -> output_Symbol, input_Symbol, {prefix_List, suffix_List
	}}] :=
	prefix

getCellularAutomatonEventApplicationFunction[{stepNumber_Integer, {inputStateID_Integer, outputStateID_Integer}} -> 
	{input_List -> output_Integer, input_List, {prefix_List, suffix_List}}] :=
	{stepNumber + 1, outputStateID} -> Drop[Drop[Join[prefix, {First[input], output, Last[input]}, suffix], 1], -1]

getCellularAutomatonEventApplicationFunction[{stepNumber_Integer, {inputStateID_Symbol, outputStateID_Integer}} -> {
	input_Symbol -> output_Symbol, input_Symbol, {prefix_List, suffix_List}}] :=
	{stepNumber + 1, outputStateID} -> prefix

getCellularAutomatonEventApplicationFunction[stepNumber_Integer -> {input_List -> output_Integer, input_List, {prefix_List,
	 suffix_List}}] :=
	(stepNumber + 1) -> Drop[Drop[Join[prefix, {First[input], output, Last[input]}, suffix], 1], -1]

getCellularAutomatonEventApplicationFunction[stepNumber_Integer -> {input_Symbol -> output_Symbol, input_Symbol, {prefix_List,
	 suffix_List}}] :=
	(stepNumber + 1) -> prefix

getCellularAutomatonEventApplicationFunction[{Automatic, {inputStateID_Integer, outputStateID_Integer}} -> {input_List
	 -> output_Integer, input_List, {prefix_List, suffix_List}}] :=
	{Automatic, outputStateID} -> Drop[Drop[Join[prefix, {First[input], output, Last[input]}, suffix], 1], -1]

getCellularAutomatonEventApplicationFunction[{Automatic, {inputStateID_Symbol, outputStateID_Integer}} -> {input_Symbol
	 -> output_Symbol, input_Symbol, {prefix_List, suffix_List}}] :=
	{Automatic, outputStateID} -> prefix



MultiwaySystem["CellularAutomaton" -> (rules : {(_Integer)..}), rest___] :=
	MultiwaySystem[<|"StateEvolutionFunction" -> (getCellularAutomatonStateEvolutionFunction[#, rules]&), "StateEquivalenceFunction"
		 -> getCellularAutomatonStateEquivalenceFunction, "StateEventFunction" -> (getCellularAutomatonStateEventFunction[#,
		 rules]&), "EventDecompositionFunction" -> getCellularAutomatonEventDecompositionFunction, "EventApplicationFunction"
		 -> getCellularAutomatonEventApplicationFunction, "SystemType" -> "CellularAutomaton", "EventSelectionFunction" -> Identity
		|>, rest]

MultiwaySystem["CellularAutomaton" -> (rules : {(_Integer)..}) -> eventSelectionFunction_, rest___] :=
	MultiwaySystem[<|"StateEvolutionFunction" -> (getCellularAutomatonStateEvolutionFunction[#, rules]&), "StateEquivalenceFunction"
		 -> getCellularAutomatonStateEquivalenceFunction, "StateEventFunction" -> (getCellularAutomatonStateEventFunction[#,
		 rules]&), "EventDecompositionFunction" -> getCellularAutomatonEventDecompositionFunction, "EventApplicationFunction"
		 -> getCellularAutomatonEventApplicationFunction, "SystemType" -> "CellularAutomaton", "EventSelectionFunction" -> getEventSelectionFunction[
		eventSelectionFunction]|>, rest]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, options : OptionsPattern[]] :=
	MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
		 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
		 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
		 stepCount, "AllStatesList", options]



preProcessInitialStates[initialStates_List, True, True] :=
	({0, RandomInteger[10^10]} -> #)& /@ initialStates

preProcessInitialStates[initialStates_List, True, False] :=
	(0 -> #)& /@ initialStates

preProcessInitialStates[initialStates_List, False, True] :=
	({Automatic, RandomInteger[10^10]} -> #)& /@ initialStates

preProcessInitialStates[initialStates_List, False, False] :=
	initialStates



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> Identity|>, initialConditions_List,
	 stepCount_Integer, "AllStatesList", options : OptionsPattern[]] :=
	getCanonicalStatesList[NestList[Union[Catenate[stateEvolutionFunction /@ #], SameTest -> stateEquivalenceFunction]&,
		 preProcessInitialStates[initialConditions, OptionValue["IncludeStepNumber"], OptionValue["IncludeStateID"]], stepCount
		], systemType]

MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction
	 : Except[Identity, _]|>, initialConditions_List, stepCount_Integer, "AllStatesList", options : OptionsPattern[]] :=
	getCanonicalStatesList[Union[eventApplicationFunction /@ #, SameTest -> stateEquivalenceFunction]& /@ MultiwaySystem[
		<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction, "StateEventFunction"
		 -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction" -> eventApplicationFunction,
		 "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions, stepCount, "AllEventsList",
		 options, "IncludeInitializationEvents" -> True], systemType]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> Identity|>, initialConditions_List,
	 stepCount_Integer, "AllStatesListUnmerged", options : OptionsPattern[]] :=
	NestList[Catenate[stateEvolutionFunction /@ #]&, preProcessInitialStates[initialConditions, OptionValue["IncludeStepNumber"
		], OptionValue["IncludeStateID"]], stepCount]

MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction
	 : Except[Identity, _]|>, initialConditions_List, stepCount_Integer, "AllStatesListUnmerged", options : OptionsPattern[
	]] :=
	getCanonicalStatesList[(eventApplicationFunction /@ #)& /@ MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction,
		 "StateEquivalenceFunction" -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction"
		 -> eventDecompositionFunction, "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, 
		"EventSelectionFunction" -> eventSelectionFunction|>, initialConditions, stepCount, "AllEventsList", options, "IncludeInitializationEvents"
		 -> True], systemType]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "StateWeights", options : OptionsPattern[]] :=
	Which[
		OptionValue["IncludeStatePathWeights"] === True,
		Normal[Counts[Catenate[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "AllStatesListUnmerged", options]]]],
		OptionValue["IncludeStateWeights"] === True,
		With[{stateCounts = Length[#]& /@ MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "AllStatesListUnmerged", "IncludeStepNumber" -> True, options]},
			If[
				OptionValue["IncludeStepNumber"],
				If[
					OptionValue["IncludeStateID"],
					(First[#] -> Last[#] * (1 / stateCounts[[First[First[First[#]]] + 1]]))& /@ Normal[Counts[Catenate[MultiwaySystem[
						<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction, "StateEventFunction"
						 -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction" -> eventApplicationFunction,
						 "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions, stepCount, "AllStatesListUnmerged",
						 "IncludeStepNumber" -> True, "IncludeStateID" -> True, options]]]],
					(First[#] -> Last[#] * (1 / stateCounts[[First[First[#]] + 1]]))& /@ Normal[Counts[Catenate[MultiwaySystem[<|"StateEvolutionFunction"
						 -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction,
						 "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction" -> eventApplicationFunction,
						 "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions, stepCount, "AllStatesListUnmerged",
						 "IncludeStepNumber" -> True, options]]]]
				],
				If[
					OptionValue["IncludeStateID"],
					(Last[First[#]] -> Last[#] * (1 / stateCounts[[First[First[First[#]]] + 1]]))& /@ Normal[Counts[Catenate[MultiwaySystem[
						<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction, "StateEventFunction"
						 -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction" -> eventApplicationFunction,
						 "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions, stepCount, "AllStatesListUnmerged",
						 "IncludeStepNumber" -> True, "IncludeStateID" -> True, options]]]],
					(Last[First[#]] -> Last[#] * (1 / stateCounts[[First[First[#]] + 1]]))& /@ Normal[Counts[Catenate[MultiwaySystem[
						<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction, "StateEventFunction"
						 -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction" -> eventApplicationFunction,
						 "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions, stepCount, "AllStatesListUnmerged",
						 "IncludeStepNumber" -> True, options]]]]
				]
			]
		],
		!OptionValue["IncludeStatePathWeights"] && !OptionValue["IncludeStateWeights"],
		None
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "StatesCountsList", options : OptionsPattern[]] :=
	Length[#]& /@ MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
		 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
		 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
		 stepCount, "AllStatesList", options]



getPredecessorStates[stateEvolutionFunction_, state_, stateEventFunction_, eventApplicationFunction_, Identity] :=
	SortBy[
		(#[[1, 1]] -> Sort[(Last /@ #)])& /@
			GatherBy[
				Catenate[
					(
							Function[x,
									x -> #
								] /@ stateEvolutionFunction[#]
						)& /@ state
				],
				First
			],
		First
	]

getPredecessorStates[stateEvolutionFunction_, state_, stateEventFunction_, eventApplicationFunction_, eventSelectionFunction
	 : Except[Identity, _]] :=
	SortBy[
		(#[[1, 1]] -> Sort[(Last /@ #)])& /@
			GatherBy[
				Catenate[
					(
							Function[x,
									x -> #
								] /@
								(
									eventApplicationFunction /@
										If[
											stateEventFunction[{#}] === {},
											{},
											eventSelectionFunction[stateEventFunction[{#}]]
										]
								)
						)& /@ state
				],
				First
			],
		First
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "PredecessorRulesList", options : OptionsPattern[]] :=
	getCanonicalPredecessorRulesList[NestList[getPredecessorStates[stateEvolutionFunction, First /@ #, stateEventFunction,
		 eventApplicationFunction, eventSelectionFunction]&, (# -> {})& /@ preProcessInitialStates[initialConditions, OptionValue[
		"IncludeStepNumber"], OptionValue["IncludeStateID"]], stepCount], systemType]



stripMetadata[expression_] :=
	If[
		Head[expression] === Rule,
		Last[expression],
		expression
	]



getWolframModelStateRenderingFunction[{xCoordinate_, yCoordinate_}, state_List, {width_, height_}] :=
	Inset[Framed[Style[ResourceFunction["WolframModelPlot"][state], Hue[0.62, 1, 0.48]], Background -> Directive[{Hue[0.63,
		 0.41, 1], Opacity[0.115]}], FrameMargins -> {{2, 2}, {0, 0}}, RoundingRadius -> 0], {xCoordinate, yCoordinate}, Center,
		 {width, height}]



getStateRenderingFunction[systemType_String, Inherited, multiplier_] :=
	"Name"

getStateRenderingFunction[systemType_String, None, multiplier_] :=
	"Circle"

getStateRenderingFunction[systemType_String, name_String, multiplier_] :=
	name

getStateRenderingFunction[systemType_String, function_Function, multiplier_] :=
	function

getStateRenderingFunction["StringSubstitutionSystem", Automatic, multiplier_] :=
	(Text[Framed[Style[stripMetadata[#2], Hue[0.62, 1, 0.48]], Background -> Directive[Opacity[0.2], Hue[0.62, 0.45, 0.87
		]], FrameMargins -> {{2, 2}, {0, 0}}, RoundingRadius -> 0, FrameStyle -> Directive[Opacity[0.5], Hue[0.62, 0.52, 0.82
		]]], #1, {0, 0}]&)

getStateRenderingFunction["ListSubstitutionSystem", Automatic, multiplier_] :=
	(Text[Framed[Style[Row[stripMetadata[#2]], Hue[0.62, 1, 0.48]], Background -> Directive[Opacity[0.2], Hue[0.62, 0.45,
		 0.87]], FrameMargins -> {{2, 2}, {0, 0}}, RoundingRadius -> 0, FrameStyle -> Directive[Opacity[0.5], Hue[0.62, 0.52,
		 0.82]]], #1, {0, 0}]&)

getStateRenderingFunction["WolframModel", Automatic, multiplier_] :=
	(getWolframModelStateRenderingFunction[#1, stripMetadata[#2], #3 * multiplier]&)

getStateRenderingFunction["CellularAutomaton", Automatic, multiplier_] :=
	(Inset[Framed[Style[ArrayPlot[{stripMetadata[#2]}], Hue[0.62, 1, 0.48]], Background -> Directive[Opacity[0.2], Hue[
		0.62, 0.45, 0.87]], FrameMargins -> {{2, 2}, {0, 0}}, RoundingRadius -> 0, FrameStyle -> Directive[Opacity[0.5], Hue[
		0.62, 0.52, 0.82]]], #1, Center, #3 * multiplier]&)



getGraphQuality[renderingFunctions_List] :=
	If[
		AllTrue[renderingFunctions, # === None || StringQ[#]&],
		"Speed",
		"Quality"
	]



getEventRenderingForm[function_, {(input_String | input_Symbol) -> output_String, (input_String | input_Symbol), {prefix_String,
	 suffix_String}}] :=
	Row[{function[prefix], Column[{function[input], function[output]}, Center, 0], function[suffix]}]

getEventRenderingForm[function_, {input_List -> output_List, input_List, {prefix_List, suffix_List}}] :=
	Row[{function[prefix], Column[{function[input], function[output]}, Center, 0], function[suffix]}]

getEventRenderingForm[function_, {input_Symbol -> output_List, input_Symbol, {prefix_List, suffix_List}}] :=
	Row[{function[prefix], Column[{Null, function[output]}, Center, 0], function[suffix]}]

getEventRenderingForm[function_, {input_List -> output_Integer, input_List, {prefix_List, suffix_List}}] :=
	Row[{Column[{function[ArrayPlot[{input}]], function[ArrayPlot[{{First[input], output, Last[input]}}]]}, Center, 0]}
		]

getEventRenderingForm[function_, {input_Symbol -> output_Symbol, input_Symbol, {prefix_List, suffix_List}}] :=
	Row[{function[ArrayPlot[{prefix}]]}]



getWolframModelGlobalEventPlot[evolution_, {destroyedStyle_ : Directive[Hue[0.6, 0.7, 0.5], Dotted], createdStyle_ :
	 Directive[Hue[0.86, 0.7, 0.5], Thick]}, options___] :=
	Module[{createdExpressions, destroyedExpressions, events, stateIndices, pictures},
		{createdExpressions, destroyedExpressions} = PositionIndex[evolution[#]]& /@ {"CreatorEvents", "DestroyerEvents"};
			
		events = Rule @@ Table[Lookup[expression, #, {}], {expression, {destroyedExpressions, createdExpressions}}]& /@ Range[
			evolution["EventsCount"]];
		stateIndices =
			FoldList[
				Join[
					DeleteCases[#, Alternatives @@ #2[[1]]],
					If[
						Length[#] > 1,
						#[[2]],
						#
					]
				]&,
				Range[Length[evolution[0]]],
				events
			];
		pictures = MapThread[ResourceFunction["WolframModelPlot"][evolution["AllExpressions"][[#]], EdgeStyle -> ReplacePart[
			Table[Automatic, Length[#]], Join[Thread[Position[#, Alternatives @@ #2][[All, 1]] -> destroyedStyle], Thread[Position[
			#, Alternatives @@ #3][[All, 1]] -> createdStyle]]], options]&, {stateIndices, Append[events[[All, 1]], {}], Prepend[
			events[[All, 2]], {}]}];
		TakeList[pictures, Prepend[Length /@ Split[evolution["EventGenerations"]], 1]]
	]



(*getWolframModelMultiwayEventRenderer[{instantiatedRule_,ruleInput_,{otherEdges_,{}}}]:=Module[{events},
events=Flatten[getWolframModelGlobalEventPlot[ResourceFunction["WolframModel"][<|"PatternRules"\[Rule]instantiatedRule|>,Join[ruleInput,otherEdges],<|"MaxEvents"\[Rule]1|>],{}]];
Graphics[{Inset[First[events],{0,0},Right,Scaled[3.5]],Inset[Graphics[{Thickness[0.011494],FaceForm[{RGBColor[0.5,0.5,0.5],Opacity[1]}],FilledCurve[{{{0,2,0},{0,1,0},{0,1,0},{0,1,0},{0,1,0},{0,1,0}}},{{{66.24000000000001,72.75066399999997},{28.6875,14.385663999999991`},{14.985,14.385663999999991`},{52.605,72.75066399999997},{14.985,131.02566399999998`},{28.6875,131.02566399999998`},{66.24000000000001,72.75066399999997}}}]}],{1,0},Center,Scaled[2]],Inset[Last[events],{2,0},Left,Scaled[3.5]]}]]*)



getWolframModelMultiwayEventRenderer[{instantiatedRule_, ruleInput_, {otherEdges_, {}}}] :=
	Module[{events},
		events = ResourceFunction["WolframModel"][<|"PatternRules" -> instantiatedRule|>, Join[ruleInput, otherEdges], <|"MaxEvents"
			 -> 1|>, "EventsStatesPlotsList"];
		Graphics[{Inset[First[events], {0, 0}, Right, Scaled[3.5]], Inset[Graphics[{Thickness[0.011494], FaceForm[{RGBColor[
			0.5, 0.5, 0.5], Opacity[1]}], FilledCurve[{{{0, 2, 0}, {0, 1, 0}, {0, 1, 0}, {0, 1, 0}, {0, 1, 0}, {0, 1, 0}}}, {{{66.24000000000001,
			 72.75066399999997}, {28.6875, 14.385663999999991`}, {14.985, 14.385663999999991`}, {52.605, 72.75066399999997}, {14.985,
			 131.02566399999998`}, {28.6875, 131.02566399999998`}, {66.24000000000001, 72.75066399999997}}}]}], {1, 0}, Center, 
			Scaled[2]], Inset[Last[events], {2, 0}, Left, Scaled[3.5]]}]
	]



getEventRenderingFunction[systemType_String, Inherited, multiplier_] :=
	"Name"

getEventRenderingFunction[systemType_String, None, multiplier_] :=
	"Diamond"

getEventRenderingFunction[systemType_String, name_String, multiplier_] :=
	name

getEventRenderingFunction[systemType_String, function_, multiplier_] :=
	function

getEventRenderingFunction["StringSubstitutionSystem", Automatic, multiplier_] :=
	(
		If[
			First[First[stripMetadata[#2]]] === Null,
			Text[Framed[Style[getEventRenderingForm[Identity, stripMetadata[#2]], Hue[0.09, 1, 0.32]], Background -> Directive[
				Opacity[0.7], RGBColor[0.259, 0.576, 1]], FrameMargins -> {{2, 2}, {0, 0}}, RoundingRadius -> 0, FrameStyle -> Directive[
				Opacity[0.4], Hue[0.09, 1, 0.91]]], #1, {0, 0}],
			Text[Framed[Style[getEventRenderingForm[Identity, stripMetadata[#2]], Hue[0.09, 1, 0.32]], Background -> Directive[
				Opacity[0.7], Hue[0.14, 0.34, 1]], FrameMargins -> {{2, 2}, {0, 0}}, RoundingRadius -> 0, FrameStyle -> Directive[Opacity[
				0.4], Hue[0.09, 1, 0.91]]], #1, {0, 0}]
		]&
	)

getEventRenderingFunction["ListSubstitutionSystem", Automatic, multiplier_] :=
	(
		If[
			First[First[stripMetadata[#2]]] === Null,
			Text[Framed[Style[getEventRenderingForm[Row, stripMetadata[#2]], Hue[0.09, 1, 0.32]], Background -> Directive[Opacity[
				0.7], RGBColor[0.259, 0.576, 1]], FrameMargins -> {{2, 2}, {0, 0}}, RoundingRadius -> 0, FrameStyle -> Directive[Opacity[
				0.4], Hue[0.09, 1, 0.91]]], #1, {0, 0}],
			Text[Framed[Style[getEventRenderingForm[Row, stripMetadata[#2]], Hue[0.09, 1, 0.32]], Background -> Directive[Opacity[
				0.7], Hue[0.14, 0.34, 1]], FrameMargins -> {{2, 2}, {0, 0}}, RoundingRadius -> 0, FrameStyle -> Directive[Opacity[0.4
				], Hue[0.09, 1, 0.91]]], #1, {0, 0}]
		]&
	)

getEventRenderingFunction["WolframModel", Automatic, multiplier_] :=
	(Inset[Framed[getWolframModelMultiwayEventRenderer[#2], FrameStyle -> Directive[Hue[0.09, 1, 0.91], Opacity[0.7]], 
		Background -> Directive[{Hue[0.14, 0.34, 1], Opacity[0.2]}]], #1, Center, #3 * 1.2 * multiplier]&)

getEventRenderingFunction["CellularAutomaton", Automatic, multiplier_] :=
	(
		If[
			First[First[stripMetadata[#2]]] === Null,
			Inset[Framed[Style[getEventRenderingForm[Identity, stripMetadata[#2]], Hue[0.09, 1, 0.32]], Background -> Directive[
				Opacity[0.7], RGBColor[0.259, 0.576, 1]], FrameMargins -> {{2, 2}, {0, 0}}, RoundingRadius -> 0, FrameStyle -> Directive[
				Opacity[0.4], Hue[0.09, 1, 0.91]]], #1, Center, #3 * multiplier],
			Inset[Framed[Style[getEventRenderingForm[Identity, stripMetadata[#2]], Hue[0.09, 1, 0.32]], Background -> Directive[
				Opacity[0.7], Hue[0.14, 0.34, 1]], FrameMargins -> {{2, 2}, {0, 0}}, RoundingRadius -> 0, FrameStyle -> Directive[Opacity[
				0.4], Hue[0.09, 1, 0.91]]], #1, Center, #3 * multiplier]
		]&
	)



getStateEventRenderingFunction[systemType_String, stateRenderingFunction_, statesList_List, eventRenderingFunction_,
	 eventsList_List, multiplier_] :=
	Join[# -> getEventRenderingFunction[systemType, eventRenderingFunction, multiplier]& /@ eventsList, # -> getStateRenderingFunction[
		systemType, stateRenderingFunction, multiplier]& /@ statesList]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "StatesGraph", options : OptionsPattern[]] :=
	If[
		stepCount > 0,
		If[
			OptionValue["IncludeEventInstances"],
			Identity,
			SimpleGraph
		][
			Graph[
				Catenate[
					Map[
						(
							Function[state,
									state -> First[#]
								] /@ Last[#]
						)&,
						Catenate[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
							 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
							 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
							 stepCount, "PredecessorRulesList", options]]
					]
				],
				VertexShapeFunction -> getStateRenderingFunction[systemType, OptionValue["StateRenderingFunction"], OptionValue[
					"VertexSizeMultiplier"]],
				EdgeStyle -> Directive[{Hue[0.75, 0, 0.35], Dashing[None], AbsoluteThickness[OptionValue["LineThickness"]]}],
				PerformanceGoal -> getGraphQuality[{OptionValue["StateRenderingFunction"]}],
				VertexWeight -> MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" 
					-> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
					 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
					|>, initialConditions, stepCount, "StateWeights", options],
				FilterRules[{options}, Options[Graph]]
			]
		],
		Graph[Catenate[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> 
			stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "AllStatesList", options]], {}, VertexShapeFunction -> getStateRenderingFunction[systemType,
			 OptionValue["StateRenderingFunction"], OptionValue["VertexSizeMultiplier"]], EdgeStyle -> Directive[{Hue[0.75, 0, 0.35
			], Dashing[None], AbsoluteThickness[OptionValue["LineThickness"]]}], PerformanceGoal -> getGraphQuality[{OptionValue[
			"StateRenderingFunction"]}], VertexWeight -> MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "StateWeights", options], FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "StatesGraphStructure", options : OptionsPattern[]] :=
	Module[{statesGraph},
		statesGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
			 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
			 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
			 stepCount, "StatesGraph", options];
		Graph[statesGraph, VertexStyle -> Directive[Opacity[0.7], Hue[0.62, 0.45, 0.87]], VertexShapeFunction -> ((# -> Automatic
			)& /@ VertexList[statesGraph]), FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionGraphFull", options : OptionsPattern[]] :=
	Module[{statesGraph},
		statesGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
			 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
			 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
			 stepCount, "StatesGraph", "IncludeStepNumber" -> True, "IncludeStateID" -> False, "IncludeEventInstances" -> True];
			
		Graph[statesGraph, VertexCoordinates -> (# -> {Automatic, stepCount - First[#]}& /@ VertexList[statesGraph]), GraphLayout
			 -> "LayeredDigraphEmbedding", VertexWeight -> MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, 
			"StateEquivalenceFunction" -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction"
			 -> eventDecompositionFunction, "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, 
			"EventSelectionFunction" -> eventSelectionFunction|>, initialConditions, stepCount, "StateWeights", "IncludeStepNumber"
			 -> True, "IncludeStateID" -> False, "IncludeEventInstances" -> True, "IncludeStateWeights" -> OptionValue["IncludeStateWeights"
			], "IncludeStatePathWeights" -> OptionValue["IncludeStatePathWeights"]], FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionGraphFullStructure", options : OptionsPattern[]] :=
	Module[{evolutionGraphFull},
		evolutionGraphFull = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionGraphFull", options];
		Graph[evolutionGraphFull, VertexShapeFunction -> ((# -> Automatic)& /@ VertexList[evolutionGraphFull]), FilterRules[
			{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionGraphUnmerged", options : OptionsPattern[]] :=
	Module[{statesGraph},
		statesGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
			 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
			 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
			 stepCount, "StatesGraph", "IncludeStepNumber" -> True, "IncludeStateID" -> True, "IncludeEventInstances" -> True];
		Graph[statesGraph, VertexCoordinates -> (# -> {Automatic, stepCount - First[First[#]]}& /@ VertexList[statesGraph]
			), GraphLayout -> "LayeredDigraphEmbedding", VertexWeight -> MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction,
			 "StateEquivalenceFunction" -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction"
			 -> eventDecompositionFunction, "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, 
			"EventSelectionFunction" -> eventSelectionFunction|>, initialConditions, stepCount, "StateWeights", "IncludeStepNumber"
			 -> True, "IncludeStateID" -> True, "IncludeEventInstances" -> True, "IncludeStateWeights" -> OptionValue["IncludeStateWeights"
			], "IncludeStatePathWeights" -> OptionValue["IncludeStatePathWeights"]], FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionGraphUnmergedStructure", options : OptionsPattern[]] :=
	Module[{evolutionGraphUnmerged},
		evolutionGraphUnmerged = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionGraphUnmerged", options];
		Graph[evolutionGraphUnmerged, VertexShapeFunction -> ((# -> Automatic)& /@ VertexList[evolutionGraphUnmerged]), FilterRules[
			{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionGraphWeighted", options : OptionsPattern[]] :=
	Module[{evolutionGraphFull, evolutionGraphEdgeList, evolutionGraphWeightList},
		evolutionGraphFull = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionGraphFull", options];
		evolutionGraphEdgeList = DeleteDuplicates[EdgeList[evolutionGraphFull]];
		evolutionGraphWeightList = (Count[EdgeList[evolutionGraphFull], #]& /@ evolutionGraphEdgeList);
		Graph[evolutionGraphEdgeList, VertexShapeFunction -> getStateRenderingFunction[systemType, OptionValue["StateRenderingFunction"
			], OptionValue["VertexSizeMultiplier"]], EdgeWeight -> evolutionGraphWeightList, VertexCoordinates -> (# -> {Automatic,
			 stepCount - First[#]}& /@ VertexList[evolutionGraphFull]), GraphLayout -> "LayeredDigraphEmbedding", VertexWeight ->
			 MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
			 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
			 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
			 stepCount, "StateWeights", "IncludeStepNumber" -> True, "IncludeStateID" -> False, "IncludeEventInstances" -> False,
			 "IncludeStateWeights" -> OptionValue["IncludeStateWeights"], "IncludeStatePathWeights" -> OptionValue["IncludeStatePathWeights"
			]], FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionGraphWeightedStructure", options : OptionsPattern[]] :=
	Module[{evolutionGraphWeighted},
		evolutionGraphWeighted = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionGraphWeighted", options];
		Graph[evolutionGraphWeighted, VertexShapeFunction -> ((# -> Automatic)& /@ VertexList[evolutionGraphWeighted]), FilterRules[
			{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionGraph", options : OptionsPattern[]] :=
	Graph[SimpleGraph[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" ->
		 stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
		 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
		|>, initialConditions, stepCount, "EvolutionGraphFull", options]], GraphLayout -> "LayeredDigraphEmbedding", VertexWeight
		 -> MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
		 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
		 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
		 stepCount, "StateWeights", "IncludeStepNumber" -> True, "IncludeStateID" -> False, "IncludeEventInstances" -> False,
		 "IncludeStateWeights" -> OptionValue["IncludeStateWeights"], "IncludeStatePathWeights" -> OptionValue["IncludeStatePathWeights"
		]], FilterRules[{options}, Options[Graph]]]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionGraphStructure", options : OptionsPattern[]] :=
	Module[{evolutionGraph},
		evolutionGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" ->
			 stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionGraph", options];
		Graph[evolutionGraph, VertexShapeFunction -> ((# -> Automatic)& /@ VertexList[evolutionGraph]), FilterRules[{options
			}, Options[Graph]]]
	]



preProcessInitialEvents[initialEvents_List, True, True] :=
	({0, {Null, RandomInteger[10^10]}} -> #)& /@ initialEvents

preProcessInitialEvents[initialEvents_List, True, False] :=
	(0 -> #)& /@ initialEvents

preProcessInitialEvents[initialEvents_List, False, True] :=
	({Automatic, {Null, RandomInteger[10^10]}} -> #)& /@ initialEvents

preProcessInitialEvents[initialEvents_List, False, False] :=
	initialEvents



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "AllEventsList", options : OptionsPattern[]] :=
	Which[
		systemType === "ListSubstitutionSystem",
		If[
			OptionValue["IncludeInitializationEvents"],
			Identity,
			Rest
		][
			NestList[
				Union[
					If[
						stateEventFunction[eventApplicationFunction /@ #] === {},
						{},
						eventSelectionFunction[stateEventFunction[eventApplicationFunction /@ #]]
					]
				]&,
				preProcessInitialEvents[({Null -> #, Null, {{}, {}}}& /@ initialConditions), OptionValue["IncludeStepNumber"], OptionValue[
					"IncludeStateID"]],
				stepCount
			]
		],
		systemType === "WolframModel",
		If[
			OptionValue["IncludeInitializationEvents"],
			Identity,
			Rest
		][
			getCanonicalEventsList[
				NestList[
					Union[
						If[
							stateEventFunction[eventApplicationFunction /@ #] === {},
							{},
							eventSelectionFunction[stateEventFunction[eventApplicationFunction /@ #]]
						]
					]&,
					preProcessInitialEvents[({Null :> #, Null, {{}, {}}}& /@ initialConditions), OptionValue["IncludeStepNumber"], 
						OptionValue["IncludeStateID"]],
					stepCount
				],
				"WolframModel"
			]
		],
		systemType === "CellularAutomaton",
		If[
			OptionValue["IncludeInitializationEvents"],
			Identity,
			Rest
		][
			NestList[
				Union[
					If[
						stateEventFunction[eventApplicationFunction /@ #] === {},
						{},
						eventSelectionFunction[stateEventFunction[eventApplicationFunction /@ #]]
					]
				]&,
				preProcessInitialEvents[({Null -> Null, Null, {#, {}}}& /@ initialConditions), OptionValue["IncludeStepNumber"],
					 OptionValue["IncludeStateID"]],
				stepCount
			]
		],
		systemType =!= "ListSubstitutionSystem" && systemType =!= "WolframModel" && systemType =!= "CellularAutomaton",
		If[
			OptionValue["IncludeInitializationEvents"],
			Identity,
			Rest
		][
			NestList[
				Union[
					If[
						stateEventFunction[eventApplicationFunction /@ #] === {},
						{},
						eventSelectionFunction[stateEventFunction[eventApplicationFunction /@ #]]
					]
				]&,
				preProcessInitialEvents[({Null -> #, Null, {"", ""}}& /@ initialConditions), OptionValue["IncludeStepNumber"], OptionValue[
					"IncludeStateID"]],
				stepCount
			]
		]
	]



getTracedStatesEdge[{(input_String | input_Symbol) -> output_String, (input_String | input_Symbol), {prefix_String, 
	suffix_String}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{DirectedEdge[{input -> output, input, {prefix, suffix}}, output]},
		{DirectedEdge[eventApplicationFunction[{input -> input, input, {prefix, suffix}}], {input -> output, input, {prefix,
			 suffix}}], DirectedEdge[{input -> output, input, {prefix, suffix}}, eventApplicationFunction[{input -> output, input,
			 {prefix, suffix}}]]}
	]

getTracedStatesEdge[{stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {
	(input_String | input_Symbol) -> output_String, (input_String | input_Symbol), {prefix_String, suffix_String}}, eventApplicationFunction_
	] :=
	If[
		input === Null,
		{DirectedEdge[{stepNumber, {inputStateID, outputStateID}} -> {input -> output, input, {prefix, suffix}}, {stepNumber,
			 outputStateID} -> output]},
		{DirectedEdge[{stepNumber - 1, inputStateID} -> eventApplicationFunction[{input -> input, input, {prefix, suffix}}
			], {stepNumber, {inputStateID, outputStateID}} -> {input -> output, input, {prefix, suffix}}], DirectedEdge[{stepNumber,
			 {inputStateID, outputStateID}} -> {input -> output, input, {prefix, suffix}}, {stepNumber, outputStateID} -> eventApplicationFunction[
			{input -> output, input, {prefix, suffix}}]]}
	]

getTracedStatesEdge[stepNumber_Integer -> {(input_String | input_Symbol) -> output_String, (input_String | input_Symbol
	), {prefix_String, suffix_String}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{DirectedEdge[stepNumber -> {input -> output, input, {prefix, suffix}}, stepNumber -> output]},
		{DirectedEdge[(stepNumber - 1) -> eventApplicationFunction[{input -> input, input, {prefix, suffix}}], stepNumber 
			-> {input -> output, input, {prefix, suffix}}], DirectedEdge[stepNumber -> {input -> output, input, {prefix, suffix}
			}, stepNumber -> eventApplicationFunction[{input -> output, input, {prefix, suffix}}]]}
	]

getTracedStatesEdge[{Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {(input_String
	 | input_Symbol) -> output_String, (input_String | input_Symbol), {prefix_String, suffix_String}}, eventApplicationFunction_
	] :=
	If[
		input === Null,
		{DirectedEdge[{Automatic, {inputStateID, outputStateID}} -> {input -> output, input, {prefix, suffix}}, {Automatic,
			 outputStateID} -> output]},
		{DirectedEdge[{Automatic, inputStateID} -> eventApplicationFunction[{input -> input, input, {prefix, suffix}}], {Automatic,
			 {inputStateID, outputStateID}} -> {input -> output, input, {prefix, suffix}}], DirectedEdge[{Automatic, {inputStateID,
			 outputStateID}} -> {input -> output, input, {prefix, suffix}}, {Automatic, outputStateID} -> eventApplicationFunction[
			{input -> output, input, {prefix, suffix}}]]}
	]



getTracedStatesEdge[{(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List
	}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{DirectedEdge[{input -> output, input, {prefix, suffix}}, output]},
		{DirectedEdge[eventApplicationFunction[{input -> input, input, {prefix, suffix}}], {input -> output, input, {prefix,
			 suffix}}], DirectedEdge[{input -> output, input, {prefix, suffix}}, eventApplicationFunction[{input -> output, input,
			 {prefix, suffix}}]]}
	]

getTracedStatesEdge[{stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {
	(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}, eventApplicationFunction_
	] :=
	If[
		input === Null,
		{DirectedEdge[{stepNumber, {inputStateID, outputStateID}} -> {input -> output, input, {prefix, suffix}}, {stepNumber,
			 outputStateID} -> output]},
		{DirectedEdge[{stepNumber - 1, inputStateID} -> eventApplicationFunction[{input -> input, input, {prefix, suffix}}
			], {stepNumber, {inputStateID, outputStateID}} -> {input -> output, input, {prefix, suffix}}], DirectedEdge[{stepNumber,
			 {inputStateID, outputStateID}} -> {input -> output, input, {prefix, suffix}}, {stepNumber, outputStateID} -> eventApplicationFunction[
			{input -> output, input, {prefix, suffix}}]]}
	]

getTracedStatesEdge[stepNumber_Integer -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), 
	{prefix_List, suffix_List}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{DirectedEdge[stepNumber -> {input -> output, input, {prefix, suffix}}, stepNumber -> output]},
		{DirectedEdge[(stepNumber - 1) -> eventApplicationFunction[{input -> input, input, {prefix, suffix}}], stepNumber 
			-> {input -> output, input, {prefix, suffix}}], DirectedEdge[stepNumber -> {input -> output, input, {prefix, suffix}
			}, stepNumber -> eventApplicationFunction[{input -> output, input, {prefix, suffix}}]]}
	]

getTracedStatesEdge[{Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {(input_List
	 | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}, eventApplicationFunction_
	] :=
	If[
		input === Null,
		{DirectedEdge[{Automatic, {inputStateID, outputStateID}} -> {input -> output, input, {prefix, suffix}}, {Automatic,
			 outputStateID} -> output]},
		{DirectedEdge[{Automatic, inputStateID} -> eventApplicationFunction[{input -> input, input, {prefix, suffix}}], {Automatic,
			 {inputStateID, outputStateID}} -> {input -> output, input, {prefix, suffix}}], DirectedEdge[{Automatic, {inputStateID,
			 outputStateID}} -> {input -> output, input, {prefix, suffix}}, {Automatic, outputStateID} -> eventApplicationFunction[
			{input -> output, input, {prefix, suffix}}]]}
	]



getTracedStatesEdge[{(input_List | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List, suffix_List
	}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{DirectedEdge[getCanonicalEvent[{input :> output, input, {prefix, suffix}}], getCanonicalHypergraph[output]]},
		{DirectedEdge[getCanonicalHypergraph[eventApplicationFunction[{input :> input, input, {prefix, suffix}}]], getCanonicalEvent[
			{input :> output, input, {prefix, suffix}}]], DirectedEdge[getCanonicalEvent[{input :> output, input, {prefix, suffix
			}}], getCanonicalHypergraph[eventApplicationFunction[{input :> output, input, {prefix, suffix}}]]]}
	]

getTracedStatesEdge[{stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {
	(input_List | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}, eventApplicationFunction_
	] :=
	If[
		input === Null,
		{DirectedEdge[getCanonicalEvent[{stepNumber, {inputStateID, outputStateID}} -> {input :> output, input, {prefix, suffix
			}}], getCanonicalHypergraph[{stepNumber, outputStateID} -> output]]},
		{DirectedEdge[getCanonicalHypergraph[{stepNumber - 1, inputStateID} -> eventApplicationFunction[{input :> input, input,
			 {prefix, suffix}}]], getCanonicalEvent[{stepNumber, {inputStateID, outputStateID}} -> {input :> output, input, {prefix,
			 suffix}}]], DirectedEdge[getCanonicalEvent[{stepNumber, {inputStateID, outputStateID}} -> {input :> output, input, 
			{prefix, suffix}}], getCanonicalHypergraph[{stepNumber, outputStateID} -> eventApplicationFunction[{input :> output,
			 input, {prefix, suffix}}]]]}
	]

getTracedStatesEdge[stepNumber_Integer -> {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol), 
	{prefix_List, suffix_List}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{DirectedEdge[getCanonicalEvent[stepNumber -> {input :> output, input, {prefix, suffix}}], getCanonicalHypergraph[
			stepNumber -> output]]},
		{DirectedEdge[getCanonicalHypergraph[(stepNumber - 1) -> eventApplicationFunction[{input :> input, input, {prefix,
			 suffix}}]], getCanonicalEvent[stepNumber -> {input :> output, input, {prefix, suffix}}]], DirectedEdge[getCanonicalEvent[
			stepNumber -> {input :> output, input, {prefix, suffix}}], getCanonicalHypergraph[stepNumber -> eventApplicationFunction[
			{input :> output, input, {prefix, suffix}}]]]}
	]

getTracedStatesEdge[{Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {(input_List
	 | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}, eventApplicationFunction_
	] :=
	If[
		input === Null,
		{DirectedEdge[getCanonicalEvent[{Automatic, {inputStateID, outputStateID}} -> {input :> output, input, {prefix, suffix
			}}], getCanonicalHypergraph[{Automatic, outputStateID} -> output]]},
		{DirectedEdge[getCanonicalHypergraph[{Automatic, inputStateID} -> eventApplicationFunction[{input :> input, input,
			 {prefix, suffix}}]], getCanonicalEvent[{Automatic, {inputStateID, outputStateID}} -> {input :> output, input, {prefix,
			 suffix}}]], DirectedEdge[getCanonicalEvent[{Automatic, {inputStateID, outputStateID}} -> {input :> output, input, {
			prefix, suffix}}], getCanonicalHypergraph[{Automatic, outputStateID} -> eventApplicationFunction[{input :> output, input,
			 {prefix, suffix}}]]]}
	]



getTracedStatesEdge[{(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {
	prefix_List, suffix_List}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{DirectedEdge[{input -> output, input, {prefix, suffix}}, prefix]},
		{DirectedEdge[eventApplicationFunction[{input -> input[[2]], input, {prefix, suffix}}], {input -> output, input, {
			prefix, suffix}}], DirectedEdge[{input -> output, input, {prefix, suffix}}, eventApplicationFunction[{input -> output,
			 input, {prefix, suffix}}]]}
	]

getTracedStatesEdge[{stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {
	(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List, suffix_List
	}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{DirectedEdge[{stepNumber, {inputStateID, outputStateID}} -> {input -> output, input, {prefix, suffix}}, {stepNumber,
			 outputStateID} -> prefix]},
		{DirectedEdge[{stepNumber - 1, inputStateID} -> eventApplicationFunction[{input -> input[[2]], input, {prefix, suffix
			}}], {stepNumber, {inputStateID, outputStateID}} -> {input -> output, input, {prefix, suffix}}], DirectedEdge[{stepNumber,
			 {inputStateID, outputStateID}} -> {input -> output, input, {prefix, suffix}}, {stepNumber, outputStateID} -> eventApplicationFunction[
			{input -> output, input, {prefix, suffix}}]]}
	]

getTracedStatesEdge[stepNumber_Integer -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List
	 | input_Symbol), {prefix_List, suffix_List}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{DirectedEdge[stepNumber -> {input -> output, input, {prefix, suffix}}, stepNumber -> prefix]},
		{DirectedEdge[(stepNumber - 1) -> eventApplicationFunction[{input -> input[[2]], input, {prefix, suffix}}], stepNumber
			 -> {input -> output, input, {prefix, suffix}}], DirectedEdge[stepNumber -> {input -> output, input, {prefix, suffix
			}}, stepNumber -> eventApplicationFunction[{input -> output, input, {prefix, suffix}}]]}
	]

getTracedStatesEdge[{Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {(input_List
	 | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List, suffix_List}}, eventApplicationFunction_
	] :=
	If[
		input === Null,
		{DirectedEdge[{Automatic, {inputStateID, outputStateID}} -> {input -> output, input, {prefix, suffix}}, {Automatic,
			 outputStateID} -> prefix]},
		{DirectedEdge[{Automatic, inputStateID} -> eventApplicationFunction[{input -> input[[2]], input, {prefix, suffix}}
			], {Automatic, {inputStateID, outputStateID}} -> {input -> output, input, {prefix, suffix}}], DirectedEdge[{Automatic,
			 {inputStateID, outputStateID}} -> {input -> output, input, {prefix, suffix}}, {Automatic, outputStateID} -> eventApplicationFunction[
			{input -> output, input, {prefix, suffix}}]]}
	]



getTracedStatesEdgeList[eventsList_List, eventApplicationFunction_] :=
	getTracedStatesEdge[#, eventApplicationFunction]& /@ eventsList



getState[{(input_String | input_Symbol) -> output_String, (input_String | input_Symbol), {prefix_String, suffix_String
	}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{output},
		{eventApplicationFunction[{input -> output, input, {prefix, suffix}}]}
	]

getState[{stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {(input_String
	 | input_Symbol) -> output_String, (input_String | input_Symbol), {prefix_String, suffix_String}}, eventApplicationFunction_
	] :=
	If[
		input === Null,
		{{stepNumber, outputStateID} -> output},
		{{stepNumber, outputStateID} -> eventApplicationFunction[{input -> output, input, {prefix, suffix}}]}
	]

getState[stepNumber_Integer -> {(input_String | input_Symbol) -> output_String, (input_String | input_Symbol), {prefix_String,
	 suffix_String}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{stepNumber -> output},
		{stepNumber -> eventApplicationFunction[{input -> output, input, {prefix, suffix}}]}
	]

getState[{Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {(input_String | input_Symbol
	) -> output_String, (input_String | input_Symbol), {prefix_String, suffix_String}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{{Automatic, outputStateID} -> output},
		{{Automatic, outputStateID} -> eventApplicationFunction[{input -> output, input, {prefix, suffix}}]}
	]



getState[{(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}, eventApplicationFunction_
	] :=
	If[
		input === Null,
		{output},
		{eventApplicationFunction[{input -> output, input, {prefix, suffix}}]}
	]

getState[{stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {(input_List
	 | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}, eventApplicationFunction_
	] :=
	If[
		input === Null,
		{{stepNumber, outputStateID} -> output},
		{{stepNumber, outputStateID} -> eventApplicationFunction[{input -> output, input, {prefix, suffix}}]}
	]

getState[stepNumber_Integer -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List,
	 suffix_List}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{stepNumber -> output},
		{stepNumber -> eventApplicationFunction[{input -> output, input, {prefix, suffix}}]}
	]

getState[{Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {(input_List | input_Symbol
	) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{{Automatic, outputStateID} -> output},
		{{Automatic, outputStateID} -> eventApplicationFunction[{input -> output, input, {prefix, suffix}}]}
	]



getState[{(input_List | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}, eventApplicationFunction_
	] :=
	If[
		input === Null,
		{getCanonicalHypergraph[output]},
		{getCanonicalHypergraph[eventApplicationFunction[{input :> output, input, {prefix, suffix}}]]}
	]

getState[{stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {(input_List
	 | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}, eventApplicationFunction_
	] :=
	If[
		input === Null,
		{{stepNumber, outputStateID} -> getCanonicalHypergraph[output]},
		{{stepNumber, outputStateID} -> getCanonicalHypergraph[eventApplicationFunction[{input :> output, input, {prefix, 
			suffix}}]]}
	]

getState[stepNumber_Integer -> {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List,
	 suffix_List}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{stepNumber -> getCanonicalHypergraph[output]},
		{stepNumber -> getCanonicalHypergraph[eventApplicationFunction[{input :> output, input, {prefix, suffix}}]]}
	]

getState[{Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {(input_List | input_Symbol
	) :> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{{Automatic, outputStateID} -> getCanonicalHypergraph[output]},
		{{Automatic, outputStateID} -> getCanonicalHypergraph[eventApplicationFunction[{input :> output, input, {prefix, suffix
			}}]]}
	]



getState[{(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List,
	 suffix_List}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{prefix},
		{eventApplicationFunction[{input -> output, input, {prefix, suffix}}]}
	]

getState[{stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {(input_List
	 | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List, suffix_List}}, eventApplicationFunction_
	] :=
	If[
		input === Null,
		{{stepNumber, outputStateID} -> prefix},
		{{stepNumber, outputStateID} -> eventApplicationFunction[{input -> output, input, {prefix, suffix}}]}
	]

getState[stepNumber_Integer -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol
	), {prefix_List, suffix_List}}, eventApplicationFunction_] :=
	If[
		input === Null,
		{stepNumber -> prefix},
		{stepNumber -> eventApplicationFunction[{input -> output, input, {prefix, suffix}}]}
	]

getState[{Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {(input_List | input_Symbol
	) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List, suffix_List}}, eventApplicationFunction_
	] :=
	If[
		input === Null,
		{{Automatic, outputStateID} -> prefix},
		{{Automatic, outputStateID} -> eventApplicationFunction[{input -> output, input, {prefix, suffix}}]}
	]



getStatesList[eventsList_List, eventApplicationFunction_] :=
	getState[#, eventApplicationFunction]& /@ eventsList



getInitialEvent[state_String] :=
	{Null -> state, Null, {"", ""}}

getInitialEvent[{stepNumber_Integer, stateID_Integer} -> state_String] :=
	{stepNumber - 1, {Null, stateID}} -> {Null -> state, Null, {"", ""}}

getInitialEvent[stepNumber_Integer -> state_String] :=
	(stepNumber - 1) -> {Null -> state, Null, {"", ""}}

getInitialEvent[{Automatic, stateID_Integer} -> state_String] :=
	{Automatic, {Null, stateID}} -> {Null -> state, Null, {"", ""}}



getInitialEvent[state_List] :=
	{Null -> state, Null, {{}, {}}} /; Depth[state] == 2

getInitialEvent[{stepNumber_Integer, stateID_Integer} -> state_List] :=
	{stepNumber - 1, {Null, stateID}} -> {Null -> state, Null, {{}, {}}} /; Depth[state] == 2

getInitialEvent[stepNumber_Integer -> state_List] :=
	(stepNumber - 1) -> {Null -> state, Null, {{}, {}}} /; Depth[state] == 2

getInitialEvent[{Automatic, stateID_Integer} -> state_List] :=
	{Automatic, {Null, stateID}} -> {Null -> state, Null, {{}, {}}} /; Depth[state] == 2



getInitialEvent[state_List] :=
	{Null :> Evaluate[getCanonicalHypergraph[state]], Null, {{}, {}}} /; Depth[state] == 3

getInitialEvent[{stepNumber_Integer, stateID_Integer} -> state_List] :=
	{stepNumber - 1, {Null, stateID}} -> {Null :> Evaluate[getCanonicalHypergraph[state]], Null, {{}, {}}} /; Depth[state
		] == 3

getInitialEvent[stepNumber_Integer -> state_List] :=
	(stepNumber - 1) -> {Null :> Evaluate[getCanonicalHypergraph[state]], Null, {{}, {}}} /; Depth[state] == 3

getInitialEvent[{Automatic, stateID_Integer} -> state_List] :=
	{Automatic, {Null, stateID}} -> {Null :> Evaluate[getCanonicalHypergraph[state]], Null, {{}, {}}} /; Depth[state] ==
		 3



getInitialEventsList[statesList_List] :=
	getInitialEvent[#]& /@ statesList



getInitialCellularAutomatonEvent[state_List] :=
	{Null -> Null, Null, {state, {}}}

getInitialCellularAutomatonEvent[{stepNumber_Integer, stateID_Integer} -> state_List] :=
	{stepNumber - 1, {Null, stateID}} -> {Null -> Null, Null, {state, {}}}

getInitialCellularAutomatonEvent[stepNumber_Integer -> state_List] :=
	(stepNumber - 1) -> {Null -> Null, Null, {state, {}}}

getInitialCellularAutomatonEvent[{Automatic, stateID_Integer} -> state_List] :=
	{Automatic, {Null, stateID}} -> {Null -> Null, Null, {state, {}}}



getInitialCellularAutomatonEventsList[statesList_List] :=
	getInitialCellularAutomatonEvent[#]& /@ statesList



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionEventsGraph", options : OptionsPattern[]] :=
	Module[{allEventsList, eventsList, canonicalizedEventsList, initializationEventsList, tracedStatesEdgeList, statesList
		},
		allEventsList =
			Which[
				systemType === "ListSubstitutionSystem",
				NestList[
					Union[
						If[
							stateEventFunction[eventApplicationFunction /@ #] === {},
							{},
							eventSelectionFunction[stateEventFunction[eventApplicationFunction /@ #]]
						]
					]&,
					preProcessInitialEvents[({Null -> #, Null, {{}, {}}}& /@ initialConditions), OptionValue["IncludeStepNumber"], 
						OptionValue["IncludeStateID"]],
					stepCount
				],
				systemType === "WolframModel",
				NestList[
					Union[
						If[
							stateEventFunction[eventApplicationFunction /@ #] === {},
							{},
							eventSelectionFunction[stateEventFunction[eventApplicationFunction /@ #]]
						]
					]&,
					preProcessInitialEvents[({Null :> #, Null, {{}, {}}}& /@ initialConditions), OptionValue["IncludeStepNumber"], 
						OptionValue["IncludeStateID"]],
					stepCount
				],
				systemType === "CellularAutomaton",
				NestList[
					Union[
						If[
							stateEventFunction[eventApplicationFunction /@ #] === {},
							{},
							eventSelectionFunction[stateEventFunction[eventApplicationFunction /@ #]]
						]
					]&,
					preProcessInitialEvents[({Null -> Null, Null, {#, {}}}& /@ initialConditions), OptionValue["IncludeStepNumber"],
						 OptionValue["IncludeStateID"]],
					stepCount
				],
				systemType =!= "ListSubstitutionSystem" && systemType =!= "WolframModel" && systemType =!= "CellularAutomaton",
				NestList[
					Union[
						If[
							stateEventFunction[eventApplicationFunction /@ #] === {},
							{},
							eventSelectionFunction[stateEventFunction[eventApplicationFunction /@ #]]
						]
					]&,
					preProcessInitialEvents[({Null -> #, Null, {"", ""}}& /@ initialConditions), OptionValue["IncludeStepNumber"], 
						OptionValue["IncludeStateID"]],
					stepCount
				]
			];
		eventsList = Catenate[allEventsList];
		canonicalizedEventsList = Catenate[If[
				OptionValue["IncludeInitializationEvents"],
				Identity,
				Rest
			][getCanonicalEventsList[allEventsList, systemType]]];
		initializationEventsList =
			If[
				OptionValue["IncludeInitializationEvents"],
				First[getCanonicalEventsList[allEventsList, systemType]],
				{}
			];
		tracedStatesEdgeList = getTracedStatesEdgeList[Catenate[If[
				OptionValue["IncludeInitializationEvents"],
				Identity,
				Rest
			][allEventsList]], eventApplicationFunction];
		statesList = Catenate[getStatesList[eventsList, eventApplicationFunction]];
		If[
			OptionValue["IncludeEventInstances"],
			Identity,
			SimpleGraph
		][Graph[statesList, Flatten[tracedStatesEdgeList], VertexShapeFunction -> getStateEventRenderingFunction[systemType,
			 OptionValue["StateRenderingFunction"], statesList, OptionValue["EventRenderingFunction"], canonicalizedEventsList, 
			OptionValue["VertexSizeMultiplier"]], PerformanceGoal -> getGraphQuality[{OptionValue["StateRenderingFunction"], OptionValue[
			"EventRenderingFunction"]}], EdgeStyle -> Directive[{Hue[0.75, 0, 0.24], Dashing[None], AbsoluteThickness[OptionValue[
			"LineThickness"]]}], VertexWeight -> MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "StateWeights", options], FilterRules[{options}, Options[Graph]]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionEventsGraphStructure", options : OptionsPattern[]] :=
	Module[{evolutionEventsGraph, statesList, initializationEventsList, canonicalizedEventsList},
		evolutionEventsGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionEventsGraph", options];
		statesList = Select[VertexList[evolutionEventsGraph], !MatchQ[#, {(input_String | input_Symbol) -> output_String, 
			(input_String | input_Symbol), {prefix_String, suffix_String}}] && !MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer
			 | inputStateID_Symbol), outputStateID_Integer}} -> {(input_String | input_Symbol) -> output_String, (input_String |
			 input_Symbol), {prefix_String, suffix_String}}] && !MatchQ[#, stepNumber_Integer -> {(input_String | input_Symbol) 
			-> output_String, (input_String | input_Symbol), {prefix_String, suffix_String}}] && !MatchQ[#, {Automatic, {(inputStateID_Integer
			 | inputStateID_Symbol), outputStateID_Integer}} -> {(input_String | input_Symbol) -> output_String, (input_String |
			 input_Symbol), {prefix_String, suffix_String}}] && !MatchQ[#, {(input_List | input_Symbol) -> output_List, (input_List
			 | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol
			), outputStateID_Integer}} -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List,
			 suffix_List}}] && !MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol
			), {prefix_List, suffix_List}}] && !MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer
			}} -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[
			#, {(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List, suffix_List
			}}] && !MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), (outputStateID_Integer | outputStateID_Symbol
			)}} -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List, 
			suffix_List}}] && !MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol),
			 (input_List | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol
			), (outputStateID_Integer | outputStateID_Symbol)}} -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol
			), (input_List | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[#, {(input_List | input_Symbol) :> output_List,
			 (input_List | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer
			 | inputStateID_Symbol), outputStateID_Integer}} -> {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol
			), {prefix_List, suffix_List}}] && !MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) :> output_List, (input_List
			 | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol
			), outputStateID_Integer}} -> {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List,
			 suffix_List}}]&];
		canonicalizedEventsList = Select[VertexList[evolutionEventsGraph], MatchQ[#, {(input_String | input_Symbol) -> output_String,
			 (input_String | input_Symbol), {prefix_String, suffix_String}}] || MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer
			 | inputStateID_Symbol), outputStateID_Integer}} -> {(input_String | input_Symbol) -> output_String, (input_String |
			 input_Symbol), {prefix_String, suffix_String}}] || MatchQ[#, stepNumber_Integer -> {(input_String | input_Symbol) ->
			 output_String, (input_String | input_Symbol), {prefix_String, suffix_String}}] || MatchQ[#, {Automatic, {(inputStateID_Integer
			 | inputStateID_Symbol), outputStateID_Integer}} -> {(input_String | input_Symbol) -> output_String, (input_String |
			 input_Symbol), {prefix_String, suffix_String}}] || MatchQ[#, {(input_List | input_Symbol) -> output_List, (input_List
			 | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol
			), outputStateID_Integer}} -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List,
			 suffix_List}}] || MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol
			), {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer
			}} -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[
			#, {(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List, suffix_List
			}}] || MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), (outputStateID_Integer | outputStateID_Symbol
			)}} -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List, 
			suffix_List}}] || MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol), 
			(input_List | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol
			), (outputStateID_Integer | outputStateID_Symbol)}} -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol
			), (input_List | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[#, {(input_List | input_Symbol) :> output_List,
			 (input_List | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer 
			| inputStateID_Symbol), outputStateID_Integer}} -> {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol
			), {prefix_List, suffix_List}}] || MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) :> output_List, (input_List
			 | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol
			), outputStateID_Integer}} -> {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List,
			 suffix_List}}]&];
		initializationEventsList = Select[VertexList[evolutionEventsGraph], MatchQ[#, {Null -> output_String, Null, {prefix_String,
			 suffix_String}}] || MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer}} -> {Null -> output_String, Null, 
			{prefix_String, suffix_String}}] || MatchQ[#, stepNumber_Integer -> {Null -> output_String, Null, {prefix_String, suffix_String
			}}] || MatchQ[#, {Automatic, {Null, outputStateID_Integer}} -> {Null -> output_String, Null, {prefix_String, suffix_String
			}}] || MatchQ[#, {Null -> output_List, Null, {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer
			}} -> {Null -> output_List, Null, {prefix_List, suffix_List}}] || MatchQ[#, stepNumber_Integer -> {Null -> output_List,
			 Null, {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {Null, outputStateID_Integer}} -> {Null -> output_List,
			 Null, {prefix_List, suffix_List}}] || MatchQ[#, {Null -> Null, Null, {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer,
			 {Null, Null}} -> {Null -> Null, Null, {prefix_List, suffix_List}}] || MatchQ[#, stepNumber_Integer -> {Null -> Null,
			 Null, {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {Null, Null}} -> {Null -> Null, Null, {prefix_List, suffix_List
			}}] || MatchQ[#, {Null :> output_List, Null, {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer
			}} -> {Null :> output_List, Null, {prefix_List, suffix_List}}] || MatchQ[#, stepNumber_Integer -> {Null :> output_List,
			 Null, {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {Null, outputStateID_Integer}} -> {Null :> output_List,
			 Null, {prefix_List, suffix_List}}]&];
		Graph[evolutionEventsGraph, VertexStyle -> Union[(# -> Directive[Opacity[0.7], Hue[0.62, 0.45, 0.87]]& /@ statesList
			), (# -> Directive[Opacity[0.7], RGBColor[0.259, 0.576, 1]]& /@ initializationEventsList), (# -> Directive[Opacity[0.7
			], Hue[0.11, 1, 0.97]]& /@ Complement[canonicalizedEventsList, initializationEventsList])], VertexShapeFunction -> (
			(# -> Automatic)& /@ VertexList[evolutionEventsGraph]), FilterRules[{options}, Options[Graph]]]
	]



removeWrappers[causalGraph_Graph, "WolframModel", options : OptionsPattern[]] :=
	Graph @@ Append[(({VertexList[causalGraph], EdgeList[causalGraph]} /. {$event[event_, stepNumber_] :> {event, stepNumber
		}, $element[element_, stepNumber_] :> {element, stepNumber}, $event[event_] :> getCanonicalEvent[event], $element[element_
		] :> getCanonicalHypergraph[element]}) /. {(stepNumber_Integer -> event_) :> ((stepNumber + 1) -> event), ({stepNumber_Integer,
		 eventID_List} -> event_) :> ({stepNumber + 1, eventID} -> event)}), options]

removeWrappers[causalGraph_Graph, Except["WolframModel"], options : OptionsPattern[]] :=
	Graph @@ Append[(({VertexList[causalGraph], EdgeList[causalGraph]} /. {$event[event_, stepNumber_] :> {event, stepNumber
		}, $element[element_, stepNumber_] :> {element, stepNumber}, $event[event_] :> event, $element[element_] :> element}
		) /. {(stepNumber_Integer -> event_) :> ((stepNumber + 1) -> event), ({stepNumber_Integer, eventID_List} -> event_) 
		:> ({stepNumber + 1, eventID} -> event)}), options]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "ElementwiseCausalGraphUnmerged", options : OptionsPattern[]] :=
	Module[{initialStates, initialEvents, elementwiseCausalGraphUnmerged, newVertexList, newEdgeList, newInitialEvents},
		
		initialStates = preProcessInitialStates[initialConditions, OptionValue["IncludeStepNumber"], OptionValue["IncludeStateID"
			]];
		If[
			systemType === "CellularAutomaton",
			initialEvents = getInitialCellularAutomatonEventsList[initialStates],
			initialEvents = getInitialEventsList[initialStates]
		];
		elementwiseCausalGraphUnmerged =
			Graph[
				Catenate[
					FoldPairList[
						Function[{state, stepNumber},
							With[{
								eventsList =
									If[
										stateEventFunction[state] === {},
										{},
										eventSelectionFunction[stateEventFunction[state]]
									]
							},
								{
									Catenate[
										Function[event,
												If[
													Head[event] === Rule,
													Join[DirectedEdge[$element[#1, stepNumber - 1], $element[#2, stepNumber]]& @@@ #1, Thread[$element[#, stepNumber
														 - 1]& /@ #2 -> (First[event] -> $event[Last[event], stepNumber - 1])], Thread[(First[event] -> $event[Last[event], 
														stepNumber - 1]) -> $element[#, stepNumber]& /@ #3]]& @@ eventDecompositionFunction[Last[event]],
													Join[DirectedEdge[$element[#1, stepNumber - 1], $element[#2, stepNumber]]& @@@ #1, Thread[$element[#, stepNumber
														 - 1]& /@ #2 -> $event[event, stepNumber - 1]], Thread[$event[event, stepNumber - 1] -> $element[#, stepNumber]& /@ 
														#3]]& @@ eventDecompositionFunction[event]
												]
											] /@ eventsList
									],
									DeleteDuplicates[eventApplicationFunction[#]& /@ eventsList, stateEquivalenceFunction]
								}
							]
						],
						initialStates,
						Range[stepCount]
					]
				]
			];
		Graph[Union[VertexList[elementwiseCausalGraphUnmerged], initialEvents], EdgeList[elementwiseCausalGraphUnmerged]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "CausalGraphUnmerged", options : OptionsPattern[]] :=
	Module[{elementwiseCausalGraphUnmerged, causalGraphUnmerged, initialEvents},
		elementwiseCausalGraphUnmerged = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "ElementwiseCausalGraphUnmerged", options];
		initialEvents =
			Which[
				systemType === "ListSubstitutionSystem",
				Union[Select[VertexList[elementwiseCausalGraphUnmerged], MatchQ[#, {Null -> state_List, Null, {{}, {}}}]&], Select[
					VertexList[elementwiseCausalGraphUnmerged], MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer}} -> {Null ->
					 state_List, Null, {{}, {}}}]&], Select[VertexList[elementwiseCausalGraphUnmerged], MatchQ[#, stepNumber_Integer -> 
					{Null -> state_List, Null, {{}, {}}}]&], Select[VertexList[elementwiseCausalGraphUnmerged], MatchQ[#, {Automatic, {Null,
					 outputStateID_Integer}} -> {Null -> state_List, Null, {{}, {}}}]&]],
				systemType === "WolframModel",
				Union[Select[VertexList[elementwiseCausalGraphUnmerged], MatchQ[#, {Null :> state_List, Null, {{}, {}}}]&], Select[
					VertexList[elementwiseCausalGraphUnmerged], MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer}} -> {Null :>
					 state_List, Null, {{}, {}}}]&], Select[VertexList[elementwiseCausalGraphUnmerged], MatchQ[#, stepNumber_Integer -> 
					{Null :> state_List, Null, {{}, {}}}]&], Select[VertexList[elementwiseCausalGraphUnmerged], MatchQ[#, {Automatic, {Null,
					 outputStateID_Integer}} -> {Null :> state_List, Null, {{}, {}}}]&]],
				systemType === "CellularAutomaton",
				Union[Select[VertexList[elementwiseCausalGraphUnmerged], MatchQ[#, {Null -> Null, Null, {state_List, {}}}]&], Select[
					VertexList[elementwiseCausalGraphUnmerged], MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer}} -> {Null ->
					 Null, Null, {state_List, {}}}]&], Select[VertexList[elementwiseCausalGraphUnmerged], MatchQ[#, stepNumber_Integer ->
					 {Null -> Null, Null, {state_List, {}}}]&], Select[VertexList[elementwiseCausalGraphUnmerged], MatchQ[#, {Automatic,
					 {Null, outputStateID_Integer}} -> {Null -> Null, Null, {state_List, {}}}]&]],
				systemType =!= "ListSubstitutionSystem" && systemType =!= "WolframModel" && systemType =!= "CellularAutomaton",
				Union[Select[VertexList[elementwiseCausalGraphUnmerged], MatchQ[#, {Null -> state_String, Null, {"", ""}}]&], Select[
					VertexList[elementwiseCausalGraphUnmerged], MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer}} -> {Null ->
					 state_String, Null, {"", ""}}]&], Select[VertexList[elementwiseCausalGraphUnmerged], MatchQ[#, stepNumber_Integer ->
					 {Null -> state_String, Null, {"", ""}}]&], Select[VertexList[elementwiseCausalGraphUnmerged], MatchQ[#, {Automatic,
					 {Null, outputStateID_Integer}} -> {Null -> state_String, Null, {"", ""}}]&]]
			];
		causalGraphUnmerged =
			With[{eventsList = Cases[VertexList[elementwiseCausalGraphUnmerged], (_$event | (_ -> _$event)), {1}], elementsToEventsGraph
				 = EdgeDelete[elementwiseCausalGraphUnmerged, DirectedEdge[(event_$event | (_ -> event_$event)), element_$element]]},
				
				Graph[
					eventsList,
					Catenate[
						Function[{originEvent},
								DirectedEdge[originEvent, #]& /@ (Cases[VertexOutComponent[elementsToEventsGraph, #], (_$event | (_ -> _$event
									)), {1}]&[Rest[VertexOutComponent[elementwiseCausalGraphUnmerged, originEvent, 1]]])
							] /@ eventsList
					]
				]
			];
		If[
			OptionValue["IncludeInitializationEvents"],
			Graph[Union[VertexList[causalGraphUnmerged], initialEvents], EdgeList[causalGraphUnmerged]],
			Graph[VertexList[causalGraphUnmerged], EdgeList[causalGraphUnmerged]]
		]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "CausalGraph", options : OptionsPattern[]] :=
	Module[{causalGraphUnmerged, initialEvents, causalGraph},
		causalGraphUnmerged = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "CausalGraphUnmerged", options];
		initialEvents =
			Which[
				systemType === "ListSubstitutionSystem",
				Union[Select[VertexList[causalGraphUnmerged], MatchQ[#, {Null -> state_List, Null, {{}, {}}}]&], Select[VertexList[
					causalGraphUnmerged], MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer}} -> {Null -> state_List, Null, {{
					}, {}}}]&], Select[VertexList[causalGraphUnmerged], MatchQ[#, stepNumber_Integer -> {Null -> state_List, Null, {{}, 
					{}}}]&], Select[VertexList[causalGraphUnmerged], MatchQ[#, {Automatic, {Null, outputStateID_Integer}} -> {Null -> state_List,
					 Null, {{}, {}}}]&]],
				systemType === "WolframModel",
				Union[Select[VertexList[causalGraphUnmerged], MatchQ[#, {Null :> state_List, Null, {{}, {}}}]&], Select[VertexList[
					causalGraphUnmerged], MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer}} -> {Null :> state_List, Null, {{
					}, {}}}]&], Select[VertexList[causalGraphUnmerged], MatchQ[#, stepNumber_Integer -> {Null :> state_List, Null, {{}, 
					{}}}]&], Select[VertexList[causalGraphUnmerged], MatchQ[#, {Automatic, {Null, outputStateID_Integer}} -> {Null :> state_List,
					 Null, {{}, {}}}]&]],
				systemType === "CellularAutomaton",
				Union[Select[VertexList[causalGraphUnmerged], MatchQ[#, {Null -> Null, Null, {state_List, {}}}]&], Select[VertexList[
					causalGraphUnmerged], MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer}} -> {Null -> Null, Null, {state_List,
					 {}}}]&], Select[VertexList[causalGraphUnmerged], MatchQ[#, stepNumber_Integer -> {Null -> Null, Null, {state_List, 
					{}}}]&], Select[VertexList[causalGraphUnmerged], MatchQ[#, {Automatic, {Null, outputStateID_Integer}} -> {Null -> Null,
					 Null, {state_List, {}}}]&]],
				systemType =!= "ListSubstitutionSystem" && systemType =!= "WolframModel" && systemType =!= "CellularAutomaton",
				Union[Select[VertexList[causalGraphUnmerged], MatchQ[#, {Null -> state_String, Null, {"", ""}}]&], Select[VertexList[
					causalGraphUnmerged], MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer}} -> {Null -> state_String, Null, 
					{"", ""}}]&], Select[VertexList[causalGraphUnmerged], MatchQ[#, stepNumber_Integer -> {Null -> state_String, Null, {
					"", ""}}]&], Select[VertexList[causalGraphUnmerged], MatchQ[#, {Automatic, {Null, outputStateID_Integer}} -> {Null ->
					 state_String, Null, {"", ""}}]&]]
			];
		initialEvents = initialEvents /. {({stepNumber_Integer, eventID_List} -> event_) :> ({stepNumber + 1, eventID} -> 
			event), (stepNumber_Integer -> event_) :> ((stepNumber + 1) -> event)};
		causalGraph = Graph[removeWrappers[Graph @@ ({VertexList[causalGraphUnmerged], EdgeList[causalGraphUnmerged]} /. {
			$event[event_, _] :> $event[event], $element[element_, _] :> $element[element]}), systemType, {VertexShapeFunction ->
			 getEventRenderingFunction[systemType, OptionValue["EventRenderingFunction"], OptionValue["VertexSizeMultiplier"]], 
			EdgeStyle -> Directive[{Hue[0, 1, 0.56], AbsoluteThickness[OptionValue["LineThickness"]]}], PerformanceGoal -> getGraphQuality[
			{OptionValue["EventRenderingFunction"]}]}], FilterRules[{options}, Options[Graph]]];
		Graph[causalGraph]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "CausalGraphStructure", options : OptionsPattern[]] :=
	Module[{causalGraph, initialEvents},
		causalGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
			 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
			 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
			 stepCount, "CausalGraph", options];
		initialEvents = Select[VertexList[causalGraph], MatchQ[#, {Null -> output_String, Null, {prefix_String, suffix_String
			}}] || MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer}} -> {Null -> output_String, Null, {prefix_String,
			 suffix_String}}] || MatchQ[#, stepNumber_Integer -> {Null -> output_String, Null, {prefix_String, suffix_String}}] 
			|| MatchQ[#, {Automatic, {Null, outputStateID_Integer}} -> {Null -> output_String, Null, {prefix_String, suffix_String
			}}] || MatchQ[#, {Null -> output_List, Null, {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer
			}} -> {Null -> output_List, Null, {prefix_List, suffix_List}}] || MatchQ[#, stepNumber_Integer -> {Null -> output_List,
			 Null, {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {Null, outputStateID_Integer}} -> {Null -> output_List,
			 Null, {prefix_List, suffix_List}}] || MatchQ[#, {Null -> Null, Null, {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer,
			 {Null, Null}} -> {Null -> Null, Null, {prefix_List, suffix_List}}] || MatchQ[#, stepNumber_Integer -> {Null -> Null,
			 Null, {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {Null, Null}} -> {Null -> Null, Null, {prefix_List, suffix_List
			}}] || MatchQ[#, {Null :> output_List, Null, {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer
			}} -> {Null :> output_List, Null, {prefix_List, suffix_List}}] || MatchQ[#, stepNumber_Integer -> {Null :> output_List,
			 Null, {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {Null, outputStateID_Integer}} -> {Null :> output_List,
			 Null, {prefix_List, suffix_List}}]&];
		Graph[causalGraph, VertexStyle -> Union[(# -> Directive[Opacity[0.7], RGBColor[0.259, 0.576, 1], EdgeForm[Directive[
			Opacity[0.7], RGBColor[0.259, 0.576, 1]]]]& /@ initialEvents), (# -> Directive[Opacity[0.7], Hue[0.11, 1, 0.97], EdgeForm[
			Directive[Opacity[0.7], Hue[0.11, 1, 0.97]]]]& /@ Complement[VertexList[causalGraph], initialEvents])], VertexShapeFunction
			 -> ((# -> Automatic)& /@ VertexList[causalGraph]), FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "LayeredCausalGraph", options : OptionsPattern[]] :=
	Module[{causalGraph},
		causalGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
			 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
			 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
			 stepCount, "CausalGraph", "IncludeStepNumber" -> True, "IncludeStateID" -> False, "IncludeInitializationEvents" -> 
			OptionValue["IncludeInitializationEvents"]];
		Graph[causalGraph, VertexCoordinates -> (# -> {Automatic, stepCount - First[#]}& /@ VertexList[causalGraph]), FilterRules[
			{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "LayeredCausalGraphStructure", options : OptionsPattern[]] :=
	Module[{layeredCausalGraph},
		layeredCausalGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "LayeredCausalGraph", options];
		Graph[layeredCausalGraph, VertexShapeFunction -> ((# -> Automatic)& /@ VertexList[layeredCausalGraph]), FilterRules[
			{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionCausalGraph", options : OptionsPattern[]] :=
	Module[{canonicalizedEventsList, allEventsList, eventsList, statesList, tracedStatesEdgeList, causalGraphFull, causalGraph,
		 causalEdgeList, initializationEventsList},
		If[
			OptionValue["IncludeStateID"],
			MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
				 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
				 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
				 stepCount, "EvolutionEventsGraph", options],
			causalGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> 
				stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
				 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
				|>, initialConditions, stepCount, "CausalGraph", options];
			allEventsList =
				Which[
					systemType === "ListSubstitutionSystem",
					NestList[
						Union[
							If[
								stateEventFunction[eventApplicationFunction /@ #] === {},
								{},
								eventSelectionFunction[stateEventFunction[eventApplicationFunction /@ #]]
							]
						]&,
						preProcessInitialEvents[({Null -> #, Null, {{}, {}}}& /@ initialConditions), OptionValue["IncludeStepNumber"],
							 OptionValue["IncludeStateID"]],
						stepCount
					],
					systemType === "WolframModel",
					NestList[
						Union[
							If[
								stateEventFunction[eventApplicationFunction /@ #] === {},
								{},
								eventSelectionFunction[stateEventFunction[eventApplicationFunction /@ #]]
							]
						]&,
						preProcessInitialEvents[({Null :> #, Null, {{}, {}}}& /@ initialConditions), OptionValue["IncludeStepNumber"],
							 OptionValue["IncludeStateID"]],
						stepCount
					],
					systemType === "CellularAutomaton",
					NestList[
						Union[
							If[
								stateEventFunction[eventApplicationFunction /@ #] === {},
								{},
								eventSelectionFunction[stateEventFunction[eventApplicationFunction /@ #]]
							]
						]&,
						preProcessInitialEvents[({Null -> Null, Null, {#, {}}}& /@ initialConditions), OptionValue["IncludeStepNumber"
							], OptionValue["IncludeStateID"]],
						stepCount
					],
					systemType =!= "ListSubstitutionSystem" && systemType =!= "WolframModel" && systemType =!= "CellularAutomaton",
					NestList[
						Union[
							If[
								stateEventFunction[eventApplicationFunction /@ #] === {},
								{},
								eventSelectionFunction[stateEventFunction[eventApplicationFunction /@ #]]
							]
						]&,
						preProcessInitialEvents[({Null -> #, Null, {"", ""}}& /@ initialConditions), OptionValue["IncludeStepNumber"],
							 OptionValue["IncludeStateID"]],
						stepCount
					]
				];
			eventsList = Catenate[allEventsList];
			causalEdgeList = EdgeList[causalGraph];
			canonicalizedEventsList = VertexList[causalGraph];
			initializationEventsList =
				If[
					OptionValue["IncludeInitializationEvents"],
					First[getCanonicalEventsList[allEventsList, systemType]],
					{}
				];
			tracedStatesEdgeList = getTracedStatesEdgeList[Catenate[If[
					OptionValue["IncludeInitializationEvents"],
					Identity,
					Rest
				][allEventsList]], eventApplicationFunction];
			statesList = Catenate[getStatesList[eventsList, eventApplicationFunction]];
			Graph[statesList, Union[Flatten[tracedStatesEdgeList], causalEdgeList], EdgeStyle -> Union[(DirectedEdge @@ #) ->
				 Directive[{Hue[0.07, 0.78, 1], AbsoluteThickness[OptionValue["LineThickness"]], Dashing[None]}]& /@ causalEdgeList,
				 (DirectedEdge @@ #) -> Directive[{Hue[0.75, 0, 0.24], Dashing[None], AbsoluteThickness[OptionValue["LineThickness"]
				]}]& /@ Flatten[tracedStatesEdgeList]], VertexShapeFunction -> getStateEventRenderingFunction[systemType, OptionValue[
				"StateRenderingFunction"], statesList, OptionValue["EventRenderingFunction"], canonicalizedEventsList, OptionValue["VertexSizeMultiplier"
				]], PerformanceGoal -> getGraphQuality[{OptionValue["StateRenderingFunction"], OptionValue["EventRenderingFunction"]
				}], VertexWeight -> MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" 
				-> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
				 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
				|>, initialConditions, stepCount, "StateWeights", options], FilterRules[{options}, Options[Graph]]]
		]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionCausalGraphStructure", options : OptionsPattern[]] :=
	Module[{evolutionCausalGraph, statesList, canonicalizedEventsList, initializationEventsList},
		evolutionCausalGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionCausalGraph", options];
		statesList = Select[VertexList[evolutionCausalGraph], !MatchQ[#, {(input_String | input_Symbol) -> output_String, 
			(input_String | input_Symbol), {prefix_String, suffix_String}}] && !MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer
			 | inputStateID_Symbol), outputStateID_Integer}} -> {(input_String | input_Symbol) -> output_String, (input_String |
			 input_Symbol), {prefix_String, suffix_String}}] && !MatchQ[#, stepNumber_Integer -> {(input_String | input_Symbol) 
			-> output_String, (input_String | input_Symbol), {prefix_String, suffix_String}}] && !MatchQ[#, {Automatic, {(inputStateID_Integer
			 | inputStateID_Symbol), outputStateID_Integer}} -> {(input_String | input_Symbol) -> output_String, (input_String |
			 input_Symbol), {prefix_String, suffix_String}}] && !MatchQ[#, {(input_List | input_Symbol) -> output_List, (input_List
			 | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol
			), outputStateID_Integer}} -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List,
			 suffix_List}}] && !MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol
			), {prefix_List, suffix_List}}] && !MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer
			}} -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[
			#, {(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List, suffix_List
			}}] && !MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), (outputStateID_Integer | outputStateID_Symbol
			)}} -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List, 
			suffix_List}}] && !MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol),
			 (input_List | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol
			), (outputStateID_Integer | outputStateID_Symbol)}} -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol
			), (input_List | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[#, {(input_List | input_Symbol) :> output_List,
			 (input_List | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer
			 | inputStateID_Symbol), outputStateID_Integer}} -> {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol
			), {prefix_List, suffix_List}}] && !MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) :> output_List, (input_List
			 | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol
			), outputStateID_Integer}} -> {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List,
			 suffix_List}}]&];
		canonicalizedEventsList = Select[VertexList[evolutionCausalGraph], MatchQ[#, {(input_String | input_Symbol) -> output_String,
			 (input_String | input_Symbol), {prefix_String, suffix_String}}] || MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer
			 | inputStateID_Symbol), outputStateID_Integer}} -> {(input_String | input_Symbol) -> output_String, (input_String |
			 input_Symbol), {prefix_String, suffix_String}}] || MatchQ[#, stepNumber_Integer -> {(input_String | input_Symbol) ->
			 output_String, (input_String | input_Symbol), {prefix_String, suffix_String}}] || MatchQ[#, {Automatic, {(inputStateID_Integer
			 | inputStateID_Symbol), outputStateID_Integer}} -> {(input_String | input_Symbol) -> output_String, (input_String |
			 input_Symbol), {prefix_String, suffix_String}}] || MatchQ[#, {(input_List | input_Symbol) -> output_List, (input_List
			 | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol
			), outputStateID_Integer}} -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List,
			 suffix_List}}] || MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol
			), {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer
			}} -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[
			#, {(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List, suffix_List
			}}] || MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), (outputStateID_Integer | outputStateID_Symbol
			)}} -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List, 
			suffix_List}}] || MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol), 
			(input_List | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol
			), (outputStateID_Integer | outputStateID_Symbol)}} -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol
			), (input_List | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[#, {(input_List | input_Symbol) :> output_List,
			 (input_List | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer 
			| inputStateID_Symbol), outputStateID_Integer}} -> {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol
			), {prefix_List, suffix_List}}] || MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) :> output_List, (input_List
			 | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol
			), outputStateID_Integer}} -> {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List,
			 suffix_List}}]&];
		initializationEventsList = Select[VertexList[evolutionCausalGraph], MatchQ[#, {Null -> output_String, Null, {prefix_String,
			 suffix_String}}] || MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer}} -> {Null -> output_String, Null, 
			{prefix_String, suffix_String}}] || MatchQ[#, stepNumber_Integer -> {Null -> output_String, Null, {prefix_String, suffix_String
			}}] || MatchQ[#, {Automatic, {Null, outputStateID_Integer}} -> {Null -> output_String, Null, {prefix_String, suffix_String
			}}] || MatchQ[#, {Null -> output_List, Null, {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer
			}} -> {Null -> output_List, Null, {prefix_List, suffix_List}}] || MatchQ[#, stepNumber_Integer -> {Null -> output_List,
			 Null, {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {Null, outputStateID_Integer}} -> {Null -> output_List,
			 Null, {prefix_List, suffix_List}}] || MatchQ[#, {Null -> Null, Null, {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer,
			 {Null, Null}} -> {Null -> Null, Null, {prefix_List, suffix_List}}] || MatchQ[#, stepNumber_Integer -> {Null -> Null,
			 Null, {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {Null, Null}} -> {Null -> Null, Null, {prefix_List, suffix_List
			}}] || MatchQ[#, {Null :> output_List, Null, {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer
			}} -> {Null :> output_List, Null, {prefix_List, suffix_List}}] || MatchQ[#, stepNumber_Integer -> {Null :> output_List,
			 Null, {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {Null, outputStateID_Integer}} -> {Null :> output_List,
			 Null, {prefix_List, suffix_List}}]&];
		Graph[evolutionCausalGraph, VertexStyle -> Union[(# -> Directive[Opacity[0.7], Hue[0.62, 0.45, 0.87]]& /@ statesList
			), (# -> Directive[Opacity[0.7], RGBColor[0.259, 0.576, 1]]& /@ initializationEventsList), (# -> Directive[Opacity[0.7
			], Hue[0.11, 1, 0.97]]& /@ Complement[canonicalizedEventsList, initializationEventsList])], VertexShapeFunction -> (
			(# -> Automatic)& /@ VertexList[evolutionCausalGraph]), FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "CausalGraphInstances", options : OptionsPattern[]] :=
	Module[{eventsList, tracedStatesEdgeList, causalGraph, causalEdgeList, evolutionCausalGraph, inputNodes, outputNodes,
		 paths},
		causalGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
			 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
			 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
			 stepCount, "CausalGraph", "IncludeStepNumber" -> True];
		causalEdgeList = EdgeList[causalGraph];
		eventsList = VertexList[causalGraph];
		tracedStatesEdgeList = getTracedStatesEdgeList[eventsList, eventApplicationFunction];
		evolutionCausalGraph = Graph[Union[Flatten[tracedStatesEdgeList], causalEdgeList]];
		inputNodes = VertexList[evolutionCausalGraph][[Position[VertexInDegree[evolutionCausalGraph], 0][[All, 1]]]];
		outputNodes = VertexList[evolutionCausalGraph][[Position[VertexOutDegree[evolutionCausalGraph], 0][[All, 1]]]];
		paths =
			Catenate[
				Module[{inputNode = #},
						Catenate[FindPath[Graph[Flatten[tracedStatesEdgeList]], inputNode, #, Infinity, All]& /@ outputNodes]
					]& /@ inputNodes
			];
		Take[DeleteDuplicates[Subgraph[Graph[causalEdgeList, VertexShapeFunction -> getEventRenderingFunction[systemType, 
			OptionValue["EventRenderingFunction"], OptionValue["VertexSizeMultiplier"]], PerformanceGoal -> getGraphQuality[{OptionValue[
			"EventRenderingFunction"]}], EdgeStyle -> Directive[{Hue[0, 1, 0.56], AbsoluteThickness[OptionValue["LineThickness"]
			]}]], #]& /@ paths], UpTo[OptionValue["MaxItems"]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "CausalGraphStructureInstances", options : OptionsPattern[]] :=
	Module[{causalGraphInstances},
		causalGraphInstances = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "CausalGraphInstances", options];
		Graph[#, VertexStyle -> Directive[Opacity[0.7], Hue[0.11, 1, 0.97]], VertexShapeFunction -> ((# -> Automatic)& /@ 
			VertexList[#]), FilterRules[{options}, Options[Graph]]]& /@ causalGraphInstances
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionCausalGraphInstances", options : OptionsPattern[]] :=
	Module[{eventsList, eventsListWithInitialization, initialEvents, statesList, tracedStatesEdgeList, causalGraph, causalGraphWithInitialization,
		 causalEdgeList, evolutionCausalGraph, inputNodes, outputNodes, paths},
		causalGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
			 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
			 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
			 stepCount, "CausalGraph", "IncludeStepNumber" -> True, "IncludeInitializationEvents" -> OptionValue["IncludeInitializationEvents"
			]];
		causalGraphWithInitialization = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "CausalGraph", "IncludeStepNumber" -> True, "IncludeInitializationEvents" -> True]
			;
		causalEdgeList = EdgeList[causalGraph];
		eventsList = VertexList[causalGraph];
		eventsListWithInitialization = VertexList[causalGraphWithInitialization];
		initialEvents =
			If[
				OptionValue["IncludeInitializationEvents"],
				Which[
					systemType === "ListSubstitutionSystem",
					Select[eventsListWithInitialization, MatchQ[#, stepNumber_Integer -> {Null -> state_List, Null, {{}, {}}}]&],
					systemType === "WolframModel",
					Select[eventsListWithInitialization, MatchQ[#, stepNumber_Integer -> {Null :> state_List, Null, {{}, {}}}]&],
					systemType === "CellularAutomaton",
					Select[eventsListWithInitialization, MatchQ[#, stepNumber_Integer -> {Null -> Null, Null, {state_List, {}}}]&],
					systemType =!= "ListSubstitutionSystem" && systemType =!= "WolframModel" && systemType =!= "CellularAutomaton",
					Select[eventsListWithInitialization, MatchQ[#, stepNumber_Integer -> {Null -> state_String, Null, {"", ""}}]&]
				],
				{}
			];
		tracedStatesEdgeList = getTracedStatesEdgeList[eventsList, eventApplicationFunction];
		statesList = Catenate[getStatesList[eventsListWithInitialization, eventApplicationFunction]];
		evolutionCausalGraph = Graph[Union[Flatten[tracedStatesEdgeList], causalEdgeList], EdgeStyle -> Union[(DirectedEdge
			 @@ #) -> Directive[{Hue[0.07, 0.78, 1], AbsoluteThickness[OptionValue["LineThickness"]], Dashing[None]}]& /@ causalEdgeList,
			 (DirectedEdge @@ #) -> Directive[{Hue[0.75, 0, 0.24], Dashing[None], AbsoluteThickness[OptionValue["LineThickness"]
			]}]& /@ Flatten[tracedStatesEdgeList]], VertexShapeFunction -> getStateEventRenderingFunction[systemType, OptionValue[
			"StateRenderingFunction"], statesList, OptionValue["EventRenderingFunction"], eventsList, OptionValue["VertexSizeMultiplier"
			]], PerformanceGoal -> getGraphQuality[{OptionValue["StateRenderingFunction"], OptionValue["EventRenderingFunction"],
			 eventsList}], FilterRules[{options}, Options[Graph]]];
		inputNodes = VertexList[evolutionCausalGraph][[Position[VertexInDegree[evolutionCausalGraph], 0][[All, 1]]]];
		outputNodes = VertexList[evolutionCausalGraph][[Position[VertexOutDegree[evolutionCausalGraph], 0][[All, 1]]]];
		paths =
			Catenate[
				Module[{inputNode = #},
						Catenate[FindPath[Graph[Flatten[tracedStatesEdgeList]], inputNode, #, Infinity, All]& /@ outputNodes]
					]& /@ inputNodes
			];
		Take[DeleteDuplicates[Subgraph[evolutionCausalGraph, #]& /@ paths], UpTo[OptionValue["MaxItems"]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionCausalGraphStructureInstances", options : OptionsPattern[]] :=
	Module[{evolutionCausalGraphInstances, statesList, initializationEventsList, canonicalizedEventsList},
		evolutionCausalGraphInstances = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionCausalGraphInstances", options];
		statesList = Flatten[Select[VertexList[#], !MatchQ[#, {(input_String | input_Symbol) -> output_String, (input_String
			 | input_Symbol), {prefix_String, suffix_String}}] && !MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol
			), outputStateID_Integer}} -> {(input_String | input_Symbol) -> output_String, (input_String | input_Symbol), {prefix_String,
			 suffix_String}}] && !MatchQ[#, stepNumber_Integer -> {(input_String | input_Symbol) -> output_String, (input_String
			 | input_Symbol), {prefix_String, suffix_String}}] && !MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol
			), outputStateID_Integer}} -> {(input_String | input_Symbol) -> output_String, (input_String | input_Symbol), {prefix_String,
			 suffix_String}}] && !MatchQ[#, {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List,
			 suffix_List}}] && !MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer
			}} -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[
			#, stepNumber_Integer -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List
			}}] && !MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer}} -> {(input_List
			 | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[#, {(input_List
			 | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List, suffix_List}}] && !
			MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), (outputStateID_Integer | outputStateID_Symbol
			)}} -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List, 
			suffix_List}}] && !MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol),
			 (input_List | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol
			), (outputStateID_Integer | outputStateID_Symbol)}} -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol
			), (input_List | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[#, {(input_List | input_Symbol) :> output_List,
			 (input_List | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer
			 | inputStateID_Symbol), outputStateID_Integer}} -> {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol
			), {prefix_List, suffix_List}}] && !MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) :> output_List, (input_List
			 | input_Symbol), {prefix_List, suffix_List}}] && !MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol
			), outputStateID_Integer}} -> {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List,
			 suffix_List}}]&]& /@ evolutionCausalGraphInstances];
		canonicalizedEventsList = Flatten[Select[VertexList[#], MatchQ[#, {(input_String | input_Symbol) -> output_String,
			 (input_String | input_Symbol), {prefix_String, suffix_String}}] || MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer
			 | inputStateID_Symbol), outputStateID_Integer}} -> {(input_String | input_Symbol) -> output_String, (input_String |
			 input_Symbol), {prefix_String, suffix_String}}] || MatchQ[#, stepNumber_Integer -> {(input_String | input_Symbol) ->
			 output_String, (input_String | input_Symbol), {prefix_String, suffix_String}}] || MatchQ[#, {Automatic, {(inputStateID_Integer
			 | inputStateID_Symbol), outputStateID_Integer}} -> {(input_String | input_Symbol) -> output_String, (input_String |
			 input_Symbol), {prefix_String, suffix_String}}] || MatchQ[#, {(input_List | input_Symbol) -> output_List, (input_List
			 | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol
			), outputStateID_Integer}} -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List,
			 suffix_List}}] || MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol
			), {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol), outputStateID_Integer
			}} -> {(input_List | input_Symbol) -> output_List, (input_List | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[
			#, {(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List, suffix_List
			}}] || MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer | inputStateID_Symbol), (outputStateID_Integer | outputStateID_Symbol
			)}} -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol), (input_List | input_Symbol), {prefix_List, 
			suffix_List}}] || MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol), 
			(input_List | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol
			), (outputStateID_Integer | outputStateID_Symbol)}} -> {(input_List | input_Symbol) -> (output_Integer | output_Symbol
			), (input_List | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[#, {(input_List | input_Symbol) :> output_List,
			 (input_List | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer, {(inputStateID_Integer 
			| inputStateID_Symbol), outputStateID_Integer}} -> {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol
			), {prefix_List, suffix_List}}] || MatchQ[#, stepNumber_Integer -> {(input_List | input_Symbol) :> output_List, (input_List
			 | input_Symbol), {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {(inputStateID_Integer | inputStateID_Symbol
			), outputStateID_Integer}} -> {(input_List | input_Symbol) :> output_List, (input_List | input_Symbol), {prefix_List,
			 suffix_List}}]&]& /@ evolutionCausalGraphInstances];
		initializationEventsList = Flatten[Select[VertexList[#], MatchQ[#, {Null -> output_String, Null, {prefix_String, suffix_String
			}}] || MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer}} -> {Null -> output_String, Null, {prefix_String,
			 suffix_String}}] || MatchQ[#, stepNumber_Integer -> {Null -> output_String, Null, {prefix_String, suffix_String}}] 
			|| MatchQ[#, {Automatic, {Null, outputStateID_Integer}} -> {Null -> output_String, Null, {prefix_String, suffix_String
			}}] || MatchQ[#, {Null -> output_List, Null, {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer
			}} -> {Null -> output_List, Null, {prefix_List, suffix_List}}] || MatchQ[#, stepNumber_Integer -> {Null -> output_List,
			 Null, {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {Null, outputStateID_Integer}} -> {Null -> output_List,
			 Null, {prefix_List, suffix_List}}] || MatchQ[#, {Null -> Null, Null, {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer,
			 {Null, Null}} -> {Null -> Null, Null, {prefix_List, suffix_List}}] || MatchQ[#, stepNumber_Integer -> {Null -> Null,
			 Null, {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {Null, Null}} -> {Null -> Null, Null, {prefix_List, suffix_List
			}}] || MatchQ[#, {Null :> output_List, Null, {prefix_List, suffix_List}}] || MatchQ[#, {stepNumber_Integer, {Null, outputStateID_Integer
			}} -> {Null :> output_List, Null, {prefix_List, suffix_List}}] || MatchQ[#, stepNumber_Integer -> {Null :> output_List,
			 Null, {prefix_List, suffix_List}}] || MatchQ[#, {Automatic, {Null, outputStateID_Integer}} -> {Null :> output_List,
			 Null, {prefix_List, suffix_List}}]&]& /@ evolutionCausalGraphInstances];
		Graph[#, VertexStyle -> Union[(# -> Directive[Opacity[0.7], Hue[0.62, 0.45, 0.87]]& /@ statesList), (# -> Directive[
			Opacity[0.7], RGBColor[0.259, 0.576, 1]]& /@ initializationEventsList), (# -> Directive[Opacity[0.7], Hue[0.11, 1, 0.97
			]]& /@ Complement[canonicalizedEventsList, initializationEventsList])], VertexShapeFunction -> ((# -> Automatic)& /@
			 VertexList[#]), FilterRules[{options}, Options[Graph]]]& /@ evolutionCausalGraphInstances
	]



getBranchPairResolvent[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, branchPair_List, stepCount_Integer] :=
	Module[{statesGraph, statesGraphNew, branchPairIntersection, inducedSubgraph},
		statesGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
			 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
			 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, branchPair,
			 stepCount, "StatesGraph"];
		statesGraphNew = Graph[Union[VertexList[statesGraph], branchPair], EdgeList[statesGraph]];
		branchPairIntersection = Intersection[VertexOutComponent[statesGraphNew, First[branchPair]], VertexOutComponent[statesGraphNew,
			 Last[branchPair]]];
		inducedSubgraph = Subgraph[statesGraphNew, branchPairIntersection];
		If[
			Length[Select[branchPairIntersection, VertexInDegree[inducedSubgraph, #] == 0&]] > 0,
			First[Select[branchPairIntersection, VertexInDegree[inducedSubgraph, #] == 0&]],
			First[branchPairIntersection]
		]
	]

getBranchPairResolvent[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, branchPair_Rule, stepCount_Integer] :=
	Module[{statesGraph, statesGraphNew, branchPairIntersection, inducedSubgraph},
		statesGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
			 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
			 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, Last[
			branchPair], stepCount, "StatesGraph"];
		statesGraphNew = Graph[Union[VertexList[statesGraph], Last[branchPair]], EdgeList[statesGraph]];
		branchPairIntersection = Intersection[VertexOutComponent[statesGraphNew, First[Last[branchPair]]], VertexOutComponent[
			statesGraphNew, Last[Last[branchPair]]]];
		inducedSubgraph = Subgraph[statesGraphNew, branchPairIntersection];
		If[
			Length[Select[branchPairIntersection, VertexInDegree[inducedSubgraph, #] == 0&]] > 0,
			First[Select[branchPairIntersection, VertexInDegree[inducedSubgraph, #] == 0&]],
			First[branchPairIntersection]
		]
	]



getStringOverlaps[string_String] :=
	Select[Table[StringJoin[StringTake[string, i], string], {i, StringLength[string] - 1}], StringMatchQ[#, string ~~ __
		]&]

getStringOverlaps[{string1_String, string2_String}] :=
	Union[getLeftStringOverlaps[string1, string2], getLeftStringOverlaps[string2, string1], getRightStringOverlaps[string1,
		 string2], getRightStringOverlaps[string2, string1]]



getLeftStringOverlaps[string1_String, string2_String] :=
	Select[Table[StringJoin[StringTake[string1, i], string2], {i, StringLength[string1] - 1}], StringMatchQ[#, string1 
		~~ __]&]



getRightStringOverlaps[string1_String, string2_String] :=
	If[
		StringPosition[string2, string1, 1] === {},
		{},
		{string2}
	]



getListOverlaps[list_List] :=
	Select[
		Table[Join[Take[list, i], list], {i, Length[list] - 1}],
		MatchQ[
			#,
			Module[{padding},
				Join[list, {padding___}]
			]
		]&
	]

getListOverlaps[{list1_List, list2_List}] :=
	Union[getLeftListOverlaps[list1, list2], getLeftListOverlaps[list2, list1], getRightListOverlaps[list1, list2], getRightListOverlaps[
		list2, list1]]



getLeftListOverlaps[list1_List, list2_List] :=
	Select[
		Table[Join[Take[list1, i], list2], {i, Length[list1] - 1}],
		MatchQ[
			#,
			Module[{padding},
				Join[list1, {padding___}]
			]
		]&
	]



getRightListOverlaps[list1_List, list2_List] :=
	If[
		SequencePosition[list2, list1, 1] === {},
		{},
		{list2}
	]



getHypergraphOverlaps[hypergraph_List] :=
	getHypergraphOverlaps[{hypergraph, hypergraph}]

getHypergraphOverlaps[{hypergraph1_List, hypergraph2_List}] :=
	With[{uniqueEdgeList1 = Map[$$1, hypergraph1, {2}], uniqueEdgeList2 = Map[$$2, hypergraph2, {2}]},
		getHypergraphUnion[uniqueEdgeList1, uniqueEdgeList2, ##]& @@@ Reap[getRemainingHypergraphOverlaps[uniqueEdgeList1,
			 uniqueEdgeList2, <||>, Graph[{}]]][[2, 1]]
	]



getRemainingHypergraphOverlaps[hypergraph1_List, hypergraph2_List, edgeMatches_Association, vertexMatches_Graph] :=
	Outer[(getAttemptedHypergraphMatch[hypergraph1, hypergraph2, edgeMatches, vertexMatches, #1, #2])&, ##]& @@ Range /@
		 Length /@ {hypergraph1, hypergraph2}



getAttemptedHypergraphMatch[hypergraph1_List, hypergraph2_List, edgeMatches_Association, vertexMatches_Graph, nextIndex1_Integer,
	 nextIndex2_Integer] :=
	With[{newEdgeMatch = getCombinedHypergraphEdgeMatch[edgeMatches, nextIndex1, nextIndex2], newVertexMatch = getCombinedHypergraphVertexMatch[
		vertexMatches, hypergraph1[[nextIndex1]], hypergraph2[[nextIndex2]]]},
			Sow[{newEdgeMatch, Graph[newVertexMatch, VertexLabels -> Automatic]}];
			getRemainingHypergraphOverlaps[hypergraph1, hypergraph2, newEdgeMatch, newVertexMatch];
		] /; hypergraphMatchQ[hypergraph1[[nextIndex1]], hypergraph2[[nextIndex2]]] && !hypergraphEdgeUsedQ[edgeMatches, nextIndex1,
			 nextIndex2] && !hypergraphBacktrackingMatchQ[edgeMatches, nextIndex1, nextIndex2]



hypergraphMatchQ[hypergraph1_List, hypergraph2_List] :=
	True /; Length[hypergraph1] == Length[hypergraph2]

hypergraphMatchQ[__] :=
	False



hypergraphEdgeUsedQ[edgeMatches_Association, nextIndex1_Integer, nextIndex2_Integer] :=
	MemberQ[Keys[edgeMatches], nextIndex1] || MemberQ[Values[edgeMatches], nextIndex2]



hypergraphBacktrackingMatchQ[<||>, nextIndex1_Integer, nextIndex2_Integer] :=
	False

hypergraphBacktrackingMatchQ[edgeMatches_Association, nextIndex1_Integer, nextIndex2_Integer] :=
	If[
			nextIndex1 < Last[Keys[edgeMatches]],
			True,
			False
		] /; Length[edgeMatches] > 0

hypergraphBacktrackingMatchQ[edgeMatches_Association, nextIndex1_Integer, nextIndex2_Integer] :=
	If[
			nextIndex1 == Last[Keys[edgeMatches]] && nextIndex2 < Last[Values[edgeMatches]],
			True,
			False
		] /; Length[edgeMatches] > 0

hypergraphBacktrackingMatchQ[__] :=
	False



getCombinedHypergraphEdgeMatch[edgeMatches_Association, newIndex1_Integer, newIndex2_Integer] :=
	Append[edgeMatches, <|newIndex1 -> newIndex2|>]



getCombinedHypergraphVertexMatch[vertexMatches_Graph, newEdge1_List, newEdge2_List] :=
	EdgeAdd[vertexMatches, Thread[UndirectedEdge[newEdge1, newEdge2]]]



getHypergraphVertexIdentificationRules[vertexMatches_Graph] :=
	Catenate[
		Function[{hyperedge},
				# -> hyperedge[[1]]& /@ hyperedge[[2 ;; ]]
			] /@ ConnectedComponents[vertexMatches]
	]



getHypergraphUnion[hypergraph1_List, hypergraph2_List, edgeMatches_Association, vertexMatches_Graph] :=
	With[{uniqueHypergraph1Edges = Complement[Range[Length[hypergraph1]], Keys[edgeMatches]], uniqueHypergraph2Edges = 
		Complement[Range[Length[hypergraph2]], Values[edgeMatches]]},
		{getHypergraphIndices[Replace[Join[hypergraph1[[uniqueHypergraph1Edges]], hypergraph2[[uniqueHypergraph2Edges]], hypergraph1
			[[Keys[edgeMatches]]]], getHypergraphVertexIdentificationRules[vertexMatches], {2}]], Association[Sort[Join[Thread[uniqueHypergraph1Edges
			 -> Range[Length[uniqueHypergraph1Edges]]], Thread[Keys[edgeMatches] -> Range[Length[edgeMatches]] + Length[uniqueHypergraph1Edges
			] + Length[uniqueHypergraph2Edges]]]]], Association[Sort[Thread[uniqueHypergraph2Edges -> Range[Length[uniqueHypergraph2Edges
			]] + Length[uniqueHypergraph1Edges]], Thread[Values[edgeMatches] -> Range[Length[edgeMatches]] + Length[uniqueHypergraph1Edges
			] + Length[uniqueHypergraph2Edges]]]]}
	]



getHypergraphIndices[hypergraph_List] :=
	With[{vertexList = Union[Catenate[hypergraph]]},
		Replace[hypergraph, Thread[vertexList -> Range[Length[vertexList]]], {2}]
	]



getOverlaps[expressions_List] :=
	getStringOverlaps[{First[expressions], First[expressions]}] /; (Length[expressions] == 1 && AllTrue[expressions, StringQ
		])

getOverlaps[expressions_List] :=
	getStringOverlaps[expressions] /; (Length[expressions] == 2 && AllTrue[expressions, StringQ])

getOverlaps[expressions_List] :=
	DeleteDuplicates[Catenate[getStringOverlaps[#]& /@ Tuples[expressions, 2]]] /; (Length[expressions] > 2 && AllTrue[
		expressions, StringQ])

getOverlaps[expressions_List] :=
	getListOverlaps[{First[expressions], First[expressions]}] /; (Length[expressions] == 1 && AllTrue[expressions, ListQ[
		#] && Depth[#] == 2&])

getOverlaps[expressions_List] :=
	getListOverlaps[expressions] /; (Length[expressions] == 2 && AllTrue[expressions, ListQ[#] && Depth[#] == 2&])

getOverlaps[expressions_List] :=
	DeleteDuplicates[Catenate[getListOverlaps[#]& /@ Tuples[expressions, 2]]] /; (Length[expressions] > 2 && AllTrue[expressions,
		 ListQ[#] && Depth[#] == 2&])

getOverlaps[expressions_List] :=
	First[#]& /@ (getHypergraphOverlaps[{First[expressions], First[expressions]}]) /; (Length[expressions] == 1 && AllTrue[
		expressions, ListQ[#] && Depth[#] == 3&])

getOverlaps[expressions_List] :=
	First[#]& /@ (getHypergraphOverlaps[expressions]) /; (Length[expressions] == 2 && AllTrue[expressions, ListQ[#] && 
		Depth[#] == 3&])

getOverlaps[expressions_List] :=
	First[#]& /@ (DeleteDuplicates[Catenate[getHypergraphOverlaps[#]& /@ Tuples[expressions, 2]]]) /; (Length[expressions
		] > 2& 7 AllTrue[expressions, ListQ[#] && Depth[#] == 3&])



convergentCanonicalBranchPairQ[rules_List, branchPair_Rule, stepCount_Integer] :=
	convergentCanonicalBranchPairQ[rules, Last[branchPair], stepCount]

convergentCanonicalBranchPairQ[rules_List, branchPair_List, stepCount_Integer] :=
	If[
			AllTrue[rules, (ListQ[First[#]] && Depth[First[#]] != 3) || (StringQ[First[#]])&],
			Module[{undirectedStatesGraph},
				undirectedStatesGraph = UndirectedGraph[MultiwaySystem[rules, branchPair, stepCount, "StatesGraph"]];
				ConnectedGraphQ[Graph[Union[VertexList[undirectedStatesGraph], branchPair], EdgeList[undirectedStatesGraph]]]
			],
			Module[{undirectedStatesGraph},
				undirectedStatesGraph = UndirectedGraph[MultiwaySystem["WolframModel" -> rules, branchPair, stepCount, "StatesGraph"
					]];
				ConnectedGraphQ[Graph[Union[VertexList[undirectedStatesGraph], branchPair], EdgeList[undirectedStatesGraph]]]
			]
		] /; !AllTrue[rules, IntegerQ[Last[#]]&]

convergentCanonicalBranchPairQ[rules_List, branchPair_List, stepCount_Integer] :=
	Module[{undirectedStatesGraph},
			undirectedStatesGraph = UndirectedGraph[MultiwaySystem[CellularAutomaton[rules], branchPair, stepCount, "StatesGraph"
				]];
			ConnectedGraphQ[Graph[Union[VertexList[undirectedStatesGraph], branchPair], EdgeList[undirectedStatesGraph]]]
		] /; AllTrue[rules, IntegerQ[Last[#]]&]



getCanonicalBranchPairResolvent[rules_List, branchPair_Rule, stepCount_Integer] :=
	getCanonicalBranchPairResolvent[rules, Last[branchPair], stepCount]

getCanonicalBranchPairResolvent[rules_List, branchPair_List, stepCount_Integer] :=
	If[
			AllTrue[rules, (ListQ[First[#]] && Depth[First[#]] != 3) || (StringQ[First[#]])&],
			Module[{statesGraph, statesGraphNew, branchPairIntersection, inducedSubgraph},
				statesGraph = MultiwaySystem[rules, branchPair, stepCount, "StatesGraph"];
				statesGraphNew = Graph[Union[VertexList[statesGraph], branchPair], EdgeList[statesGraph]];
				branchPairIntersection = Intersection[VertexOutComponent[statesGraphNew, First[branchPair]], VertexOutComponent[
					statesGraphNew, Last[branchPair]]];
				inducedSubgraph = Subgraph[statesGraphNew, branchPairIntersection];
				If[
					Length[Select[branchPairIntersection, VertexInDegree[inducedSubgraph, #] == 0&]] > 0,
					First[Select[branchPairIntersection, VertexInDegree[inducedSubgraph, #] == 0&]],
					First[branchPairIntersection]
				]
			],
			Module[{statesGraph, statesGraphNew, branchPairIntersection, inducedSubgraph},
				statesGraph = MultiwaySystem["WolframModel" -> rules, branchPair, stepCount, "StatesGraph"];
				statesGraphNew = Graph[Union[VertexList[statesGraph], branchPair], EdgeList[statesGraph]];
				branchPairIntersection = Intersection[VertexOutComponent[statesGraphNew, First[branchPair]], VertexOutComponent[
					statesGraphNew, Last[branchPair]]];
				inducedSubgraph = Subgraph[statesGraphNew, branchPairIntersection];
				If[
					Length[Select[branchPairIntersection, VertexInDegree[inducedSubgraph, #] == 0&]] > 0,
					First[Select[branchPairIntersection, VertexInDegree[inducedSubgraph, #] == 0&]],
					First[branchPairIntersection]
				]
			]
		] /; !AllTrue[rules, IntegerQ[Last[#]]&]

getCanonicalBranchPairResolvent[rules_List, branchPair_List, stepCount_Integer] :=
	Module[{statesGraph, statesGraphNew, branchPairIntersection, inducedSubgraph},
			statesGraph = MultiwaySystem[CellularAutomaton[rules], branchPair, stepCount, "StatesGraph"];
			statesGraphNew = Graph[Union[VertexList[statesGraph], branchPair], EdgeList[statesGraph]];
			branchPairIntersection = Intersection[VertexOutComponent[statesGraphNew, First[branchPair]], VertexOutComponent[statesGraphNew,
				 Last[branchPair]]];
			inducedSubgraph = Subgraph[statesGraphNew, branchPairIntersection];
			If[
				Length[Select[branchPairIntersection, VertexInDegree[inducedSubgraph, #] == 0&]] > 0,
				First[Select[branchPairIntersection, VertexInDegree[inducedSubgraph, #] == 0&]],
				First[branchPairIntersection]
			]
		] /; AllTrue[rules, IntegerQ[Last[#]]&]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "BranchPairsList", options : OptionsPattern[]] :=
	Module[{initialStatesGraph, branchingStates, branchPairsWithDuplication},
		initialStatesGraph = SimpleGraph[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "StatesGraph", options]];
		branchingStates = VertexList[initialStatesGraph][[Position[VertexOutDegree[initialStatesGraph], _ ? (# >= 2&)][[All,
			 1]]]];
		branchPairsWithDuplication = {};
		If[
			OptionValue["GivePredecessors"],
			(branchPairsWithDuplication = Join[branchPairsWithDuplication, Thread[# -> Subsets[Rest[VertexOutComponent[initialStatesGraph,
				 {#}, 1]], {2}]]])& /@ branchingStates,
			(branchPairsWithDuplication = Join[branchPairsWithDuplication, Subsets[Rest[VertexOutComponent[initialStatesGraph,
				 {#}, 1]], {2}]])& /@ branchingStates
		];
		DeleteDuplicates[branchPairsWithDuplication]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "NewBranchPairsList", options : OptionsPattern[]] :=
	Module[{branchPairs, oldBranchPairs},
		If[
			stepCount > 0,
			branchPairs = Sort /@ MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
				 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
				 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
				|>, initialConditions, stepCount, "BranchPairsList", options];
			oldBranchPairs = Sort /@ MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
				 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
				 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
				|>, initialConditions, stepCount - 1, "BranchPairsList", options];
			Complement[branchPairs, oldBranchPairs],
			{}
		]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionBranchPairsList", options : OptionsPattern[]] :=
	Module[{initialEvolutionGraph, branchingStates, evolutionBranchPairsWithDuplication},
		initialEvolutionGraph = SimpleGraph[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionGraph", options]];
		branchingStates = VertexList[initialEvolutionGraph][[Position[VertexOutDegree[initialEvolutionGraph], _ ? (# >= 2&
			)][[All, 1]]]];
		evolutionBranchPairsWithDuplication = {};
		If[
			OptionValue["GivePredecessors"],
			(evolutionBranchPairsWithDuplication = Join[evolutionBranchPairsWithDuplication, Thread[# -> Subsets[Rest[VertexOutComponent[
				initialEvolutionGraph, {#}, 1]], {2}]]])& /@ branchingStates,
			(evolutionBranchPairsWithDuplication = Join[evolutionBranchPairsWithDuplication, Subsets[Rest[VertexOutComponent[
				initialEvolutionGraph, {#}, 1]], {2}]])& /@ branchingStates
		];
		DeleteDuplicates[evolutionBranchPairsWithDuplication]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "NewEvolutionBranchPairsList", options : OptionsPattern[]] :=
	Module[{evolutionBranchPairs, oldEvolutionBranchPairs},
		If[
			stepCount > 0,
			evolutionBranchPairs = Map[Sort, MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
				 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
				 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
				|>, initialConditions, stepCount, "EvolutionBranchPairsList", options], {2}];
			oldEvolutionBranchPairs = Map[Sort, MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
				 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
				 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
				|>, initialConditions, stepCount - 1, "EvolutionBranchPairsList", options], {2}];
			Complement[evolutionBranchPairs, oldEvolutionBranchPairs],
			{}
		]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "BranchPairEventsList", options : OptionsPattern[]] :=
	Module[{initialEvolutionEventsGraph, branchingStates, branchPairEventsWithDuplication},
		initialEvolutionEventsGraph = SimpleGraph[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionEventsGraph", options]];
		branchingStates = VertexList[initialEvolutionEventsGraph][[Position[VertexOutDegree[initialEvolutionEventsGraph], 
			_ ? (# >= 2&)][[All, 1]]]];
		branchPairEventsWithDuplication = {};
		If[
			OptionValue["GivePredecessors"],
			(branchPairEventsWithDuplication = Join[branchPairEventsWithDuplication, Thread[# -> Subsets[Rest[VertexOutComponent[
				initialEvolutionEventsGraph, {#}, 1]], {2}]]])& /@ branchingStates,
			(branchPairEventsWithDuplication = Join[branchPairEventsWithDuplication, Subsets[Rest[VertexOutComponent[initialEvolutionEventsGraph,
				 {#}, 1]], {2}]])& /@ branchingStates
		];
		DeleteDuplicates[branchPairEventsWithDuplication]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "NewBranchPairEventsList", options : OptionsPattern[]] :=
	Module[{branchPairEvents, oldBranchPairEvents},
		If[
			stepCount > 0,
			branchPairEvents = Sort /@ MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
				 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
				 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
				|>, initialConditions, stepCount, "BranchPairEventsList", options];
			oldBranchPairEvents = Sort /@ MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
				 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
				 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
				|>, initialConditions, stepCount - 1, "BranchPairEventsList", options];
			Complement[branchPairEvents, oldBranchPairEvents],
			{}
		]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionBranchPairEventsList", options : OptionsPattern[]] :=
	Module[{initialEvolutionEventsGraph, branchingStates, evolutionBranchPairEventsWithDuplication},
		initialEvolutionEventsGraph = SimpleGraph[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionEventsGraph", "IncludeStepNumber" -> True]];
		branchingStates = VertexList[initialEvolutionEventsGraph][[Position[VertexOutDegree[initialEvolutionEventsGraph], 
			_ ? (# >= 2&)][[All, 1]]]];
		evolutionBranchPairEventsWithDuplication = {};
		If[
			OptionValue["GivePredecessors"],
			(evolutionBranchPairEventsWithDuplication = Join[evolutionBranchPairEventsWithDuplication, Thread[# -> Subsets[Rest[
				VertexOutComponent[initialEvolutionEventsGraph, {#}, 1]], {2}]]])& /@ branchingStates,
			(evolutionBranchPairEventsWithDuplication = Join[evolutionBranchPairEventsWithDuplication, Subsets[Rest[VertexOutComponent[
				initialEvolutionEventsGraph, {#}, 1]], {2}]])& /@ branchingStates
		];
		DeleteDuplicates[evolutionBranchPairEventsWithDuplication]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "NewEvolutionBranchPairEventsList", options : OptionsPattern[]] :=
	Module[{evolutionBranchPairEvents, oldEvolutionBranchPairEvents},
		If[
			stepCount > 0,
			evolutionBranchPairEvents = (First[#] -> Sort[Last[#]])& /@ MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction,
				 "StateEquivalenceFunction" -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction"
				 -> eventDecompositionFunction, "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, 
				"EventSelectionFunction" -> eventSelectionFunction|>, initialConditions, stepCount, "EvolutionBranchPairEventsList",
				 options];
			oldEvolutionBranchPairEvents = (First[#] -> Sort[Last[#]])& /@ MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction,
				 "StateEquivalenceFunction" -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction"
				 -> eventDecompositionFunction, "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, 
				"EventSelectionFunction" -> eventSelectionFunction|>, initialConditions, stepCount - 1, "EvolutionBranchPairEventsList",
				 options];
			Complement[evolutionBranchPairEvents, oldEvolutionBranchPairEvents],
			{}
		]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "BranchialGraph", options : OptionsPattern[]] :=
	Module[{newBranchPairs, allStatesList},
		newBranchPairs = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" ->
			 stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "NewBranchPairsList", "GivePredecessors" -> False, "IncludeStepNumber" -> OptionValue[
			"IncludeStepNumber"], "IncludeStateID" -> OptionValue["IncludeStateID"]];
		allStatesList =
			If[
				OptionValue["IncludeFullBranchialSpace"],
				Last[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
					 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
					 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
					 stepCount, "AllStatesList", options]],
				VertexList[Graph[UndirectedEdge @@@ newBranchPairs]]
			];
		Graph[allStatesList, UndirectedEdge @@@ newBranchPairs, VertexShapeFunction -> getStateRenderingFunction[systemType,
			 OptionValue["StateRenderingFunction"], OptionValue["VertexSizeMultiplier"]], EdgeStyle -> Hue[0.89, 0.97, 0.71], PerformanceGoal
			 -> getGraphQuality[{OptionValue["StateRenderingFunction"]}], VertexWeight -> MultiwaySystem[<|"StateEvolutionFunction"
			 -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction,
			 "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction" -> eventApplicationFunction,
			 "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions, stepCount, "StateWeights",
			 options], FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "BranchialGraphStructure", options : OptionsPattern[]] :=
	Module[{branchialGraph},
		branchialGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" ->
			 stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "BranchialGraph", options];
		Graph[branchialGraph, VertexStyle -> Directive[Opacity[0.7], Hue[0.62, 0.45, 0.87]], VertexShapeFunction -> ((# ->
			 Automatic)& /@ VertexList[branchialGraph]), FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "AllStatesBranchialGraph", options : OptionsPattern[]] :=
	Module[{branchPairs, allStatesList},
		branchPairs = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
			 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
			 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
			 stepCount, "BranchPairsList", "GivePredecessors" -> False, "IncludeStepNumber" -> OptionValue["IncludeStepNumber"],
			 "IncludeStateID" -> OptionValue["IncludeStateID"]];
		allStatesList =
			If[
				OptionValue["IncludeFullBranchialSpace"],
				Catenate[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
					 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
					 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
					 stepCount, "AllStatesList", options]],
				VertexList[Graph[UndirectedEdge @@@ branchPairs]]
			];
		Graph[allStatesList, UndirectedEdge @@@ branchPairs, VertexShapeFunction -> getStateRenderingFunction[systemType, 
			OptionValue["StateRenderingFunction"], OptionValue["VertexSizeMultiplier"]], EdgeStyle -> Hue[0.89, 0.97, 0.71], PerformanceGoal
			 -> getGraphQuality[{OptionValue["StateRenderingFunction"]}], VertexWeight -> MultiwaySystem[<|"StateEvolutionFunction"
			 -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction,
			 "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction" -> eventApplicationFunction,
			 "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions, stepCount, "StateWeights",
			 options], FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "AllStatesBranchialGraphStructure", options : OptionsPattern[]] :=
	Module[{allStatesBranchialGraph},
		allStatesBranchialGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "AllStatesBranchialGraph", options];
		Graph[allStatesBranchialGraph, VertexStyle -> Directive[Opacity[0.7], Hue[0.62, 0.45, 0.87]], VertexShapeFunction 
			-> ((# -> Automatic)& /@ VertexList[allStatesBranchialGraph]), FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionBranchialGraph", options : OptionsPattern[]] :=
	Module[{newEvolutionBranchPairs, allStatesList},
		newEvolutionBranchPairs = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "NewEvolutionBranchPairsList", "GivePredecessors" -> False];
		allStatesList =
			If[
				OptionValue["IncludeFullBranchialSpace"],
				Last[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
					 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
					 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
					 stepCount, "AllStatesList", "IncludeStepNumber" -> True, "IncludeStateID" -> False, "IncludeEventInstances" -> False
					]],
				VertexList[Graph[UndirectedEdge @@@ newEvolutionBranchPairs]]
			];
		Graph[allStatesList, UndirectedEdge @@@ newEvolutionBranchPairs, VertexShapeFunction -> getStateRenderingFunction[
			systemType, OptionValue["StateRenderingFunction"], OptionValue["VertexSizeMultiplier"]], EdgeStyle -> Hue[0.89, 0.97,
			 0.71], PerformanceGoal -> getGraphQuality[{OptionValue["StateRenderingFunction"]}], VertexWeight -> MultiwaySystem[
			<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction, "StateEventFunction"
			 -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction" -> eventApplicationFunction,
			 "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions, stepCount, "StateWeights",
			 "IncludeStepNumber" -> True, "IncludeStateID" -> False, "IncludeEventInstances" -> False, "IncludeStateWeights" -> 
			OptionValue["IncludeStateWeights"], "IncludeStatePathWeights" -> OptionValue["IncludeStatePathWeights"]], FilterRules[
			{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionBranchialGraphStructure", options : OptionsPattern[]] :=
	Module[{evolutionBranchialGraph},
		evolutionBranchialGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionBranchialGraph", options];
		Graph[evolutionBranchialGraph, VertexStyle -> Directive[Opacity[0.7], Hue[0.62, 0.45, 0.87]], VertexShapeFunction 
			-> ((# -> Automatic)& /@ VertexList[evolutionBranchialGraph]), FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "AllStatesEvolutionBranchialGraph", options : OptionsPattern[]] :=
	Module[{evolutionBranchPairs, allStatesList},
		evolutionBranchPairs = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionBranchPairsList", "GivePredecessors" -> False];
		allStatesList =
			If[
				OptionValue["IncludeFullBranchialSpace"],
				Catenate[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
					 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
					 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
					 stepCount, "AllStatesList", "IncludeStepNumber" -> True, "IncludeStateID" -> False, "IncludeEventInstances" -> False
					]],
				VertexList[Graph[UndirectedEdge @@@ evolutionBranchPairs]]
			];
		Graph[allStatesList, UndirectedEdge @@@ evolutionBranchPairs, VertexShapeFunction -> getStateRenderingFunction[systemType,
			 OptionValue["StateRenderingFunction"], OptionValue["VertexSizeMultiplier"]], EdgeStyle -> Hue[0.89, 0.97, 0.71], PerformanceGoal
			 -> getGraphQuality[{OptionValue["StateRenderingFunction"]}], VertexWeight -> MultiwaySystem[<|"StateEvolutionFunction"
			 -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction,
			 "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction" -> eventApplicationFunction,
			 "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions, stepCount, "StateWeights",
			 "IncludeStepNumber" -> True, "IncludeStateID" -> False, "IncludeEventInstances" -> False, "IncludeStateWeights" -> 
			OptionValue["IncludeStateWeights"], "IncludeStatePathWeights" -> OptionValue["IncludeStatePathWeights"]], FilterRules[
			{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "AllStatesEvolutionBranchialGraphStructure", options : OptionsPattern[
	]] :=
	Module[{allStatesEvolutionBranchialGraph},
		allStatesEvolutionBranchialGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "AllStatesEvolutionBranchialGraph", options];
		Graph[allStatesEvolutionBranchialGraph, VertexStyle -> Directive[Opacity[0.7], Hue[0.62, 0.45, 0.87]], VertexShapeFunction
			 -> ((# -> Automatic)& /@ VertexList[allStatesEvolutionBranchialGraph]), FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EventBranchialGraph", options : OptionsPattern[]] :=
	Module[{newBranchPairEvents, allEventsList},
		newBranchPairEvents = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "NewBranchPairEventsList", "GivePredecessors" -> False, "IncludeStepNumber" -> OptionValue[
			"IncludeStepNumber"], "IncludeStateID" -> OptionValue["IncludeStateID"]];
		allEventsList =
			If[
				OptionValue["IncludeFullBranchialSpace"],
				Last[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
					 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
					 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
					 stepCount, "AllEventsList", options]],
				VertexList[Graph[UndirectedEdge @@@ newBranchPairEvents]]
			];
		Graph[allEventsList, UndirectedEdge @@@ newBranchPairEvents, VertexShapeFunction -> getEventRenderingFunction[systemType,
			 OptionValue["EventRenderingFunction"], OptionValue["VertexSizeMultiplier"]], EdgeStyle -> Hue[0.89, 0.97, 0.71], FilterRules[
			{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EventBranchialGraphStructure", options : OptionsPattern[]] :=
	Module[{eventsBranchialGraph},
		eventsBranchialGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EventBranchialGraph", options];
		Graph[eventsBranchialGraph, VertexStyle -> Directive[Opacity[0.7], Hue[0.11, 1, 0.97]], VertexShapeFunction -> ((#
			 -> Automatic)& /@ VertexList[eventsBranchialGraph]), FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "AllEventsBranchialGraph", options : OptionsPattern[]] :=
	Module[{branchPairEvents, allEventsList},
		branchPairEvents = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "BranchPairEventsList", "GivePredecessors" -> False, "IncludeStepNumber" -> OptionValue[
			"IncludeStepNumber"], "IncludeStateID" -> OptionValue["IncludeStateID"]];
		allEventsList =
			If[
				OptionValue["IncludeFullBranchialSpace"],
				Catenate[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
					 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
					 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
					 stepCount, "AllEventsList", options]],
				VertexList[Graph[UndirectedEdge @@@ branchPairEvents]]
			];
		Graph[allEventsList, UndirectedEdge @@@ branchPairEvents, VertexShapeFunction -> getEventRenderingFunction[systemType,
			 OptionValue["EventRenderingFunction"], OptionValue["VertexSizeMultiplier"]], EdgeStyle -> Hue[0.89, 0.97, 0.71], FilterRules[
			{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "AllEventsBranchialGraphStructure", options : OptionsPattern[]] :=
	Module[{allEventsBranchialGraph},
		allEventsBranchialGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "AllEventsBranchialGraph", options];
		Graph[allEventsBranchialGraph, VertexStyle -> Directive[Opacity[0.7], Hue[0.11, 1, 0.97]], VertexShapeFunction -> 
			((# -> Automatic)& /@ VertexList[allEventsBranchialGraph]), FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionEventBranchialGraph", options : OptionsPattern[]] :=
	Module[{newEvolutionBranchPairEvents, allEventsList},
		newEvolutionBranchPairEvents = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "NewEvolutionBranchPairEventsList", "GivePredecessors" -> False, "IncludeStepNumber"
			 -> OptionValue["IncludeStepNumber"], "IncludeStateID" -> OptionValue["IncludeStateID"]];
		allEventsList =
			If[
				OptionValue["IncludeFullBranchialSpace"],
				Last[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
					 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
					 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
					 stepCount, "AllEventsList", options]],
				VertexList[Graph[UndirectedEdge @@@ newEvolutionBranchPairEvents]]
			];
		Graph[allEventsList, UndirectedEdge @@@ newEvolutionBranchPairEvents, VertexShapeFunction -> getEventRenderingFunction[
			systemType, OptionValue["EventRenderingFunction"], OptionValue["VertexSizeMultiplier"]], EdgeStyle -> Hue[0.89, 0.97,
			 0.71], FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionEventBranchialGraphStructure", options : OptionsPattern[]] :=
	Module[{evolutionEventsBranchialGraph},
		evolutionEventsBranchialGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionEventBranchialGraph", options];
		Graph[evolutionEventsBranchialGraph, VertexStyle -> Directive[Opacity[0.7], Hue[0.11, 1, 0.97]], VertexShapeFunction
			 -> ((# -> Automatic)& /@ VertexList[evolutionEventsBranchialGraph]), FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "AllEventsEvolutionBranchialGraph", options : OptionsPattern[]] :=
	Module[{evolutionBranchPairEvents, allEventsList},
		evolutionBranchPairEvents = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionBranchPairEventsList", "GivePredecessors" -> False, "IncludeStepNumber" 
			-> OptionValue["IncludeStepNumber"], "IncludeStateID" -> OptionValue["IncludeStateID"]];
		allEventsList =
			If[
				OptionValue["IncludeFullBranchialSpace"],
				Catenate[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
					 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
					 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
					 stepCount, "AllEventsList", "IncludeStepNumber" -> True, "IncludeStateID" -> OptionValue["IncludeStateID"]]],
				VertexList[Graph[UndirectedEdge @@@ evolutionBranchPairEvents]]
			];
		Graph[allEventsList, UndirectedEdge @@@ evolutionBranchPairEvents, VertexShapeFunction -> getEventRenderingFunction[
			systemType, OptionValue["EventRenderingFunction"], OptionValue["VertexSizeMultiplier"]], EdgeStyle -> Hue[0.89, 0.97,
			 0.71], FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "AllEventsEvolutionBranchialGraphStructure", options : OptionsPattern[
	]] :=
	Module[{allEventsEvolutionBranchialGraph},
		allEventsEvolutionBranchialGraph = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "AllEventsEvolutionBranchialGraph", options];
		Graph[allEventsEvolutionBranchialGraph, VertexShapeFunction -> ((# -> Automatic)& /@ VertexList[allEventsEvolutionBranchialGraph
			]), VertexStyle -> Directive[Opacity[0.7], Hue[0.11, 1, 0.97]], FilterRules[{options}, Options[Graph]]]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "BranchPairResolutionsList", options : OptionsPattern[]] :=
	Module[{branchPairsList, newBranchPairsList, combinedBranchPairsList, finalStatesGraph, terminalStates},
		branchPairsList =
			If[
				stepCount > 0,
				MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
					 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
					 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
					 stepCount - 1, "BranchPairsList", options],
				{}
			];
		newBranchPairsList = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "NewBranchPairsList", options];
		combinedBranchPairsList = Union[branchPairsList, newBranchPairsList];
		finalStatesGraph = SimpleGraph[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "StatesGraph", options]];
		terminalStates = VertexList[finalStatesGraph][[Position[VertexOutDegree[finalStatesGraph], 0][[All, 1]]]];
		With[{terminalState = #},
				If[
					OptionValue["GivePredecessors"],
					(branchPairsList = Select[branchPairsList, !SubsetQ[VertexOutComponent[ReverseGraph[finalStatesGraph], terminalState
						], Last[#]]&]),
					(branchPairsList = Select[branchPairsList, !SubsetQ[VertexOutComponent[ReverseGraph[finalStatesGraph], terminalState
						], #]&])
				]
			]& /@ terminalStates;
		<|
			"Resolved" ->
				If[
					OptionValue["GiveResolvents"],
					(# -> getBranchPairResolvent[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" ->
						 stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
						 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
						|>, #, stepCount])& /@ Complement[combinedBranchPairsList, Union[branchPairsList, newBranchPairsList]],
					Complement[combinedBranchPairsList, Union[branchPairsList, newBranchPairsList]]
				],
			"Unresolved" -> Union[branchPairsList, newBranchPairsList]
		|>
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionBranchPairResolutionsList", options : OptionsPattern[]] :=
	Module[{evolutionBranchPairsList, newEvolutionBranchPairsList, combinedEvolutionBranchPairsList, finalEvolutionGraph,
		 terminalStates},
		evolutionBranchPairsList =
			If[
				stepCount > 0,
				MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" -> stateEquivalenceFunction,
					 "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction, "EventApplicationFunction"
					 -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction|>, initialConditions,
					 stepCount - 1, "EvolutionBranchPairsList", options],
				{}
			];
		newEvolutionBranchPairsList = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "NewEvolutionBranchPairsList", options];
		combinedEvolutionBranchPairsList = Union[evolutionBranchPairsList, newEvolutionBranchPairsList];
		finalEvolutionGraph = SimpleGraph[MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionGraph", options]];
		terminalStates = VertexList[finalEvolutionGraph][[Position[VertexOutDegree[finalEvolutionGraph], 0][[All, 1]]]];
		With[{terminalState = #},
				If[
					OptionValue["GivePredecessors"],
					(evolutionBranchPairsList = Select[evolutionBranchPairsList, !SubsetQ[VertexOutComponent[ReverseGraph[finalEvolutionGraph
						], terminalState], Last[#]]&]),
					(evolutionBranchPairsList = Select[evolutionBranchPairsList, !SubsetQ[VertexOutComponent[ReverseGraph[finalEvolutionGraph
						], terminalState], #]&])
				]
			]& /@ terminalStates;
		<|
			"Resolved" ->
				If[
					OptionValue["GiveResolvents"],
					(# -> getBranchPairResolvent[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction" ->
						 stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
						 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
						|>, #, stepCount])& /@ Complement[combinedEvolutionBranchPairsList, Union[evolutionBranchPairsList, newEvolutionBranchPairsList
						]],
					Complement[combinedEvolutionBranchPairsList, Union[evolutionBranchPairsList, newEvolutionBranchPairsList]]
				],
			"Unresolved" -> Union[evolutionBranchPairsList, newEvolutionBranchPairsList]
		|>
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "CausalInvariantQ", options : OptionsPattern[]] :=
	Module[{unresolvedBranchPairsList, resolvedBranchPairsList},
		unresolvedBranchPairsList = Sort /@ MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, Ceiling[stepCount / 2], "BranchPairResolutionsList", options]["Unresolved"];
		resolvedBranchPairsList = Sort /@ MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "BranchPairResolutionsList", options]["Resolved"];
		Length[Complement[unresolvedBranchPairsList, resolvedBranchPairsList]] == 0
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionCausalInvariantQ", options : OptionsPattern[]] :=
	Module[{unresolvedEvolutionBranchPairsList, resolvedEvolutionBranchPairsList},
		unresolvedEvolutionBranchPairsList = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, Ceiling[stepCount / 2], "EvolutionBranchPairResolutionsList", options]["Unresolved"];
		resolvedEvolutionBranchPairsList = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionBranchPairResolutionsList", options]["Resolved"];
		Length[Complement[unresolvedEvolutionBranchPairsList, resolvedEvolutionBranchPairsList]] == 0
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "KnuthBendixCompletion", options : OptionsPattern[]] :=
	Module[{unresolvedBranchPairsList},
		unresolvedBranchPairsList = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "BranchPairResolutionsList", options]["Unresolved"];
		Catenate[{First[#] -> Last[#], Last[#] -> First[#]}& /@ unresolvedBranchPairsList]
	]



MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction_, "StateEquivalenceFunction" -> stateEquivalenceFunction_,
	 "StateEventFunction" -> stateEventFunction_, "EventDecompositionFunction" -> eventDecompositionFunction_, "EventApplicationFunction"
	 -> eventApplicationFunction_, "SystemType" -> systemType_String, "EventSelectionFunction" -> eventSelectionFunction_
	|>, initialConditions_List, stepCount_Integer, "EvolutionKnuthBendixCompletion", options : OptionsPattern[]] :=
	Module[{unresolvedEvolutionBranchPairsList},
		unresolvedEvolutionBranchPairsList = MultiwaySystem[<|"StateEvolutionFunction" -> stateEvolutionFunction, "StateEquivalenceFunction"
			 -> stateEquivalenceFunction, "StateEventFunction" -> stateEventFunction, "EventDecompositionFunction" -> eventDecompositionFunction,
			 "EventApplicationFunction" -> eventApplicationFunction, "SystemType" -> systemType, "EventSelectionFunction" -> eventSelectionFunction
			|>, initialConditions, stepCount, "EvolutionBranchPairResolutionsList", options]["Unresolved"];
		Catenate[{Last[First[#]] -> Last[Last[#]], Last[Last[#]] -> Last[First[#]]}& /@ unresolvedEvolutionBranchPairsList
			]
	]
