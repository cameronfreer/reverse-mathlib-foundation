/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge
import RMFoundationBridgeMeta

/-!
# Bridge audit: axioms and headline dependencies

Run via `lake env lean scripts/Audit.lean`; any failure is a hard error.

* **Axiom audit**: every declaration owned by an `RMFoundationBridge` module — including
  private and compiler-generated auxiliaries — depends only on the standard axioms.
* **Dependency gate**: the headline `rca0_not_semantically_implies_wkl` must reach, in
  its transitive constant closure (types and values), all three load-bearing inputs:
  context adequacy (`forward_adequacy`), the unconditional statement adapter
  (`models_wklSentence_iff`), and the frozen Kleene-tree separation
  (`not_weakKonigAt_recursivePart`). A refactor that severs any of these — e.g. a
  restatement that no longer routes through the adapter — fails the gate.
-/

open Lean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Headlines with their load-bearing dependency gates: each headline must reach every
`required` dependency in its transitive constant closure and none of the `forbidden`
ones. -/
structure Gate where
  headline : Name
  required : List Name
  forbidden : List Name := []

/-- The derived ŴKL → Hall composition must stay out of every export leaf. -/
def derivedOnly : List Name :=
  [``RMFoundationBridge.models_hallSentence_of_models_wklSentence]

/-- Foundation's formula-witness second-order existential rule (comprehension built
into the logic) must stay out of the standard-calculus route: its exclusion is
load-bearing, so it is gate-checked, not merely visible in the inductive
definition. -/
def formulaWitness : List Name :=
  [``LO.SecondOrder.Derivation.exs₂]

def gates : List Gate :=
  [{ headline := ``RMFoundationBridge.rca0_not_semantically_implies_wkl
     required := [``RMFoundationBridge.forward_adequacy,
       ``RMFoundationBridge.models_wklSentence_iff,
       ``ReverseMathlib.Omega.not_weakKonigAt_recursivePart] },
   { headline := ``RMFoundationBridge.rca0_not_derives_wkl
     required := [``RMFoundationBridge.soundness,
       ``RMFoundationBridge.forward_adequacy,
       ``RMFoundationBridge.models_wklSentence_iff,
       ``ReverseMathlib.Omega.not_weakKonigAt_recursivePart] },
   { headline := ``RMFoundationBridge.rca0_not_semantically_implies_efilc
     required := [``RMFoundationBridge.forward_adequacy,
       ``RMFoundationBridge.models_efilcSentence_iff,
       ``RMFoundationBridge.models_wklSentence_iff,
       ``ReverseMathlib.Omega.efilcAt_of_weakKonigAt,
       ``ReverseMathlib.Omega.not_weakKonigAt_recursivePart] },
   -- The export surface: each record reaches exactly its named theorem, and no export
   -- leaf reaches the derived composition.
   { headline := ``RMFoundationBridge.rca0RealizationExport
     required := [``RMFoundationBridge.forward_adequacy]
     forbidden := derivedOnly },
   { headline := ``RMFoundationBridge.wklAdapterExport
     required := [``RMFoundationBridge.models_wklSentence_iff]
     forbidden := derivedOnly },
   { headline := ``RMFoundationBridge.efilcAdapterExport
     required := [``RMFoundationBridge.models_efilcSentence_iff]
     forbidden := derivedOnly },
   { headline := ``RMFoundationBridge.hallAdapterExport
     required := [``RMFoundationBridge.models_hallSentence_iff]
     forbidden := derivedOnly },
   { headline := ``RMFoundationBridge.bridgeCalculusExport
     required := [``RMFoundationBridge.soundness]
     forbidden := derivedOnly },
   { headline := ``RMFoundationBridge.wklNonderivabilityExport
     required := [``RMFoundationBridge.rca0_not_derives_wkl,
       ``RMFoundationBridge.soundness]
     forbidden := derivedOnly },
   { headline := ``RMFoundationBridge.wklCountermodelExport
     required := [``RMFoundationBridge.rca0_not_semantically_implies_wkl]
     forbidden := derivedOnly },
   -- The pinned standard calculus: its own direct soundness, never through the
   -- Henkin-safe calculus's derivability (no record carries an embedding or licenses
   -- a derivability transfer between the calculi).
   { headline := ``RMFoundationBridge.rca0_not_stdLK_proves_wkl
     required := [``RMFoundationBridge.StdLK.soundness,
       ``RMFoundationBridge.forward_adequacy,
       ``RMFoundationBridge.models_wklSentence_iff,
       ``ReverseMathlib.Omega.not_weakKonigAt_recursivePart]
     forbidden := formulaWitness },
   { headline := ``RMFoundationBridge.stdCalculusExport
     required := [``RMFoundationBridge.StdLK.soundness]
     forbidden := derivedOnly ++ formulaWitness },
   { headline := ``RMFoundationBridge.calculusComparisonExport
     required := [``RMFoundationBridge.StdLK.soundness,
       ``RMFoundationBridge.soundness]
     forbidden := derivedOnly ++ formulaWitness },
   { headline := ``RMFoundationBridge.wklStandardNonprovabilityExport
     required := [``RMFoundationBridge.rca0_not_stdLK_proves_wkl,
       ``RMFoundationBridge.StdLK.soundness]
     forbidden := derivedOnly ++ formulaWitness }]

/-- Transitive constant closure over types and values (fail-open on missing constants
is impossible: every used constant of an elaborated declaration is in the
environment). -/
partial def closure (env : Environment) : List Name → NameSet → NameSet
  | [], seen => seen
  | n :: rest, seen =>
    if seen.contains n then closure env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => closure env rest seen
      | some ci => closure env (ci.getUsedConstantsAsSet.toList ++ rest) seen

#eval show CoreM Unit from do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let mut swept := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := moduleNames.getD idx.toNat .anonymous
      if (`RMFoundationBridge).isPrefixOf mod ∨
          (`RMFoundationBridgeMeta).isPrefixOf mod then
        let axs ← collectAxioms name
        for a in axs do
          unless allowedAxioms.contains a do
            throwError "axiom audit (sweep): {name} depends on disallowed axiom {a}"
        swept := swept + 1
  for g in gates do
    let axs ← collectAxioms g.headline
    for a in axs do
      unless allowedAxioms.contains a do
        throwError "axiom audit: {g.headline} depends on disallowed axiom {a}"
    let reached := closure env [g.headline] {}
    for d in g.required do
      unless reached.contains d do
        throwError "dependency gate: {g.headline} does not reach {d}"
    for d in g.forbidden do
      if reached.contains d then
        throwError "dependency gate: {g.headline} must not reach {d}"
  IO.println s!"bridge audit: swept {swept} declaration(s), axioms clean; all \
{gates.length} headline(s) pass their dependency gates"
