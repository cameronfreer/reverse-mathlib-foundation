/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge

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
listed dependency in its transitive constant closure. -/
def gates : List (Name × List Name) :=
  [(``RMFoundationBridge.rca0_not_semantically_implies_wkl,
    [``RMFoundationBridge.forward_adequacy,
     ``RMFoundationBridge.models_wklSentence_iff,
     ``ReverseMathlib.Omega.not_weakKonigAt_recursivePart]),
   (``RMFoundationBridge.rca0_not_derives_wkl,
    [``RMFoundationBridge.soundness,
     ``RMFoundationBridge.forward_adequacy,
     ``RMFoundationBridge.models_wklSentence_iff,
     ``ReverseMathlib.Omega.not_weakKonigAt_recursivePart])]

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
      if (`RMFoundationBridge).isPrefixOf (moduleNames.getD idx.toNat .anonymous) then
        let axs ← collectAxioms name
        for a in axs do
          unless allowedAxioms.contains a do
            throwError "axiom audit (sweep): {name} depends on disallowed axiom {a}"
        swept := swept + 1
  for (headline, requiredDeps) in gates do
    let axs ← collectAxioms headline
    for a in axs do
      unless allowedAxioms.contains a do
        throwError "axiom audit: {headline} depends on disallowed axiom {a}"
    let reached := closure env [headline] {}
    for d in requiredDeps do
      unless reached.contains d do
        throwError "dependency gate: {headline} does not reach {d}"
  IO.println s!"bridge audit: swept {swept} declaration(s), axioms clean; all \
{gates.length} headline(s) reach their required dependencies"
