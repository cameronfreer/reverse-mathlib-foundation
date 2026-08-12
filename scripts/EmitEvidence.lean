/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge
import RMFoundationBridgeMeta

/-!
# The backend-evidence emitter: `rmlib-bridge-evidence/2`

Run via `BRIDGE_EXPORT_REVISION=<40-hex> lake env lean scripts/EmitEvidence.lean`;
writes `evidence/rmlib-bridge-evidence.json` deterministically (fixed field order, no
timestamps). Contract: `docs/evidence-schema.md`.

* Only the bridge export revision is passed explicitly; the three dependency revisions
  are derived from `lake-manifest.json` and the toolchain from `lean-toolchain`. Every
  revision is validated as full lowercase 40-hex.
* Closed status, direction, calculus, and comparison tags are produced by
  pattern-matching the typed export-surface constructors — never `Repr`, never
  hand-written strings. Record ids, theorem names, and external keys are this emitter's
  explicit manifest.
* The fingerprint block is the `lean-interface-expr/1` manifest over the union of the
  per-record roots (the declared context predicate and capabilities, which the importer
  verifies against the resolved crosswalk anchors).
-/

open Lean RMFoundationBridge RMFoundationBridgeMeta

namespace EmitEvidence

def isHex40 (s : String) : Bool :=
  s.length == 40 && s.toList.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-! ### Closed tags, by constructor pattern-matching -/

def directionTag : RealizationDirection → String
  | .forward => "forward"

def realizationStatusTag : RealizationStatus → String
  | .realizationOnly => "realizationOnly"

def adapterStatusTag : AdapterStatus → String
  | .unconditional => "unconditional"

def calculusIdTag : BridgeCalculusId → String
  | .henkinSafeV1 => "henkinSafeV1"

def comparisonTag : CalculusComparisonStatus → String
  | .pending => "pending"

def scopeTag : SemanticScopeTag → String
  | .allModels => "allModels"

def modelClassTag : ModelClassTag → String
  | .foundationStruc2General => "foundationStruc2General"

/-! ### Revision provenance -/

/-- Manifest package names may be guillemet-quoted (`«reverse-mathlib»`); normalize
before matching. -/
def normalizePkgName (s : String) : String :=
  (s.replace "«" "").replace "»" ""

def manifestRev (packages : Array Json) (pkg : String) : Except String String := do
  for p in packages do
    if ((p.getObjValAs? String "name").toOption.map normalizePkgName) == some pkg then
      let some rev := (p.getObjValAs? String "rev").toOption
        | .error s!"manifest package {pkg} has no rev"
      unless isHex40 rev do .error s!"manifest rev for {pkg} is not lowercase 40-hex"
      return rev
  .error s!"package {pkg} not found in lake-manifest.json"

/-! ### The record manifest (ids, theorem names, external keys) -/

def adapterRecord (id theorem_ sentence capability variantKey : String)
    (export_ : String) (statusTag : String) : Json :=
  Json.mkObj
    [("kind", "statementAdapter"), ("id", id), ("status", "backendChecked"),
     ("export", export_), ("theorem", theorem_), ("sentence", sentence),
     ("capability", capability), ("variantKey", variantKey),
     ("adapterStatus", statusTag)]

end EmitEvidence

open EmitEvidence in
#eval show Lean.CoreM Unit from do
  let env ← getEnv
  -- revisions
  let some bridgeRev ← IO.getEnv "BRIDGE_EXPORT_REVISION"
    | throwError "BRIDGE_EXPORT_REVISION not set"
  unless isHex40 bridgeRev do
    throwError "BRIDGE_EXPORT_REVISION is not lowercase 40-hex"
  let manifestText ← IO.FS.readFile "lake-manifest.json"
  let manifestJson ← IO.ofExcept (Json.parse manifestText)
  let packages ← IO.ofExcept (manifestJson.getObjValAs? (Array Json) "packages")
  let rmRev ← IO.ofExcept (manifestRev packages "reverse-mathlib")
  let fdRev ← IO.ofExcept (manifestRev packages "Foundation")
  let mlRev ← IO.ofExcept (manifestRev packages "mathlib")
  let toolchain := (← IO.FS.readFile "lean-toolchain").trimAscii.toString
  -- fingerprints: the union manifest over the per-record roots
  let moduleNames := env.allImportedModuleNames
  let rmOwned : Lean.Name → Bool := fun n =>
    match env.getModuleIdxFor? n with
    | some idx =>
        (`ReverseMathlib).isPrefixOf (moduleNames.getD idx.toNat .anonymous)
    | none => false
  let roots := [``ReverseMathlib.Omega.IsTuringIdeal,
    ``ReverseMathlib.Omega.WeakKonigAt, ``ReverseMathlib.Omega.EFILCAt,
    ``ReverseMathlib.Omega.CountableHallAt]
  let fps ← IO.ofExcept (manifest env rmOwned roots)
  let fpJson := Json.arr <| fps.toArray.map fun (n, p) =>
    Json.mkObj [("name", toString n), ("canonicalInterface", p)]
  -- records: closed tags from the typed export surface; ids/names/keys are this manifest
  let records : Array Json := #[
    Json.mkObj
      [("kind", "contextRealization"), ("id", "realization.rca0.turingIdeal"),
       ("status", "backendChecked"),
       ("export", "RMFoundationBridge.rca0RealizationExport"),
       ("theorem", "RMFoundationBridge.forward_adequacy"),
       ("theory", "RMFoundationBridge.Rca0Theory"),
       ("contextKey", "rca0/turingIdealOmega"),
       ("context", "ReverseMathlib.Omega.IsTuringIdeal"),
       ("direction", directionTag rca0RealizationExport.direction),
       ("realizationStatus", realizationStatusTag rca0RealizationExport.status)],
    adapterRecord "adapter.wkl.binaryTree.foundationL2"
      "RMFoundationBridge.models_wklSentence_iff"
      "RMFoundationBridge.wklSentence" "ReverseMathlib.Omega.WeakKonigAt"
      "wkl/binaryTree.turingIdealOmega"
      "RMFoundationBridge.wklAdapterExport"
      (adapterStatusTag wklAdapterExport.status),
    adapterRecord "adapter.efilc.explicitSequential.enumeratedFibers.foundationL2"
      "RMFoundationBridge.models_efilcSentence_iff"
      "RMFoundationBridge.efilcSentence" "ReverseMathlib.Omega.EFILCAt"
      "efilc/explicitSequential.enumeratedFibers.turingIdealOmega"
      "RMFoundationBridge.efilcAdapterExport"
      (adapterStatusTag efilcAdapterExport.status),
    adapterRecord
      "adapter.countableHall.oneSidedInjective.enumeratedCandidates.foundationL2"
      "RMFoundationBridge.models_hallSentence_iff"
      "RMFoundationBridge.hallSentence" "ReverseMathlib.Omega.CountableHallAt"
      "countableHall/oneSidedInjective.enumeratedCandidates.turingIdealOmega"
      "RMFoundationBridge.hallAdapterExport"
      (adapterStatusTag hallAdapterExport.status),
    Json.mkObj
      [("kind", "calculusIdentity"), ("id", "calculus.henkinSafeV1"),
       ("status", "backendChecked"),
       ("export", "RMFoundationBridge.bridgeCalculusExport"),
       ("calculusId", calculusIdTag bridgeCalculusExport.id),
       ("derivability", "RMFoundationBridge.Derivable"),
       ("soundness", "RMFoundationBridge.soundness_sentence"),
       ("standardComparison", comparisonTag bridgeCalculusExport.comparison)],
    Json.mkObj
      [("kind", "calculusNonderivability"),
       ("id", "nonderivability.rca0.wkl.henkinSafeV1"),
       ("status", "backendChecked"),
       ("export", "RMFoundationBridge.wklNonderivabilityExport"),
       ("theorem", "RMFoundationBridge.rca0_not_derives_wkl"),
       ("calculusRecord", "calculus.henkinSafeV1"),
       ("sentenceAdapter", "adapter.wkl.binaryTree.foundationL2"),
       ("theory", "RMFoundationBridge.Rca0Theory"),
       ("sentence", "RMFoundationBridge.wklSentence")],
    Json.mkObj
      [("kind", "semanticCountermodel"),
       ("id", "countermodel.rca0.wkl.allModels"),
       ("status", "backendChecked"),
       ("export", "RMFoundationBridge.wklCountermodelExport"),
       ("theorem", "RMFoundationBridge.rca0_not_semantically_implies_wkl"),
       ("contextRealization", "realization.rca0.turingIdeal"),
       ("sentenceAdapter", "adapter.wkl.binaryTree.foundationL2"),
       ("theory", "RMFoundationBridge.Rca0Theory"),
       ("sentence", "RMFoundationBridge.wklSentence"),
       ("scope", scopeTag wklCountermodelExport.scope),
       ("modelClass", modelClassTag wklCountermodelExport.modelClass),
       ("witnessProvenance", "omegaStructure"),
       ("witnessBase", "ReverseMathlib.Omega.recursivePart")]]
  let out := Json.mkObj
    [("schema", "rmlib-bridge-evidence/2"),
     ("fingerprintSchema", "lean-interface-expr/1"),
     ("source", Json.mkObj
       [("repository", "cameronfreer/reverse-mathlib-foundation"),
        ("revision", bridgeRev),
        ("toolchain", toolchain),
        ("dependencies", Json.mkObj
          [("reverse-mathlib", rmRev), ("Foundation", fdRev),
           ("mathlib", mlRev)])]),
     ("namespace", "rmFoundationBridge"),
     ("checking", Json.mkObj
       [("mechanism", "leanKernel"),
        ("allowedAxioms",
          Json.arr #["Classical.choice", "Quot.sound", "propext"]),
        ("audit", "lake env lean scripts/Audit.lean")]),
     ("fingerprints", fpJson),
     ("records", Json.arr records)]
  IO.FS.createDirAll "evidence"
  IO.FS.writeFile "evidence/rmlib-bridge-evidence.json" (out.pretty ++ "\n")
  IO.println s!"emitted evidence/rmlib-bridge-evidence.json: {records.size} record(s), \
{fps.length} fingerprint(s); revision {bridgeRev}; reverse-mathlib {rmRev}"
