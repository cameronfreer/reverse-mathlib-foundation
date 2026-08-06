/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge
import RMFoundationBridgeMeta

/-!
# Conformance fixtures for the `lean-interface-expr/1` encoder

Run via `lake env lean scripts/FingerprintSpike.lean`; any failed fixture is a hard
error, and any change to `RMFoundationBridgeMeta.InterfaceEncoder` must keep this
green. Pinned fixtures (`docs/evidence-schema.md` §Fingerprints):

* semantic definition-body change → mismatch;
* theorem proof-body change → equal (statements only);
* binder-name-only change → equal; metadata-only change → equal;
* **opaque body change → mismatch** (owned opaques carry meaning);
* **mutual recursor → covers every inductive of the group**;
* missing or extra covered declaration → hard failure.

(The checked-vs-docs-only-revision fixture is established at the git layer: the two
revisions have no `.lean` diff, hence identical environments.)
-/

open Lean RMFoundationBridgeMeta

namespace FingerprintSpike

def fixA : ℕ → Prop := fun n => n + 0 = n
/-- Binder-name-only twin of `fixA`. -/
def fixA' : ℕ → Prop := fun m => m + 0 = m
/-- Semantic body change from `fixA`. -/
def fixB : ℕ → Prop := fun n => n + 1 = n

theorem fixT1 : 0 + 0 = 0 := rfl
/-- Proof-body twin of `fixT1`. -/
theorem fixT2 : 0 + 0 = 0 := by simp

opaque fixO1 : ℕ := 1
/-- Opaque-body twin of `fixO1` with a different value. -/
opaque fixO2 : ℕ := 2

mutual
  inductive MutA : Type where
    | base : MutA
    | ofB : MutB → MutA
  inductive MutB : Type where
    | ofA : MutA → MutB
end

end FingerprintSpike

open FingerprintSpike in
#eval show Lean.CoreM Unit from do
  let env ← getEnv
  let ph := `FINGERPRINT_PLACEHOLDER
  -- binder-name-only change → equal payloads
  let pA ← IO.ofExcept (declPayloadAs env ``fixA ph)
  let pA' ← IO.ofExcept (declPayloadAs env ``fixA' ph)
  unless pA == pA' do throwError "fixture failed: binder rename changed the payload"
  -- semantic body change → mismatch
  let pB ← IO.ofExcept (declPayloadAs env ``fixB ph)
  if pA == pB then throwError "fixture failed: body change not detected"
  -- proof-body change → equal payloads
  let pT1 ← IO.ofExcept (declPayloadAs env ``fixT1 ph)
  let pT2 ← IO.ofExcept (declPayloadAs env ``fixT2 ph)
  unless pT1 == pT2 do throwError "fixture failed: proof body leaked into payload"
  -- opaque body change → mismatch
  let pO1 ← IO.ofExcept (declPayloadAs env ``fixO1 ph)
  let pO2 ← IO.ofExcept (declPayloadAs env ``fixO2 ph)
  if pO1 == pO2 then throwError "fixture failed: opaque body change not detected"
  -- metadata-only change → equal encodings
  let eNat := Lean.mkConst ``Nat
  let c1 ← IO.ofExcept (encodeExpr [] eNat)
  let c2 ← IO.ofExcept (encodeExpr [] (Lean.Expr.mdata {} eNat))
  unless c1 == c2 do throwError "fixture failed: mdata not stripped"
  -- mutual recursor → every inductive of the group is covered
  let ownedFix : Lean.Name → Bool := fun n => (`FingerprintSpike).isPrefixOf n
  let mMut ← IO.ofExcept (manifest env ownedFix [``FingerprintSpike.MutA.rec])
  unless mMut.any (·.1 == ``FingerprintSpike.MutA) do
    throwError "fixture failed: mutual recursor missed MutA"
  unless mMut.any (·.1 == ``FingerprintSpike.MutB) do
    throwError "fixture failed: mutual recursor missed MutB"
  -- missing or extra covered declaration → hard failure, both directions
  let m1 ← IO.ofExcept (manifest env ownedFix [``fixA, ``fixB])
  let m2 ← IO.ofExcept (manifest env ownedFix [``fixA])
  if (compareManifests m1 m2).isOk then
    throwError "fixture failed: under-coverage accepted"
  if (compareManifests m2 m1).isOk then
    throwError "fixture failed: over-coverage accepted"
  IO.ofExcept (compareManifests m1 m1)
  -- real-root closure visibility: the adapter/context roots reach the deep frozen
  -- vocabulary
  let moduleNames := env.allImportedModuleNames
  let rmOwned : Lean.Name → Bool := fun n =>
    match env.getModuleIdxFor? n with
    | some idx =>
        (`ReverseMathlib).isPrefixOf (moduleNames.getD idx.toNat .anonymous)
    | none => false
  let roots := [``ReverseMathlib.Omega.WeakKonigAt, ``ReverseMathlib.Omega.EFILCAt,
    ``ReverseMathlib.Omega.CountableHallAt, ``ReverseMathlib.Omega.IsTuringIdeal]
  let m ← IO.ofExcept (manifest env rmOwned roots)
  let total := m.foldl (fun acc (_, p) => acc + p.length) 0
  let mustReach := [``ReverseMathlib.Omega.InternalFunction,
    ``ReverseMathlib.Omega.seqCode, ``ReverseMathlib.Omega.decodeSeq,
    ``ReverseMathlib.Omega.IsBinaryPathThrough,
    ``ReverseMathlib.Omega.InternalHallFamily]
  for d in mustReach do
    unless m.any (·.1 == d) do
      throwError "real-root closure failed to reach {d}"
  IO.println s!"fingerprint spike: all fixtures pass; real-root closure covers \
{m.length} declaration(s), {total} payload bytes"
