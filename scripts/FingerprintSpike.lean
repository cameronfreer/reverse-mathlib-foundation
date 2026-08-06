/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge

/-!
# Fingerprint spike: the `lean-interface-expr/1` encoder and its regression fixtures

Run via `lake env lean scripts/FingerprintSpike.lean`; any failed fixture is a hard
error. This spikes the canonical interface encoding of `docs/evidence-schema.md`
**before** the emitter or importer lands:

* `Expr` constructors encoded directly — no pretty-printing, no `Expr.toString`;
* `mdata` stripped; binder names ignored, binder info kept; universe parameters
  normalized by position; explicit name/literal escaping; free variables and
  metavariables are hard errors;
* payloads: type always; bodies for definitions; constructor types for inductives
  (constructors/recursors attributed to their inductive); theorem **statements only**;
* closure: recursive semantic-interface closure over owned dependencies;
* manifest comparison: exact equality of the covered-name set and every payload.

Pinned fixtures (schema §Fingerprints): semantic body change → mismatch; proof-body
change → equal; binder-name-only change → equal; metadata-only change → equal;
missing/extra covered declaration → hard failure. (Fixture 1 — checked vs. docs-only
revision — is established at the git layer: the two revisions have no `.lean` diff,
hence identical environments.)
-/

open Lean

namespace FingerprintSpike

def escapeStr (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (if c = '\\' then "\\\\" else if c = '"' then "\\\"" else c.toString)) ""

def encodeName : Name → String
  | .anonymous => "_"
  | .str p s => encodeName p ++ ".\"" ++ escapeStr s ++ "\""
  | .num p n => encodeName p ++ ".#" ++ toString n

def levelParamIdx (ps : List Name) (n : Name) : Except String Nat :=
  match ps.idxOf? n with
  | some i => .ok i
  | none => .error s!"unbound universe parameter {n}"

partial def encodeLevel (ps : List Name) : Level → Except String String
  | .zero => .ok "0"
  | .succ l => do return s!"(s {← encodeLevel ps l})"
  | .max a b => do return s!"(max {← encodeLevel ps a} {← encodeLevel ps b})"
  | .imax a b => do return s!"(imax {← encodeLevel ps a} {← encodeLevel ps b})"
  | .param n => do return s!"(u {← levelParamIdx ps n})"
  | .mvar _ => .error "level metavariable"

def biTag : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "si"
  | .instImplicit => "ii"

partial def encodeExpr (ps : List Name) : Expr → Except String String
  | .bvar i => .ok s!"(b {i})"
  | .fvar _ => .error "free variable in closed declaration"
  | .mvar _ => .error "metavariable in closed declaration"
  | .sort u => do return s!"(S {← encodeLevel ps u})"
  | .const n ls => do
      let ls' ← ls.mapM (encodeLevel ps)
      return s!"(c {encodeName n}{String.join (ls'.map (" " ++ ·))})"
  | .app f a => do return s!"(a {← encodeExpr ps f} {← encodeExpr ps a})"
  | .lam _ t b bi => do
      return s!"(l {biTag bi} {← encodeExpr ps t} {← encodeExpr ps b})"
  | .forallE _ t b bi => do
      return s!"(P {biTag bi} {← encodeExpr ps t} {← encodeExpr ps b})"
  | .letE _ t v b _ => do
      return s!"(L {← encodeExpr ps t} {← encodeExpr ps v} {← encodeExpr ps b})"
  | .lit (.natVal n) => .ok s!"(n {n})"
  | .lit (.strVal s) => .ok s!"(str \"{escapeStr s}\")"
  | .mdata _ e => encodeExpr ps e
  | .proj n i e => do return s!"(pr {encodeName n} {i} {← encodeExpr ps e})"

/-- Constructors and recursors are attributed to their inductive. -/
def canonicalName (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | some (.ctorInfo v) => v.induct
  | some (.recInfo v) => v.all.headD n
  | _ => n

/-- The canonical payload, rendered with a caller-chosen display name (the manifest
uses the real name; fixtures use a placeholder to compare across differently named
twins). -/
def declPayloadAs (env : Environment) (n : Name) (display : Name) :
    Except String String := do
  let some ci := env.find? n | .error s!"unknown declaration {n}"
  let ps := ci.levelParams
  let ty ← encodeExpr ps ci.type
  let head := s!"{encodeName display} {ps.length} {ty}"
  match ci with
  | .defnInfo v => do return s!"(def {head} {← encodeExpr ps v.value})"
  | .thmInfo _ => return s!"(thm {head})"
  | .axiomInfo _ => return s!"(ax {head})"
  | .opaqueInfo _ => return s!"(op {head})"
  | .quotInfo _ => return s!"(quot {head})"
  | .inductInfo v => do
      let ctors ← v.ctors.mapM fun c => do
        let some (.ctorInfo cv) := env.find? c | throw s!"missing constructor {c}"
        return s!"({encodeName c} {← encodeExpr cv.levelParams cv.type})"
      return s!"(ind {head} (ctors{String.join (ctors.map (" " ++ ·))}))"
  | .ctorInfo _ => .error s!"constructor {n} must be canonicalized to its inductive"
  | .recInfo _ => .error s!"recursor {n} must be canonicalized to its inductive"

def declPayload (env : Environment) (n : Name) : Except String String :=
  declPayloadAs env n n

/-- The interface dependencies: constants of the included components only — never
theorem proof bodies. -/
def interfaceDeps (env : Environment) (n : Name) : Except String (Array Name) := do
  let some ci := env.find? n | .error s!"unknown declaration {n}"
  match ci with
  | .defnInfo v => return v.type.getUsedConstants ++ v.value.getUsedConstants
  | .inductInfo v => do
      let mut acc := ci.type.getUsedConstants
      for c in v.ctors do
        let some (.ctorInfo cv) := env.find? c | throw s!"missing constructor {c}"
        acc := acc ++ cv.type.getUsedConstants
      return acc
  | _ => return ci.type.getUsedConstants

/-- The recursive semantic-interface closure over `owned` declarations. -/
partial def coveredSet (env : Environment) (owned : Name → Bool) :
    List Name → NameSet → Except String NameSet
  | [], seen => .ok seen
  | n :: rest, seen => do
    let n := canonicalName env n
    if seen.contains n then coveredSet env owned rest seen
    else if !owned n then coveredSet env owned rest seen
    else do
      let deps ← interfaceDeps env n
      coveredSet env owned (deps.toList ++ rest) (seen.insert n)

/-- The manifest: sorted (name, payload) pairs over the covered set. -/
def manifest (env : Environment) (owned : Name → Bool) (roots : List Name) :
    Except String (List (Name × String)) := do
  let seen ← coveredSet env owned roots {}
  let names := seen.toList.mergeSort (fun a b => Name.lt a b)
  names.mapM fun n => do return (n, ← declPayload env n)

/-- Exact comparison: same covered-name set, every payload equal. -/
def compareManifests (a b : List (Name × String)) : Except String Unit := do
  if a.map (·.1) ≠ b.map (·.1) then
    .error "covered-name sets differ"
  for ((n, pa), (_, pb)) in a.zip b do
    if pa ≠ pb then .error s!"payload mismatch at {n}"
  return ()

/-! ### Fixtures -/

/-- Root with a dependency chain. -/
def fixDeep (n : ℕ) : Prop := n ∈ ReverseMathlib.Omega.decodeSeq n

def fixA : ℕ → Prop := fun n => n + 0 = n
/-- Binder-name-only twin of `fixA`. -/
def fixA' : ℕ → Prop := fun m => m + 0 = m
/-- Semantic body change from `fixA`. -/
def fixB : ℕ → Prop := fun n => n + 1 = n

theorem fixT1 : 0 + 0 = 0 := rfl
/-- Proof-body twin of `fixT1`. -/
theorem fixT2 : 0 + 0 = 0 := by simp

end FingerprintSpike

open FingerprintSpike in
#eval show Lean.CoreM Unit from do
  let env ← getEnv
  let ph := `FINGERPRINT_PLACEHOLDER
  -- Fixture 4a: binder-name-only change → equal payloads.
  let pA ← IO.ofExcept (declPayloadAs env ``fixA ph)
  let pA' ← IO.ofExcept (declPayloadAs env ``fixA' ph)
  unless pA == pA' do throwError "fixture 4a failed: binder rename changed the payload"
  -- Fixture 2: semantic body change → mismatch.
  let pB ← IO.ofExcept (declPayloadAs env ``fixB ph)
  if pA == pB then throwError "fixture 2 failed: body change not detected"
  -- Fixture 3: proof-body change → equal payloads (statements only).
  let pT1 ← IO.ofExcept (declPayloadAs env ``fixT1 ph)
  let pT2 ← IO.ofExcept (declPayloadAs env ``fixT2 ph)
  unless pT1 == pT2 do throwError "fixture 3 failed: proof body leaked into payload"
  -- Fixture 4b: metadata-only change → equal encodings.
  let eNat := Lean.mkConst ``Nat
  let eMd := Lean.Expr.mdata {} eNat
  let c1 ← IO.ofExcept (encodeExpr [] eNat)
  let c2 ← IO.ofExcept (encodeExpr [] eMd)
  unless c1 == c2 do throwError "fixture 4b failed: mdata not stripped"
  -- Fixture 5: missing or extra covered declaration → hard failure.
  let ownedFix : Lean.Name → Bool := fun n => (`FingerprintSpike).isPrefixOf n
  let m1 ← IO.ofExcept (manifest env ownedFix [``fixA, ``fixB])
  let m2 ← IO.ofExcept (manifest env ownedFix [``fixA])
  match compareManifests m1 m2 with
  | .ok _ => throwError "fixture 5 failed: under-coverage accepted"
  | .error _ => pure ()
  match compareManifests m2 m1 with
  | .ok _ => throwError "fixture 5 failed: over-coverage accepted"
  | .error _ => pure ()
  -- Self-comparison sanity.
  IO.ofExcept (compareManifests m1 m1)
  -- Real-root closure visibility: the adapter/context roots reach the deep frozen
  -- vocabulary; print the covered set and total payload size.
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
  IO.println s!"covered: {m.map (·.1)}"
