/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.Delta0Recursive
import RMFoundationBridge.Delta0Agreement

/-!
# F1 item 5, third layer: the Σ⁰₁ stage predicate

**The composition point**: this module is the first consumer of both
`recursiveIn_bevalNat` (relative computability) and `beval_agrees` (semantic
correctness), which meet here for the first time.

**No nested partial search.** The witness tuple for the whole strict existential prefix
is a **single** search variable, packed by nested pairing (the arity is implicit in the
pairing depth rather than a separate flattening — this avoids non-definitional index
casts, and preserves the operative invariant exactly): every intermediate predicate in
the derivation-directed construction is **total**, witnesses decode
total-with-fallback (`Nat.unpair` is total; the environment code decodes with `getD`),
and `bevalNat` runs **once**, at the Δ⁰₀ leaf, under the correctly ordered extended
environment (each existential step conses its witness onto the environment code —
slot `#0`, the de Bruijn convention verified by `ofFn_cons`). `beval_agrees` enters only
for semantic correctness.

The deliverable is the **total** stage predicate with its relative computability and its
specification — dovetail-ready for the later Δ⁰₁ decision, whose equivalence premise
will prove termination and correctness but never enters an executable stage predicate.
No `Part`-valued semidecider exists in this module.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

open Classical in
/-- The Δ⁰₀ leaf, bridged: `bevalNat` at a coded environment equals Tarski truth — the
composition of the executable normalization with the agreement theorem. -/
theorem bevalNat_ofFn_eq_one_iff {N n : ℕ} (A : Fin N → Set ℕ) (𝕊 : Set (Set ℕ))
    (c : Delta0Code N n) (e : Fin n → ℕ) :
    bevalNat (finiteParamOracle A) c (seqCode (List.ofFn e)) = 1 ↔
      EvalN 𝕊 c.toFormula A e := by
  rw [bevalNat, decodeSeq_seqCode,
    show oracleAnswers (finiteParamOracle A) = membershipOracle A from rfl,
    beval_agrees A 𝕊 c e]
  by_cases h : EvalN 𝕊 c.toFormula A e <;> simp [h]

/-- **Every strict Σ⁰₁ formula has a total, oracle-recursive stage predicate**: hits at
some witness code characterize Tarski truth over every environment. Built by induction
on the derivation: the Δ⁰₀ base is one `bevalNat` run; each existential step repacks the
stage predicate totally — the new witness code pairs the fresh witness with the inner
code, and the fresh witness is consed onto the environment code at de Bruijn slot `0`.
The equivalence premise of the future Δ⁰₁ decision never appears here. -/
theorem IsSigma01.exists_stage {N : ℕ} (A : Fin N → Set ℕ) (𝕊 : Set (Set ℕ)) :
    ∀ {n : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n},
      IsSigma01 φ →
      ∃ R : ℕ → ℕ,
        (Nat.RecursiveIn {charFn (finiteParamOracle A)} fun p => Part.some (R p)) ∧
        ∀ e : Fin n → ℕ,
          (EvalN 𝕊 φ A e ↔
            ∃ wc : ℕ, R (Nat.pair (seqCode (List.ofFn e)) wc) = 1) := by
  intro n φ h
  induction h with
  | @delta0 n' φ' h0 =>
      obtain ⟨c, rfl⟩ := h0.exists_code
      refine ⟨fun p => bevalNat (finiteParamOracle A) c p.unpair.1,
        (recursiveIn_comp_primrec (recursiveIn_bevalNat _ c)
          (Primrec.fst.comp Primrec.unpair)).of_eq fun p => rfl,
        fun e => ?_⟩
      constructor
      · intro he
        refine ⟨0, ?_⟩
        simp only [Nat.unpair_pair]
        exact (bevalNat_ofFn_eq_one_iff A 𝕊 c e).mpr he
      · rintro ⟨wc, hwc⟩
        simp only [Nat.unpair_pair] at hwc
        exact (bevalNat_ofFn_eq_one_iff A 𝕊 c e).mp hwc
  | @exs n' φ' _ ih =>
      obtain ⟨R, hR, hspec⟩ := ih
      refine ⟨fun p => R (Nat.pair
          (seqCode (p.unpair.2.unpair.1 :: decodeSeq p.unpair.1))
          p.unpair.2.unpair.2), ?_, fun e => ?_⟩
      · refine recursiveIn_comp_primrec hR ?_
        exact Primrec₂.comp (f := Nat.pair) Primrec₂.natPair
          (Primrec₂.comp (f := fun x ec => seqCode (x :: decodeSeq ec)) primrec_consCode
            (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
            (Primrec.fst.comp Primrec.unpair))
          (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      · rw [show (EvalN 𝕊 (.exs₁ φ') A e) =
            (∃ x : ℕ, EvalN 𝕊 φ' A (x :> e)) from rfl]
        constructor
        · rintro ⟨x, hx⟩
          obtain ⟨wc, hwc⟩ := (hspec (x :> e)).mp hx
          refine ⟨Nat.pair x wc, ?_⟩
          simp only [Nat.unpair_pair, decodeSeq_seqCode, ← ofFn_cons]
          exact hwc
        · rintro ⟨wc, hwc⟩
          simp only [Nat.unpair_pair, decodeSeq_seqCode, ← ofFn_cons] at hwc
          exact ⟨wc.unpair.1, (hspec (wc.unpair.1 :> e)).mpr ⟨wc.unpair.2, hwc⟩⟩

end RMFoundationBridge
