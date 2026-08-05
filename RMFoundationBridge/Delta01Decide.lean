/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.Sigma01Stage

/-!
# F1 item 5, fourth layer: the dovetailed Δ⁰₁ decision

**One stage variable, searched against the disjunction** of the positive stage predicate
and the negative costage predicate — never one unbounded `Part` search bound before the
other. Tie-breaking is executable and arbitrary, **positive-first**: the answer bit
consults only the positive predicate at the found stage.

The equivalence premise appears **only** in correctness, in exactly its three permitted
roles: it proves some stage eventually hits (termination of the single `rfind`), it
proves the selected side correct, and it rules out contradictory hits. It never enters
the executable stage predicate, which is total and built before the premise is used.

The conclusion is a set-level Turing reduction (`≤ᵀ`) to the finite-parameter oracle —
`IsTuringIdeal` and internal-set packaging remain absent until the internality layer.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-- **The dovetailed Δ⁰₁ decision**: given a strict Σ⁰₁ matrix and a strict Π⁰₁ matrix
that agree pointwise over the distinguished variable (the equivalence premise), the
defined set is Turing-reducible to the finite-parameter oracle. -/
theorem delta01_reducible {N k : ℕ} (A : Fin N → Set ℕ) (𝕊 : Set (Set ℕ))
    {φ ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (k + 1)}
    (hφ : IsSigma01 φ) (hψ : IsPi01 ψ) (e : Fin k → ℕ)
    (heq : ∀ x : ℕ, EvalN 𝕊 φ A (x :> e) ↔ EvalN 𝕊 ψ A (x :> e)) :
    {x : ℕ | EvalN 𝕊 φ A (x :> e)} ≤ᵀ finiteParamOracle A := by
  classical
  obtain ⟨Rσ, hRσ, hspecσ⟩ := IsSigma01.exists_stage A 𝕊 hφ
  obtain ⟨Rπ, hRπ, hspecπ⟩ := IsPi01.exists_costage A 𝕊 hψ
  set E0 : ℕ := seqCode (List.ofFn e) with hE0
  have env_eq : ∀ x : ℕ, seqCode (x :: decodeSeq E0) = seqCode (List.ofFn (x :> e)) := by
    intro x
    rw [hE0, decodeSeq_seqCode, ← ofFn_cons]
  have henv : Primrec fun x : ℕ => seqCode (x :: decodeSeq E0) :=
    Primrec₂.comp (f := fun x ec => seqCode (x :: decodeSeq ec)) primrec_consCode
      Primrec.id (Primrec.const E0)
  have hq : Primrec fun m : ℕ =>
      Nat.pair (seqCode (m.unpair.1 :: decodeSeq E0)) m.unpair.2 :=
    Primrec₂.comp (f := Nat.pair) Primrec₂.natPair
      (henv.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.snd.comp Primrec.unpair)
  have hRσq : Nat.RecursiveIn {charFn (finiteParamOracle A)} fun m =>
      Part.some (Rσ (Nat.pair (seqCode (m.unpair.1 :: decodeSeq E0)) m.unpair.2)) :=
    recursiveIn_comp_primrec hRσ hq
  have hRπq : Nat.RecursiveIn {charFn (finiteParamOracle A)} fun m =>
      Part.some (Rπ (Nat.pair (seqCode (m.unpair.1 :: decodeSeq E0)) m.unpair.2)) :=
    recursiveIn_comp_primrec hRπ hq
  have hstop : Nat.RecursiveIn {charFn (finiteParamOracle A)} fun m =>
      Part.some (if Rσ (Nat.pair (seqCode (m.unpair.1 :: decodeSeq E0)) m.unpair.2) = 1
          ∨ Rπ (Nat.pair (seqCode (m.unpair.1 :: decodeSeq E0)) m.unpair.2) = 1
        then 0 else 1) := by
    have hif : Primrec fun v : ℕ =>
        if v.unpair.1 = 1 ∨ v.unpair.2 = 1 then 0 else 1 :=
      Primrec.ite
        (PrimrecPred.or
          (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1))
          (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1)))
        (Primrec.const 0) (Primrec.const 1)
    exact (recursiveIn_comp_total (recursiveIn_of_primrec hif)
      (recursiveIn_pair_total hRσq hRπq)).of_eq fun m => by
      simp [Nat.unpair_pair]
  have hpos : Nat.RecursiveIn {charFn (finiteParamOracle A)} fun m =>
      Part.some (if Rσ (Nat.pair (seqCode (m.unpair.1 :: decodeSeq E0)) m.unpair.2) = 1
        then 1 else 0) := by
    have hif : Primrec fun v : ℕ => if v = 1 then 1 else 0 :=
      Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1))
        (Primrec.const 1) (Primrec.const 0)
    exact (recursiveIn_comp_total (recursiveIn_of_primrec hif) hRσq).of_eq fun m => rfl
  have hid : Nat.RecursiveIn {charFn (finiteParamOracle A)} fun a => Part.some a :=
    (recursiveIn_of_primrec Primrec.id).of_eq fun a => rfl
  have hfinal := Nat.RecursiveIn.comp hpos
    (Nat.RecursiveIn.pair hid (Nat.RecursiveIn.rfind hstop))
  refine hfinal.of_eq fun x => ?_
  simp only [Nat.unpair_pair, env_eq]
  -- the three permitted uses of the equivalence premise
  have hσ_of_hit : ∀ s, Rσ (Nat.pair (seqCode (List.ofFn (x :> e))) s) = 1 →
      EvalN 𝕊 φ A (x :> e) := fun s hs => (hspecσ (x :> e)).mpr ⟨s, hs⟩
  have hπ_of_hit : ∀ s, Rπ (Nat.pair (seqCode (List.ofFn (x :> e))) s) = 1 →
      ¬ EvalN 𝕊 φ A (x :> e) := fun s hs hx =>
    ((hspecπ (x :> e)).mpr ⟨s, hs⟩) ((heq x).mp hx)
  have hhits : ∃ s : ℕ,
      Rσ (Nat.pair (seqCode (List.ofFn (x :> e))) s) = 1 ∨
      Rπ (Nat.pair (seqCode (List.ofFn (x :> e))) s) = 1 := by
    by_cases hx : EvalN 𝕊 φ A (x :> e)
    · obtain ⟨wc, hwc⟩ := (hspecσ (x :> e)).mp hx
      exact ⟨wc, Or.inl hwc⟩
    · obtain ⟨wc, hwc⟩ := (hspecπ (x :> e)).mp fun hψx => hx ((heq x).mpr hψx)
      exact ⟨wc, Or.inr hwc⟩
  set p : ℕ →. Bool := fun n => (fun m => decide (m = 0)) <$>
    Part.some (if Rσ (Nat.pair (seqCode (List.ofFn (x :> e))) n) = 1 ∨
        Rπ (Nat.pair (seqCode (List.ofFn (x :> e))) n) = 1 then 0 else 1) with hp
  have hp_eval : ∀ n : ℕ, p n = Part.some (decide
      (Rσ (Nat.pair (seqCode (List.ofFn (x :> e))) n) = 1 ∨
       Rπ (Nat.pair (seqCode (List.ofFn (x :> e))) n) = 1)) := by
    intro n
    simp only [hp]
    by_cases h : Rσ (Nat.pair (seqCode (List.ofFn (x :> e))) n) = 1 ∨
        Rπ (Nat.pair (seqCode (List.ofFn (x :> e))) n) = 1
    · rw [if_pos h, decide_eq_true h]
      rfl
    · rw [if_neg h, decide_eq_false h]
      rfl
  have hdom : (Nat.rfind p).Dom := by
    obtain ⟨s, hs⟩ := hhits
    refine Nat.rfind_dom.mpr ⟨s, ?_, fun {m} _ => by rw [hp_eval m]; trivial⟩
    rw [hp_eval s]
    exact Part.mem_some_iff.mpr (decide_eq_true hs).symm
  set s₀ : ℕ := (Nat.rfind p).get hdom with hs₀def
  have hs₀mem : s₀ ∈ Nat.rfind p := Part.get_mem hdom
  have hs₀hit : Rσ (Nat.pair (seqCode (List.ofFn (x :> e))) s₀) = 1 ∨
      Rπ (Nat.pair (seqCode (List.ofFn (x :> e))) s₀) = 1 := by
    have h := Nat.rfind_spec hs₀mem
    rw [hp_eval s₀] at h
    exact of_decide_eq_true (Part.mem_some_iff.mp h).symm
  rw [show charFn {x : ℕ | EvalN 𝕊 φ A (x :> e)} x =
      Part.some (if EvalN 𝕊 φ A (x :> e) then 1 else 0) from rfl]
  rw [Part.eq_some_iff]
  have hseq : (Nat.pair <$> Part.some x <*> Nat.rfind p) =
      (Nat.rfind p).map (Nat.pair x) := by
    simp [Seq.seq]
  refine Part.mem_bind_iff.mpr ⟨Nat.pair x s₀, ?_, ?_⟩
  · rw [hseq]
    exact Part.mem_map (Nat.pair x) hs₀mem
  · simp only [Nat.unpair_pair]
    by_cases hx : EvalN 𝕊 φ A (x :> e)
    · have hσ : Rσ (Nat.pair (seqCode (List.ofFn (x :> e))) s₀) = 1 := by
        rcases hs₀hit with h | h
        · exact h
        · exact absurd hx (hπ_of_hit s₀ h)
      rw [if_pos hσ, if_pos hx]
      exact Part.mem_some 1
    · have hσ : ¬ Rσ (Nat.pair (seqCode (List.ofFn (x :> e))) s₀) = 1 := fun h =>
        hx (hσ_of_hit s₀ h)
      rw [if_neg hσ, if_neg hx]
      exact Part.mem_some 0

end RMFoundationBridge
