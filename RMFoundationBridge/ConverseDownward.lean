/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.OracleTranscriptCode
import RMFoundationBridge.ConverseStructural
import RMFoundationBridge.HierarchyRew

/-!
# Converse adequacy, Slice C3: the Σ⁰₁ output predicate and downward closure

The last clause of the converse. From the checker of Slice C2 this module builds:

* **the general Σ⁰₁ output predicate** `outputMatrix`, with one oracle-set slot and three
  explicit number slots `(n, e, v)`: "the oracle code numbered `e`, run on `n` against
  the oracle of the set in slot `0`, outputs `v`". It is strictly Σ⁰₁ by construction
  (one `∃¹` over a `Delta0Code 1 4`), and its **standard-ℕ agreement**
  (`evalN_outputMatrix`) is the literal statement
  `v ∈ OracleCode.eval (charFn B) (OracleCode.ofNatCode e) n`.
  That agreement is a theorem of the metatheory about standard ℕ; nothing here claims
  that any object theory proves it, nor that the object theory proves totality or
  determinism of the coded function.
* **the polarity pair**: `Out₁ := outputMatrix` at `v = 1` (Σ⁰₁) and `Out₀`, the same
  matrix at `v = 0` (Σ⁰₁, by substitution); the Π⁰₁ definition is `∼Out₀`
  (`IsSigma01.neg`). Their agreement `Out₁ ↔ ∼Out₀` at a reducing code
  (`out_one_iff_not_out_zero`) visibly uses **totality** (the characteristic function is
  defined at every input, so one of the two outputs occurs) and **determinism**
  (`Part.mem_unique`: they never occur together).
* **downward closure** `mem_of_reducible_of_models_rca0`: comprehension on the pair,
  at set assignment `![B]` and number parameters `(e, 1)`, recovers exactly `A`. The
  reduced set `A` occurs only in this metatheoretic argument, through
  `eval (charFn B) c = charFn A`; the formula and its set assignment mention `B` alone.

Bridge-local: nothing is exported or ingested, and the bundled Turing-ideal converse
(with nonemptiness and join from Slice A) is the subject of Slice D.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-! ### An entry in a table, as a code -/

/-- `memTableCode (T, K, e, n, v)`: `T = pair L S` with `L, S ≤ T`, and the entry
`(K, e, n, v)` occurs at some index below `L` (support at the length, off the seed).
Beneath the binders `#0 = S`, `#1 = L`, `#2 = T`, `#3 = K`, `#4 = e`, `#5 = n`, `#6 = v`. -/
def memTableCode : Delta0Code 1 5 :=
  .bex (tSucc #0) (.bex (tSucc #1)
    (.and (pairCode.app ![#1, #0, #2]) (supportsCode.app ![#0, #1, #3, #4, #5, #6])))

theorem evalN_memTableCode {𝕊 : Set (Set ℕ)} {E : Fin 1 → Set ℕ} (T K e n v : ℕ) :
    EvalN 𝕊 memTableCode.toFormula E ![T, K, e, n, v] ↔
      (⟨K, e, n, v⟩ : Entry) ∈ tableOf T := by
  simp only [memTableCode, Delta0Code.toFormula, evalN_bexLT, evalN_and,
    Delta0Code.evalN_app, tval_vecCons, tval_vecEmpty, evalN_pairCode, evalN_supportsCode]
  constructor
  · rintro ⟨L, -, S, -, hT, hs⟩
    have hT' : T = Nat.pair L S := hT
    have hs' : SupportsAt S L ⟨K, e, n, v⟩ := hs
    subst hT'
    have hL : (tableOf (Nat.pair L S)).length = L := by rw [tableOf_length, Nat.unpair_pair]
    apply supports_length_iff.mp
    rw [hL]
    exact (supportsAt_iff_supports (T := Nat.pair L S)
      (by rw [Nat.unpair_pair]) _).mp (by rw [Nat.unpair_pair]; exact hs')
  · intro h
    refine ⟨T.unpair.1, Nat.lt_succ_of_le (Nat.unpair_left_le T),
      T.unpair.2, Nat.lt_succ_of_le (Nat.unpair_right_le T),
      show T = Nat.pair T.unpair.1 T.unpair.2 from (Nat.pair_unpair T).symm, ?_⟩
    have := supports_length_iff.mpr h
    rw [tableOf_length] at this
    exact (supportsAt_iff_supports le_rfl _).mpr this

/-! ### The general Σ⁰₁ output predicate -/

/-- The Δ⁰₀ body beneath the transcript quantifier, slots `(T, n, e, v)`: some fuel
`K ≤ T` has the target entry `(K, e, n, v)` in a verified table. Beneath the binder
`#0 = K`, `#1 = T`, `#2 = n`, `#3 = e`, `#4 = v`. -/
def outputBodyCode : Delta0Code 1 4 :=
  .bex (tSucc #0) (.and (verifiedCode.app ![#1]) (memTableCode.app ![#1, #0, #3, #2, #4]))

/-- **The general Σ⁰₁ output predicate**, slots `(n, e, v)` with the oracle set at set
slot `0`: `∃ T, outputBody(T, n, e, v)`. -/
def outputMatrix : SecondOrder.Semiformula ℒₒᵣ Empty Empty 1 3 :=
  .exs₁ outputBodyCode.toFormula

theorem outputMatrix_isSigma01 : IsSigma01 (Ξ := Empty) (ξ := Empty) outputMatrix :=
  .exs (.delta0 (Delta0Code.toFormula_isDelta0 _))

/-- **Standard-ℕ agreement of the output predicate**: at set assignment `![B]` and number
assignment `![n, e, v]`, the predicate holds iff the frozen unbounded evaluation of the
code numbered `e` on `n`, against `charFn B`, contains `v`. A metatheoretic statement
about standard ℕ; no object theory is claimed to prove it. -/
theorem evalN_outputMatrix {𝕊 : Set (Set ℕ)} (B : Set ℕ) (n e v : ℕ) :
    EvalN 𝕊 outputMatrix ![B] ![n, e, v] ↔
      v ∈ OracleCode.eval (charFn B) (OracleCode.ofNatCode e) n := by
  rw [charFn_eq_coe_oracleOf, OracleCode.evaln_complete]
  simp only [outputMatrix, evalN_exs₁, outputBodyCode, Delta0Code.toFormula, evalN_bexLT,
    evalN_and, Delta0Code.evalN_app, tval_vecCons, tval_vecEmpty, evalN_verifiedCode,
    evalN_memTableCode]
  constructor
  · rintro ⟨T, K, -, hV, hm⟩
    have hV' : Verified B (tableOf T) := hV
    have hm' : (⟨K, e, n, v⟩ : Entry) ∈ tableOf T := hm
    have := verified_sound hV' hm'
    exact ⟨K, this⟩
  · rintro ⟨K, hK⟩
    obtain ⟨L, hL, hmem⟩ := verified_complete K (OracleCode.ofNatCode e) hK
    refine ⟨Nat.pair L.length (Nat.unbeta (L.map Entry.toNat)), K, ?_, ?_, ?_⟩
    · -- the fuel is a component of an entry of the table, hence bounded by the code
      show K < Nat.pair L.length (Nat.unbeta (L.map Entry.toNat)) + 1
      have h1 := supports_length_iff.mpr hmem
      rw [← exists_tableOf L, tableOf_length] at h1
      rw [← exists_tableOf L] at hmem
      have := (supportsAt_iff_supports le_rfl _).mpr h1
      have hK := this.fuel_le
      simp only [targetEntry] at hK
      exact Nat.lt_succ_of_le (le_trans hK (Nat.unpair_right_le _))
    · show Verified B (tableOf (Nat.pair L.length (Nat.unbeta (L.map Entry.toNat))))
      rw [exists_tableOf]
      exact hL
    · show (⟨K, e, n, v⟩ : Entry) ∈ tableOf (Nat.pair L.length (Nat.unbeta (L.map Entry.toNat)))
      rw [exists_tableOf]
      simpa [targetEntry, encodeCode_ofNatCode] using hmem

/-! ### The polarity pair: outputs `1` and `0` -/

/-- `Out₀`: the output predicate with `v` fixed to `0`, in the same slots `(n, e, v)` (the
`v` slot is then ignored). Σ⁰₁ by substitution. -/
def outZeroMatrix : SecondOrder.Semiformula ℒₒᵣ Empty Empty 1 3 :=
  Rew.subst ![#0, #1, tNum 0] ▹ outputMatrix

theorem outZeroMatrix_isSigma01 : IsSigma01 (Ξ := Empty) (ξ := Empty) outZeroMatrix :=
  outputMatrix_isSigma01.rew _

/-- The Π⁰₁ definition: **no output-`0` transcript**. -/
def notOutZeroMatrix : SecondOrder.Semiformula ℒₒᵣ Empty Empty 1 3 := ∼outZeroMatrix

theorem notOutZeroMatrix_isPi01 : IsPi01 (Ξ := Empty) (ξ := Empty) notOutZeroMatrix :=
  outZeroMatrix_isSigma01.neg

theorem evalN_outZeroMatrix {𝕊 : Set (Set ℕ)} (B : Set ℕ) (n e v : ℕ) :
    EvalN 𝕊 outZeroMatrix ![B] ![n, e, v] ↔
      0 ∈ OracleCode.eval (charFn B) (OracleCode.ofNatCode e) n := by
  rw [outZeroMatrix, evalN_rew_subst]
  have henv : (fun i => tval (![#0, #1, tNum 0] i) ![n, e, v]) = ![n, e, 0] := by
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ j =>
      induction j using Fin.cases with
      | zero => rfl
      | succ k =>
        induction k using Fin.cases with
        | zero => exact tval_tNum 0 _
        | succ l => exact l.elim0
  rw [henv]
  exact evalN_outputMatrix B n e 0

theorem evalN_notOutZeroMatrix {𝕊 : Set (Set ℕ)} (B : Set ℕ) (n e v : ℕ) :
    EvalN 𝕊 notOutZeroMatrix ![B] ![n, e, v] ↔
      ¬ 0 ∈ OracleCode.eval (charFn B) (OracleCode.ofNatCode e) n := by
  rw [notOutZeroMatrix, evalN_neg, evalN_outZeroMatrix]

/-- The downward-closure comprehension instance (`outputMatrix` as the Σ⁰₁ definition,
`∼Out₀` as the Π⁰₁ one, two number parameters `e, v`) is an axiom of the theory. -/
theorem outputComprehension_mem_theory :
    comprehensionSentence (k := 2) outputMatrix notOutZeroMatrix ∈ Rca0Theory :=
  AxiomOrigin.delta1Comprehension outputMatrix_isSigma01 notOutZeroMatrix_isPi01

/-- **Polarity agreement at a reducing code**: output `1` iff no output `0`. The forward
direction is **determinism** (`Part.mem_unique`: the two outputs never occur together);
the backward direction is **totality** (`charFn_dom`: an output occurs, and it is `0` or
`1`). -/
theorem out_one_iff_not_out_zero {A B : Set ℕ} {c : OracleCode}
    (hc : OracleCode.eval (charFn B) c = charFn A) (x : ℕ) :
    1 ∈ OracleCode.eval (charFn B) c x ↔ ¬ 0 ∈ OracleCode.eval (charFn B) c x := by
  rw [hc]
  constructor
  · intro h1 h0
    exact absurd (Part.mem_unique h1 h0) one_ne_zero
  · intro h0
    have hget : (charFn A x).get (charFn_dom A x) ∈ charFn A x := Part.get_mem _
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (le_one_of_mem_charFn hget) with h | h
    · exact absurd (h ▸ hget) h0
    · exact h ▸ hget

/-! ### Downward closure -/

/-- **Downward closure of every model**: if `B` is in the part and `A ≤ᵀ B`, then `A` is in
the part. The reducing code `c` comes from `exists_code`; comprehension on the polarity
pair at set assignment `![B]` and number parameters `(encodeCode c, 1)` produces a set
whose extension is, by `evalN_outputMatrix` and `one_mem_charFn_iff`, exactly `A`. The
set `A` occurs only here, through `eval (charFn B) c = charFn A`. -/
theorem mem_of_reducible_of_models_rca0 {Ω : OmegaPart} (h : Ω.toFoundation ⊧* Rca0Theory)
    {A B : Set ℕ} (hB : B ∈ Ω) (hAB : A ≤ᵀ B) : A ∈ Ω := by
  obtain ⟨c, hc⟩ := OracleCode.exists_code.mp hAB
  have hσ := Semantics.modelsSet_iff.mp h outputComprehension_mem_theory
  rw [models_comprehensionInstance_iff] at hσ
  have hE : ∀ i : Fin 1, ![B] i ∈ Ω.sets := by
    intro i
    induction i using Fin.cases with
    | zero => exact hB
    | succ j => exact j.elim0
  have hout : ∀ x v : ℕ, EvalN Ω.sets outputMatrix ![B] (x :> ![c.encodeCode, v]) ↔
      v ∈ OracleCode.eval (charFn B) c x := fun x v => by
    rw [show (x :> ![c.encodeCode, v]) = ![x, c.encodeCode, v] from rfl, evalN_outputMatrix,
      ofNatCode_encodeCode]
  have hnot : ∀ x : ℕ, EvalN Ω.sets notOutZeroMatrix ![B] (x :> ![c.encodeCode, 1]) ↔
      ¬ 0 ∈ OracleCode.eval (charFn B) c x := fun x => by
    rw [show (x :> ![c.encodeCode, 1]) = ![x, c.encodeCode, 1] from rfl,
      evalN_notOutZeroMatrix, ofNatCode_encodeCode]
  obtain ⟨X, hX, hext⟩ := hσ ![B] hE ![c.encodeCode, 1] fun x => by
    rw [hout x 1, hnot x]
    exact out_one_iff_not_out_zero hc x
  have : X = A := by
    ext x
    rw [hext x, hout x 1, hc, one_mem_charFn_iff]
  rw [← this]
  exact hX

end RMFoundationBridge
