/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.SeqArith

/-!
# F1 step 4, second layer: open tree, level, and path predicates

The three open `ℒₒᵣ` predicates the ŴKL sentence quantifies — binary-tree-ness, a node
at every level, and path-through — with evaluation equivalences terminating at the
**frozen** `ReverseMathlib.Omega` definitions (`IsBinaryTreeCode`, `HasNodeAtEveryLevel`,
`IsBinaryPathThrough`), verbatim. Set variables are parameters (`X P T : Fin N`), so the
sentence layer can bind them with `∀²`/`∃²` at the indices the binders assign; each
equivalence holds for every `𝕊`, every set assignment `E`, and every environment, with
the set side evaluated literally at `E X` — no coding translation, no closure premise.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-! ### The 1-ary substitution combinator -/

/-- Apply a 1-ary formula at a term. -/
def app₁ {N n : ℕ} (φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 1)
    (t₁ : Semiterm ℒₒᵣ Empty n) : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n :=
  Rew.subst ![t₁] ▹ φ

theorem evalN_app₁ {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}
    (φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 1)
    (t₁ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₁ φ t₁) E e ↔ EvalN 𝕊 φ E ![tval t₁ e] := by
  unfold app₁ EvalN
  rw [eval_rew φ (Rew.subst ![t₁]) E Empty.elim e]
  have hb : (Semiterm.val (M := ℕ) (s := standardInterpretation) e Empty.elim ∘
      (Rew.subst ![t₁]) ∘ Semiterm.bvar) = ![tval t₁ e] := by
    funext i
    induction i using Fin.cases with
    | zero => simp [FirstOrder.Rew.subst, tval]
    | succ j => exact j.elim0
  have hf : (Semiterm.val (M := ℕ) (s := standardInterpretation) e Empty.elim ∘
      (Rew.subst ![t₁]) ∘ Semiterm.fvar) = Empty.elim := by
    funext y
    exact y.elim
  rw [hb, hf]

/-! ### Bit-sequence-ness -/

/-- Bit-sequence-ness of a code: argument `(c)` — every decoded entry, read through the
entry graph, is below `2`. Out-of-range entries default to `0`, which is harmless. -/
def bitSeqFormula {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 1 :=
  .all₁ (.all₁ (impF (app₃ seqEntGraph #2 #1 #0) (fLt #0 (tSucc tOne))))

section bitSeq

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

/-- The `getD`-characterization of the frozen `IsBitSeqCode`. -/
theorem isBitSeqCode_char {c : ℕ} :
    (∀ i a : ℕ, (decodeSeq c).getD i 0 = a → a < 2) ↔ IsBitSeqCode c := by
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := h i _ (getD_of_lt hi)
    omega
  · intro h i a ha
    rcases Nat.lt_or_ge i (decodeSeq c).length with hi | hi
    · rw [getD_of_lt hi] at ha
      have := h _ (List.getElem_mem hi)
      omega
    · rw [getD_of_length_le hi] at ha
      omega

theorem evalN_bitSeqFormula (c : ℕ) :
    EvalN 𝕊 (bitSeqFormula (N := N)) E ![c] ↔ IsBitSeqCode c := by
  have h : EvalN 𝕊 (bitSeqFormula (N := N)) E ![c] ↔
      ∀ i a : ℕ, EvalN 𝕊 (impF (app₃ seqEntGraph #2 #1 #0) (fLt #0 (tSucc tOne))) E
        (a :> i :> ![c]) := Iff.rfl
  rw [h, ← isBitSeqCode_char]
  refine forall_congr' fun i => forall_congr' fun a => ?_
  rw [evalN_impF]
  exact imp_congr (evalN_app₃_seqEntGraph _ _ _ _) Iff.rfl

theorem evalN_app₁_bitSeqFormula (t₁ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₁ (bitSeqFormula (N := N)) t₁) E e ↔ IsBitSeqCode (tval t₁ e) := by
  rw [evalN_app₁, evalN_bitSeqFormula]

end bitSeq

/-! ### The three open predicates -/

/-- Binary-tree-ness of the set variable `X`: every member is a bit-sequence code and
every truncation of a member (routed through the take graph) is a member. -/
def treeFormula {N : ℕ} (X : Fin N) : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 0 :=
  .all₁ (impF (.bvar X #0)
    (app₁ bitSeqFormula #0 ⋏
      .all₁ (.exs₁ (app₃ seqTakeGraph #2 #1 #0 ⋏ .bvar X #0))))

/-- A node at every level in the set variable `X`. -/
def levelFormula {N : ℕ} (X : Fin N) : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 0 :=
  .all₁ (.exs₁ (.bvar X #0 ⋏ app₂ seqLenGraph #0 #1))

/-- `P` is a path through `T` (both set variables): for every length, some member of
`T` of that length agrees entrywise with the bit-`1` positions of `P`. -/
def pathFormula {N : ℕ} (P T : Fin N) : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 0 :=
  .all₁ (.exs₁ (.bvar T #0 ⋏ app₂ seqLenGraph #0 #1 ⋏
    ballLT #1 (iffF (app₃ seqEntGraph #1 #0 tOne) (.bvar P #0))))

section predicates

variable {𝕊 : Set (Set ℕ)} {N : ℕ} {E : Fin N → Set ℕ}

/-- The member-pointwise form of the frozen `IsBinaryTreeCode`. -/
theorem isBinaryTreeCode_iff {T : Set ℕ} :
    IsBinaryTreeCode T ↔
      ∀ c ∈ T, IsBitSeqCode c ∧ ∀ k, seqCode ((decodeSeq c).take k) ∈ T :=
  ⟨fun ⟨h1, h2⟩ c hc => ⟨h1 c hc, h2 c hc⟩,
   fun h => ⟨fun c hc => (h c hc).1, fun c hc => (h c hc).2⟩⟩

/-- **Tree adequacy**: the tree predicate evaluates to the frozen `IsBinaryTreeCode` at
the assigned set, for every `𝕊`, `E`, and environment. -/
theorem evalN_treeFormula (X : Fin N) (e : Fin 0 → ℕ) :
    EvalN 𝕊 (treeFormula X) E e ↔ IsBinaryTreeCode (E X) := by
  have h : EvalN 𝕊 (treeFormula X) E e ↔
      ∀ c : ℕ, EvalN 𝕊 (impF (.bvar X #0)
        (app₁ bitSeqFormula #0 ⋏
          .all₁ (.exs₁ (app₃ seqTakeGraph #2 #1 #0 ⋏ .bvar X #0)))) E (c :> e) :=
    Iff.rfl
  rw [h, isBinaryTreeCode_iff]
  refine forall_congr' fun c => ?_
  rw [evalN_impF]
  have h2 : EvalN 𝕊 (app₁ bitSeqFormula #0 ⋏
        .all₁ (.exs₁ (app₃ seqTakeGraph #2 #1 #0 ⋏ .bvar X #0))) E (c :> e) ↔
      EvalN 𝕊 (app₁ bitSeqFormula #0) E (c :> e) ∧
        ∀ k : ℕ, ∃ t : ℕ,
          EvalN 𝕊 (app₃ seqTakeGraph #2 #1 #0) E (t :> k :> c :> e) ∧
          EvalN 𝕊 (.bvar X #0) E (t :> k :> c :> e) := Iff.rfl
  rw [h2]
  refine imp_congr Iff.rfl (and_congr (evalN_app₁_bitSeqFormula _ _) ?_)
  refine forall_congr' fun k => ?_
  constructor
  · rintro ⟨t, ht, hmem⟩
    have ht' : t = seqCode ((decodeSeq c).take k) :=
      (evalN_app₃_seqTakeGraph _ _ _ _).mp ht
    have hmem' : t ∈ E X := hmem
    rwa [ht'] at hmem'
  · intro hmem
    exact ⟨seqCode ((decodeSeq c).take k), (evalN_app₃_seqTakeGraph _ _ _ _).mpr rfl,
      hmem⟩

/-- **Level adequacy**: the level predicate evaluates to the frozen
`HasNodeAtEveryLevel` at the assigned set. -/
theorem evalN_levelFormula (X : Fin N) (e : Fin 0 → ℕ) :
    EvalN 𝕊 (levelFormula X) E e ↔ HasNodeAtEveryLevel (E X) := by
  have h : EvalN 𝕊 (levelFormula X) E e ↔
      ∀ m : ℕ, ∃ c : ℕ, EvalN 𝕊 (.bvar X #0) E (c :> m :> e) ∧
        EvalN 𝕊 (app₂ seqLenGraph #0 #1) E (c :> m :> e) := Iff.rfl
  rw [h]
  exact forall_congr' fun m => exists_congr fun c =>
    and_congr Iff.rfl (evalN_app₂_seqLenGraph _ _ _)

/-- **Path adequacy**: the path predicate evaluates to the frozen
`IsBinaryPathThrough` at the assigned sets. -/
theorem evalN_pathFormula (P T : Fin N) (e : Fin 0 → ℕ) :
    EvalN 𝕊 (pathFormula P T) E e ↔ IsBinaryPathThrough (E P) (E T) := by
  have h : EvalN 𝕊 (pathFormula P T) E e ↔
      ∀ m : ℕ, ∃ c : ℕ, EvalN 𝕊 (.bvar T #0) E (c :> m :> e) ∧
        (EvalN 𝕊 (app₂ seqLenGraph #0 #1) E (c :> m :> e) ∧
          EvalN 𝕊 (ballLT #1 (iffF (app₃ seqEntGraph #1 #0 tOne) (.bvar P #0))) E
            (c :> m :> e)) := Iff.rfl
  rw [h]
  refine forall_congr' fun m => exists_congr fun c => and_congr Iff.rfl
    (and_congr (evalN_app₂_seqLenGraph _ _ _) ?_)
  rw [evalN_ballLT]
  refine forall_congr' fun i => imp_congr Iff.rfl ?_
  rw [evalN_iffF]
  exact iff_congr (evalN_app₃_seqEntGraph _ _ _ _) Iff.rfl

end predicates

end RMFoundationBridge
