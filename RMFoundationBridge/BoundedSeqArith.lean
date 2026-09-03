/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.HierarchyRew
import RMFoundationBridge.SeqArith

/-!
# Converse adequacy, Slice B: the classified Δ⁰₀ sequence-arithmetic toolkit

`SeqArith.lean` arithmetizes the coding operations with **unbounded** witnesses and, by
its own contract, claims no hierarchy classification. The downward-closure clause of the
converse needs the same content **inside the strict hierarchy**: the computation-history
checker of the next slice must be a Δ⁰₀ matrix with one set slot, so every witness it
quantifies must be bounded by a term, with a proof that the bound suffices. This module
supplies that toolkit without touching `SeqArith`'s contract.

The acceptance boundary is semantic, not merely syntactic. For each operation:

* the checker is a `Delta0Code` (so `toFormula_isDelta0` classifies its translation
  for free — no separate derivation is hand-built);
* the **bound-sufficiency** theorem is stated on plain ℕ, separately from any syntax:
  the bounded search is equivalent to the unbounded characterization
  (`mod_bounded_char`, `div_bounded_char`, `fst_bounded_char`, `snd_bounded_char`,
  `beta_bounded_char`), with the bound named explicitly;
* the **standard-ℕ agreement** theorem says the translation's Tarski evaluation is the
  literal arithmetic fact, for every `𝕊`, set assignment, and environment.

The witnesses and their bounds:

| operation | witness | bound | why it suffices |
|---|---|---|---|
| `w % m` (`modCode`) | quotient `q` | `q < w + 1` | `w / m ≤ w` |
| `w / m` (`divCode`) | remainder `r` | `r < m` | `w % m < m` |
| `(unpair s).1` (`fstCode`) | second component `b` | `b < s + 1` | `unpair_right_le` |
| `(unpair s).2` (`sndCode`) | first component `a` | `a < s + 1` | `unpair_left_le` |
| `Nat.beta s i` (`betaCode`) | both components | `< s + 1` | both `unpair` bounds |

`pairCode` needs no witness at all. Also here: **code-level rewriting**
(`Delta0Code.rew`, with `toFormula_rew`), so codes compose through the same substitution
combinator as the formulas (`app₃`) while staying codes.

Nothing here mentions `OmegaPart`, `OracleCode`, or any ideal premise.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder

/-! ### Code-level rewriting -/

namespace Delta0Code

variable {N : ℕ}

/-- Rewriting a code along a number-variable rewrite: terms are rewritten in place, and
beneath a bounded binder the rewrite is lifted by `q`, exactly as `rew_ballLT` /
`rew_bexLT` compute on the denoted formulas. -/
def rew : ∀ {n₁ n₂ : ℕ}, Rew ℒₒᵣ Empty n₁ Empty n₂ → Delta0Code N n₁ → Delta0Code N n₂
  | _, _, ω, .eq t s => .eq (ω t) (ω s)
  | _, _, ω, .neq t s => .neq (ω t) (ω s)
  | _, _, ω, .lt t s => .lt (ω t) (ω s)
  | _, _, ω, .nlt t s => .nlt (ω t) (ω s)
  | _, _, ω, .mem X t => .mem X (ω t)
  | _, _, ω, .notMem X t => .notMem X (ω t)
  | _, _, _, .verum => .verum
  | _, _, _, .falsum => .falsum
  | _, _, ω, .and c d => .and (c.rew ω) (d.rew ω)
  | _, _, ω, .or c d => .or (c.rew ω) (d.rew ω)
  | _, _, ω, .ball t c => .ball (ω t) (c.rew ω.q)
  | _, _, ω, .bex t c => .bex (ω t) (c.rew ω.q)

/-- Rewriting a two-term relation atom. -/
private theorem rew_rel₂ {n₁ n₂ : ℕ} (ω : Rew ℒₒᵣ Empty n₁ Empty n₂)
    (R : (ℒₒᵣ : Language).Rel 2) (t s : Semiterm ℒₒᵣ Empty n₁) :
    (ω ▹ (.rel R ![t, s] : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n₁)) =
      .rel R ![ω t, ω s] := by
  rw [SecondOrder.Semiformula.rew_rel]
  congr 1
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
    induction j using Fin.cases with
    | zero => rfl
    | succ k => exact k.elim0

private theorem rew_nrel₂ {n₁ n₂ : ℕ} (ω : Rew ℒₒᵣ Empty n₁ Empty n₂)
    (R : (ℒₒᵣ : Language).Rel 2) (t s : Semiterm ℒₒᵣ Empty n₁) :
    (ω ▹ (.nrel R ![t, s] : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n₁)) =
      .nrel R ![ω t, ω s] := by
  rw [SecondOrder.Semiformula.rew_nrel]
  congr 1
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
    induction j using Fin.cases with
    | zero => rfl
    | succ k => exact k.elim0

/-- The denoted formula of a rewritten code is the rewritten denoted formula. -/
theorem toFormula_rew : ∀ {n₁ n₂ : ℕ} (ω : Rew ℒₒᵣ Empty n₁ Empty n₂)
    (c : Delta0Code N n₁), (c.rew ω).toFormula = ω ▹ c.toFormula
  | _, _, ω, .eq t s => (rew_rel₂ ω _ t s).symm
  | _, _, ω, .neq t s => (rew_nrel₂ ω _ t s).symm
  | _, _, ω, .lt t s => (rew_rel₂ ω _ t s).symm
  | _, _, ω, .nlt t s => (rew_nrel₂ ω _ t s).symm
  | _, _, ω, .mem X t => rfl
  | _, _, ω, .notMem X t => rfl
  | _, _, _, .verum => rfl
  | _, _, _, .falsum => rfl
  | _, _, ω, .and c d => by
      show (c.rew ω).toFormula ⋏ (d.rew ω).toFormula = ω ▹ (c.toFormula ⋏ d.toFormula)
      rw [toFormula_rew ω c, toFormula_rew ω d]
      rfl
  | _, _, ω, .or c d => by
      show (c.rew ω).toFormula ⋎ (d.rew ω).toFormula = ω ▹ (c.toFormula ⋎ d.toFormula)
      rw [toFormula_rew ω c, toFormula_rew ω d]
      rfl
  | _, _, ω, .ball t c => by
      show ballLT (ω t) (c.rew ω.q).toFormula = ω ▹ ballLT t c.toFormula
      rw [rew_ballLT, toFormula_rew ω.q c]
  | _, _, ω, .bex t c => by
      show bexLT (ω t) (c.rew ω.q).toFormula = ω ▹ bexLT t c.toFormula
      rw [rew_bexLT, toFormula_rew ω.q c]

/-- Apply a 3-ary code at three terms (the code-level `app₃`). -/
def app₃ {n : ℕ} (c : Delta0Code N 3) (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) :
    Delta0Code N n :=
  c.rew (Rew.subst ![t₁, t₂, t₃])

theorem toFormula_app₃ {n : ℕ} (c : Delta0Code N 3) (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) :
    (c.app₃ t₁ t₂ t₃).toFormula = RMFoundationBridge.app₃ c.toFormula t₁ t₂ t₃ :=
  toFormula_rew _ c

/-- Evaluating an applied code is evaluating the code at the terms' values. -/
theorem evalN_app₃ {𝕊 : Set (Set ℕ)} {E : Fin N → Set ℕ} {n : ℕ} (c : Delta0Code N 3)
    (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (c.app₃ t₁ t₂ t₃).toFormula E e ↔
      EvalN 𝕊 c.toFormula E ![tval t₁ e, tval t₂ e, tval t₃ e] := by
  rw [toFormula_app₃, RMFoundationBridge.evalN_app₃]

end Delta0Code

/-! ### Bound sufficiency, on plain ℕ -/

/-- The quotient is bounded by the dividend: the bounded remainder search is the
remainder characterization. -/
theorem mod_bounded_char {w m y : ℕ} :
    (∃ q < w + 1, w = q * m + y ∧ y < m) ↔ y = w % m ∧ 0 < m := by
  rw [← mod_char]
  constructor
  · rintro ⟨q, -, h⟩
    exact ⟨q, h⟩
  · rintro ⟨q, hq, hy⟩
    refine ⟨q, ?_, hq, hy⟩
    have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le y) hy
    have : q ≤ q * m := Nat.le_mul_of_pos_right q hm
    omega

/-- The remainder is bounded by the modulus: the bounded quotient search is the
quotient characterization. -/
theorem div_bounded_char {w m y : ℕ} :
    (∃ r < m, w = y * m + r) ↔ y = w / m ∧ 0 < m := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨?_, Nat.lt_of_le_of_lt (Nat.zero_le r) hr⟩
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.lt_of_le_of_lt (Nat.zero_le r) hr),
      Nat.div_eq_of_lt hr, Nat.add_zero]
  · rintro ⟨rfl, hm⟩
    exact ⟨w % m, Nat.mod_lt _ hm, by rw [Nat.mul_comm]; exact (Nat.div_add_mod w m).symm⟩

/-- The second component of an unpairing is bounded by the pair: the bounded search is
the first-projection characterization. -/
theorem fst_bounded_char {s a : ℕ} :
    (∃ b < s + 1, s = Nat.pair a b) ↔ a = (Nat.unpair s).1 := by
  constructor
  · rintro ⟨b, -, rfl⟩
    rw [Nat.unpair_pair]
  · rintro rfl
    exact ⟨(Nat.unpair s).2, Nat.lt_succ_of_le (Nat.unpair_right_le s),
      (Nat.pair_unpair s).symm⟩

/-- The first component of an unpairing is bounded by the pair. -/
theorem snd_bounded_char {s b : ℕ} :
    (∃ a < s + 1, s = Nat.pair a b) ↔ b = (Nat.unpair s).2 := by
  constructor
  · rintro ⟨a, -, rfl⟩
    rw [Nat.unpair_pair]
  · rintro rfl
    exact ⟨(Nat.unpair s).1, Nat.lt_succ_of_le (Nat.unpair_left_le s),
      (Nat.pair_unpair s).symm⟩

/-- Both components of β's packed witness are bounded by the witness. -/
theorem beta_bounded_char {s i y : ℕ} :
    (∃ w < s + 1, ∃ d < s + 1, s = Nat.pair w d ∧
      (y = w % ((i + 1) * d + 1) ∧ 0 < (i + 1) * d + 1)) ↔ y = Nat.beta s i := by
  rw [eq_beta_iff]
  constructor
  · rintro ⟨w, -, d, -, h⟩
    exact ⟨w, d, h⟩
  · rintro ⟨w, d, rfl, h⟩
    exact ⟨w, Nat.lt_succ_of_le (Nat.left_le_pair w d), d,
      Nat.lt_succ_of_le (Nat.right_le_pair w d), rfl, h⟩

/-! ### The codes -/

/-- `pairCode (a, b, y)`: `y = Nat.pair a b`. Quantifier-free; its translation is
literally `pairGraph`. -/
def pairCode {N : ℕ} : Delta0Code N 3 :=
  .or (.and (.lt #0 #1) (.eq #2 (tAdd (tMul #1 #1) #0)))
    (.and (.nlt #0 #1) (.eq #2 (tAdd (tAdd (tMul #0 #0) #0) #1)))

theorem pairCode_toFormula {N : ℕ} : (pairCode (N := N)).toFormula = pairGraph := rfl

/-- `modCode (w, m, y)`: `∃ q < w + 1, w = q · m + y ∧ y < m`. Beneath the binder
`#0 = q`, `#1 = w`, `#2 = m`, `#3 = y`. -/
def modCode {N : ℕ} : Delta0Code N 3 :=
  .bex (tSucc #0) (.and (.eq #1 (tAdd (tMul #0 #2) #3)) (.lt #3 #2))

/-- `divCode (w, m, y)`: `∃ r < m, w = y · m + r`. Beneath the binder `#0 = r`,
`#1 = w`, `#2 = m`, `#3 = y`. -/
def divCode {N : ℕ} : Delta0Code N 3 :=
  .bex #1 (.eq #1 (tAdd (tMul #3 #2) #0))

/-- `fstCode (s, a)`: `∃ b < s + 1, s = pair a b`. Beneath the binder `#0 = b`,
`#1 = s`, `#2 = a`. -/
def fstCode {N : ℕ} : Delta0Code N 2 :=
  .bex (tSucc #0) (pairCode.app₃ #2 #0 #1)

/-- `sndCode (s, b)`: `∃ a < s + 1, s = pair a b`. Beneath the binder `#0 = a`,
`#1 = s`, `#2 = b`. -/
def sndCode {N : ℕ} : Delta0Code N 2 :=
  .bex (tSucc #0) (pairCode.app₃ #0 #2 #1)

/-- `betaCode (s, i, y)`: `∃ w < s + 1, ∃ d < s + 1, s = pair w d ∧ y = w % ((i+1)·d + 1)`.
Beneath both binders `#0 = d`, `#1 = w`, `#2 = s`, `#3 = i`, `#4 = y` — the same slots
as `betaGraph`, now with bounded binders. -/
def betaCode {N : ℕ} : Delta0Code N 3 :=
  .bex (tSucc #0) (.bex (tSucc #1) (.and (pairCode.app₃ #1 #0 #2)
    (modCode.app₃ #1 (tSucc (tMul (tSucc #3) #0)) #4)))

/-! ### Standard-ℕ agreement -/

section agreement

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

theorem evalN_pairCode (a b y : ℕ) :
    EvalN 𝕊 (pairCode (N := N)).toFormula E ![a, b, y] ↔ y = Nat.pair a b := by
  rw [pairCode_toFormula, evalN_pairGraph]

theorem evalN_modCode (w m y : ℕ) :
    EvalN 𝕊 (modCode (N := N)).toFormula E ![w, m, y] ↔ y = w % m ∧ 0 < m := by
  rw [← mod_bounded_char]
  exact Iff.rfl

theorem evalN_divCode (w m y : ℕ) :
    EvalN 𝕊 (divCode (N := N)).toFormula E ![w, m, y] ↔ y = w / m ∧ 0 < m := by
  rw [← div_bounded_char]
  exact Iff.rfl

theorem evalN_fstCode (s a : ℕ) :
    EvalN 𝕊 (fstCode (N := N)).toFormula E ![s, a] ↔ a = (Nat.unpair s).1 := by
  rw [← fst_bounded_char]
  change (∃ b : ℕ, b < s + 1 ∧
    EvalN 𝕊 (pairCode.app₃ #2 #0 #1).toFormula E (b :> ![s, a])) ↔ _
  refine exists_congr fun b => and_congr Iff.rfl ?_
  rw [Delta0Code.evalN_app₃, evalN_pairCode]
  rfl

theorem evalN_sndCode (s b : ℕ) :
    EvalN 𝕊 (sndCode (N := N)).toFormula E ![s, b] ↔ b = (Nat.unpair s).2 := by
  rw [← snd_bounded_char]
  change (∃ a : ℕ, a < s + 1 ∧
    EvalN 𝕊 (pairCode.app₃ #0 #2 #1).toFormula E (a :> ![s, b])) ↔ _
  refine exists_congr fun a => and_congr Iff.rfl ?_
  rw [Delta0Code.evalN_app₃, evalN_pairCode]
  rfl

theorem evalN_betaCode (s i y : ℕ) :
    EvalN 𝕊 (betaCode (N := N)).toFormula E ![s, i, y] ↔ y = Nat.beta s i := by
  rw [← beta_bounded_char]
  change (∃ w : ℕ, w < s + 1 ∧ ∃ d : ℕ, d < s + 1 ∧
    (EvalN 𝕊 (pairCode.app₃ #1 #0 #2).toFormula E (d :> w :> ![s, i, y]) ∧
     EvalN 𝕊 (modCode.app₃ #1 (tSucc (tMul (tSucc #3) #0)) #4).toFormula E
       (d :> w :> ![s, i, y]))) ↔ _
  refine exists_congr fun w => and_congr Iff.rfl (exists_congr fun d =>
    and_congr Iff.rfl (and_congr ?_ ?_))
  · rw [Delta0Code.evalN_app₃, evalN_pairCode]
    rfl
  · rw [Delta0Code.evalN_app₃, evalN_modCode]
    rfl

/-- Applied forms, the shape later layers consume. -/
theorem evalN_app₃_betaCode (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 ((betaCode (N := N)).app₃ t₁ t₂ t₃).toFormula E e ↔
      tval t₃ e = Nat.beta (tval t₁ e) (tval t₂ e) := by
  rw [Delta0Code.evalN_app₃, evalN_betaCode]

theorem evalN_app₃_pairCode (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 ((pairCode (N := N)).app₃ t₁ t₂ t₃).toFormula E e ↔
      tval t₃ e = Nat.pair (tval t₁ e) (tval t₂ e) := by
  rw [Delta0Code.evalN_app₃, evalN_pairCode]

end agreement

/-! ### Classification, for the record

The translations are Δ⁰₀ by `toFormula_isDelta0`; these instances pin the fact for the
codes that the next slice composes. -/

example {N : ℕ} : IsDelta0 (betaCode (N := N)).toFormula := Delta0Code.toFormula_isDelta0 _
example {N : ℕ} : IsDelta0 (modCode (N := N)).toFormula := Delta0Code.toFormula_isDelta0 _

/-! ### Executable fixtures

`Nat.pair 5 1 = 31` and `Nat.beta 31 0 = 5 % 2 = 1`; the evaluator scans the bounded
witnesses and finds them. -/

example : Delta0Code.beval fixtureChi (pairCode : Delta0Code 1 3) [5, 1, 31] = true := rfl
example : Delta0Code.beval fixtureChi (modCode : Delta0Code 1 3) [31, 2, 1] = true := rfl
example : Delta0Code.beval fixtureChi (modCode : Delta0Code 1 3) [31, 2, 0] = false := rfl
example : Delta0Code.beval fixtureChi (divCode : Delta0Code 1 3) [31, 2, 15] = true := rfl
example : Delta0Code.beval fixtureChi (fstCode : Delta0Code 1 2) [31, 5] = true := rfl
example : Delta0Code.beval fixtureChi (sndCode : Delta0Code 1 2) [31, 1] = true := rfl
example : Delta0Code.beval fixtureChi (betaCode : Delta0Code 1 3) [31, 0, 1] = true := by
  decide
example : Delta0Code.beval fixtureChi (betaCode : Delta0Code 1 3) [31, 0, 0] = false := by
  decide

end RMFoundationBridge
