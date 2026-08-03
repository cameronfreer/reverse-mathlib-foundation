/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.ArithmeticalRew

/-!
# F1 step 2 (third slice): the strict syntactic Σ⁰₁/Π⁰₁ prefix hierarchy

Three levels are kept permanently distinct, and this module implements only the first:

1. **strict syntactic membership** (this module): `IsDelta0`, `IsSigma01`, `IsPi01` are
   derivations over the literal syntax tree;
2. *semantic equivalence to a formula in a class* is a different notion and gets its own
   definitions when first needed — no lemma here conflates the two, and any future
   normalization theorem must carry its own evaluation-equivalence theorem;
3. *universal closure* of open schema instances into sentences belongs to `Rca0Theory`;
   the closed schema sentence may quantify over set parameters with `∀²` even though its
   matrix is arithmetical — the hierarchy classifies the **open matrix**, never the
   completed sentence.

Conventions (Simpson [Sim09] §I.7, claimed): `Δ⁰₀` is closed under connectives and the
**bounded** quantifiers `ballLT`/`bexLT` (the defined forms `∀x(¬x<t ∨ φ)` and
`∃x(x<t ∧ φ)`, bound term shifted past the new variable); `Σ⁰₁`/`Π⁰₁` are unbounded
`∃¹`/`∀¹` prefixes over `Δ⁰₀`. Set parameters are membership atoms and never count toward
the number-quantifier class. Negation swaps the classes. Neither class receives an
implication-closure theorem — the negative fixtures at the bottom keep that executable.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder

variable {Ξ ξ : Type*} {N n : ℕ}

/-! ### Bounded quantifiers as defined forms -/

/-- Bounded universal quantifier `∀ x < t, φ`: the defined form `∀¹(¬(#0 < t⁺) ∨ φ)`,
with the bound shifted past the new variable. -/
def ballLT (t : Semiterm ℒₒᵣ ξ n) (φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N (n + 1)) :
    SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n :=
  .all₁ (.or (.nrel Language.ORing.Rel.lt ![#0, Rew.bShift t]) φ)

/-- Bounded existential quantifier `∃ x < t, φ`: the defined form `∃¹((#0 < t⁺) ∧ φ)`. -/
def bexLT (t : Semiterm ℒₒᵣ ξ n) (φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N (n + 1)) :
    SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n :=
  .exs₁ (.and (.rel Language.ORing.Rel.lt ![#0, Rew.bShift t]) φ)

/-! ### Δ⁰₀: atoms, connectives, bounded quantifiers -/

/-- Strict syntactic Δ⁰₀ over `ℒₒᵣ`: atoms (including set-membership atoms — set
parameters do not count toward the hierarchy), connectives, and the bounded quantifier
forms. No unbounded quantifier, no second-order quantifier. -/
inductive IsDelta0 : ∀ {N n : ℕ}, SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n → Prop
  | rel {N n k : ℕ} (R : (ℒₒᵣ : Language).Rel k) (v : Fin k → Semiterm ℒₒᵣ ξ n) :
      IsDelta0 (N := N) (.rel R v)
  | nrel {N n k : ℕ} (R : (ℒₒᵣ : Language).Rel k) (v : Fin k → Semiterm ℒₒᵣ ξ n) :
      IsDelta0 (N := N) (.nrel R v)
  | bvar {N n : ℕ} (X : Fin N) (t : Semiterm ℒₒᵣ ξ n) : IsDelta0 (.bvar X t)
  | nbvar {N n : ℕ} (X : Fin N) (t : Semiterm ℒₒᵣ ξ n) : IsDelta0 (.nbvar X t)
  | fvar {N n : ℕ} (X : Ξ) (t : Semiterm ℒₒᵣ ξ n) : IsDelta0 (N := N) (.fvar X t)
  | nfvar {N n : ℕ} (X : Ξ) (t : Semiterm ℒₒᵣ ξ n) : IsDelta0 (N := N) (.nfvar X t)
  | verum {N n : ℕ} : IsDelta0 (N := N) (n := n) .verum
  | falsum {N n : ℕ} : IsDelta0 (N := N) (n := n) .falsum
  | and {N n : ℕ} {φ ψ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n} :
      IsDelta0 φ → IsDelta0 ψ → IsDelta0 (φ ⋏ ψ)
  | or {N n : ℕ} {φ ψ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n} :
      IsDelta0 φ → IsDelta0 ψ → IsDelta0 (φ ⋎ ψ)
  | ball {N n : ℕ} (t : Semiterm ℒₒᵣ ξ n)
      {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N (n + 1)} :
      IsDelta0 φ → IsDelta0 (ballLT t φ)
  | bex {N n : ℕ} (t : Semiterm ℒₒᵣ ξ n)
      {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N (n + 1)} :
      IsDelta0 φ → IsDelta0 (bexLT t φ)

/-- Every Δ⁰₀ formula is arithmetical. -/
theorem IsDelta0.isArithmetical {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n}
    (h : IsDelta0 φ) : IsArithmetical φ := by
  induction h with
  | rel R v => exact .rel R v
  | nrel R v => exact .nrel R v
  | bvar X t => exact .bvar X t
  | nbvar X t => exact .nbvar X t
  | fvar X t => exact .fvar X t
  | nfvar X t => exact .nfvar X t
  | verum => exact .verum
  | falsum => exact .falsum
  | and _ _ ihφ ihψ => exact .and ihφ ihψ
  | or _ _ ihφ ihψ => exact .or ihφ ihψ
  | ball t _ ih => exact .all₁ (.or (.nrel _ _) ih)
  | bex t _ ih => exact .exs₁ (.and (.rel _ _) ih)

/-- Negation preserves Δ⁰₀: the defined bounded forms are dual under the negation-normal
syntax (`∼(ballLT t φ) = bexLT t (∼φ)` definitionally). -/
theorem IsDelta0.neg {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n} (h : IsDelta0 φ) :
    IsDelta0 (∼φ) := by
  induction h with
  | rel R v => exact .nrel R v
  | nrel R v => exact .rel R v
  | bvar X t => exact .nbvar X t
  | nbvar X t => exact .bvar X t
  | fvar X t => exact .nfvar X t
  | nfvar X t => exact .fvar X t
  | verum => exact .falsum
  | falsum => exact .verum
  | and _ _ ihφ ihψ => exact .or ihφ ihψ
  | or _ _ ihφ ihψ => exact .and ihφ ihψ
  | ball t _ ih => exact .bex t ih
  | bex t _ ih => exact .ball t ih

/-! ### Σ⁰₁ and Π⁰₁: unbounded prefixes over Δ⁰₀ -/

/-- Strict syntactic Σ⁰₁: an `∃¹` prefix over Δ⁰₀. -/
inductive IsSigma01 : ∀ {N n : ℕ}, SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n → Prop
  | delta0 {N n : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n} :
      IsDelta0 φ → IsSigma01 φ
  | exs {N n : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N (n + 1)} :
      IsSigma01 φ → IsSigma01 (.exs₁ φ)

/-- Strict syntactic Π⁰₁: a `∀¹` prefix over Δ⁰₀. -/
inductive IsPi01 : ∀ {N n : ℕ}, SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n → Prop
  | delta0 {N n : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n} :
      IsDelta0 φ → IsPi01 φ
  | all {N n : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N (n + 1)} :
      IsPi01 φ → IsPi01 (.all₁ φ)

theorem IsSigma01.isArithmetical {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n}
    (h : IsSigma01 φ) : IsArithmetical φ := by
  induction h with
  | delta0 h0 => exact h0.isArithmetical
  | exs _ ih => exact .exs₁ ih

theorem IsPi01.isArithmetical {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n}
    (h : IsPi01 φ) : IsArithmetical φ := by
  induction h with
  | delta0 h0 => exact h0.isArithmetical
  | all _ ih => exact .all₁ ih

/-- Negation maps Σ⁰₁ to Π⁰₁. -/
theorem IsSigma01.neg {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n} (h : IsSigma01 φ) :
    IsPi01 (∼φ) := by
  induction h with
  | delta0 h0 => exact .delta0 h0.neg
  | exs _ ih => exact .all ih

/-- Negation maps Π⁰₁ to Σ⁰₁. -/
theorem IsPi01.neg {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n} (h : IsPi01 φ) :
    IsSigma01 (∼φ) := by
  induction h with
  | delta0 h0 => exact .delta0 h0.neg
  | all _ ih => exact .exs ih

/-! ### Regression fixtures

The boundary theorems of the hierarchy, executable. There is **no** normalization theorem
in this module, so there is nothing that could owe an evaluation-equivalence theorem yet;
the rule stands for any future transform. Universal closure and its exactly-once capture
fixture arrive with `Rca0Theory`. -/

/-- Fixture: set parameters do not alter the number-quantifier class — a formula whose
matrix consults a set parameter is Σ⁰₁ purely by its number prefix. -/
example (X : Ξ) : IsSigma01 (.exs₁ (.fvar X #0) :
    SecondOrder.Semiformula ℒₒᵣ Ξ ξ 0 0) :=
  .exs (.delta0 (.fvar X _))

/-- Fixture: negation swaps the classes on a concrete Σ⁰₁ formula. -/
example (X : Ξ) : IsPi01 (∼(.exs₁ (.fvar X #0) :
    SecondOrder.Semiformula ℒₒᵣ Ξ ξ 0 0)) :=
  (IsSigma01.exs (.delta0 (.fvar X _))).neg

/-- Fixture: second-order quantifiers inhabit neither class. -/
theorem not_isSigma01_exs₂ {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ (N + 1) n} :
    ¬ IsSigma01 (Semiformula.exs₂ φ) := by
  intro h
  cases h with
  | delta0 h0 => exact nomatch h0

/-- Fixture: second-order quantifiers inhabit neither class. -/
theorem not_isPi01_all₂ {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ (N + 1) n} :
    ¬ IsPi01 (Semiformula.all₂ φ) := by
  intro h
  cases h with
  | delta0 h0 => exact nomatch h0

/-- Fixture: **no implication-closure theorem** — the material implication of two strict
Σ⁰₁ formulas is not strictly Σ⁰₁ (its antecedent contributes an unbounded universal that
is not a bounded form). A closure theorem for either class would contradict this. -/
theorem not_isSigma01_imp_fixture :
    ¬ IsSigma01 ((∼(.exs₁ .verum) ⋎ .exs₁ .verum :
      SecondOrder.Semiformula ℒₒᵣ Empty ℕ 0 0)) := by
  intro h
  cases h with
  | delta0 h0 =>
    cases h0 with
    | or hl hr => exact nomatch hl

end RMFoundationBridge
