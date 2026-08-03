/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.Hierarchy

/-!
# F1 step 2 (fourth slice): substitution preservation for the hierarchy classes

The schemas of `Rca0Theory` build their instances by substituting terms into class
matrices, so class preservation under rewriting must exist **before** any schema consumes
the classes. Two operations are sanctioned:

* **number-variable rewriting** (`IsDelta0.rew`, `IsSigma01.rew`, `IsPi01.rew`): each
  bounded form commutes with rewriting (`rew_ballLT`, `rew_bexLT` — equations of literal
  syntax, not semantic equivalences), so the classes are preserved unconditionally;
* **set-bound-variable renaming** (`IsDelta0.bmap`, `IsSigma01.bmap`, `IsPi01.bmap`):
  term positions are untouched, so preservation is definitional.

Second-order substitution is *not* given a preservation theorem here: the classes live
under `IsArithmetical`, and any future need routes through the sanctioned admissible-`Rew`
API of `ArithmeticalRew`, never a fresh unconditional lemma.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder

variable {Ξ ξ ξ₁ ξ₂ : Type*} {N n n₁ n₂ : ℕ}

/-! ### The bounded forms commute with number-variable rewriting -/

/-- Rewriting a bounded universal: literal-syntax equation (the fresh variable is fixed,
the bound commutes with the shift). -/
theorem rew_ballLT (ω : FirstOrder.Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) (t : Semiterm ℒₒᵣ ξ₁ n₁)
    (φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ₁ N (n₁ + 1)) :
    ω ▹ ballLT t φ = ballLT (ω t) (ω.q ▹ φ) := by
  have hv : (fun i => ω.q (![#0, Rew.bShift t] i)) =
      ![(#0 : Semiterm ℒₒᵣ ξ₂ (n₂ + 1)), Rew.bShift (ω t)] := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j =>
      induction j using Fin.cases with
      | zero => simp
      | succ k => exact k.elim0
  have hL : ω ▹ ballLT t φ =
      SecondOrder.Semiformula.all₁
        ((SecondOrder.Semiformula.nrel Language.ORing.Rel.lt
          fun i => ω.q (![#0, Rew.bShift t] i)).or (ω.q ▹ φ)) := rfl
  rw [hL, hv]
  rfl

/-- Rewriting a bounded existential: literal-syntax equation. -/
theorem rew_bexLT (ω : FirstOrder.Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) (t : Semiterm ℒₒᵣ ξ₁ n₁)
    (φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ₁ N (n₁ + 1)) :
    ω ▹ bexLT t φ = bexLT (ω t) (ω.q ▹ φ) := by
  have hv : (fun i => ω.q (![#0, Rew.bShift t] i)) =
      ![(#0 : Semiterm ℒₒᵣ ξ₂ (n₂ + 1)), Rew.bShift (ω t)] := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j =>
      induction j using Fin.cases with
      | zero => simp
      | succ k => exact k.elim0
  have hL : ω ▹ bexLT t φ =
      SecondOrder.Semiformula.exs₁
        ((SecondOrder.Semiformula.rel Language.ORing.Rel.lt
          fun i => ω.q (![#0, Rew.bShift t] i)).and (ω.q ▹ φ)) := rfl
  rw [hL, hv]
  rfl

/-! ### Class preservation under number-variable rewriting -/

/-- Δ⁰₀ is preserved by number-variable rewriting, unconditionally. -/
theorem IsDelta0.rew {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ₁ N n₁} (h : IsDelta0 φ) :
    ∀ {n₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂),
      IsDelta0 (ω ▹ φ) := by
  induction h with
  | rel R v => exact fun ω => .rel R _
  | nrel R v => exact fun ω => .nrel R _
  | bvar X t => exact fun ω => .bvar X _
  | nbvar X t => exact fun ω => .nbvar X _
  | fvar X t => exact fun ω => .fvar X _
  | nfvar X t => exact fun ω => .nfvar X _
  | verum => exact fun ω => .verum
  | falsum => exact fun ω => .falsum
  | and _ _ ihφ ihψ => exact fun ω => .and (ihφ ω) (ihψ ω)
  | or _ _ ihφ ihψ => exact fun ω => .or (ihφ ω) (ihψ ω)
  | ball t _ ih => exact fun ω => rew_ballLT ω t _ ▸ IsDelta0.ball (ω t) (ih ω.q)
  | bex t _ ih => exact fun ω => rew_bexLT ω t _ ▸ IsDelta0.bex (ω t) (ih ω.q)

/-- Σ⁰₁ is preserved by number-variable rewriting, unconditionally. -/
theorem IsSigma01.rew {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ₁ N n₁} (h : IsSigma01 φ) :
    ∀ {n₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂),
      IsSigma01 (ω ▹ φ) := by
  induction h with
  | delta0 h0 => exact fun ω => .delta0 (h0.rew ω)
  | exs _ ih => exact fun ω => .exs (ih ω.q)

/-- Π⁰₁ is preserved by number-variable rewriting, unconditionally. -/
theorem IsPi01.rew {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ₁ N n₁} (h : IsPi01 φ) :
    ∀ {n₂ : ℕ} (ω : FirstOrder.Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂),
      IsPi01 (ω ▹ φ) := by
  induction h with
  | delta0 h0 => exact fun ω => .delta0 (h0.rew ω)
  | all _ ih => exact fun ω => .all (ih ω.q)

/-! ### Class preservation under set-bound-variable renaming (definitional) -/

/-- Δ⁰₀ is preserved by set-bvar renaming: term positions are untouched. -/
theorem IsDelta0.bmap {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n} (h : IsDelta0 φ) :
    ∀ {M : ℕ} (f : Fin N → Fin M), IsDelta0 (SecondOrder.Semiformula.bmap f φ) := by
  induction h with
  | rel R v => exact fun f => .rel R _
  | nrel R v => exact fun f => .nrel R _
  | bvar X t => exact fun f => .bvar (f X) _
  | nbvar X t => exact fun f => .nbvar (f X) _
  | fvar X t => exact fun f => .fvar X _
  | nfvar X t => exact fun f => .nfvar X _
  | verum => exact fun f => .verum
  | falsum => exact fun f => .falsum
  | and _ _ ihφ ihψ => exact fun f => .and (ihφ f) (ihψ f)
  | or _ _ ihφ ihψ => exact fun f => .or (ihφ f) (ihψ f)
  | ball t _ ih => exact fun f => .ball t (ih f)
  | bex t _ ih => exact fun f => .bex t (ih f)

/-- Σ⁰₁ is preserved by set-bvar renaming. -/
theorem IsSigma01.bmap {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n} (h : IsSigma01 φ) :
    ∀ {M : ℕ} (f : Fin N → Fin M), IsSigma01 (SecondOrder.Semiformula.bmap f φ) := by
  induction h with
  | delta0 h0 => exact fun f => .delta0 (h0.bmap f)
  | exs _ ih => exact fun f => .exs (ih f)

/-- Π⁰₁ is preserved by set-bvar renaming. -/
theorem IsPi01.bmap {φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n} (h : IsPi01 φ) :
    ∀ {M : ℕ} (f : Fin N → Fin M), IsPi01 (SecondOrder.Semiformula.bmap f φ) := by
  induction h with
  | delta0 h0 => exact fun f => .delta0 (h0.bmap f)
  | all _ ih => exact fun f => .all (ih f)

end RMFoundationBridge
