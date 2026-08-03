/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.Arithmetical

/-!
# F1 step 2 (second slice): the restricted rewrite-preservation API

Arithmeticality is **not** preserved by arbitrary second-order rewriting: a `Rew` may
substitute a set variable by a formula containing `∀²`/`∃²`. The admissibility condition
is exact, not an approximation: every `bv` and `fv` image is itself arithmetical
(`Rew.IsArithmetical`). This is the same restriction that separates Δ⁰₁ comprehension from
unrestricted comprehension, encoded here as a theorem hypothesis — and made executable by
the negative regression fixtures at the bottom, so no future generalization can quantify a
preservation theorem over unrestricted `Rew` without breaking the build.

Sanctioned API (everything is strict syntactic arithmeticality, never semantic
equivalence):

* number-variable rewriting preserves `IsArithmetical` unconditionally
  (`IsArithmetical.rew`);
* set-bound-variable renaming preserves it unconditionally (`IsArithmetical.bmap`);
* `Rew.IsArithmetical` holds for the identity (`Rew.isArithmetical_id`) and for
  set-variable renamings (`Rew.isArithmetical_rewrite`), and is preserved by composition
  (`Rew.IsArithmetical.comp`) and by the quantifier lift (`Rew.IsArithmetical.q`);
* applying an admissible rewrite preserves `IsArithmetical`
  (`IsArithmetical.app`);
* there is deliberately **no** preservation theorem over arbitrary `Rew`.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder

variable {L : Language} {Ξ ξ Ξ₁ Ξ₂ Ξ₃ ξ₁ ξ₂ : Type*}

/-! ### Unconditional preservations: number-variable rewriting, set-variable renaming -/

/-- Number-variable rewriting preserves arithmeticality unconditionally: `rewAux` maps
term positions and passes through the set layer structurally. Induction on the
derivation, with the rewrite generalized through the first-order quantifier lift. -/
theorem IsArithmetical.rew {n₁ N : ℕ} {φ : SecondOrder.Semiformula L Ξ ξ₁ N n₁}
    (h : IsArithmetical φ) :
    ∀ {n₂ : ℕ} (ω : FirstOrder.Rew L ξ₁ n₁ ξ₂ n₂),
      IsArithmetical (SecondOrder.Semiformula.rew ω φ) := by
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
  | all₁ _ ih => exact fun ω => .all₁ (ih ω.q)
  | exs₁ _ ih => exact fun ω => .exs₁ (ih ω.q)

/-- Set-bound-variable renaming preserves arithmeticality unconditionally: an ordinary
derivation transformation. -/
theorem IsArithmetical.bmap {N n : ℕ} {φ : SecondOrder.Semiformula L Ξ ξ N n}
    (h : IsArithmetical φ) :
    ∀ {M : ℕ} (f : Fin N → Fin M), IsArithmetical (SecondOrder.Semiformula.bmap f φ) := by
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
  | all₁ _ ih => exact fun f => .all₁ (ih f)
  | exs₁ _ ih => exact fun f => .exs₁ (ih f)

/-! ### Admissible second-order rewrites -/

/-- **The admissibility condition** for second-order rewriting over arithmetical formulas:
every set-variable image (bound and free) is itself arithmetical. Exactly the fault line
of restricted comprehension, as a hypothesis. -/
def _root_.LO.SecondOrder.Rew.IsArithmetical {N₁ N₂ : ℕ}
    (Ω : SecondOrder.Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) : Prop :=
  (∀ X, RMFoundationBridge.IsArithmetical (Ω.bv X)) ∧
    (∀ X, RMFoundationBridge.IsArithmetical (Ω.fv X))

/-- The identity rewrite is admissible. -/
theorem _root_.LO.SecondOrder.Rew.isArithmetical_id {N : ℕ} :
    (SecondOrder.Rew.id : SecondOrder.Rew L Ξ N Ξ N ξ).IsArithmetical :=
  ⟨fun X => .bvar X _, fun X => .fvar X _⟩

/-- Set-variable renamings are admissible. -/
theorem _root_.LO.SecondOrder.Rew.isArithmetical_rewrite {N : ℕ} (f : Ξ₁ → Ξ₂) :
    (SecondOrder.Rew.rewrite (L := L) (ξ := ξ) (N := N) f).IsArithmetical :=
  ⟨fun X => .bvar X _, fun X => .fvar (f X) _⟩

/-- The quantifier lift of an admissible rewrite is admissible: the fresh variable maps to
a membership atom, and every prior image is only renamed. -/
theorem _root_.LO.SecondOrder.Rew.IsArithmetical.q {N₁ N₂ : ℕ}
    {Ω : SecondOrder.Rew L Ξ₁ N₁ Ξ₂ N₂ ξ} (h : Ω.IsArithmetical) :
    Ω.q.IsArithmetical := by
  refine ⟨fun X => ?_, fun X => (h.2 X).bmap _⟩
  cases X using Fin.cases with
  | zero => exact .bvar 0 _
  | succ X => exact (h.1 X).bmap _

/-- Applying an admissible rewrite preserves arithmeticality: induction on the
derivation — membership cases consume the `bv`/`fv` admissibility images through the
unconditional number-variable rewriting lemma; there is no second-order case to
consider. Strict syntactic arithmeticality on both sides. -/
theorem IsArithmetical.app {N₁ n : ℕ} {φ : SecondOrder.Semiformula L Ξ₁ ξ N₁ n}
    (h : IsArithmetical φ) :
    ∀ {N₂ : ℕ} {Ω : SecondOrder.Rew L Ξ₁ N₁ Ξ₂ N₂ ξ},
      Ω.IsArithmetical → IsArithmetical (Ω.app φ) := by
  induction h with
  | rel R v => exact fun _ => .rel R _
  | nrel R v => exact fun _ => .nrel R _
  | bvar X t => exact fun hΩ => (hΩ.1 X).rew _
  | nbvar X t => exact fun hΩ => ((hΩ.1 X).rew _).neg
  | fvar X t => exact fun hΩ => (hΩ.2 X).rew _
  | nfvar X t => exact fun hΩ => ((hΩ.2 X).rew _).neg
  | verum => exact fun _ => .verum
  | falsum => exact fun _ => .falsum
  | and _ _ ihφ ihψ => exact fun hΩ => .and (ihφ hΩ) (ihψ hΩ)
  | or _ _ ihφ ihψ => exact fun hΩ => .or (ihφ hΩ) (ihψ hΩ)
  | all₁ _ ih => exact fun hΩ => .all₁ (ih hΩ)
  | exs₁ _ ih => exact fun hΩ => .exs₁ (ih hΩ)

/-- Composition preserves admissibility (needs the application theorem: composed images
are admissible rewrites applied to arithmetical images). -/
theorem _root_.LO.SecondOrder.Rew.IsArithmetical.comp {N₁ N₂ N₃ : ℕ}
    {Ω₂₃ : SecondOrder.Rew L Ξ₂ N₂ Ξ₃ N₃ ξ} {Ω₁₂ : SecondOrder.Rew L Ξ₁ N₁ Ξ₂ N₂ ξ}
    (h₂₃ : Ω₂₃.IsArithmetical) (h₁₂ : Ω₁₂.IsArithmetical) :
    (Ω₂₃.comp Ω₁₂).IsArithmetical :=
  ⟨fun X => (h₁₂.1 X).app h₂₃, fun X => (h₁₂.2 X).app h₂₃⟩

/-! ### Negative regression fixtures: the boundary is executable

A rewrite sending a set variable to `∃² ⊤` is not admissible, and applying it to the
corresponding membership atom produces a non-arithmetical formula. These fixtures keep the
restriction load-bearing in CI: an unconditional preservation theorem over arbitrary `Rew`
would contradict them. -/

/-- The inadmissible fixture: the single set variable maps to `∃² ⊤`. -/
def badRew : SecondOrder.Rew ℒₒᵣ Empty 1 Empty 0 ℕ where
  bv _ := SecondOrder.Semiformula.exs₂ ⊤
  fv X := X.elim

/-- `badRew` is not admissible. -/
theorem not_isArithmetical_badRew : ¬ badRew.IsArithmetical :=
  fun h => IsArithmetical.not_exs₂ (h.1 0)

/-- Applying `badRew` to the membership atom `#0 ∈# 0` (arithmetical) yields a
non-arithmetical formula: the restriction is semantic fault, not bookkeeping. -/
theorem not_isArithmetical_badRew_app :
    ¬ IsArithmetical
      (badRew.app (SecondOrder.Semiformula.bvar 0 (#0) :
        SecondOrder.Semiformula ℒₒᵣ Empty ℕ 1 1)) := by
  intro h
  exact IsArithmetical.not_exs₂ h

end RMFoundationBridge
