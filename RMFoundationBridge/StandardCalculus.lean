/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Foundation.SecondOrder.Derivation
import RMFoundationBridge.HenkinCalculus

/-!
# F3, third layer: the pinned standard calculus `l2VarWitnessLK.v1`

**What is pinned.** A bridge-defined, fully specified one-sided LK presentation of the
conventional two-sorted predicate logic *assumed* (not printed) in Simpson [Sim09] §I.2,
which specifies "the usual logical axioms and rules" over the two-sorted language L₂ and
assumes both sorts nonempty. The rule set follows Foundation's pinned
`LO.SecondOrder.Derivation` shape (`Foundation/SecondOrder/Derivation.lean` at the pinned
revision) **except for the second-order existential rule**: Foundation's `exs₂` witnesses
with an arbitrary formula (`φ/⟦ψ⟧`), which builds unrestricted comprehension into the
logic and is sound only for full semantics; here `exs₂` witnesses with a **set variable**
(`φ/⟦#0 ∈& X⟧`) — the only set terms L₂ has — so comprehension can enter only through
axioms; and **logical equality is included** (`eqRefl`, `eqSubst` — Simpson's "usual
logical axioms, including equality"), sound against structures whose equality symbol
means identity (`EqCorrect`, an explicit hypothesis of soundness). The judgment is
Prop-valued (only soundness is consumed downstream); the rules are otherwise verbatim,
over Foundation's own `Sequent`/`Semiproposition` syntax.

**Direct soundness, no embedding, no completeness.** `soundness` proves: a derivable
sequent has a true member in **every** `Struc₂ ℒₒᵣ` under every assignment of the free
number variables to the domain and of the free set variables to the designated
second-order part. The theory-level corollary `soundness_provable` needs the designated
part **nonempty** — exactly Simpson's nonempty-sort assumption, surfacing as the
hypothesis `M.sets.Nonempty` (a free set variable must have somewhere to point). The
deliberate contrast with the Henkin-safe calculus is checked below:
`stdLK_derives_exs₂_verum` shows this calculus proves `∃X ⊤` outright, which
`RMFoundationBridge.Derivable` cannot (it is sound for empty designated parts) — this
refutes the identity-preserving embedding of this calculus into the Henkin-safe one;
**no claim is made about the reverse direction**. Both calculi are independently
sound, and nothing here carries or licenses a derivability transfer between them.

**Semantic transport.** The one new lemma over `EvalTransport` is `eval_app`: evaluating
a second-order rewriting `Ω.app φ` (class substitution: every set variable maps to an
abstract) is evaluating `φ` at the **defined classes** of `Ω`'s abstracts. `free₁`,
`shift₁`, and the variable-witness substitution are all `Rew.app`s, so their sequent
rules become corollaries of one lemma. First-order bookkeeping (`free₀`, `shift₀`,
`φ/[t]`) is already covered by the unconditional `eval_rew`.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder

/-! ### Semantic transport for second-order rewriting -/

section evalApp

variable {L : Language} {M : Type*} [𝓈 : Structure L M] {Ξ Ξ₁ Ξ₂ ξ : Type*}

/-- Substituting a single term into a one-number-slot matrix, over arbitrary free sorts:
the specialization of `eval_rew` the atom cases of `eval_app` need. -/
theorem eval_subst_fin1 {𝕊 : Set (Set M)} {F : Ξ → Set M} {N n : ℕ}
    (ψ : SecondOrder.Semiformula L Ξ ξ N 1) (t : Semiterm L ξ n)
    (E : Fin N → Set M) (f : ξ → M) (e : Fin n → M) :
    (ψ/[t]).Eval 𝕊 F f E e ↔ ψ.Eval 𝕊 F f E ![Semiterm.val e f t] := by
  have h := eval_rew (𝕊 := 𝕊) (F := F) ψ (FirstOrder.Rew.subst ![t]) E f e
  have hf : (Semiterm.val e f ∘ (FirstOrder.Rew.subst ![t]) ∘ Semiterm.fvar) = f := by
    funext x
    simp
  have hb : (Semiterm.val e f ∘ (FirstOrder.Rew.subst ![t]) ∘ Semiterm.bvar) =
      ![Semiterm.val e f t] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => exact j.elim0
  rw [hf, hb] at h
  exact h

/-- The defined class of an abstract: the set it carves out of the domain. -/
def definedClass {N : ℕ} (𝕊 : Set (Set M)) (F : Ξ → Set M) (f : ξ → M)
    (E : Fin N → Set M) (ψ : SecondOrder.Semiformula L Ξ ξ N 1) : Set M :=
  {x | ψ.Eval 𝕊 F f E ![x]}

/-- Beneath a fresh set binder, the lifted rewriting's bound-slot classes are the new
set followed by the original classes. -/
theorem definedClass_q_bv {𝕊 : Set (Set M)} {f : ξ → M} {N₁ N₂ : ℕ}
    (Ω : SecondOrder.Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (F : Ξ₂ → Set M) (E : Fin N₂ → Set M)
    (X : Set M) :
    (fun Y => definedClass 𝕊 F f (X :> E) ((SecondOrder.Rew.q Ω).bv Y)) =
      (X :> fun Y => definedClass 𝕊 F f E (Ω.bv Y)) := by
  funext Y
  cases Y using Fin.cases with
  | zero =>
      rw [SecondOrder.Rew.q_bv_zero]
      ext x
      simp [definedClass]
  | succ Z =>
      show definedClass 𝕊 F f (X :> E)
        (SecondOrder.Semiformula.bmap Fin.succ (Ω.bv Z)) = _
      ext x
      simp only [definedClass, Set.mem_setOf_eq, Matrix.cons_val_succ]
      exact eval_bmap_succ (Ω.bv Z) X E ![x]

/-- Beneath a fresh set binder, the lifted rewriting's free-variable classes are the
original classes — the new set is invisible to them. -/
theorem definedClass_q_fv {𝕊 : Set (Set M)} {f : ξ → M} {N₁ N₂ : ℕ}
    (Ω : SecondOrder.Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (F : Ξ₂ → Set M) (E : Fin N₂ → Set M)
    (X : Set M) :
    (fun Y => definedClass 𝕊 F f (X :> E) ((SecondOrder.Rew.q Ω).fv Y)) =
      (fun Y => definedClass 𝕊 F f E (Ω.fv Y)) := by
  funext Y
  show definedClass 𝕊 F f (X :> E)
    (SecondOrder.Semiformula.bmap Fin.succ (Ω.fv Y)) = _
  ext x
  simp only [definedClass, Set.mem_setOf_eq]
  exact eval_bmap_succ (Ω.fv Y) X E ![x]

/-- **Evaluating a second-order rewriting**: `Ω.app φ` is `φ` evaluated at the defined
classes of `Ω`'s abstracts — `{x | Ω.fv X holds at x}` for each free set variable and
`{x | Ω.bv X holds at x}` for each bound set slot. The defined classes need not lie in
`𝕊`; only the set-quantifier cases consult `𝕊`, and they extend both sides
identically. -/
theorem eval_app {𝕊 : Set (Set M)} {f : ξ → M} :
    ∀ {N₁ n : ℕ} (φ : SecondOrder.Semiformula L Ξ₁ ξ N₁ n) {N₂ : ℕ}
      (Ω : SecondOrder.Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (F : Ξ₂ → Set M) (E : Fin N₂ → Set M)
      (e : Fin n → M),
      ((Ω.app φ).Eval 𝕊 F f E e ↔
        φ.Eval 𝕊 (fun X => definedClass 𝕊 F f E (Ω.fv X)) f
          (fun X => definedClass 𝕊 F f E (Ω.bv X)) e)
  | _, _, .rel R v, _, Ω, F, E, e => Iff.rfl
  | _, _, .nrel R v, _, Ω, F, E, e => Iff.rfl
  | _, _, .bvar X t, _, Ω, F, E, e => eval_subst_fin1 (Ω.bv X) t E f e
  | _, _, .nbvar X t, _, Ω, F, E, e =>
      (SecondOrder.Semiformula.EvalAux_neg ((Ω.bv X)/[t])).trans
        (not_congr (eval_subst_fin1 (𝕊 := 𝕊) (F := F) (Ω.bv X) t E f e))
  | _, _, .fvar X t, _, Ω, F, E, e => eval_subst_fin1 (Ω.fv X) t E f e
  | _, _, .nfvar X t, _, Ω, F, E, e =>
      (SecondOrder.Semiformula.EvalAux_neg ((Ω.fv X)/[t])).trans
        (not_congr (eval_subst_fin1 (𝕊 := 𝕊) (F := F) (Ω.fv X) t E f e))
  | _, _, .verum, _, Ω, F, E, e => Iff.rfl
  | _, _, .falsum, _, Ω, F, E, e => Iff.rfl
  | _, _, .and φ ψ, _, Ω, F, E, e =>
      and_congr (eval_app φ Ω F E e) (eval_app ψ Ω F E e)
  | _, _, .or φ ψ, _, Ω, F, E, e =>
      or_congr (eval_app φ Ω F E e) (eval_app ψ Ω F E e)
  | _, _, .all₁ φ, _, Ω, F, E, e =>
      forall_congr' fun x => eval_app φ Ω F E (x :> e)
  | _, _, .exs₁ φ, _, Ω, F, E, e =>
      exists_congr fun x => eval_app φ Ω F E (x :> e)
  | _, _, .all₂ φ, _, Ω, F, E, e =>
      forall_congr' fun X => imp_congr_right fun _ => by
        have h := eval_app (𝕊 := 𝕊) (f := f) φ (SecondOrder.Rew.q Ω) F (X :> E) e
        rw [definedClass_q_bv, definedClass_q_fv] at h
        exact h
  | _, _, .exs₂ φ, _, Ω, F, E, e =>
      exists_congr fun X => and_congr Iff.rfl (by
        have h := eval_app (𝕊 := 𝕊) (f := f) φ (SecondOrder.Rew.q Ω) F (X :> E) e
        rw [definedClass_q_bv, definedClass_q_fv] at h
        exact h)

end evalApp

/-! ### Sequent-level transport corollaries

All at the sequent surface: `Proposition ℒₒᵣ` entries, empty slot valuations, free
variables carrying everything. -/

section sequentTransport

variable {M : Type*} [𝓈 : Structure ℒₒᵣ M] {𝕊 : Set (Set M)}

/-- Negation at the evaluation surface. -/
theorem eval_neg' {N n : ℕ} {Ξ ξ : Type*} {F : Ξ → Set M} {f : ξ → M}
    {E : Fin N → Set M} {e : Fin n → M} (φ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n) :
    (∼φ).Eval 𝕊 F f E e ↔ ¬ φ.Eval 𝕊 F f E e :=
  SecondOrder.Semiformula.EvalAux_neg φ

/-- `shift₀` under a prepended number value is the original evaluation. -/
theorem eval_shift₀ (φ : SecondOrder.Proposition ℒₒᵣ) (F : ℕ → Set M) (f : ℕ → M)
    (x : M) :
    (SecondOrder.Semiproposition.shift₀ φ).Eval 𝕊 F (x :>ₙ f) ![] ![] ↔
      φ.Eval 𝕊 F f ![] ![] := by
  have h := eval_rew (𝕊 := 𝕊) (F := F) φ (FirstOrder.Rew.shift (L := ℒₒᵣ) (n := 0)) ![] (x :>ₙ f) ![]
  have hf : (Semiterm.val ![] (x :>ₙ f) ∘ (FirstOrder.Rew.shift (L := ℒₒᵣ) (n := 0)) ∘ Semiterm.fvar) = f := by
    funext k
    simp
  have hb : (Semiterm.val ![] (x :>ₙ f) ∘ (FirstOrder.Rew.shift (L := ℒₒᵣ) (n := 0)) ∘ Semiterm.bvar) =
      (![] : Fin 0 → M) := by
    funext i
    exact i.elim0
  rw [hf, hb] at h
  exact h

/-- `free₀` under a prepended number value is evaluation at that value in the freed
slot. -/
theorem eval_free₀ (φ : SecondOrder.Semiproposition ℒₒᵣ 0 1) (F : ℕ → Set M)
    (f : ℕ → M) (x : M) :
    (SecondOrder.Semiproposition.free₀ φ).Eval 𝕊 F (x :>ₙ f) ![] ![] ↔
      φ.Eval 𝕊 F f ![] ![x] := by
  have h := eval_rew (𝕊 := 𝕊) (F := F) φ (FirstOrder.Rew.free (L := ℒₒᵣ) (n := 0)) ![] (x :>ₙ f) ![]
  have hf : (Semiterm.val ![] (x :>ₙ f) ∘ (FirstOrder.Rew.free (L := ℒₒᵣ) (n := 0)) ∘ Semiterm.fvar) = f := by
    funext k
    simp
  have hb : (Semiterm.val ![] (x :>ₙ f) ∘ (FirstOrder.Rew.free (L := ℒₒᵣ) (n := 0)) ∘ Semiterm.bvar) =
      ![x] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => exact j.elim0
  rw [hf, hb] at h
  exact h

/-- Term instantiation at the sequent surface. -/
theorem eval_subst_term (φ : SecondOrder.Semiproposition ℒₒᵣ 0 1)
    (t : Semiterm ℒₒᵣ ℕ 0) (F : ℕ → Set M) (f : ℕ → M) :
    (φ/[t]).Eval 𝕊 F f ![] ![] ↔ φ.Eval 𝕊 F f ![] ![Semiterm.val ![] f t] :=
  eval_subst_fin1 φ t ![] f ![]

/-- `shift₁` under a prepended set value is the original evaluation. -/
theorem eval_shift₁ (φ : SecondOrder.Proposition ℒₒᵣ) (F : ℕ → Set M) (f : ℕ → M)
    (X : Set M) :
    (SecondOrder.Semiproposition.shift₁ φ).Eval 𝕊 (X :>ₙ F) f ![] ![] ↔
      φ.Eval 𝕊 F f ![] ![] := by
  have h := eval_app (𝕊 := 𝕊) (f := f) φ (SecondOrder.Rew.shift) (X :>ₙ F) ![] ![]
  have hF : (fun Y => definedClass 𝕊 (X :>ₙ F) f ![]
      ((SecondOrder.Rew.shift (L := ℒₒᵣ)).fv Y)) = F := by
    funext k
    ext x
    simp [definedClass]
  have hE : (fun Y => definedClass 𝕊 (X :>ₙ F) f ![]
      ((SecondOrder.Rew.shift (L := ℒₒᵣ)).bv Y)) = (![] : Fin 0 → Set M) := by
    funext i
    exact i.elim0
  rw [hF, hE] at h
  exact h

/-- `free₁` under a prepended set value is evaluation at that set in the freed slot. -/
theorem eval_free₁ (φ : SecondOrder.Semiproposition ℒₒᵣ 1 0) (F : ℕ → Set M)
    (f : ℕ → M) (X : Set M) :
    (SecondOrder.Semiproposition.free₁ φ).Eval 𝕊 (X :>ₙ F) f ![] ![] ↔
      φ.Eval 𝕊 F f ![X] ![] := by
  have h := eval_app (𝕊 := 𝕊) (f := f) φ (SecondOrder.Rew.free) (X :>ₙ F) ![] ![]
  have hF : (fun Y => definedClass 𝕊 (X :>ₙ F) f ![]
      ((SecondOrder.Rew.free (L := ℒₒᵣ) (N := 0)).fv Y)) = F := by
    funext k
    ext x
    simp [definedClass]
  have hE : (fun Y => definedClass 𝕊 (X :>ₙ F) f ![]
      ((SecondOrder.Rew.free (L := ℒₒᵣ) (N := 0)).bv Y)) = ![X] := by
    funext i
    cases i using Fin.cases with
    | zero =>
        have hbv : (SecondOrder.Rew.free (L := ℒₒᵣ) (ξ := ℕ) (N := 0)).bv 0 =
            SecondOrder.Semiformula.fvar 0 (#0 : Semiterm ℒₒᵣ ℕ 1) :=
          SecondOrder.Rew.free_bvar_last 0
        rw [hbv]
        ext x
        simp [definedClass]
    | succ j => exact j.elim0
  rw [hF, hE] at h
  exact h

/-- Variable-witness set instantiation: substituting the abstract `{y | y ∈ X_k}` is
evaluation at the assigned set `F k` itself. -/
theorem eval_subst_var (φ : SecondOrder.Semiproposition ℒₒᵣ 1 0) (k : ℕ)
    (F : ℕ → Set M) (f : ℕ → M) :
    (SecondOrder.Semiproposition.subst₁ φ
        ![(SecondOrder.Semiformula.fvar k (#0 : Semiterm ℒₒᵣ ℕ 1) : SecondOrder.Semiformula ℒₒᵣ ℕ ℕ 0 1)]).Eval
        𝕊 F f ![] ![] ↔
      φ.Eval 𝕊 F f ![F k] ![] := by
  have h := eval_app (𝕊 := 𝕊) (f := f) φ
    (SecondOrder.Rew.subst ![(SecondOrder.Semiformula.fvar k (#0 : Semiterm ℒₒᵣ ℕ 1) : SecondOrder.Semiformula ℒₒᵣ ℕ ℕ 0 1)])
    F ![] ![]
  have hF : (fun Y => definedClass 𝕊 F f ![]
      ((SecondOrder.Rew.subst
        ![(SecondOrder.Semiformula.fvar k (#0 : Semiterm ℒₒᵣ ℕ 1) : SecondOrder.Semiformula ℒₒᵣ ℕ ℕ 0 1)]).fv Y)) = F := by
    funext m
    ext x
    simp [definedClass]
  have hE : (fun Y => definedClass 𝕊 F f ![]
      ((SecondOrder.Rew.subst
        ![(SecondOrder.Semiformula.fvar k (#0 : Semiterm ℒₒᵣ ℕ 1) : SecondOrder.Semiformula ℒₒᵣ ℕ ℕ 0 1)]).bv Y)) =
      ![F k] := by
    funext i
    cases i using Fin.cases with
    | zero =>
        ext x
        simp [definedClass]
    | succ j => exact j.elim0
  rw [hF, hE] at h
  exact h

/-- Evaluating an equality atom is the structure's equality relation at the term
values. -/
theorem eval_eqF (t₁ t₂ : Semiterm ℒₒᵣ ℕ 0) (F : ℕ → Set M) (f : ℕ → M) :
    (eqF t₁ t₂ : SecondOrder.Proposition ℒₒᵣ).Eval 𝕊 F f ![] ![] ↔
      Structure.rel (L := ℒₒᵣ) (M := M) Language.ORing.Rel.eq
        ![Semiterm.val ![] f t₁, Semiterm.val ![] f t₂] := by
  have hv : (Semiterm.val (![] : Fin 0 → M) f ∘ ![t₁, t₂]) =
      ![Semiterm.val ![] f t₁, Semiterm.val ![] f t₂] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j =>
        cases j using Fin.cases with
        | zero => simp
        | succ k => exact k.elim0
  show Structure.rel (L := ℒₒᵣ) (M := M) Language.ORing.Rel.eq
    (Semiterm.val ![] f ∘ ![t₁, t₂]) ↔ _
  rw [hv]

/-- A coerced sentence evaluates independently of the free-variable assignments,
as its sentence satisfaction. -/
theorem eval_emb_sentence (σ : SecondOrder.Sentence ℒₒᵣ) (F : ℕ → Set M) (f : ℕ → M) :
    ((σ : SecondOrder.Proposition ℒₒᵣ)).Eval 𝕊 F f ![] ![] ↔
      σ.Eval 𝕊 Empty.elim Empty.elim ![] ![] := by
  have h₁ := eval_app (𝕊 := 𝕊) (f := f)
    (FirstOrder.Rewriting.emb (ξ := ℕ) σ) (SecondOrder.Rew.emb (ο := Empty)) F ![] ![]
  have hbv : (fun X => definedClass 𝕊 F f ![]
      ((SecondOrder.Rew.emb (L := ℒₒᵣ) (Ξ := ℕ) (ξ := ℕ) (ο := Empty) (N := 0)).bv X)) =
      (![] : Fin 0 → Set M) := funext fun i => i.elim0
  have hfv : (fun X => definedClass 𝕊 F f ![]
      ((SecondOrder.Rew.emb (L := ℒₒᵣ) (Ξ := ℕ) (ξ := ℕ) (ο := Empty) (N := 0)).fv X)) =
      (Empty.elim : Empty → Set M) := funext fun X => X.elim
  rw [hbv, hfv] at h₁
  have h₂ := eval_rew (𝕊 := 𝕊) (F := (Empty.elim : Empty → Set M)) σ
    (FirstOrder.Rew.emb (L := ℒₒᵣ) (o := Empty) (ξ := ℕ) (n := 0)) ![] f ![]
  have hf : (Semiterm.val ![] f ∘
      (FirstOrder.Rew.emb (L := ℒₒᵣ) (o := Empty) (ξ := ℕ) (n := 0)) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := funext fun x => x.elim
  have hb : (Semiterm.val ![] f ∘
      (FirstOrder.Rew.emb (L := ℒₒᵣ) (o := Empty) (ξ := ℕ) (n := 0)) ∘ Semiterm.bvar) =
      (![] : Fin 0 → M) := funext fun i => i.elim0
  rw [hf, hb] at h₂
  exact h₁.trans h₂

end sequentTransport

/-- **Equality-correct semantics**: the structure interprets the equality symbol as
identity — the hypothesis Simpson's logical equality axioms are sound against. The
standard interpretation on ℕ satisfies it definitionally
(`standardInterpretation_eq`). -/
def EqCorrect (M : Struc₂ ℒₒᵣ) : Prop :=
  ∀ a b : M.Dom, Structure.rel (L := ℒₒᵣ) (M := M.Dom) Language.ORing.Rel.eq ![a, b] ↔ a = b

/-! ### The pinned standard calculus -/

/-- **`l2VarWitnessLK.v1`** — the pinned standard calculus: a one-sided LK for the
two-sorted language L₂, over Foundation's own `Sequent`/`Semiproposition` syntax,
mirroring Foundation's pinned `LO.SecondOrder.Derivation` rule for rule with a single
change: `exs₂` witnesses with a **set variable** (the only set terms L₂ has), never a
formula. This is the conventional two-sorted predicate logic assumed in Simpson [Sim09]
§I.2 (nonempty sorts, "usual logical axioms and rules"), in a fully specified LK
presentation of the bridge's own choosing — the identification with Simpson's prose is a
documented reading, not a checked theorem. Prop-valued: only soundness is consumed. -/
inductive StdLK : SecondOrder.Sequent ℒₒᵣ → Prop
  | identity {φ : SecondOrder.Proposition ℒₒᵣ} : StdLK [φ, ∼φ]
  | cut {φ : SecondOrder.Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ} :
      StdLK (φ :: Γ) → StdLK (∼φ :: Γ) → StdLK Γ
  | wk {Γ Δ : SecondOrder.Sequent ℒₒᵣ} : StdLK Γ → Γ ⊆ Δ → StdLK Δ
  | verum : StdLK [⊤]
  | and {φ ψ : SecondOrder.Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ} :
      StdLK (φ :: Γ) → StdLK (ψ :: Γ) → StdLK (φ ⋏ ψ :: Γ)
  | or {φ ψ : SecondOrder.Proposition ℒₒᵣ} {Γ : SecondOrder.Sequent ℒₒᵣ} :
      StdLK (φ :: ψ :: Γ) → StdLK (φ ⋎ ψ :: Γ)
  | all₁ {φ : SecondOrder.Semiproposition ℒₒᵣ 0 1} {Γ : SecondOrder.Sequent ℒₒᵣ} :
      StdLK (φ.free₀ :: SecondOrder.Sequent.shift₀ Γ) → StdLK ((∀¹ φ) :: Γ)
  | exs₁ {φ : SecondOrder.Semiproposition ℒₒᵣ 0 1} {Γ : SecondOrder.Sequent ℒₒᵣ}
      (t : Semiterm ℒₒᵣ ℕ 0) : StdLK (φ/[t] :: Γ) → StdLK ((∃¹ φ) :: Γ)
  | all₂ {φ : SecondOrder.Semiproposition ℒₒᵣ 1 0} {Γ : SecondOrder.Sequent ℒₒᵣ} :
      StdLK (φ.free₁ :: SecondOrder.Sequent.shift₁ Γ) → StdLK ((∀² φ) :: Γ)
  | exs₂ {φ : SecondOrder.Semiproposition ℒₒᵣ 1 0} {Γ : SecondOrder.Sequent ℒₒᵣ} (X : ℕ) :
      StdLK (SecondOrder.Semiproposition.subst₁ φ
        ![(SecondOrder.Semiformula.fvar X (#0 : Semiterm ℒₒᵣ ℕ 1) : SecondOrder.Semiformula ℒₒᵣ ℕ ℕ 0 1)] :: Γ) →
      StdLK ((∃² φ) :: Γ)
  | eqRefl (t : Semiterm ℒₒᵣ ℕ 0) : StdLK [eqF t t]
  | eqSubst (t₁ t₂ : Semiterm ℒₒᵣ ℕ 0) (φ : SecondOrder.Semiproposition ℒₒᵣ 0 1) :
      StdLK [∼(eqF t₁ t₂), ∼(φ/[t₁]), φ/[t₂]]

/-- **The deliberate contrast with the Henkin-safe calculus**: the standard calculus
proves `∃X ⊤` outright — the nonempty-sort assumption at work. `Derivable ∅` cannot
prove this sentence (it is sound for structures with an empty designated part). -/
theorem stdLK_derives_exs₂_verum :
    StdLK [(∃² (⊤ : SecondOrder.Semiproposition ℒₒᵣ 1 0) : SecondOrder.Proposition ℒₒᵣ)] :=
  StdLK.exs₂ 0 StdLK.verum

/-! ### Soundness -/

/-- **Direct soundness of the pinned standard calculus** — for every second-order
structure, arbitrary designated part: a derivable sequent has a true member under every
assignment of free set variables **into the designated part** and free number variables
into the domain. Nonemptiness of the part is not needed here (it is needed to *produce*
an assignment, in `soundness_provable`); no completeness claim is made anywhere. -/
theorem StdLK.soundness {Δ : SecondOrder.Sequent ℒₒᵣ} (d : StdLK Δ) (M : Struc₂ ℒₒᵣ)
    (heq : EqCorrect M) :
    ∀ (F : ℕ → Set M.Dom), (∀ k, F k ∈ M.sets) → ∀ f : ℕ → M.Dom,
      ∃ φ ∈ Δ, φ.Eval M.sets F f ![] ![] := by
  induction d with
  | @identity φ =>
      intro F hF f
      by_cases h : φ.Eval M.sets F f ![] ![]
      · exact ⟨φ, by simp, h⟩
      · exact ⟨∼φ, by simp, (eval_neg' φ).mpr h⟩
  | @cut φ Γ _ _ ih₁ ih₂ =>
      intro F hF f
      obtain ⟨ψ, hmem, hψ⟩ := ih₁ F hF f
      rcases List.mem_cons.mp hmem with rfl | hmem
      · obtain ⟨χ, hmem', hχ⟩ := ih₂ F hF f
        rcases List.mem_cons.mp hmem' with rfl | hmem'
        · exact absurd hψ ((eval_neg' ψ).mp hχ)
        · exact ⟨χ, hmem', hχ⟩
      · exact ⟨ψ, hmem, hψ⟩
  | @wk Γ Δ _ hsub ih =>
      intro F hF f
      obtain ⟨ψ, hmem, hψ⟩ := ih F hF f
      exact ⟨ψ, hsub hmem, hψ⟩
  | verum =>
      intro F hF f
      exact ⟨⊤, by simp, trivial⟩
  | @and φ ψ Γ _ _ ih₁ ih₂ =>
      intro F hF f
      obtain ⟨χ₁, hmem₁, hχ₁⟩ := ih₁ F hF f
      rcases List.mem_cons.mp hmem₁ with h₁ | hmem₁
      · obtain ⟨χ₂, hmem₂, hχ₂⟩ := ih₂ F hF f
        rcases List.mem_cons.mp hmem₂ with h₂ | hmem₂
        · exact ⟨φ ⋏ ψ, by simp, ⟨h₁ ▸ hχ₁, h₂ ▸ hχ₂⟩⟩
        · exact ⟨χ₂, by simp [hmem₂], hχ₂⟩
      · exact ⟨χ₁, by simp [hmem₁], hχ₁⟩
  | @or φ ψ Γ _ ih =>
      intro F hF f
      obtain ⟨χ, hmem, hχ⟩ := ih F hF f
      rcases List.mem_cons.mp hmem with h₁ | hmem
      · exact ⟨φ ⋎ ψ, by simp, Or.inl (h₁ ▸ hχ)⟩
      · rcases List.mem_cons.mp hmem with h₂ | hmem
        · exact ⟨φ ⋎ ψ, by simp, Or.inr (h₂ ▸ hχ)⟩
        · exact ⟨χ, by simp [hmem], hχ⟩
  | @all₁ φ Γ _ ih =>
      intro F hF f
      by_cases hΓ : ∃ ψ ∈ Γ, ψ.Eval M.sets F f ![] ![]
      · obtain ⟨ψ, hmem, hψ⟩ := hΓ
        exact ⟨ψ, by simp [hmem], hψ⟩
      · refine ⟨∀¹ φ, by simp, ?_⟩
        intro x
        obtain ⟨ψ, hmem, hψ⟩ := ih F hF (x :>ₙ f)
        rcases List.mem_cons.mp hmem with h₁ | hmem
        · exact (eval_free₀ φ F f x).mp (h₁ ▸ hψ)
        · obtain ⟨χ, hχmem, hχeq⟩ := List.mem_map.mp hmem
          exact absurd ⟨χ, hχmem, (eval_shift₀ χ F f x).mp (hχeq ▸ hψ)⟩ hΓ
  | @exs₁ φ Γ t _ ih =>
      intro F hF f
      obtain ⟨ψ, hmem, hψ⟩ := ih F hF f
      rcases List.mem_cons.mp hmem with h₁ | hmem
      · exact ⟨∃¹ φ, by simp,
          ⟨Semiterm.val ![] f t, (eval_subst_term φ t F f).mp (h₁ ▸ hψ)⟩⟩
      · exact ⟨ψ, by simp [hmem], hψ⟩
  | @all₂ φ Γ _ ih =>
      intro F hF f
      by_cases hΓ : ∃ ψ ∈ Γ, ψ.Eval M.sets F f ![] ![]
      · obtain ⟨ψ, hmem, hψ⟩ := hΓ
        exact ⟨ψ, by simp [hmem], hψ⟩
      · refine ⟨∀² φ, by simp, ?_⟩
        intro X hX
        obtain ⟨ψ, hmem, hψ⟩ := ih (X :>ₙ F) (by
          intro k
          cases k with
          | zero => exact hX
          | succ k => exact hF k) f
        rcases List.mem_cons.mp hmem with h₁ | hmem
        · exact (eval_free₁ φ F f X).mp (h₁ ▸ hψ)
        · obtain ⟨χ, hχmem, hχeq⟩ := List.mem_map.mp hmem
          exact absurd ⟨χ, hχmem, (eval_shift₁ χ F f X).mp (hχeq ▸ hψ)⟩ hΓ
  | @exs₂ φ Γ X _ ih =>
      intro F hF f
      obtain ⟨ψ, hmem, hψ⟩ := ih F hF f
      rcases List.mem_cons.mp hmem with h₁ | hmem
      · exact ⟨∃² φ, by simp,
          ⟨F X, hF X, (eval_subst_var φ X F f).mp (h₁ ▸ hψ)⟩⟩
      · exact ⟨ψ, by simp [hmem], hψ⟩
  | eqRefl t =>
      intro F hF f
      refine ⟨eqF t t, by simp, ?_⟩
      exact (eval_eqF t t F f).mpr ((heq _ _).mpr rfl)
  | eqSubst t₁ t₂ φ =>
      intro F hF f
      by_cases he : (eqF t₁ t₂ : SecondOrder.Proposition ℒₒᵣ).Eval M.sets F f ![] ![]
      · by_cases hφ : φ.Eval M.sets F f ![] ![Semiterm.val ![] f t₁]
        · refine ⟨φ/[t₂], by simp, ?_⟩
          rw [eval_subst_term]
          have hval : Semiterm.val ![] f t₁ = Semiterm.val ![] f t₂ :=
            (heq _ _).mp ((eval_eqF t₁ t₂ F f).mp he)
          rw [← hval]
          exact hφ
        · refine ⟨∼(φ/[t₁]), by simp, ?_⟩
          rw [eval_neg' (φ/[t₁]), eval_subst_term]
          exact hφ
      · exact ⟨∼(eqF t₁ t₂), by simp, (eval_neg' _).mpr he⟩

/-! ### Theory-level provability and its soundness -/

/-- Provability of a sentence from a sentence theory in the pinned standard calculus,
mirroring Foundation's `Schema.Derivation` shape: a finite list of axiom instances from
the theory, with the goal derivable from their negations. -/
def StdLKProvable (Γ : Set (SecondOrder.Sentence ℒₒᵣ)) (σ : SecondOrder.Sentence ℒₒᵣ) :
    Prop :=
  ∃ axms : List (SecondOrder.Sentence ℒₒᵣ), (∀ τ ∈ axms, τ ∈ Γ) ∧
    StdLK ((σ : SecondOrder.Proposition ℒₒᵣ) ::
      axms.map fun (τ : SecondOrder.Sentence ℒₒᵣ) => ∼(τ : SecondOrder.Proposition ℒₒᵣ))

/-- **Theory-level soundness of the pinned standard calculus**: over any second-order
structure whose designated part is **nonempty** (Simpson's nonempty-sort assumption,
surfacing exactly here — a free set variable needs somewhere to point), a sentence
provable from `Γ` holds in every model of `Γ`. Direct soundness — no embedding into the
Henkin-safe calculus and no completeness theorem anywhere. -/
theorem StdLKProvable.soundness {Γ : Set (SecondOrder.Sentence ℒₒᵣ)}
    {σ : SecondOrder.Sentence ℒₒᵣ} (h : StdLKProvable Γ σ) (M : Struc₂ ℒₒᵣ)
    (hne : M.sets.Nonempty) (heq : EqCorrect M) (hΓ : ∀ τ ∈ Γ, M ⊧ τ) : M ⊧ σ := by
  obtain ⟨axms, haxms, hd⟩ := h
  obtain ⟨S₀, hS₀⟩ := hne
  have hdom : Nonempty M.Dom := M.nonempty
  obtain ⟨x₀⟩ := hdom
  obtain ⟨ψ, hmem, hψ⟩ := hd.soundness M heq (fun _ => S₀) (fun _ => hS₀) (fun _ => x₀)
  rcases List.mem_cons.mp hmem with h₁ | hmem
  · exact models_def.mpr ((eval_emb_sentence σ _ _).mp (h₁ ▸ hψ))
  · obtain ⟨τ, hτmem, hτeq⟩ := List.mem_map.mp hmem
    rw [← hτeq] at hψ
    exact absurd
      ((eval_emb_sentence τ _ _).mpr (models_def.mp (hΓ τ (haxms τ hτmem))))
      ((eval_neg' _).mp hψ)

end RMFoundationBridge
