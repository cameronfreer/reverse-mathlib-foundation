/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.ParamOracle
import RMFoundationBridge.SchemaExpansion

/-!
# F1 item 5, second layer (first slice): the executable Δ⁰₀ evaluator

The compile target for `IsDelta0` derivations. Since derivations live in `Prop`, the
executable side is a `Type`-level deep embedding `Delta0Code` whose constructors mirror
the derivation rules exactly; **compilation is by induction on the derivation**
(`IsDelta0.exists_code`), never by inspecting arbitrary formula syntax — the existence of
a code is a proposition, extracted inside the `Prop` goals (like `X ∈ Ω`) that consume
it.

The invariant is encoded in the type: `Delta0Code (N : ℕ) : ℕ → Type` — the set-slot
count is a fixed parameter, the number-slot count is the index that changes under
`ball`/`bex`, and the code itself is the structural argument of `toFormula`,
`toFormula_isDelta0`, and `beval`, so every defining equation is definitional.

The **executable Boolean evaluator** `Delta0Code.beval` is total and kept separate from
its semantic agreement proof (exactly as the transcript verifier was separated in the ω
work): abstract in the oracle answer function `χ : ℕ → Bool`, set atoms consulted through
the `paramQuery` channel codes, bounded quantifiers evaluated by finite scans. The later
Σ⁰₁ search iterates this clean predicate.

This slice: term layer (with primitive-recursiveness and agreement), code type,
compilation, evaluator, and executable fixtures — positive and negative set atoms, both
bounded quantifiers, and a quantified body reading the surviving **outer** number
variable beneath the binder. Tarski agreement and `Nat.RecursiveIn` follow in separate
slices.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-! ### The term layer: evaluation from a plain number environment -/

/-- Evaluate an arithmetic term over `ℕ` from a list environment (`bvar i` reads
`l.getD i 0`; no free variables exist). The slot count is fixed — terms bind nothing —
so the recursion is structural on the term and every equation is definitional. -/
def termValEnv {n : ℕ} : Semiterm ℒₒᵣ Empty n → List ℕ → ℕ
  | #i, l => l.getD i 0
  | &x, _ => x.elim
  | .func Language.ORing.Func.zero _, _ => 0
  | .func Language.ORing.Func.one _, _ => 1
  | .func Language.ORing.Func.add v, l => termValEnv (v 0) l + termValEnv (v 1) l
  | .func Language.ORing.Func.mul v, l => termValEnv (v 0) l * termValEnv (v 1) l

/-- Agreement with Foundation's term evaluation under the explicit standard
interpretation. -/
theorem termValEnv_agrees {n : ℕ} : ∀ (t : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ),
    termValEnv t (List.ofFn e) =
      (letI : Structure ℒₒᵣ ℕ := standardInterpretation
       t.val e Empty.elim)
  | #i, e => by
      simp [termValEnv, List.getD_eq_getElem?_getD]
  | &x, _ => x.elim
  | .func Language.ORing.Func.zero _, e => rfl
  | .func Language.ORing.Func.one _, e => rfl
  | .func Language.ORing.Func.add v, e => by
      rw [show termValEnv (Semiterm.func Language.ORing.Func.add v) (List.ofFn e) =
            termValEnv (v 0) (List.ofFn e) + termValEnv (v 1) (List.ofFn e) from rfl,
        termValEnv_agrees (v 0) e, termValEnv_agrees (v 1) e]
      rfl
  | .func Language.ORing.Func.mul v, e => by
      rw [show termValEnv (Semiterm.func Language.ORing.Func.mul v) (List.ofFn e) =
            termValEnv (v 0) (List.ofFn e) * termValEnv (v 1) (List.ofFn e) from rfl,
        termValEnv_agrees (v 0) e, termValEnv_agrees (v 1) e]
      rfl

/-- Term evaluation from a **coded** environment is primitive recursive, pointwise in the
fixed term (the formula fixes its terms; no uniform term compiler is needed). -/
theorem primrec_termValEnv {n : ℕ} : ∀ (t : Semiterm ℒₒᵣ Empty n),
    Primrec fun ec : ℕ => termValEnv t (decodeSeq ec)
  | #i =>
      (Primrec₂.comp primrec_seqGet Primrec.id (Primrec.const i.1)).of_eq fun _ => rfl
  | &x => x.elim
  | .func Language.ORing.Func.zero _ => (Primrec.const 0).of_eq fun _ => rfl
  | .func Language.ORing.Func.one _ => (Primrec.const 1).of_eq fun _ => rfl
  | .func Language.ORing.Func.add v =>
      (Primrec.nat_add.comp (primrec_termValEnv (v 0))
        (primrec_termValEnv (v 1))).of_eq fun _ => rfl
  | .func Language.ORing.Func.mul v =>
      (Primrec.nat_mul.comp (primrec_termValEnv (v 0))
        (primrec_termValEnv (v 1))).of_eq fun _ => rfl

/-! ### The code type: `IsDelta0`'s constructors, as data -/

/-- The deep-embedded Δ⁰₀ fragment: one constructor per `IsDelta0` derivation rule. The
set-slot count `N` is a **fixed parameter**; the number-slot count is the index changed
by `ball`/`bex`. Set atoms carry the `Fin N` parameter index consumed through
`paramQuery`. -/
inductive Delta0Code (N : ℕ) : ℕ → Type
  | eq {n : ℕ} (t s : Semiterm ℒₒᵣ Empty n) : Delta0Code N n
  | neq {n : ℕ} (t s : Semiterm ℒₒᵣ Empty n) : Delta0Code N n
  | lt {n : ℕ} (t s : Semiterm ℒₒᵣ Empty n) : Delta0Code N n
  | nlt {n : ℕ} (t s : Semiterm ℒₒᵣ Empty n) : Delta0Code N n
  | mem {n : ℕ} (X : Fin N) (t : Semiterm ℒₒᵣ Empty n) : Delta0Code N n
  | notMem {n : ℕ} (X : Fin N) (t : Semiterm ℒₒᵣ Empty n) : Delta0Code N n
  | verum {n : ℕ} : Delta0Code N n
  | falsum {n : ℕ} : Delta0Code N n
  | and {n : ℕ} (c d : Delta0Code N n) : Delta0Code N n
  | or {n : ℕ} (c d : Delta0Code N n) : Delta0Code N n
  | ball {n : ℕ} (t : Semiterm ℒₒᵣ Empty n) (c : Delta0Code N (n + 1)) : Delta0Code N n
  | bex {n : ℕ} (t : Semiterm ℒₒᵣ Empty n) (c : Delta0Code N (n + 1)) : Delta0Code N n

namespace Delta0Code

variable {N : ℕ}

/-- The denoted formula. -/
def toFormula : ∀ {n : ℕ}, Delta0Code N n → SecondOrder.Semiformula ℒₒᵣ Empty Empty N n
  | _, .eq t s => eqF t s
  | _, .neq t s => neF t s
  | _, .lt t s => ltF t s
  | _, .nlt t s => nltF t s
  | _, .mem X t => .bvar X t
  | _, .notMem X t => .nbvar X t
  | _, .verum => .verum
  | _, .falsum => .falsum
  | _, .and c d => c.toFormula ⋏ d.toFormula
  | _, .or c d => c.toFormula ⋎ d.toFormula
  | _, .ball t c => ballLT t c.toFormula
  | _, .bex t c => bexLT t c.toFormula

/-- Every denoted formula carries a Δ⁰₀ derivation. -/
theorem toFormula_isDelta0 : ∀ {n : ℕ} (c : Delta0Code N n), IsDelta0 c.toFormula
  | _, .eq _ _ => .rel _ _
  | _, .neq _ _ => .nrel _ _
  | _, .lt _ _ => .rel _ _
  | _, .nlt _ _ => .nrel _ _
  | _, .mem X t => .bvar X t
  | _, .notMem X t => .nbvar X t
  | _, .verum => .verum
  | _, .falsum => .falsum
  | _, .and c d => .and c.toFormula_isDelta0 d.toFormula_isDelta0
  | _, .or c d => .or c.toFormula_isDelta0 d.toFormula_isDelta0
  | _, .ball t c => .ball t c.toFormula_isDelta0
  | _, .bex t c => .bex t c.toFormula_isDelta0

end Delta0Code

/-- Two-entry vector eta: `![v 0, v 1] = v`. -/
private theorem vec2_eta {α : Type*} (v : Fin 2 → α) : ![v 0, v 1] = v := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
    induction j using Fin.cases with
    | zero => rfl
    | succ k => exact k.elim0

/-- **Compilation, by induction on the derivation**: every Δ⁰₀ formula is denoted by some
code. The existence is a proposition — extraction happens inside the `Prop` goals that
consume it — and no arbitrary formula syntax is ever inspected. -/
theorem IsDelta0.exists_code :
    ∀ {N n : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n},
      IsDelta0 φ → ∃ c : Delta0Code N n, c.toFormula = φ := by
  intro N n φ h
  induction h with
  | rel R v =>
      cases R with
      | eq => exact ⟨.eq (v 0) (v 1), congrArg _ (vec2_eta v)⟩
      | lt => exact ⟨.lt (v 0) (v 1), congrArg _ (vec2_eta v)⟩
  | nrel R v =>
      cases R with
      | eq => exact ⟨.neq (v 0) (v 1), congrArg _ (vec2_eta v)⟩
      | lt => exact ⟨.nlt (v 0) (v 1), congrArg _ (vec2_eta v)⟩
  | bvar X t => exact ⟨.mem X t, rfl⟩
  | nbvar X t => exact ⟨.notMem X t, rfl⟩
  | fvar X t => exact X.elim
  | nfvar X t => exact X.elim
  | verum => exact ⟨.verum, rfl⟩
  | falsum => exact ⟨.falsum, rfl⟩
  | and _ _ ihφ ihψ =>
      obtain ⟨c, rfl⟩ := ihφ
      obtain ⟨d, rfl⟩ := ihψ
      exact ⟨.and c d, rfl⟩
  | or _ _ ihφ ihψ =>
      obtain ⟨c, rfl⟩ := ihφ
      obtain ⟨d, rfl⟩ := ihψ
      exact ⟨.or c d, rfl⟩
  | ball t _ ih =>
      obtain ⟨c, rfl⟩ := ih
      exact ⟨.ball t c, rfl⟩
  | bex t _ ih =>
      obtain ⟨c, rfl⟩ := ih
      exact ⟨.bex t c, rfl⟩

/-! ### The executable evaluator -/

namespace Delta0Code

/-- **The total Boolean evaluator**, abstract in the oracle answer function `χ`. Set
atoms are consulted through the `paramQuery` channel codes; bounded quantifiers are
finite scans; the environment grows by consing at the head — de Bruijn slot `#0`.
Executable and separate from its agreement proof. -/
def beval {N : ℕ} (χ : ℕ → Bool) : ∀ {n : ℕ}, Delta0Code N n → List ℕ → Bool
  | _, .eq t s, l => termValEnv t l == termValEnv s l
  | _, .neq t s, l => !(termValEnv t l == termValEnv s l)
  | _, .lt t s, l => decide (termValEnv t l < termValEnv s l)
  | _, .nlt t s, l => !decide (termValEnv t l < termValEnv s l)
  | _, .mem X t, l => χ (paramQuery X (termValEnv t l))
  | _, .notMem X t, l => !χ (paramQuery X (termValEnv t l))
  | _, .verum, _ => true
  | _, .falsum, _ => false
  | _, .and c d, l => beval χ c l && beval χ d l
  | _, .or c d, l => beval χ c l || beval χ d l
  | _, .ball t c, l => (List.range (termValEnv t l)).all fun x => beval χ c (x :: l)
  | _, .bex t c, l => (List.range (termValEnv t l)).any fun x => beval χ c (x :: l)

end Delta0Code

/-! ### Executable fixtures: set atoms (both signs), both bounded quantifiers, and the
surviving outer environment -/

/-- A concrete oracle answer function: the even channel of a one-parameter oracle for
`A = {2, 5}` (so `χ (2n) = (n ∈ {2,5})`). -/
def fixtureChi : ℕ → Bool := fun q => q == 4 || q == 10

/-- Fixture: a positive set atom evaluates through the query channel. -/
example : Delta0Code.beval fixtureChi (.mem 0 #0 : Delta0Code 1 1) [2] = true := rfl

/-- Fixture: a negative set atom evaluates through the query channel. -/
example : Delta0Code.beval fixtureChi (.notMem 0 #0 : Delta0Code 1 1) [3] = true := rfl

/-- Fixture: bounded universal — `∀ x < 3, (x ∈ A₀ → x = 2)` scans finitely and holds
(only `2 < 3` lies in `{2, 5}`). -/
example : Delta0Code.beval fixtureChi
    ((.ball #0 (.or (.notMem 0 #0) (.eq #0 (succT (succT zeroT))))) : Delta0Code 1 1)
    [3] = true := rfl

/-- Fixture: bounded existential — some `x < 3` lies in `A₀` (namely `2`). -/
example : Delta0Code.beval fixtureChi
    ((.bex #0 (.mem 0 #0)) : Delta0Code 1 1) [3] = true := rfl

/-- Fixture: the bounded existential fails when the bound is too small (no `x < 2` is in
`{2, 5}`). -/
example : Delta0Code.beval fixtureChi
    ((.bex #0 (.mem 0 #0)) : Delta0Code 1 1) [2] = false := rfl

/-- Fixture: the quantified body reads the surviving **outer** number variable beneath
the binder — `∀ x < 3, x < outer` with `#0` the new variable and `#1` the old
environment: true at `outer = 5`. -/
example : Delta0Code.beval fixtureChi
    ((.ball (succT (succT (succT zeroT))) (.lt #0 #1)) : Delta0Code 1 1) [5] = true := rfl

/-- Fixture: the same body is false at `outer = 2` (`x = 2` fails `2 < 2`) — so the old
environment genuinely survives beneath the binder, at the shifted slot. -/
example : Delta0Code.beval fixtureChi
    ((.ball (succT (succT (succT zeroT))) (.lt #0 #1)) : Delta0Code 1 1) [2] = false :=
  rfl

end RMFoundationBridge
