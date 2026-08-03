/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.UnivClose

/-!
# F1 step 3: the semantic RCA₀ theory on ω-structures, defined syntactically

**Pinned conventions** (claimed source: Simpson [Sim09], Definition I.2.4 for the basic
axioms and §I.7 for the schemas — claimed, unverified against a pinned snapshot):

* **language**: `ℒₒᵣ` — `0, 1, +, ·, =, <`; the successor `t + 1` is a defined term;
* **set parameters**: membership atoms against set variables; there is **no set-equality
  symbol** in the language;
* **extensionality** is a property of this semantics, not an omitted axiom whose strength
  is silently assumed: set variables range over *actual subsets of ℕ* (`Set ℕ` drawn from
  `Ω.sets`), so two extensionally equal sets are literally the same object of the
  metatheory, and no separate identity predicate exists to diverge from membership;
* **classes**: the strict structural Σ⁰₁/Π⁰₁ of `Hierarchy.lean` (bounded quantifiers via
  `<`; a `≤`-bound is the derived `< t+1`);
* **induction**: Σ⁰₁ induction **only** — the origin predicate admits an induction
  sentence exclusively through a `IsSigma01` derivation for its matrix, so full induction
  cannot be admitted by accident even though standard ℕ satisfies it metatheoretically;
* **comprehension**: pair-based Δ⁰₁ — a Σ⁰₁ matrix and a Π⁰₁ matrix, an equivalence
  premise, then existence of their common extension; never simultaneous strict membership
  of one syntax tree;
* **parameters**: schema matrices carry `N` set slots and `k` extra number slots beyond
  the distinguished variable (the full schemes, not a parameter-free subclass); instances
  become sentences by `univClose`, whose exactly-once capture is structural.

The theory is defined through the inductive **axiom-origin predicate** `AxiomOrigin`, so
satisfaction proofs are ordinary case analysis over origins.

Freshness in comprehension is structural: the matrix is transported by
`bmap Fin.succ` before the output set is bound at index `0`, so the bound set is fresh
and every original parameter survives (shifted) for `univClose`.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder

/-! ### Term and formula abbreviations (de Bruijn, `ℒₒᵣ`) -/

variable {Ξ ξ : Type*} {N n k : ℕ}

/-- The term `0`. -/
def zeroT {ξ : Type*} {n : ℕ} : Semiterm ℒₒᵣ ξ n := .func Language.ORing.Func.zero ![]

/-- The term `1`. -/
def oneT {ξ : Type*} {n : ℕ} : Semiterm ℒₒᵣ ξ n := .func Language.ORing.Func.one ![]

/-- Addition. -/
def addT {ξ : Type*} {n : ℕ} (t s : Semiterm ℒₒᵣ ξ n) : Semiterm ℒₒᵣ ξ n :=
  .func Language.ORing.Func.add ![t, s]

/-- Multiplication. -/
def mulT {ξ : Type*} {n : ℕ} (t s : Semiterm ℒₒᵣ ξ n) : Semiterm ℒₒᵣ ξ n :=
  .func Language.ORing.Func.mul ![t, s]

/-- The defined successor `t + 1`. -/
def succT {ξ : Type*} {n : ℕ} (t : Semiterm ℒₒᵣ ξ n) : Semiterm ℒₒᵣ ξ n := addT t oneT

/-- Equality atom. -/
def eqF (t s : Semiterm ℒₒᵣ ξ n) : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n :=
  .rel Language.ORing.Rel.eq ![t, s]

/-- Negated equality atom. -/
def neF (t s : Semiterm ℒₒᵣ ξ n) : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n :=
  .nrel Language.ORing.Rel.eq ![t, s]

/-- Order atom. -/
def ltF (t s : Semiterm ℒₒᵣ ξ n) : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n :=
  .rel Language.ORing.Rel.lt ![t, s]

/-- Negated order atom. -/
def nltF (t s : Semiterm ℒₒᵣ ξ n) : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n :=
  .nrel Language.ORing.Rel.lt ![t, s]

/-- Material implication in the negation-normal syntax. -/
def impF (φ ψ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n) :
    SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n := ∼φ ⋎ ψ

/-- Material biconditional in the negation-normal syntax. -/
def iffF (φ ψ : SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n) :
    SecondOrder.Semiformula ℒₒᵣ Ξ ξ N n := (∼φ ⋎ ψ) ⋏ (∼ψ ⋎ φ)

/-! ### The basic arithmetic axioms ([Sim09] I.2.4, claimed) -/

/-- `∀m, m + 1 ≠ 0`. -/
def basicSuccNeZero : SecondOrder.Sentence ℒₒᵣ :=
  univClose (neF (succT #0) zeroT : SecondOrder.Semiformula ℒₒᵣ Empty Empty 0 1)

/-- `∀m n, m + 1 = n + 1 → m = n`. -/
def basicSuccInj : SecondOrder.Sentence ℒₒᵣ :=
  univClose (impF (eqF (succT #0) (succT #1)) (eqF #0 #1) :
    SecondOrder.Semiformula ℒₒᵣ Empty Empty 0 2)

/-- `∀m, m + 0 = m`. -/
def basicAddZero : SecondOrder.Sentence ℒₒᵣ :=
  univClose (eqF (addT #0 zeroT) #0 : SecondOrder.Semiformula ℒₒᵣ Empty Empty 0 1)

/-- `∀m n, m + (n + 1) = (m + n) + 1`. -/
def basicAddSucc : SecondOrder.Sentence ℒₒᵣ :=
  univClose (eqF (addT #0 (succT #1)) (succT (addT #0 #1)) :
    SecondOrder.Semiformula ℒₒᵣ Empty Empty 0 2)

/-- `∀m, m · 0 = 0`. -/
def basicMulZero : SecondOrder.Sentence ℒₒᵣ :=
  univClose (eqF (mulT #0 zeroT) zeroT : SecondOrder.Semiformula ℒₒᵣ Empty Empty 0 1)

/-- `∀m n, m · (n + 1) = (m · n) + m`. -/
def basicMulSucc : SecondOrder.Sentence ℒₒᵣ :=
  univClose (eqF (mulT #0 (succT #1)) (addT (mulT #0 #1) #0) :
    SecondOrder.Semiformula ℒₒᵣ Empty Empty 0 2)

/-- `∀m, ¬ m < 0`. -/
def basicNotLtZero : SecondOrder.Sentence ℒₒᵣ :=
  univClose (nltF #0 zeroT : SecondOrder.Semiformula ℒₒᵣ Empty Empty 0 1)

/-- `∀m n, m < n + 1 ↔ (m < n ∨ m = n)`. -/
def basicLtSuccIff : SecondOrder.Sentence ℒₒᵣ :=
  univClose (iffF (ltF #0 (succT #1)) (ltF #0 #1 ⋎ eqF #0 #1) :
    SecondOrder.Semiformula ℒₒᵣ Empty Empty 0 2)

/-! ### The schema constructors -/

/-- The Σ⁰₁ induction instance for a matrix `φ` with the induction variable at slot `#0`,
`k` further number parameters, and `N` set parameters:
`(φ(0) ∧ ∀m (φ(m) → φ(m+1))) → ∀m φ(m)`, universally closed over all parameters. -/
def inductionSentence (φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (k + 1)) :
    SecondOrder.Sentence ℒₒᵣ :=
  univClose (impF
    ((Rew.subst (zeroT :> Semiterm.bvar) ▹ φ) ⋏
      .all₁ (impF φ (Rew.subst (succT #0 :> fun i => #(i.succ)) ▹ φ)))
    (.all₁ φ))

/-- The Δ⁰₁ comprehension instance for matrices `φ` (intended Σ⁰₁) and `ψ` (intended
Π⁰₁), each with the comprehension variable at slot `#0`, `k` further number parameters,
and `N` set parameters:
`(∀m (φ(m) ↔ ψ(m))) → ∃X ∀m (m ∈ X ↔ φ(m))`, universally closed.

The bound output set is **fresh structurally**: `φ` is transported by `bmap Fin.succ`
before `X` is bound at set index `0`, so every original set parameter survives (shifted)
and none can be captured. -/
def comprehensionSentence (φ ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (k + 1)) :
    SecondOrder.Sentence ℒₒᵣ :=
  univClose (impF
    (.all₁ (iffF φ ψ))
    (.exs₂ (.all₁ (iffF (.bvar 0 #0) (SecondOrder.Semiformula.bmap Fin.succ φ)))))

/-! ### The theory, through its axiom-origin predicate -/

/-- **The axiom origins of semantic RCA₀ on ω-structures**: each basic arithmetic axiom,
Σ⁰₁ induction (the matrix must carry a strict `IsSigma01` derivation — full induction is
structurally inadmissible), and pair-based Δ⁰₁ comprehension (a strict Σ⁰₁ matrix, a
strict Π⁰₁ matrix). Satisfaction proofs proceed by case analysis on the origin. -/
inductive AxiomOrigin : SecondOrder.Sentence ℒₒᵣ → Prop
  | succNeZero : AxiomOrigin basicSuccNeZero
  | succInj : AxiomOrigin basicSuccInj
  | addZero : AxiomOrigin basicAddZero
  | addSucc : AxiomOrigin basicAddSucc
  | mulZero : AxiomOrigin basicMulZero
  | mulSucc : AxiomOrigin basicMulSucc
  | notLtZero : AxiomOrigin basicNotLtZero
  | ltSuccIff : AxiomOrigin basicLtSuccIff
  | sigma1Induction {N k : ℕ} {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (k + 1)}
      (hφ : IsSigma01 φ) : AxiomOrigin (inductionSentence φ)
  | delta1Comprehension {N k : ℕ}
      {φ ψ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (k + 1)}
      (hφ : IsSigma01 φ) (hψ : IsPi01 ψ) : AxiomOrigin (comprehensionSentence φ ψ)

/-- Semantic RCA₀ on ω-structures, as a set of second-order sentences. -/
def Rca0Theory : Set (SecondOrder.Sentence ℒₒᵣ) := {σ | AxiomOrigin σ}

end RMFoundationBridge
