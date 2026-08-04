/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.Basic

/-!
# F1 item 5, first layer: the finite-parameter oracle

The raw construction is **independent of `Ω`** — `finiteParamOracle : (Fin N → Set ℕ) →
Set ℕ` — with ideal membership as a separate theorem. The index type is deliberately
`Fin N`, not an arbitrary finite type: the `Fin N` order **is** the formula-variable
order, and the evaluator will depend on that alignment.

Recursive orientation: `N = 0` gives `∅`; `N = n + 1` gives
`joinSet (A 0) (finiteParamOracle (A ∘ Fin.succ))`.

The ideal-membership proof consumes closure in exactly two places —
`recursiveSet_empty` at zero and binary `join` at successor. No element of `Ω`, no
enumeration of `Ω`, and no selected default set appears anywhere in this module.

The query embedding makes the nested-track convention explicit:
`query 0 n = 2n`, `query (i+1) n = 2 · query_tail i n + 1`, with
`paramQuery_mem_iff` equating oracle membership at that code with `n ∈ A i`, and a
primitive-recursiveness theorem for later bounded evaluation. Three concrete channel
fixtures pin the alignment of `Fin` order, universal-closure order, and oracle-track
order before any evaluator depends on it.
-/

namespace RMFoundationBridge

open ReverseMathlib.Omega

/-! ### The oracle -/

/-- The finite-parameter oracle: iterated binary join, head on the even channel. Raw
construction, independent of any second-order part. -/
def finiteParamOracle : ∀ {N : ℕ}, (Fin N → Set ℕ) → Set ℕ
  | 0, _ => ∅
  | _ + 1, A => joinSet (A 0) (finiteParamOracle (A ∘ Fin.succ))

@[simp] theorem finiteParamOracle_zero (A : Fin 0 → Set ℕ) :
    finiteParamOracle A = ∅ := rfl

theorem finiteParamOracle_succ {N : ℕ} (A : Fin (N + 1) → Set ℕ) :
    finiteParamOracle A = joinSet (A 0) (finiteParamOracle (A ∘ Fin.succ)) := rfl

/-! ### Head/tail membership normal forms -/

/-- Head normal form: the even channel is parameter `0`. -/
theorem two_mul_mem_finiteParamOracle {N : ℕ} {A : Fin (N + 1) → Set ℕ} {n : ℕ} :
    2 * n ∈ finiteParamOracle A ↔ n ∈ A 0 :=
  two_mul_mem_joinSet

/-- Tail normal form: the odd channel is the tail oracle. -/
theorem two_mul_add_one_mem_finiteParamOracle {N : ℕ} {A : Fin (N + 1) → Set ℕ}
    {n : ℕ} : 2 * n + 1 ∈ finiteParamOracle A ↔ n ∈ finiteParamOracle (A ∘ Fin.succ) :=
  two_mul_add_one_mem_joinSet

/-! ### Every parameter reduces to the oracle -/

theorem param_le_finiteParamOracle :
    ∀ {N : ℕ} (A : Fin N → Set ℕ) (i : Fin N), A i ≤ᵀ finiteParamOracle A
  | _ + 1, A, i => by
      induction i using Fin.cases with
      | zero => exact left_le_joinSet (A 0) (finiteParamOracle (A ∘ Fin.succ))
      | succ j =>
        exact (param_le_finiteParamOracle (A ∘ Fin.succ) j).trans
          (right_le_joinSet (A 0) (finiteParamOracle (A ∘ Fin.succ)))

/-! ### Ideal membership — closure consumed in exactly two places -/

/-- The oracle belongs to every Turing ideal containing the parameters:
`recursiveSet_empty` at zero, binary `join` at successor, and nothing else. -/
theorem finiteParamOracle_mem {Ω : OmegaPart} (h : IsTuringIdeal Ω) :
    ∀ {N : ℕ} {A : Fin N → Set ℕ}, (∀ i, A i ∈ Ω) → finiteParamOracle A ∈ Ω
  | 0, _, _ => h.mem_of_recursive recursiveSet_empty
  | _ + 1, _, hA => h.join (hA 0) (finiteParamOracle_mem h fun j => hA j.succ)

/-! ### The query embedding (nested-track convention, explicit) -/

/-- The query code of parameter `i` at input `n`:
`query 0 n = 2n`; `query (i+1) n = 2 · query_tail i n + 1`. -/
def paramQuery : ∀ {N : ℕ}, Fin N → ℕ → ℕ
  | _ + 1, i, n => Fin.cases (2 * n) (fun j => 2 * paramQuery j n + 1) i

@[simp] theorem paramQuery_zero {N : ℕ} (n : ℕ) :
    paramQuery (0 : Fin (N + 1)) n = 2 * n := by
  simp [paramQuery]

@[simp] theorem paramQuery_succ {N : ℕ} (j : Fin N) (n : ℕ) :
    paramQuery j.succ n = 2 * paramQuery j n + 1 := by
  simp [paramQuery]

/-- Oracle membership at the query code is exactly parameter membership. -/
theorem paramQuery_mem_iff :
    ∀ {N : ℕ} (A : Fin N → Set ℕ) (i : Fin N) (n : ℕ),
      paramQuery i n ∈ finiteParamOracle A ↔ n ∈ A i
  | _ + 1, A, i, n => by
      induction i using Fin.cases with
      | zero =>
        rw [paramQuery_zero]
        exact two_mul_mem_finiteParamOracle
      | succ j =>
        rw [paramQuery_succ]
        exact two_mul_add_one_mem_finiteParamOracle.trans
          (paramQuery_mem_iff (A ∘ Fin.succ) j n)

/-- The query embedding is primitive recursive (for later bounded evaluation). -/
theorem primrec_paramQuery : ∀ {N : ℕ} (i : Fin N), Primrec (paramQuery i) := by
  intro N
  induction N with
  | zero => exact fun i => i.elim0
  | succ N ih =>
    intro i
    induction i using Fin.cases with
    | zero =>
      have h : Primrec fun n : ℕ => 2 * n :=
        Primrec.nat_mul.comp (Primrec.const 2) Primrec.id
      exact h.of_eq fun n => (paramQuery_zero n).symm
    | succ j =>
      have h : Primrec fun n : ℕ => 2 * paramQuery j n + 1 :=
        Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 2) (ih j)) (Primrec.const 1)
      exact h.of_eq fun n => (paramQuery_succ j n).symm

/-! ### Channel fixtures: `Fin` order = closure order = oracle-track order -/

/-- Fixture: zero parameters give the empty oracle. -/
example : finiteParamOracle (![] : Fin 0 → Set ℕ) = ∅ := rfl

/-- Fixture: parameter zero uses the even channel. -/
example (A : Set ℕ) (n : ℕ) : 2 * n ∈ finiteParamOracle ![A] ↔ n ∈ A :=
  two_mul_mem_finiteParamOracle

/-- Fixture: in the two-parameter case, parameter one uses the nested odd/even channel —
a reversal between `Fin` order, universal-closure order, and oracle-track order would
break this before any evaluator depends on it. -/
example (A B : Set ℕ) (n : ℕ) :
    2 * (2 * n) + 1 ∈ finiteParamOracle ![A, B] ↔ n ∈ B := by
  rw [two_mul_add_one_mem_finiteParamOracle, two_mul_mem_finiteParamOracle]
  simp

/-- Fixture: the query embedding computes the expected codes. -/
example (n : ℕ) : paramQuery (0 : Fin 2) n = 2 * n := paramQuery_zero n

example (n : ℕ) : paramQuery (1 : Fin 2) n = 2 * (2 * n) + 1 := by
  rw [show (1 : Fin 2) = (0 : Fin 1).succ from rfl, paramQuery_succ, paramQuery_zero]

end RMFoundationBridge
