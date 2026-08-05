/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Logic.Godel.GodelBetaFunction
import RMFoundationBridge.Delta0Agreement

/-!
# F1 step 4, first layer: arithmetic graph formulas for the canonical coding

The ŴKL sentence must talk, inside `ℒₒᵣ`, about the **frozen** coding
(`seqCode`/`decodeSeq`, mathlib's iterated-`Nat.pair` list encoding) — not about an
alternative arithmetic-friendly coding, which would force set translation and smuggle a
closure premise into statement adequacy. This module supplies first-order graph formulas
for the coding operations the frozen tree predicates consume — decoded length, decoded
entry (`getD`-semantics), truncation re-encoded — together with **unconditional
standard-ℕ adequacy** theorems: each formula's Tarski evaluation is the literal
`decodeSeq`-fact, for every `𝕊`, every set assignment, and every environment.

The recursion along the nested pairing is arithmetized by Gödel's β function
(`Nat.beta`/`Nat.unbeta`, mathlib): a coded run of the tail chain is quantified with one
unbounded `∃`. **No hierarchy classification is claimed or needed** — the adapter target
is semantic truth over standard ℕ, where arbitrary first-order formulas evaluate
classically; `IsDelta0`/`IsSigma01` never appear.

Design constraints kept throughout: every graph is a small composition of earlier graphs
through the substitution combinators (`app₂`/`app₃`), so literal de Bruijn indices stay
shallow; every adequacy statement is in `![…]`-environment form with an applied
(`app`-composed) corollary, which is the only form later layers consume. Nothing here
mentions `OmegaPart`, internal sets, or any ideal premise.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-! ### The frozen coding, structurally -/

theorem seqCode_nil : seqCode [] = 0 := rfl

theorem seqCode_cons (a : ℕ) (l : List ℕ) :
    seqCode (a :: l) = Nat.pair a (seqCode l) + 1 := by
  simp [seqCode, Encodable.encode_list_cons]

/-- Bijectivity, in the form every graph proof uses: a number is the code of a list iff
it decodes to it. -/
theorem eq_seqCode_iff {x : ℕ} {l : List ℕ} : x = seqCode l ↔ decodeSeq x = l :=
  ⟨fun h => by rw [h, decodeSeq_seqCode], fun h => by rw [← h, seqCode_decodeSeq]⟩

/-! ### Terms over `ℒₒᵣ` and their standard values -/

/-- Standard value of a closed-free-variable term: the bridge-owned name for term
evaluation under `standardInterpretation`. -/
def tval {n : ℕ} (t : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) : ℕ :=
  letI : Structure ℒₒᵣ ℕ := standardInterpretation
  t.val e Empty.elim

/-- The zero term. -/
def tZero {n : ℕ} : Semiterm ℒₒᵣ Empty n := Semiterm.func Language.ORing.Func.zero ![]

/-- The one term. -/
def tOne {n : ℕ} : Semiterm ℒₒᵣ Empty n := Semiterm.func Language.ORing.Func.one ![]

/-- Addition of terms. -/
def tAdd {n : ℕ} (t s : Semiterm ℒₒᵣ Empty n) : Semiterm ℒₒᵣ Empty n :=
  Semiterm.func Language.ORing.Func.add ![t, s]

/-- Multiplication of terms. -/
def tMul {n : ℕ} (t s : Semiterm ℒₒᵣ Empty n) : Semiterm ℒₒᵣ Empty n :=
  Semiterm.func Language.ORing.Func.mul ![t, s]

/-- Successor as a defined term. -/
def tSucc {n : ℕ} (t : Semiterm ℒₒᵣ Empty n) : Semiterm ℒₒᵣ Empty n := tAdd t tOne

@[simp] theorem tval_bvar {n : ℕ} (i : Fin n) (e : Fin n → ℕ) : tval #i e = e i := rfl

@[simp] theorem tval_tZero {n : ℕ} (e : Fin n → ℕ) : tval tZero e = 0 := rfl

@[simp] theorem tval_tOne {n : ℕ} (e : Fin n → ℕ) : tval tOne e = 1 := rfl

@[simp] theorem tval_tAdd {n : ℕ} (t s : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    tval (tAdd t s) e = tval t e + tval s e := rfl

@[simp] theorem tval_tMul {n : ℕ} (t s : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    tval (tMul t s) e = tval t e * tval s e := rfl

@[simp] theorem tval_tSucc {n : ℕ} (t : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    tval (tSucc t) e = tval t e + 1 := rfl

/-! ### Arithmetic atoms -/

/-- Equality atom. -/
def fEq {N n : ℕ} (t s : Semiterm ℒₒᵣ Empty n) :
    SecondOrder.Semiformula ℒₒᵣ Empty Empty N n :=
  .rel Language.ORing.Rel.eq ![t, s]

/-- Strict-order atom. -/
def fLt {N n : ℕ} (t s : Semiterm ℒₒᵣ Empty n) :
    SecondOrder.Semiformula ℒₒᵣ Empty Empty N n :=
  .rel Language.ORing.Rel.lt ![t, s]

/-- Negated strict-order atom (NNF dual). -/
def fNlt {N n : ℕ} (t s : Semiterm ℒₒᵣ Empty n) :
    SecondOrder.Semiformula ℒₒᵣ Empty Empty N n :=
  .nrel Language.ORing.Rel.lt ![t, s]

section evalAtoms

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

theorem evalN_fEq {t s : Semiterm ℒₒᵣ Empty n} {e : Fin n → ℕ} :
    EvalN 𝕊 (fEq (N := N) t s) E e ↔ tval t e = tval s e := Iff.rfl

theorem evalN_fLt {t s : Semiterm ℒₒᵣ Empty n} {e : Fin n → ℕ} :
    EvalN 𝕊 (fLt (N := N) t s) E e ↔ tval t e < tval s e := Iff.rfl

theorem evalN_fNlt {t s : Semiterm ℒₒᵣ Empty n} {e : Fin n → ℕ} :
    EvalN 𝕊 (fNlt (N := N) t s) E e ↔ ¬ tval t e < tval s e := Iff.rfl

theorem evalN_exs₁ {φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N (n + 1)}
    {e : Fin n → ℕ} : EvalN 𝕊 (.exs₁ φ) E e ↔ ∃ x : ℕ, EvalN 𝕊 φ E (x :> e) := Iff.rfl

end evalAtoms

/-! ### Substitution combinators

Applying a fixed-arity graph at terms of an ambient arity, with the evaluation identity
proved once (`eval_rew`). Later layers only ever consume applied forms. -/

/-- Apply a 2-ary formula at two terms. -/
def app₂ {N n : ℕ} (φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 2)
    (t₁ t₂ : Semiterm ℒₒᵣ Empty n) : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n :=
  Rew.subst ![t₁, t₂] ▹ φ

/-- Apply a 3-ary formula at three terms. -/
def app₃ {N n : ℕ} (φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 3)
    (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) : SecondOrder.Semiformula ℒₒᵣ Empty Empty N n :=
  Rew.subst ![t₁, t₂, t₃] ▹ φ

section evalApp

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

theorem evalN_app₂ (φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 2)
    (t₁ t₂ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₂ φ t₁ t₂) E e ↔ EvalN 𝕊 φ E ![tval t₁ e, tval t₂ e] := by
  unfold app₂ EvalN
  rw [eval_rew φ (Rew.subst ![t₁, t₂]) E Empty.elim e]
  have hb : (Semiterm.val (M := ℕ) (s := standardInterpretation) e Empty.elim ∘
      (Rew.subst ![t₁, t₂]) ∘ Semiterm.bvar) = ![tval t₁ e, tval t₂ e] := by
    funext i
    induction i using Fin.cases with
    | zero => simp [FirstOrder.Rew.subst, tval]
    | succ j =>
      induction j using Fin.cases with
      | zero => simp [FirstOrder.Rew.subst, tval]
      | succ k => exact k.elim0
  have hf : (Semiterm.val (M := ℕ) (s := standardInterpretation) e Empty.elim ∘
      (Rew.subst ![t₁, t₂]) ∘ Semiterm.fvar) = Empty.elim := by
    funext y
    exact y.elim
  rw [hb, hf]

theorem evalN_app₃ (φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 3)
    (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₃ φ t₁ t₂ t₃) E e ↔
      EvalN 𝕊 φ E ![tval t₁ e, tval t₂ e, tval t₃ e] := by
  unfold app₃ EvalN
  rw [eval_rew φ (Rew.subst ![t₁, t₂, t₃]) E Empty.elim e]
  have hb : (Semiterm.val (M := ℕ) (s := standardInterpretation) e Empty.elim ∘
      (Rew.subst ![t₁, t₂, t₃]) ∘ Semiterm.bvar) =
      ![tval t₁ e, tval t₂ e, tval t₃ e] := by
    funext i
    induction i using Fin.cases with
    | zero => simp [FirstOrder.Rew.subst, tval]
    | succ j =>
      induction j using Fin.cases with
      | zero => simp [FirstOrder.Rew.subst, tval]
      | succ k =>
        induction k using Fin.cases with
        | zero => simp [FirstOrder.Rew.subst, tval]
        | succ m => exact m.elim0
  have hf : (Semiterm.val (M := ℕ) (s := standardInterpretation) e Empty.elim ∘
      (Rew.subst ![t₁, t₂, t₃]) ∘ Semiterm.fvar) = Empty.elim := by
    funext y
    exact y.elim
  rw [hb, hf]

end evalApp

/-! ### The pairing graph -/

/-- Graph of `Nat.pair`: arguments `(a, b, y)`, meaning `y = Nat.pair a b`. -/
def pairGraph {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 3 :=
  (fLt #0 #1 ⋏ fEq #2 (tAdd (tMul #1 #1) #0)) ⋎
  (fNlt #0 #1 ⋏ fEq #2 (tAdd (tAdd (tMul #0 #0) #0) #1))

section pairGraph

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

theorem evalN_pairGraph (a b y : ℕ) :
    EvalN 𝕊 (pairGraph (N := N)) E ![a, b, y] ↔ y = Nat.pair a b := by
  have h : EvalN 𝕊 (pairGraph (N := N)) E ![a, b, y] ↔
      ((a < b ∧ y = b * b + a) ∨ (¬ a < b ∧ y = a * a + a + b)) := Iff.rfl
  rw [h]
  by_cases hab : a < b <;> simp [Nat.pair, hab]

theorem evalN_app₃_pairGraph (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₃ (pairGraph (N := N)) t₁ t₂ t₃) E e ↔
      tval t₃ e = Nat.pair (tval t₁ e) (tval t₂ e) := by
  rw [evalN_app₃, evalN_pairGraph]

end pairGraph

/-! ### The remainder graph -/

/-- Graph of remainder at a positive modulus: arguments `(w, m, y)`, meaning
`y = w % m ∧ 0 < m` (the formula `∃ q, w = q * m + y ∧ y < m`). -/
def modGraph {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 3 :=
  .exs₁ (fEq #1 (tAdd (tMul #0 #2) #3) ⋏ fLt #3 #2)

section modGraph

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

/-- The remainder characterization the graph evaluates to. -/
theorem mod_char {w m y : ℕ} : (∃ q, w = q * m + y ∧ y < m) ↔ y = w % m ∧ 0 < m := by
  constructor
  · rintro ⟨q, rfl, hy⟩
    refine ⟨?_, Nat.lt_of_le_of_lt (Nat.zero_le y) hy⟩
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  · rintro ⟨rfl, hm⟩
    exact ⟨w / m, by rw [Nat.mul_comm]; exact (Nat.div_add_mod w m).symm,
      Nat.mod_lt _ hm⟩

theorem evalN_modGraph (w m y : ℕ) :
    EvalN 𝕊 (modGraph (N := N)) E ![w, m, y] ↔ y = w % m ∧ 0 < m := by
  have h : EvalN 𝕊 (modGraph (N := N)) E ![w, m, y] ↔
      (∃ q, w = q * m + y ∧ y < m) := Iff.rfl
  rw [h, mod_char]

theorem evalN_app₃_modGraph (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₃ (modGraph (N := N)) t₁ t₂ t₃) E e ↔
      tval t₃ e = tval t₁ e % tval t₂ e ∧ 0 < tval t₂ e := by
  rw [evalN_app₃, evalN_modGraph]

end modGraph

/-! ### The β graph -/

/-- Graph of Gödel's β: arguments `(s, i, y)`, meaning `y = Nat.beta s i` — the packed
witness `s` unpairs into the remainder base and the modulus seed. -/
def betaGraph {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 3 :=
  .exs₁ (.exs₁ (app₃ pairGraph #1 #0 #2 ⋏
    app₃ modGraph #1 (tSucc (tMul (tSucc #3) #0)) #4))

section betaGraph

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

/-- The β characterization the graph evaluates to. -/
theorem eq_beta_iff {s i y : ℕ} :
    y = Nat.beta s i ↔
      ∃ w d, s = Nat.pair w d ∧ (y = w % ((i + 1) * d + 1) ∧ 0 < (i + 1) * d + 1) := by
  constructor
  · rintro rfl
    exact ⟨s.unpair.1, s.unpair.2, (Nat.pair_unpair s).symm, rfl, Nat.succ_pos _⟩
  · rintro ⟨w, d, rfl, rfl, -⟩
    rw [Nat.beta, Nat.unpair_pair]

theorem evalN_betaGraph (s i y : ℕ) :
    EvalN 𝕊 (betaGraph (N := N)) E ![s, i, y] ↔ y = Nat.beta s i := by
  have h : EvalN 𝕊 (betaGraph (N := N)) E ![s, i, y] ↔
      ∃ w d : ℕ, EvalN 𝕊 (app₃ pairGraph #1 #0 #2) E (d :> w :> ![s, i, y]) ∧
        EvalN 𝕊 (app₃ modGraph #1 (tSucc (tMul (tSucc #3) #0)) #4) E
          (d :> w :> ![s, i, y]) := Iff.rfl
  rw [h, eq_beta_iff]
  exact exists_congr fun w => exists_congr fun d =>
    and_congr (evalN_app₃_pairGraph _ _ _ _) (evalN_app₃_modGraph _ _ _ _)

theorem evalN_app₃_betaGraph (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₃ (betaGraph (N := N)) t₁ t₂ t₃) E e ↔
      tval t₃ e = Nat.beta (tval t₁ e) (tval t₂ e) := by
  rw [evalN_app₃, evalN_betaGraph]

end betaGraph

/-! ### The cons graph and the tail step -/

/-- Graph of the coding cons: arguments `(a, y, x)`, meaning `x = Nat.pair a y + 1` —
by `seqCode_cons`, `x` codes a sequence with head `a` whose tail is coded by `y`. -/
def consGraph {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 3 :=
  .exs₁ (app₃ pairGraph #1 #2 #0 ⋏ fEq #3 (tSucc #0))

section consGraph

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

theorem evalN_consGraph (a y x : ℕ) :
    EvalN 𝕊 (consGraph (N := N)) E ![a, y, x] ↔ x = Nat.pair a y + 1 := by
  have h : EvalN 𝕊 (consGraph (N := N)) E ![a, y, x] ↔
      ∃ p : ℕ, EvalN 𝕊 (app₃ pairGraph #1 #2 #0) E (p :> ![a, y, x]) ∧
        EvalN 𝕊 (fEq #3 (tSucc #0)) E (p :> ![a, y, x]) := Iff.rfl
  rw [h]
  constructor
  · rintro ⟨p, h₁, h₂⟩
    have h₁' : p = Nat.pair a y := (evalN_app₃_pairGraph _ _ _ _).mp h₁
    have h₂' : x = p + 1 := h₂
    rw [h₂', h₁']
  · intro hx
    refine ⟨Nat.pair a y, (evalN_app₃_pairGraph _ _ _ _).mpr rfl, ?_⟩
    exact hx

theorem evalN_app₃_consGraph (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₃ (consGraph (N := N)) t₁ t₂ t₃) E e ↔
      tval t₃ e = Nat.pair (tval t₁ e) (tval t₂ e) + 1 := by
  rw [evalN_app₃, evalN_consGraph]

end consGraph

/-- The tail step: arguments `(x, y)`, meaning `x` is a nonempty-sequence code whose
decoded tail is coded by `y`, for some head. -/
def tailStepGraph {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 2 :=
  .exs₁ (app₃ consGraph #0 #2 #1)

section tailStepGraph

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

theorem evalN_tailStepGraph (x y : ℕ) :
    EvalN 𝕊 (tailStepGraph (N := N)) E ![x, y] ↔ ∃ a, x = Nat.pair a y + 1 := by
  have h : EvalN 𝕊 (tailStepGraph (N := N)) E ![x, y] ↔
      ∃ a : ℕ, EvalN 𝕊 (app₃ consGraph #0 #2 #1) E (a :> ![x, y]) := Iff.rfl
  rw [h]
  exact exists_congr fun a => evalN_app₃_consGraph _ _ _ _

theorem evalN_app₂_tailStepGraph (t₁ t₂ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₂ (tailStepGraph (N := N)) t₁ t₂) E e ↔
      ∃ a, tval t₁ e = Nat.pair a (tval t₂ e) + 1 := by
  rw [evalN_app₂, evalN_tailStepGraph]

/-- The step relation, decoded: exactly the cons decomposition of the decoded
sequences. -/
theorem tailStep_iff_decode {x y : ℕ} :
    (∃ a, x = Nat.pair a y + 1) ↔ ∃ a, decodeSeq x = a :: decodeSeq y := by
  refine exists_congr fun a => ?_
  rw [← eq_seqCode_iff, seqCode_cons, seqCode_decodeSeq]

end tailStepGraph

/-! ### β-coded runs of the tail chain -/

/-- A β-coded run of the tail chain: `s` β-codes a chain starting at `c` whose first `n`
steps each decompose as a coding cons. Stated in pair form, matching the formula; the
decoded meaning is `RunN.beta_eq`. -/
def RunN (c n s : ℕ) : Prop :=
  Nat.beta s 0 = c ∧ ∀ j < n, ∃ a, Nat.beta s j = Nat.pair a (Nat.beta s (j + 1)) + 1

/-- Along a run, the β values are exactly the codes of the dropped suffixes. -/
theorem RunN.beta_eq {c n s : ℕ} (h : RunN c n s) :
    ∀ j, j ≤ n → Nat.beta s j = seqCode ((decodeSeq c).drop j)
  | 0, _ => by rw [h.1, List.drop_zero, seqCode_decodeSeq]
  | j + 1, hj => by
      obtain ⟨a, ha⟩ := h.2 j (Nat.lt_of_succ_le hj)
      have hprev := h.beta_eq j (Nat.le_of_succ_le hj)
      have h1 : decodeSeq (Nat.beta s j) = a :: decodeSeq (Nat.beta s (j + 1)) :=
        eq_seqCode_iff.mp (by rw [ha, seqCode_cons, seqCode_decodeSeq])
      have h2 : (decodeSeq c).drop j = a :: decodeSeq (Nat.beta s (j + 1)) := by
        rw [← h1, hprev, decodeSeq_seqCode]
      have h3 : (decodeSeq c).drop (j + 1) = decodeSeq (Nat.beta s (j + 1)) := by
        rw [← List.drop_drop, h2, List.drop_one, List.tail_cons]
      rw [h3, seqCode_decodeSeq]

/-- A run of length `n` forces `n` non-nil suffixes: the run length is at most the
decoded length. -/
theorem RunN.le_length {c n s : ℕ} (h : RunN c n s) : n ≤ (decodeSeq c).length := by
  rcases Nat.lt_or_ge (decodeSeq c).length n with hlt | h'
  · exfalso
    obtain ⟨a, ha⟩ := h.2 (decodeSeq c).length hlt
    have h0 := h.beta_eq (decodeSeq c).length (Nat.le_of_lt hlt)
    rw [List.drop_length, seqCode_nil] at h0
    rw [h0] at ha
    exact Nat.succ_ne_zero _ ha.symm
  · exact h'

/-- β of an `unbeta`-packed value table: mathlib's Beta Function Lemma, specialized to
the `map`-over-`range` witnesses every existence proof below constructs. -/
theorem beta_unbeta_map_range {f : ℕ → ℕ} {n : ℕ} {j : ℕ} (hj : j ≤ n) :
    Nat.beta (Nat.unbeta ((List.range (n + 1)).map f)) j = f j := by
  have hjlen : j < ((List.range (n + 1)).map f).length := by
    rw [List.length_map, List.length_range]
    exact Nat.lt_succ_of_le hj
  have hcoe := Nat.beta_unbeta_coe ((List.range (n + 1)).map f) ⟨j, hjlen⟩
  rw [show ((⟨j, hjlen⟩ : Fin _) : ℕ) = j from rfl] at hcoe
  rw [hcoe]
  simp [List.getElem_map, List.getElem_range]

/-- β of the canonical chain witness: the coded suffixes, read back. -/
theorem beta_unbeta_chain {c n : ℕ} (j : ℕ) (hj : j ≤ n) :
    Nat.beta
      (Nat.unbeta ((List.range (n + 1)).map fun i => seqCode ((decodeSeq c).drop i)))
      j = seqCode ((decodeSeq c).drop j) :=
  beta_unbeta_map_range hj

/-- Every prefix of the tail chain is β-coded: runs exist up to the decoded length. -/
theorem runN_exists {c n : ℕ} (h : n ≤ (decodeSeq c).length) : ∃ s, RunN c n s := by
  refine ⟨Nat.unbeta ((List.range (n + 1)).map fun j => seqCode ((decodeSeq c).drop j)),
    ?_, ?_⟩
  · have hβ := beta_unbeta_chain (c := c) (n := n) 0 (Nat.zero_le n)
    rw [hβ, List.drop_zero, seqCode_decodeSeq]
  · intro j hj
    have hβj := beta_unbeta_chain (c := c) (n := n) j (Nat.le_of_lt hj)
    have hβj1 := beta_unbeta_chain (c := c) (n := n) (j + 1) (Nat.succ_le_of_lt hj)
    have hjlen : j < (decodeSeq c).length := Nat.lt_of_lt_of_le hj h
    have hd := List.drop_eq_getElem_cons hjlen
    exact ⟨_, by rw [hβj, hβj1, hd, seqCode_cons]⟩

/-! ### The run graph and the length graph -/

/-- One run step, as a graph: arguments `(j, s)` — the `j`-th β value of `s` cons-steps
to the `(j+1)`-st. -/
def runStepGraph {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 2 :=
  .exs₁ (.exs₁ (app₃ betaGraph #3 #2 #1 ⋏ app₃ betaGraph #3 (tSucc #2) #0 ⋏
    app₂ tailStepGraph #1 #0))

section runGraph

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

theorem evalN_runStepGraph (j s : ℕ) :
    EvalN 𝕊 (runStepGraph (N := N)) E ![j, s] ↔
      ∃ a, Nat.beta s j = Nat.pair a (Nat.beta s (j + 1)) + 1 := by
  have h : EvalN 𝕊 (runStepGraph (N := N)) E ![j, s] ↔
      ∃ x y : ℕ, EvalN 𝕊 (app₃ betaGraph #3 #2 #1) E (y :> x :> ![j, s]) ∧
        EvalN 𝕊 (app₃ betaGraph #3 (tSucc #2) #0) E (y :> x :> ![j, s]) ∧
        EvalN 𝕊 (app₂ tailStepGraph #1 #0) E (y :> x :> ![j, s]) := Iff.rfl
  rw [h]
  constructor
  · rintro ⟨x, y, h₁, h₂, h₃⟩
    have h₁' : x = Nat.beta s j := (evalN_app₃_betaGraph _ _ _ _).mp h₁
    have h₂' : y = Nat.beta s (j + 1) := (evalN_app₃_betaGraph _ _ _ _).mp h₂
    have h₃' : ∃ a, x = Nat.pair a y + 1 := (evalN_app₂_tailStepGraph _ _ _).mp h₃
    obtain ⟨a, ha⟩ := h₃'
    exact ⟨a, by rw [← h₁', ← h₂', ha]⟩
  · rintro ⟨a, ha⟩
    exact ⟨Nat.beta s j, Nat.beta s (j + 1), (evalN_app₃_betaGraph _ _ _ _).mpr rfl,
      (evalN_app₃_betaGraph _ _ _ _).mpr rfl,
      (evalN_app₂_tailStepGraph _ _ _).mpr ⟨a, ha⟩⟩

theorem evalN_app₂_runStepGraph (t₁ t₂ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₂ (runStepGraph (N := N)) t₁ t₂) E e ↔
      ∃ a, Nat.beta (tval t₂ e) (tval t₁ e) =
        Nat.pair a (Nat.beta (tval t₂ e) (tval t₁ e + 1)) + 1 := by
  rw [evalN_app₂, evalN_runStepGraph]

/-- The run graph: arguments `(c, n, s)`, meaning `RunN c n s`. -/
def runGraph {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 3 :=
  app₃ betaGraph #2 tZero #0 ⋏ ballLT #1 (app₂ runStepGraph #0 #3)

theorem evalN_runGraph (c n s : ℕ) :
    EvalN 𝕊 (runGraph (N := N)) E ![c, n, s] ↔ RunN c n s := by
  have h : EvalN 𝕊 (runGraph (N := N)) E ![c, n, s] ↔
      EvalN 𝕊 (app₃ betaGraph #2 tZero #0) E ![c, n, s] ∧
        EvalN 𝕊 (ballLT #1 (app₂ runStepGraph #0 #3)) E ![c, n, s] := Iff.rfl
  rw [h, evalN_ballLT]
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₁' : c = Nat.beta s 0 := (evalN_app₃_betaGraph _ _ _ _).mp h₁
    refine ⟨h₁'.symm, fun j hj => ?_⟩
    exact (evalN_app₂_runStepGraph _ _ _).mp (h₂ j hj)
  · rintro ⟨h₁, h₂⟩
    refine ⟨(evalN_app₃_betaGraph _ _ _ _).mpr h₁.symm, fun j hj => ?_⟩
    exact (evalN_app₂_runStepGraph _ _ _).mpr (h₂ j hj)

theorem evalN_app₃_runGraph (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₃ (runGraph (N := N)) t₁ t₂ t₃) E e ↔
      RunN (tval t₁ e) (tval t₂ e) (tval t₃ e) := by
  rw [evalN_app₃, evalN_runGraph]

end runGraph

/-- The length graph: arguments `(c, n)`, meaning `(decodeSeq c).length = n` — a run of
length `n` whose last β value is the nil code. -/
def seqLenGraph {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 2 :=
  .exs₁ (app₃ runGraph #1 #2 #0 ⋏ app₃ betaGraph #0 #2 tZero)

section seqLenGraph

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

/-- The length characterization the graph evaluates to. -/
theorem length_char {c m : ℕ} :
    (∃ s, RunN c m s ∧ 0 = Nat.beta s m) ↔ (decodeSeq c).length = m := by
  constructor
  · rintro ⟨s, hrun, h0⟩
    have hd := hrun.beta_eq m (Nat.le_refl m)
    have hnil : (decodeSeq c).drop m = [] := by
      have : seqCode ((decodeSeq c).drop m) = seqCode [] := by
        rw [seqCode_nil, ← hd, ← h0]
      exact seqCode_injective this
    exact Nat.le_antisymm (List.drop_eq_nil_iff.mp hnil) hrun.le_length
  · rintro rfl
    obtain ⟨s, hs⟩ := runN_exists (c := c) (Nat.le_refl _)
    refine ⟨s, hs, ?_⟩
    rw [hs.beta_eq _ (Nat.le_refl _), List.drop_length, seqCode_nil]

theorem evalN_seqLenGraph (c m : ℕ) :
    EvalN 𝕊 (seqLenGraph (N := N)) E ![c, m] ↔ (decodeSeq c).length = m := by
  have h : EvalN 𝕊 (seqLenGraph (N := N)) E ![c, m] ↔
      ∃ s : ℕ, EvalN 𝕊 (app₃ runGraph #1 #2 #0) E (s :> ![c, m]) ∧
        EvalN 𝕊 (app₃ betaGraph #0 #2 tZero) E (s :> ![c, m]) := Iff.rfl
  rw [h, ← length_char]
  exact exists_congr fun s =>
    and_congr (evalN_app₃_runGraph _ _ _ _) (evalN_app₃_betaGraph _ _ _ _)

theorem evalN_app₂_seqLenGraph (t₁ t₂ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₂ (seqLenGraph (N := N)) t₁ t₂) E e ↔
      (decodeSeq (tval t₁ e)).length = tval t₂ e := by
  rw [evalN_app₂, evalN_seqLenGraph]

end seqLenGraph

/-! ### The entry graph -/

/-- `getD` on both sides of the length boundary. -/
theorem getD_of_lt {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 = l[i] :=
  Eq.symm (List.getElem_eq_getD 0)

theorem getD_of_length_le {l : List ℕ} {i : ℕ} (h : l.length ≤ i) : l.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- Entry at a β value: arguments `(s, i, a)`, meaning the `i`-th β value of `s` is a
cons code with head `a`. -/
def entAtGraph {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 3 :=
  .exs₁ (.exs₁ (app₃ betaGraph #2 #3 #1 ⋏ app₃ consGraph #4 #0 #1))

section entAtGraph

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

theorem evalN_entAtGraph (s i a : ℕ) :
    EvalN 𝕊 (entAtGraph (N := N)) E ![s, i, a] ↔
      ∃ b, Nat.beta s i = Nat.pair a b + 1 := by
  have h : EvalN 𝕊 (entAtGraph (N := N)) E ![s, i, a] ↔
      ∃ x b : ℕ, EvalN 𝕊 (app₃ betaGraph #2 #3 #1) E (b :> x :> ![s, i, a]) ∧
        EvalN 𝕊 (app₃ consGraph #4 #0 #1) E (b :> x :> ![s, i, a]) := Iff.rfl
  rw [h]
  constructor
  · rintro ⟨x, b, h₁, h₂⟩
    have h₁' : x = Nat.beta s i := (evalN_app₃_betaGraph _ _ _ _).mp h₁
    have h₂' : x = Nat.pair a b + 1 := (evalN_app₃_consGraph _ _ _ _).mp h₂
    exact ⟨b, by rw [← h₁']; exact h₂'⟩
  · rintro ⟨b, hb⟩
    exact ⟨Nat.beta s i, b, (evalN_app₃_betaGraph _ _ _ _).mpr rfl,
      (evalN_app₃_consGraph _ _ _ _).mpr hb⟩

theorem evalN_app₃_entAtGraph (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₃ (entAtGraph (N := N)) t₁ t₂ t₃) E e ↔
      ∃ b, Nat.beta (tval t₁ e) (tval t₂ e) = Nat.pair (tval t₃ e) b + 1 := by
  rw [evalN_app₃, evalN_entAtGraph]

end entAtGraph

/-- The entry graph: arguments `(c, i, a)`, meaning `(decodeSeq c).getD i 0 = a` — the
in-range disjunct reads the head of the `i`-th suffix along a run; the out-of-range
disjunct pins the default `0` past the decoded length. -/
def seqEntGraph {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 3 :=
  (.exs₁ (app₃ runGraph #1 #2 #0 ⋏ app₃ entAtGraph #0 #2 #3)) ⋎
  (fEq #2 tZero ⋏ bexLT (tSucc #1) (app₂ seqLenGraph #1 #0))

section seqEntGraph

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

/-- The in-range characterization: a run to `i` whose end is a cons with head `a` is
exactly an in-bounds entry. -/
theorem ent_char {c i a : ℕ} :
    (∃ s, RunN c i s ∧ ∃ b, Nat.beta s i = Nat.pair a b + 1) ↔
      i < (decodeSeq c).length ∧ (decodeSeq c).getD i 0 = a := by
  constructor
  · rintro ⟨s, hrun, b, hb⟩
    have hsi : Nat.beta s i = seqCode ((decodeSeq c).drop i) :=
      hrun.beta_eq i (Nat.le_refl i)
    have h1 : decodeSeq (Nat.beta s i) = a :: decodeSeq b :=
      eq_seqCode_iff.mp (by rw [hb, seqCode_cons, seqCode_decodeSeq])
    rw [hsi, decodeSeq_seqCode] at h1
    have hi : i < (decodeSeq c).length := by
      rcases Nat.lt_or_ge i (decodeSeq c).length with h' | h'
      · exact h'
      · exfalso
        rw [List.drop_eq_nil_iff.mpr h'] at h1
        simp at h1
    refine ⟨hi, ?_⟩
    rw [List.drop_eq_getElem_cons hi] at h1
    injection h1 with h1a _
    rw [getD_of_lt hi]
    exact h1a
  · rintro ⟨hi, ha⟩
    obtain ⟨s, hs⟩ := runN_exists (Nat.le_of_lt hi)
    refine ⟨s, hs, seqCode ((decodeSeq c).drop (i + 1)), ?_⟩
    rw [hs.beta_eq i (Nat.le_refl i), List.drop_eq_getElem_cons hi, seqCode_cons]
    rw [getD_of_lt hi] at ha
    rw [ha]

/-- The entry characterization the graph evaluates to. -/
theorem getD_char {c i a : ℕ} :
    ((∃ s, RunN c i s ∧ ∃ b, Nat.beta s i = Nat.pair a b + 1) ∨
      (a = 0 ∧ ∃ m, m < i + 1 ∧ (decodeSeq c).length = m)) ↔
      (decodeSeq c).getD i 0 = a := by
  rw [ent_char]
  rcases Nat.lt_or_ge i (decodeSeq c).length with hi | hi
  · constructor
    · rintro (⟨-, ha⟩ | ⟨rfl, m, hm, hlen⟩)
      · exact ha
      · exfalso
        omega
    · intro ha
      exact Or.inl ⟨hi, ha⟩
  · have h0 : (decodeSeq c).getD i 0 = 0 := getD_of_length_le hi
    constructor
    · rintro (⟨hlt, -⟩ | ⟨rfl, -⟩)
      · exfalso
        omega
      · exact h0
    · intro ha
      exact Or.inr ⟨by rw [← ha, h0], (decodeSeq c).length, by omega, rfl⟩

theorem evalN_seqEntGraph (c i a : ℕ) :
    EvalN 𝕊 (seqEntGraph (N := N)) E ![c, i, a] ↔ (decodeSeq c).getD i 0 = a := by
  have h : EvalN 𝕊 (seqEntGraph (N := N)) E ![c, i, a] ↔
      (∃ s : ℕ, EvalN 𝕊 (app₃ runGraph #1 #2 #0) E (s :> ![c, i, a]) ∧
        EvalN 𝕊 (app₃ entAtGraph #0 #2 #3) E (s :> ![c, i, a])) ∨
      (EvalN 𝕊 (fEq #2 tZero) E ![c, i, a] ∧
        EvalN 𝕊 (bexLT (tSucc #1) (app₂ seqLenGraph #1 #0)) E ![c, i, a]) := Iff.rfl
  rw [h, ← getD_char]
  refine or_congr ?_ ?_
  · exact exists_congr fun s =>
      and_congr (evalN_app₃_runGraph _ _ _ _) (evalN_app₃_entAtGraph _ _ _ _)
  · refine and_congr evalN_fEq ?_
    rw [evalN_bexLT]
    exact exists_congr fun m => and_congr Iff.rfl (evalN_app₂_seqLenGraph _ _ _)

theorem evalN_app₃_seqEntGraph (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₃ (seqEntGraph (N := N)) t₁ t₂ t₃) E e ↔
      (decodeSeq (tval t₁ e)).getD (tval t₂ e) 0 = tval t₃ e := by
  rw [evalN_app₃, evalN_seqEntGraph]

end seqEntGraph

/-! ### The take graph -/

/-- A cons at a β position of the built chain: arguments `(s', j, a)` — the `j`-th β
value of `s'` conses `a` onto the `(j+1)`-st. -/
def consAtGraph {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 3 :=
  .exs₁ (.exs₁ (app₃ betaGraph #2 (tSucc #3) #1 ⋏ app₃ betaGraph #2 #3 #0 ⋏
    app₃ consGraph #4 #1 #0))

section takeGraph

variable {𝕊 : Set (Set ℕ)} {N n : ℕ} {E : Fin N → Set ℕ}

theorem evalN_consAtGraph (s' j a : ℕ) :
    EvalN 𝕊 (consAtGraph (N := N)) E ![s', j, a] ↔
      Nat.beta s' j = Nat.pair a (Nat.beta s' (j + 1)) + 1 := by
  have h : EvalN 𝕊 (consAtGraph (N := N)) E ![s', j, a] ↔
      ∃ x y : ℕ, EvalN 𝕊 (app₃ betaGraph #2 (tSucc #3) #1) E (y :> x :> ![s', j, a]) ∧
        EvalN 𝕊 (app₃ betaGraph #2 #3 #0) E (y :> x :> ![s', j, a]) ∧
        EvalN 𝕊 (app₃ consGraph #4 #1 #0) E (y :> x :> ![s', j, a]) := Iff.rfl
  rw [h]
  constructor
  · rintro ⟨x, y, h₁, h₂, h₃⟩
    have h₁' : x = Nat.beta s' (j + 1) := (evalN_app₃_betaGraph _ _ _ _).mp h₁
    have h₂' : y = Nat.beta s' j := (evalN_app₃_betaGraph _ _ _ _).mp h₂
    have h₃' : y = Nat.pair a x + 1 := (evalN_app₃_consGraph _ _ _ _).mp h₃
    rw [← h₂', ← h₁']
    exact h₃'
  · intro hy
    exact ⟨Nat.beta s' (j + 1), Nat.beta s' j, (evalN_app₃_betaGraph _ _ _ _).mpr rfl,
      (evalN_app₃_betaGraph _ _ _ _).mpr rfl, (evalN_app₃_consGraph _ _ _ _).mpr hy⟩

theorem evalN_app₃_consAtGraph (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₃ (consAtGraph (N := N)) t₁ t₂ t₃) E e ↔
      Nat.beta (tval t₁ e) (tval t₂ e) =
        Nat.pair (tval t₃ e) (Nat.beta (tval t₁ e) (tval t₂ e + 1)) + 1 := by
  rw [evalN_app₃, evalN_consAtGraph]

/-- One build step: arguments `(j, s, s')` — some head read from the run chain at `j` is
consed by the built chain at `j`. -/
def buildStepGraph {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 3 :=
  .exs₁ (app₃ entAtGraph #2 #1 #0 ⋏ app₃ consAtGraph #3 #1 #0)

theorem evalN_buildStepGraph (j s s' : ℕ) :
    EvalN 𝕊 (buildStepGraph (N := N)) E ![j, s, s'] ↔
      ∃ a, (∃ b, Nat.beta s j = Nat.pair a b + 1) ∧
        Nat.beta s' j = Nat.pair a (Nat.beta s' (j + 1)) + 1 := by
  have h : EvalN 𝕊 (buildStepGraph (N := N)) E ![j, s, s'] ↔
      ∃ a : ℕ, EvalN 𝕊 (app₃ entAtGraph #2 #1 #0) E (a :> ![j, s, s']) ∧
        EvalN 𝕊 (app₃ consAtGraph #3 #1 #0) E (a :> ![j, s, s']) := Iff.rfl
  rw [h]
  exact exists_congr fun a =>
    and_congr (evalN_app₃_entAtGraph _ _ _ _) (evalN_app₃_consAtGraph _ _ _ _)

theorem evalN_app₃_buildStepGraph (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₃ (buildStepGraph (N := N)) t₁ t₂ t₃) E e ↔
      ∃ a, (∃ b, Nat.beta (tval t₂ e) (tval t₁ e) = Nat.pair a b + 1) ∧
        Nat.beta (tval t₃ e) (tval t₁ e) =
          Nat.pair a (Nat.beta (tval t₃ e) (tval t₁ e + 1)) + 1 := by
  rw [evalN_app₃, evalN_buildStepGraph]

/-- The built chain: `s'` β-codes the suffix codes of the truncation, driven by the head
reads of the run chain `s`. Stated in pair form, matching the formula. -/
def BuildN (s s' m : ℕ) : Prop :=
  0 = Nat.beta s' m ∧ ∀ j < m, ∃ a, (∃ b, Nat.beta s j = Nat.pair a b + 1) ∧
    Nat.beta s' j = Nat.pair a (Nat.beta s' (j + 1)) + 1

/-- The build graph: arguments `(s, s', m)`, meaning `BuildN s s' m`. -/
def buildGraph {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 3 :=
  app₃ betaGraph #1 #2 tZero ⋏ ballLT #2 (app₃ buildStepGraph #0 #1 #2)

theorem evalN_buildGraph (s s' m : ℕ) :
    EvalN 𝕊 (buildGraph (N := N)) E ![s, s', m] ↔ BuildN s s' m := by
  have h : EvalN 𝕊 (buildGraph (N := N)) E ![s, s', m] ↔
      EvalN 𝕊 (app₃ betaGraph #1 #2 tZero) E ![s, s', m] ∧
        EvalN 𝕊 (ballLT #2 (app₃ buildStepGraph #0 #1 #2)) E ![s, s', m] := Iff.rfl
  rw [h, evalN_ballLT]
  refine and_congr (evalN_app₃_betaGraph _ _ _ _) ?_
  exact forall_congr' fun j => imp_congr Iff.rfl (evalN_app₃_buildStepGraph _ _ _ _)

theorem evalN_app₃_buildGraph (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₃ (buildGraph (N := N)) t₁ t₂ t₃) E e ↔
      BuildN (tval t₁ e) (tval t₂ e) (tval t₃ e) := by
  rw [evalN_app₃, evalN_buildGraph]

/-- Dropping past the truncation point is nil. -/
theorem drop_take_self (l : List ℕ) (m : ℕ) : (l.take m).drop m = [] :=
  List.drop_eq_nil_iff.mpr
    (by rw [List.length_take]; exact Nat.min_le_left m l.length)

/-- Along a run and its built chain, the built β values are exactly the codes of the
dropped suffixes of the truncation — downward induction from the nil top. -/
theorem BuildN.beta_eq_aux {c m s s' : ℕ} (hrun : RunN c m s)
    (hm : m ≤ (decodeSeq c).length) (hb : BuildN s s' m) :
    ∀ d j, j + d = m → Nat.beta s' j = seqCode (((decodeSeq c).take m).drop j)
  | 0, j, hj => by
      have hjm : j = m := by omega
      subst hjm
      rw [drop_take_self, seqCode_nil]
      exact hb.1.symm
  | d + 1, j, hj => by
      have hjm : j < m := by omega
      obtain ⟨a, ⟨b, hab⟩, hcons⟩ := hb.2 j hjm
      have hsj : Nat.beta s j = seqCode ((decodeSeq c).drop j) :=
        hrun.beta_eq j (Nat.le_of_lt hjm)
      have hjlen : j < (decodeSeq c).length := Nat.lt_of_lt_of_le hjm hm
      have h1 : decodeSeq (Nat.beta s j) = a :: decodeSeq b :=
        eq_seqCode_iff.mp (by rw [hab, seqCode_cons, seqCode_decodeSeq])
      rw [hsj, decodeSeq_seqCode, List.drop_eq_getElem_cons hjlen] at h1
      injection h1 with h1a _
      have hIH := BuildN.beta_eq_aux hrun hm hb d (j + 1) (by omega)
      have hjlen' : j < ((decodeSeq c).take m).length := by
        rw [List.length_take]
        exact Nat.lt_min.mpr ⟨hjm, hjlen⟩
      rw [List.drop_eq_getElem_cons hjlen', seqCode_cons, List.getElem_take, ← hIH,
        hcons, ← h1a]

/-- The built chain exists for every run within the decoded length. -/
theorem buildN_exists {c m s : ℕ} (hrun : RunN c m s)
    (hm : m ≤ (decodeSeq c).length) :
    ∃ s', BuildN s s' m ∧ Nat.beta s' 0 = seqCode ((decodeSeq c).take m) := by
  refine ⟨Nat.unbeta ((List.range (m + 1)).map fun j =>
    seqCode (((decodeSeq c).take m).drop j)), ⟨?_, ?_⟩, ?_⟩
  · rw [beta_unbeta_map_range (Nat.le_refl m), drop_take_self, seqCode_nil]
  · intro j hj
    have hjlen : j < (decodeSeq c).length := Nat.lt_of_lt_of_le hj hm
    obtain ⟨a, hab⟩ := hrun.2 j hj
    have hsj : Nat.beta s j = seqCode ((decodeSeq c).drop j) :=
      hrun.beta_eq j (Nat.le_of_lt hj)
    have h1 : decodeSeq (Nat.beta s j) = a :: decodeSeq (Nat.beta s (j + 1)) :=
      eq_seqCode_iff.mp (by rw [hab, seqCode_cons, seqCode_decodeSeq])
    rw [hsj, decodeSeq_seqCode, List.drop_eq_getElem_cons hjlen] at h1
    injection h1 with h1a _
    refine ⟨a, ⟨_, hab⟩, ?_⟩
    rw [beta_unbeta_map_range (Nat.le_of_lt hj),
      beta_unbeta_map_range (Nat.succ_le_of_lt hj)]
    have hjlen' : j < ((decodeSeq c).take m).length := by
      rw [List.length_take]
      exact Nat.lt_min.mpr ⟨hj, hjlen⟩
    rw [List.drop_eq_getElem_cons hjlen', seqCode_cons, List.getElem_take, ← h1a]
  · rw [beta_unbeta_map_range (Nat.zero_le m), List.drop_zero]

/-- Reading the truncation off a built chain: arguments `(c, m, t)`. -/
def takeRunGraph {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 3 :=
  .exs₁ (.exs₁ (app₃ runGraph #2 #3 #1 ⋏ app₃ buildGraph #1 #0 #3 ⋏
    app₃ betaGraph #0 tZero #4))

theorem evalN_takeRunGraph (c m t : ℕ) :
    EvalN 𝕊 (takeRunGraph (N := N)) E ![c, m, t] ↔
      ∃ s s', RunN c m s ∧ BuildN s s' m ∧ t = Nat.beta s' 0 := by
  have h : EvalN 𝕊 (takeRunGraph (N := N)) E ![c, m, t] ↔
      ∃ s s' : ℕ, EvalN 𝕊 (app₃ runGraph #2 #3 #1) E (s' :> s :> ![c, m, t]) ∧
        EvalN 𝕊 (app₃ buildGraph #1 #0 #3) E (s' :> s :> ![c, m, t]) ∧
        EvalN 𝕊 (app₃ betaGraph #0 tZero #4) E (s' :> s :> ![c, m, t]) := Iff.rfl
  rw [h]
  exact exists_congr fun s => exists_congr fun s' =>
    and_congr (evalN_app₃_runGraph _ _ _ _)
      (and_congr (evalN_app₃_buildGraph _ _ _ _) (evalN_app₃_betaGraph _ _ _ _))

theorem evalN_app₃_takeRunGraph (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₃ (takeRunGraph (N := N)) t₁ t₂ t₃) E e ↔
      ∃ s s', RunN (tval t₁ e) (tval t₂ e) s ∧ BuildN s s' (tval t₂ e) ∧
        tval t₃ e = Nat.beta s' 0 := by
  rw [evalN_app₃, evalN_takeRunGraph]

/-- The take graph: arguments `(c, k, t)`, meaning `t = seqCode ((decodeSeq c).take k)`.
The existential `m` is `min k (decoded length)`, pinned by the two `Min` disjuncts. -/
def seqTakeGraph {N : ℕ} : SecondOrder.Semiformula ℒₒᵣ Empty Empty N 3 :=
  .exs₁ (((fEq #0 #2 ⋏ .exs₁ (app₃ runGraph #2 #1 #0)) ⋎
    (app₂ seqLenGraph #1 #0 ⋏ fLt #0 (tSucc #2))) ⋏
    app₃ takeRunGraph #1 #0 #3)

/-- The truncation characterization the graph evaluates to. -/
theorem take_char {c k t : ℕ} :
    (∃ m, ((m = k ∧ ∃ s, RunN c m s) ∨
        ((decodeSeq c).length = m ∧ m < k + 1)) ∧
      ∃ s s', RunN c m s ∧ BuildN s s' m ∧ t = Nat.beta s' 0) ↔
      t = seqCode ((decodeSeq c).take k) := by
  constructor
  · rintro ⟨m, hmin, s, s', hrun, hbuild, ht⟩
    have hm : m ≤ (decodeSeq c).length := hrun.le_length
    have htake : (decodeSeq c).take m = (decodeSeq c).take k := by
      rcases hmin with ⟨rfl, -⟩ | ⟨hlen, hmk⟩
      · rfl
      · rw [← hlen, List.take_length]
        exact (List.take_of_length_le (by omega)).symm
    have hβ0 := BuildN.beta_eq_aux hrun hm hbuild m 0 (Nat.zero_add m)
    rw [ht, hβ0, List.drop_zero, htake]
  · rintro rfl
    rcases Nat.lt_or_ge (decodeSeq c).length k with hk | hk
    · refine ⟨(decodeSeq c).length, Or.inr ⟨rfl, by omega⟩, ?_⟩
      obtain ⟨s, hs⟩ := runN_exists (Nat.le_refl _)
      obtain ⟨s', hb, h0⟩ := buildN_exists hs (Nat.le_refl _)
      refine ⟨s, s', hs, hb, ?_⟩
      rw [h0, List.take_length, List.take_of_length_le (Nat.le_of_lt hk)]
    · refine ⟨k, Or.inl ⟨rfl, runN_exists hk⟩, ?_⟩
      obtain ⟨s, hs⟩ := runN_exists hk
      obtain ⟨s', hb, h0⟩ := buildN_exists hs hk
      exact ⟨s, s', hs, hb, h0.symm⟩

theorem evalN_seqTakeGraph (c k t : ℕ) :
    EvalN 𝕊 (seqTakeGraph (N := N)) E ![c, k, t] ↔
      t = seqCode ((decodeSeq c).take k) := by
  have h : EvalN 𝕊 (seqTakeGraph (N := N)) E ![c, k, t] ↔
      ∃ m : ℕ,
        ((EvalN 𝕊 (fEq #0 #2) E (m :> ![c, k, t]) ∧
          ∃ s : ℕ, EvalN 𝕊 (app₃ runGraph #2 #1 #0) E (s :> m :> ![c, k, t])) ∨
         (EvalN 𝕊 (app₂ seqLenGraph #1 #0) E (m :> ![c, k, t]) ∧
          EvalN 𝕊 (fLt #0 (tSucc #2)) E (m :> ![c, k, t]))) ∧
        EvalN 𝕊 (app₃ takeRunGraph #1 #0 #3) E (m :> ![c, k, t]) := Iff.rfl
  rw [h, ← take_char]
  refine exists_congr fun m => and_congr (or_congr ?_ ?_) (evalN_app₃_takeRunGraph _ _ _ _)
  · exact and_congr evalN_fEq (exists_congr fun s => evalN_app₃_runGraph _ _ _ _)
  · exact and_congr (evalN_app₂_seqLenGraph _ _ _) evalN_fLt

theorem evalN_app₃_seqTakeGraph (t₁ t₂ t₃ : Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (app₃ (seqTakeGraph (N := N)) t₁ t₂ t₃) E e ↔
      tval t₃ e = seqCode ((decodeSeq (tval t₁ e)).take (tval t₂ e)) := by
  rw [evalN_app₃, evalN_seqTakeGraph]

end takeGraph

end RMFoundationBridge
