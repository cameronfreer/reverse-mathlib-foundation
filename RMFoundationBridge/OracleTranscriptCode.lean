/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.BoundedSeqArith
import RMFoundationBridge.OracleTranscript

/-!
# Converse adequacy, Slice C2: the classified transcript checker and its agreement

The syntactic half of downward closure: a `Delta0Code 1 1` — one set slot for the oracle
set `B`, one number slot for the transcript code `T` — whose Tarski evaluation is
**exactly** the semantic predicate `Verified B (tableOf T)` of Slice C1, in both
directions, for every standard-ℕ set domain and assignment.

**Pinned conventions.**

* `T = pair L S`; the table is precisely the first `L` values `Nat.beta S i`, each decoded
  by the C1 convention `Entry.ofNat` (`tableOf`).
* Codes are read arithmetically through `encodeCode`'s literal equations: `0`–`4` are the
  five base constructors, and every `c ≥ 5` is `2·(2·m) + 5` (pair), `2·(2·m + 1) + 5`
  (comp), `2·(2·m) + 1 + 5` (prec), or `2·(2·m + 1) + 1 + 5` (rfind'); for pair, comp,
  and prec the two sub-codes are the unpairing of `m`, while rfind' uses `m` itself as
  its sub-code. The **constructor-shape theorem** (`codeShape`) is
  bidirectional and covers **arbitrary** naturals: each falls into exactly one of the nine
  cases, the arithmetic branch agrees with `ofNatCode`, and encoding each constructor
  yields its branch. The formula is the exhaustive nine-way disjunction — never a family
  of implications that a malformed code could satisfy vacuously.
* Every inner witness carries an explicit bound: entry components by the entry, entries
  by the seed `S` (`Nat.beta S i ≤ S`), the pair witnesses by the pair, the predecessor
  fuel by the stored fuel. Constructor decoding uses no division or remainder checker:
  the residue shapes are stated through `2·(2·m) + …` equations with `m` a bounded
  witness. Reading an entry off the seed goes through `betaCode`, hence through
  `modCode`'s bounded remainder — always at the positive modulus `(i + 1)·d + 1`, so the
  toolkit's positive-modulus boundary is respected.
* The reduced set `A` does not occur in this module.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-! ### Toolkit additions: numerals and generic substitution -/

/-- The numeral term `n`, as `n` successors of zero. -/
def tNum {n : ℕ} : ℕ → Semiterm ℒₒᵣ Empty n
  | 0 => tZero
  | m + 1 => tSucc (tNum m)

@[simp] theorem tval_tNum {n : ℕ} (m : ℕ) (e : Fin n → ℕ) : tval (tNum m) e = m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [tNum, tval_tSucc, ih]

/-- Evaluation of an arbitrary-arity substitution: the values of the substituted
terms. -/
theorem evalN_rew_subst {𝕊 : Set (Set ℕ)} {N m n : ℕ} {E : Fin N → Set ℕ}
    (φ : SecondOrder.Semiformula ℒₒᵣ Empty Empty N m) (v : Fin m → Semiterm ℒₒᵣ Empty n)
    (e : Fin n → ℕ) :
    EvalN 𝕊 (Rew.subst v ▹ φ) E e ↔ EvalN 𝕊 φ E (fun i => tval (v i) e) := by
  unfold EvalN
  rw [eval_rew φ (Rew.subst v) E Empty.elim e]
  have hb : (Semiterm.val (M := ℕ) (s := standardInterpretation) e Empty.elim ∘
      (Rew.subst v) ∘ Semiterm.bvar) = fun i => tval (v i) e := by
    funext i
    simp [FirstOrder.Rew.subst, tval]
  have hf : (Semiterm.val (M := ℕ) (s := standardInterpretation) e Empty.elim ∘
      (Rew.subst v) ∘ Semiterm.fvar) = Empty.elim := by
    funext y
    exact y.elim
  rw [hb, hf]

namespace Delta0Code

/-- Apply a code at a vector of terms (the arbitrary-arity `app`). -/
def app {N m n : ℕ} (c : Delta0Code N m) (v : Fin m → Semiterm ℒₒᵣ Empty n) :
    Delta0Code N n :=
  c.rew (Rew.subst v)

theorem evalN_app {𝕊 : Set (Set ℕ)} {N m n : ℕ} {E : Fin N → Set ℕ} (c : Delta0Code N m)
    (v : Fin m → Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    EvalN 𝕊 (c.app v).toFormula E e ↔ EvalN 𝕊 c.toFormula E (fun i => tval (v i) e) := by
  rw [app, toFormula_rew, evalN_rew_subst]

end Delta0Code

/-- Term-value vectors normalize entrywise, so the `![…]`-form agreement theorems fire
after `Delta0Code.evalN_app`. -/
theorem tval_vecCons {n m : ℕ} (t : Semiterm ℒₒᵣ Empty n)
    (v : Fin m → Semiterm ℒₒᵣ Empty n) (e : Fin n → ℕ) :
    (fun i => tval (Matrix.vecCons t v i) e) = Matrix.vecCons (tval t e) fun i => tval (v i) e := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j => rfl

theorem tval_vecEmpty {n : ℕ} (e : Fin n → ℕ) :
    (fun i => tval ((![] : Fin 0 → Semiterm ℒₒᵣ Empty n) i) e) = ![] := by
  funext i
  exact i.elim0

/-- β is bounded by its seed. -/
theorem Nat.beta_le (s i : ℕ) : Nat.beta s i ≤ s :=
  le_trans (Nat.mod_le _ _) (Nat.unpair_left_le s)

/-! ### The constructor-shape theorem, for arbitrary naturals -/

theorem encodeCode_ofNatCode (m : ℕ) : (OracleCode.ofNatCode m).encodeCode = m := by
  rw [← OracleCode.ofNatCode_eq, ← OracleCode.encodeCode_eq]
  exact Denumerable.encode_ofNat m

/-- The nine arithmetic shapes of a code, with the composite shapes stated through
`encodeCode`'s literal equations. -/
inductive CodeShape : ℕ → Prop
  | zero : CodeShape 0
  | succ : CodeShape 1
  | left : CodeShape 2
  | right : CodeShape 3
  | oracle : CodeShape 4
  | pair (m : ℕ) : CodeShape (2 * (2 * m) + 5)
  | comp (m : ℕ) : CodeShape (2 * (2 * m + 1) + 5)
  | prec (m : ℕ) : CodeShape (2 * (2 * m) + 1 + 5)
  | rfind' (m : ℕ) : CodeShape (2 * (2 * m + 1) + 1 + 5)

/-- Every natural has a shape. -/
theorem codeShape (c : ℕ) : CodeShape c := by
  rcases lt_or_ge c 5 with h | h
  · rcases c with _ | _ | _ | _ | _ | c
    · exact .zero
    · exact .succ
    · exact .left
    · exact .right
    · exact .oracle
    · omega
  · have hr : (c - 5) % 4 = 0 ∨ (c - 5) % 4 = 1 ∨ (c - 5) % 4 = 2 ∨ (c - 5) % 4 = 3 := by
      omega
    rcases hr with hr | hr | hr | hr
    · rw [show c = 2 * (2 * ((c - 5) / 4)) + 5 by omega]; exact .pair _
    · rw [show c = 2 * (2 * ((c - 5) / 4)) + 1 + 5 by omega]; exact .prec _
    · rw [show c = 2 * (2 * ((c - 5) / 4) + 1) + 5 by omega]; exact .comp _
    · rw [show c = 2 * (2 * ((c - 5) / 4) + 1) + 1 + 5 by omega]; exact .rfind' _

/-- **Uniqueness of shape**: the nine shapes are pairwise exclusive and each composite
form is injective in `m` — every base value is below `5` while every composite value is
at least `5` (base/composite separation), the four composite forms are pairwise disjoint
(six cross-exclusions), and each of the four is injective. Together with `codeShape`,
every natural has exactly one shape with exactly one parameter. (The clause agreement
handles these facts inline; this theorem names them.) -/
theorem codeShape_unique (m m' : ℕ) :
    -- base/composite separation
    (5 ≤ 2 * (2 * m) + 5 ∧ 5 ≤ 2 * (2 * m + 1) + 5 ∧ 5 ≤ 2 * (2 * m) + 1 + 5 ∧
      5 ≤ 2 * (2 * m + 1) + 1 + 5) ∧
    -- injectivity of each composite form
    (2 * (2 * m) + 5 = 2 * (2 * m') + 5 → m = m') ∧
    (2 * (2 * m + 1) + 5 = 2 * (2 * m' + 1) + 5 → m = m') ∧
    (2 * (2 * m) + 1 + 5 = 2 * (2 * m') + 1 + 5 → m = m') ∧
    (2 * (2 * m + 1) + 1 + 5 = 2 * (2 * m' + 1) + 1 + 5 → m = m') ∧
    -- pairwise disjointness of the composite forms
    (2 * (2 * m) + 5 ≠ 2 * (2 * m' + 1) + 5) ∧ (2 * (2 * m) + 5 ≠ 2 * (2 * m') + 1 + 5) ∧
    (2 * (2 * m) + 5 ≠ 2 * (2 * m' + 1) + 1 + 5) ∧
    (2 * (2 * m + 1) + 5 ≠ 2 * (2 * m') + 1 + 5) ∧
    (2 * (2 * m + 1) + 5 ≠ 2 * (2 * m' + 1) + 1 + 5) ∧
    (2 * (2 * m) + 1 + 5 ≠ 2 * (2 * m' + 1) + 1 + 5) := by
  omega

/-- `ofNatCode` at `n + 5`, by the decoder's own equation. -/
theorem ofNatCode_add_five (n : ℕ) :
    OracleCode.ofNatCode (n + 5) =
      match n.bodd, n.div2.bodd with
      | false, false => .pair (OracleCode.ofNatCode n.div2.div2.unpair.1)
          (OracleCode.ofNatCode n.div2.div2.unpair.2)
      | false, true => .comp (OracleCode.ofNatCode n.div2.div2.unpair.1)
          (OracleCode.ofNatCode n.div2.div2.unpair.2)
      | true, false => .prec (OracleCode.ofNatCode n.div2.div2.unpair.1)
          (OracleCode.ofNatCode n.div2.div2.unpair.2)
      | true, true => .rfind' (OracleCode.ofNatCode n.div2.div2) :=
  OracleCode.ofNatCode.eq_6 n

/-- The arithmetic branches agree with the decoder (forward direction of the shape
theorem), one lemma per composite constructor. -/
theorem ofNatCode_pair_shape (m : ℕ) :
    OracleCode.ofNatCode (2 * (2 * m) + 5) =
      .pair (OracleCode.ofNatCode m.unpair.1) (OracleCode.ofNatCode m.unpair.2) := by
  rw [show 2 * (2 * m) = Nat.bit false (Nat.bit false m) by simp [Nat.bit_val],
    ofNatCode_add_five]
  simp

theorem ofNatCode_comp_shape (m : ℕ) :
    OracleCode.ofNatCode (2 * (2 * m + 1) + 5) =
      .comp (OracleCode.ofNatCode m.unpair.1) (OracleCode.ofNatCode m.unpair.2) := by
  rw [show 2 * (2 * m + 1) = Nat.bit false (Nat.bit true m) by simp [Nat.bit_val],
    ofNatCode_add_five]
  simp

theorem ofNatCode_prec_shape (m : ℕ) :
    OracleCode.ofNatCode (2 * (2 * m) + 1 + 5) =
      .prec (OracleCode.ofNatCode m.unpair.1) (OracleCode.ofNatCode m.unpair.2) := by
  rw [show 2 * (2 * m) + 1 = Nat.bit true (Nat.bit false m) by simp [Nat.bit_val],
    ofNatCode_add_five]
  simp

theorem ofNatCode_rfind'_shape (m : ℕ) :
    OracleCode.ofNatCode (2 * (2 * m + 1) + 1 + 5) =
      .rfind' (OracleCode.ofNatCode m) := by
  rw [show 2 * (2 * m + 1) + 1 = Nat.bit true (Nat.bit true m) by simp [Nat.bit_val],
    ofNatCode_add_five]
  simp

/-- Encoding each constructor gives its branch (the converse direction), literally
`encodeCode`'s equations. -/
theorem encodeCode_pair (cf cg : OracleCode) :
    (OracleCode.pair cf cg).encodeCode =
      2 * (2 * Nat.pair cf.encodeCode cg.encodeCode) + 5 := rfl
theorem encodeCode_comp (cf cg : OracleCode) :
    (OracleCode.comp cf cg).encodeCode =
      2 * (2 * Nat.pair cf.encodeCode cg.encodeCode + 1) + 5 := rfl
theorem encodeCode_prec (cf cg : OracleCode) :
    (OracleCode.prec cf cg).encodeCode =
      2 * (2 * Nat.pair cf.encodeCode cg.encodeCode) + 1 + 5 := rfl
theorem encodeCode_rfind' (cf : OracleCode) :
    (OracleCode.rfind' cf).encodeCode = 2 * (2 * cf.encodeCode + 1) + 1 + 5 := rfl

/-! ### Tables: `T = pair L S`, entries `β S i`, decoded by the C1 convention -/

/-- The table a transcript code denotes: precisely the first `L = (unpair T).1` values
`Nat.beta S i` with `S = (unpair T).2`, each decoded by `Entry.ofNat`. -/
def tableOf (T : ℕ) : List Entry :=
  (List.range T.unpair.1).map fun i => Entry.ofNat (Nat.beta T.unpair.2 i)

theorem tableOf_length (T : ℕ) : (tableOf T).length = T.unpair.1 := by
  simp [tableOf]

theorem tableOf_getElem? (T i : ℕ) : getElem? (tableOf T) i =
      if i < T.unpair.1 then some (Entry.ofNat (Nat.beta T.unpair.2 i)) else none := by
  simp only [tableOf, List.getElem?_map]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

/-- Every list is the table of some code: length paired with the `unbeta` seed, read back
through the checked β agreement at every `i < L`. -/
theorem exists_tableOf (L : List Entry) :
    tableOf (Nat.pair L.length (Nat.unbeta (L.map Entry.toNat))) = L := by
  apply List.ext_getElem?
  intro i
  rw [tableOf_getElem?, Nat.unpair_pair]
  simp only
  by_cases hi : i < L.length
  · rw [if_pos hi, List.getElem?_eq_getElem hi]
    have hlen : i < (L.map Entry.toNat).length := by simpa using hi
    have := Nat.beta_unbeta_coe (L.map Entry.toNat) ⟨i, hlen⟩
    simp only [Fin.getElem_fin, List.getElem_map] at this
    rw [this, Entry.ofNat_toNat]
  · rw [if_neg hi, List.getElem?_eq_none (Nat.le_of_not_lt hi)]

/-- Support read directly off the seed: an earlier index whose β-entry decodes to `e`. -/
def SupportsAt (S i : ℕ) (e : Entry) : Prop := ∃ j < i, Entry.ofNat (Nat.beta S j) = e

/-- Below the length, seed support is table support. -/
theorem supportsAt_iff_supports {T : ℕ} {i : ℕ} (hi : i ≤ T.unpair.1) (e : Entry) :
    SupportsAt T.unpair.2 i e ↔ Supports (tableOf T) i e := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, by rw [tableOf_getElem?, if_pos (by omega)]⟩
  · rintro ⟨j, hj, hje⟩
    rw [tableOf_getElem?, if_pos (by omega)] at hje
    exact ⟨j, hj, Option.some_injective _ hje⟩

/-! ### Component bounds: everything read off an entry is bounded by it -/

theorem Entry.fuel_ofNat_le (m : ℕ) : (Entry.ofNat m).fuel ≤ m := Nat.unpair_left_le m
theorem Entry.code_ofNat_le (m : ℕ) : (Entry.ofNat m).code ≤ m :=
  le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le m)
theorem Entry.input_ofNat_le (m : ℕ) : (Entry.ofNat m).input ≤ m :=
  le_trans (Nat.unpair_left_le _) (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le m))
theorem Entry.output_ofNat_le (m : ℕ) : (Entry.ofNat m).output ≤ m :=
  le_trans (Nat.unpair_right_le _) (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le m))

theorem SupportsAt.fuel_le {S i : ℕ} {e : Entry} (h : SupportsAt S i e) : e.fuel ≤ S :=
  let ⟨j, _, hj⟩ := h
  hj ▸ le_trans (Entry.fuel_ofNat_le _) (Nat.beta_le S j)
theorem SupportsAt.code_le {S i : ℕ} {e : Entry} (h : SupportsAt S i e) : e.code ≤ S :=
  let ⟨j, _, hj⟩ := h
  hj ▸ le_trans (Entry.code_ofNat_le _) (Nat.beta_le S j)
theorem SupportsAt.input_le {S i : ℕ} {e : Entry} (h : SupportsAt S i e) : e.input ≤ S :=
  let ⟨j, _, hj⟩ := h
  hj ▸ le_trans (Entry.input_ofNat_le _) (Nat.beta_le S j)
theorem SupportsAt.output_le {S i : ℕ} {e : Entry} (h : SupportsAt S i e) :
    e.output ≤ S :=
  let ⟨j, _, hj⟩ := h
  hj ▸ le_trans (Entry.output_ofNat_le _) (Nat.beta_le S j)

/-! ### Layer 1: the entry decoder -/

/-- `decodeEntryCode (e, K, c, n, x)`: `e = pair K (pair c (pair n x))`, with the two
intermediate pairs as witnesses, `p` bounded by `e` and `q` by `p`. Beneath the binders
`#0 = q`, `#1 = p`, `#2 = e`, `#3 = K`, `#4 = c`, `#5 = n`, `#6 = x`; each bound is read
in the environment just outside its own binder. -/
def decodeEntryCode : Delta0Code 1 5 :=
  .bex (tSucc #0) (.bex (tSucc #0)
    (.and (pairCode.app ![#3, #1, #2]) (.and (pairCode.app ![#4, #0, #1])
      (pairCode.app ![#5, #6, #0]))))

section layer1

variable {𝕊 : Set (Set ℕ)} {E : Fin 1 → Set ℕ}

theorem evalN_decodeEntryCode (e K c n x : ℕ) :
    EvalN 𝕊 decodeEntryCode.toFormula E ![e, K, c, n, x] ↔
      e = Entry.toNat ⟨K, c, n, x⟩ := by
  rw [show decodeEntryCode.toFormula = bexLT (tSucc #0) (bexLT (tSucc #0)
    ((pairCode.app ![#3, #1, #2]).toFormula ⋏ ((pairCode.app ![#4, #0, #1]).toFormula ⋏
      (pairCode.app ![#5, #6, #0]).toFormula))) from rfl]
  simp only [evalN_bexLT, evalN_and, Delta0Code.evalN_app, tval_vecCons, tval_vecEmpty,
    evalN_pairCode]
  change (∃ p, p < e + 1 ∧ ∃ q, q < p + 1 ∧
    (e = Nat.pair K p ∧ p = Nat.pair c q ∧ q = Nat.pair n x)) ↔ _
  constructor
  · rintro ⟨p, -, q, -, rfl, rfl, rfl⟩
    rfl
  · rintro rfl
    exact ⟨_, Nat.lt_succ_of_le (Nat.right_le_pair _ _), _,
      Nat.lt_succ_of_le (Nat.right_le_pair _ _), rfl, rfl, rfl⟩

end layer1

/-! ### Layer 2: support at a strictly earlier index -/

/-- `supportsCode (S, i, K, c, n, x)`: some `j < i` has `β S j = e` with `e` decoding to
`(K, c, n, x)`; `e` is bounded by the seed. Beneath the binders `#0 = e`, `#1 = j`,
`#2 = S`, `#3 = i`, `#4 = K`, `#5 = c`, `#6 = n`, `#7 = x`. -/
def supportsCode : Delta0Code 1 6 :=
  .bex #1 (.bex (tSucc #1)
    (.and (betaCode.app ![#2, #1, #0]) (decodeEntryCode.app ![#0, #4, #5, #6, #7])))

section layer2

variable {𝕊 : Set (Set ℕ)} {E : Fin 1 → Set ℕ}

theorem evalN_supportsCode (S i K c n x : ℕ) :
    EvalN 𝕊 supportsCode.toFormula E ![S, i, K, c, n, x] ↔
      SupportsAt S i ⟨K, c, n, x⟩ := by
  rw [show supportsCode.toFormula = bexLT #1 (bexLT (tSucc #1)
    ((betaCode.app ![#2, #1, #0]).toFormula ⋏
      (decodeEntryCode.app ![#0, #4, #5, #6, #7]).toFormula)) from rfl]
  simp only [evalN_bexLT, evalN_and, Delta0Code.evalN_app, tval_vecCons, tval_vecEmpty,
    evalN_betaCode, evalN_decodeEntryCode]
  change (∃ j, j < i ∧ ∃ e, e < S + 1 ∧ (e = Nat.beta S j ∧ e = Entry.toNat ⟨K, c, n, x⟩))
    ↔ _
  constructor
  · rintro ⟨j, hj, e, -, rfl, he⟩
    exact ⟨j, hj, by rw [he, Entry.ofNat_toNat]⟩
  · rintro ⟨j, hj, he⟩
    refine ⟨j, hj, Nat.beta S j, Nat.lt_succ_of_le (Nat.beta_le S j), rfl, ?_⟩
    rw [← he, Entry.toNat_ofNat]

end layer2

/-! ### Layer 3: the nine evaluator clauses

Slots of every case code: `(S, i, k, c, n, x)` = `#0 … #5` at the top; an original slot
`j` sits at `#(j + d)` beneath `d` binders. Every bound is read in the environment just
outside its own binder. `sup(K', c', n', x')` abbreviates `supportsCode` applied at
`(S, i, K', c', n', x')`. -/

/-- Term for `2·(2·m) + 5` with `m` at `#0` (the `pair` shape). -/
def shapePairT {n : ℕ} : Semiterm ℒₒᵣ Empty (n + 1) :=
  tAdd (tMul (tNum 2) (tMul (tNum 2) #0)) (tNum 5)
/-- `2·(2·m + 1) + 5` (the `comp` shape). -/
def shapeCompT {n : ℕ} : Semiterm ℒₒᵣ Empty (n + 1) :=
  tAdd (tMul (tNum 2) (tSucc (tMul (tNum 2) #0))) (tNum 5)
/-- `2·(2·m) + 1 + 5` (the `prec` shape). -/
def shapePrecT {n : ℕ} : Semiterm ℒₒᵣ Empty (n + 1) :=
  tAdd (tSucc (tMul (tNum 2) (tMul (tNum 2) #0))) (tNum 5)
/-- `2·(2·m + 1) + 1 + 5` (the `rfind'` shape). -/
def shapeRfindT {n : ℕ} : Semiterm ℒₒᵣ Empty (n + 1) :=
  tAdd (tSucc (tMul (tNum 2) (tSucc (tMul (tNum 2) #0)))) (tNum 5)

/-- `c = 0 ∧ x = 0`. -/
def caseZeroCode : Delta0Code 1 6 := .and (.eq #3 (tNum 0)) (.eq #5 (tNum 0))
/-- `c = 1 ∧ x = n + 1`. -/
def caseSuccCode : Delta0Code 1 6 := .and (.eq #3 (tNum 1)) (.eq #5 (tSucc #4))
/-- `c = 2 ∧ x = (unpair n).1`. -/
def caseLeftCode : Delta0Code 1 6 := .and (.eq #3 (tNum 2)) (fstCode.app ![#4, #5])
/-- `c = 3 ∧ x = (unpair n).2`. -/
def caseRightCode : Delta0Code 1 6 := .and (.eq #3 (tNum 3)) (sndCode.app ![#4, #5])
/-- `c = 4 ∧ ((x = 1 ∧ n ∈ B) ∨ (x = 0 ∧ n ∉ B))` — the single set atom. -/
def caseOracleCode : Delta0Code 1 6 :=
  .and (.eq #3 (tNum 4))
    (.or (.and (.eq #5 (tNum 1)) (.mem 0 #4)) (.and (.eq #5 (tNum 0)) (.notMem 0 #4)))

/-- `∃ m ≤ c, c = 2(2m)+5 ∧ ∃ cf cg ≤ m, m = pair cf cg ∧ ∃ y z ≤ S,
sup(k+1, cf, n, y) ∧ sup(k+1, cg, n, z) ∧ x = pair y z`. -/
def casePairCode : Delta0Code 1 6 :=
  .bex (tSucc #3) (.and (.eq #4 shapePairT)
    (.bex (tSucc #0) (.bex (tSucc #1) (.and (pairCode.app ![#1, #0, #2])
      (.bex (tSucc #3) (.bex (tSucc #4)
        (.and (supportsCode.app ![#5, #6, tSucc #7, #3, #9, #1])
          (.and (supportsCode.app ![#5, #6, tSucc #7, #2, #9, #0])
            (pairCode.app ![#1, #0, #10])))))))))

/-- `∃ m ≤ c, c = 2(2m+1)+5 ∧ ∃ cf cg ≤ m, m = pair cf cg ∧ ∃ y ≤ S,
sup(k+1, cg, n, y) ∧ sup(k+1, cf, y, x)`. -/
def caseCompCode : Delta0Code 1 6 :=
  .bex (tSucc #3) (.and (.eq #4 shapeCompT)
    (.bex (tSucc #0) (.bex (tSucc #1) (.and (pairCode.app ![#1, #0, #2])
      (.bex (tSucc #3)
        (.and (supportsCode.app ![#4, #5, tSucc #6, #1, #8, #0])
          (supportsCode.app ![#4, #5, tSucc #6, #2, #0, #9])))))))

/-- `∃ m ≤ c, c = 2(2m)+1+5 ∧ ∃ cf cg ≤ m, m = pair cf cg ∧ ∃ a b ≤ n, n = pair a b ∧
((b = 0 ∧ sup(k+1, cf, a, x)) ∨ (∃ m' < b, b = m'+1 ∧ ∃ i' p ≤ S, p = pair a m' ∧
sup(k, c, p, i') ∧ ∃ r q ≤ S, r = pair m' i' ∧ q = pair a r ∧ sup(k+1, cg, q, x)))`. -/
def casePrecCode : Delta0Code 1 6 :=
  .bex (tSucc #3) (.and (.eq #4 shapePrecT)
    (.bex (tSucc #0) (.bex (tSucc #1) (.and (pairCode.app ![#1, #0, #2])
      (.bex (tSucc #7) (.bex (tSucc #8) (.and (pairCode.app ![#1, #0, #9])
        (.or (.and (.eq #0 (tNum 0)) (supportsCode.app ![#5, #6, tSucc #7, #3, #1, #10]))
          (.bex #0 (.and (.eq #1 (tSucc #0))
            (.bex (tSucc #6) (.bex (tSucc #7) (.and (pairCode.app ![#4, #2, #0])
              (.and (supportsCode.app ![#8, #9, #10, #11, #0, #1])
                (.bex (tSucc #8) (.and (pairCode.app ![#3, #2, #0])
                  (.bex (tSucc #9) (.and (pairCode.app ![#6, #1, #0])
                    (supportsCode.app ![#10, #11, tSucc #12, #7, #0, #15])))))))))))))))))))

/-- `∃ m ≤ c, c = 2(2m+1)+1+5 ∧ ∃ a b ≤ n, n = pair a b ∧ ∃ y ≤ S, sup(k+1, m, n, y) ∧
((y = 0 ∧ x = b) ∨ (y ≠ 0 ∧ ∃ p ≤ S, p = pair a (b+1) ∧ sup(k, c, p, x)))`. -/
def caseRfindCode : Delta0Code 1 6 :=
  .bex (tSucc #3) (.and (.eq #4 shapeRfindT)
    (.bex (tSucc #5) (.bex (tSucc #6) (.and (pairCode.app ![#1, #0, #7])
      (.bex (tSucc #3) (.and (supportsCode.app ![#4, #5, tSucc #6, #3, #8, #0])
        (.or (.and (.eq #0 (tNum 0)) (.eq #9 #1))
          (.and (.neq #0 (tNum 0))
            (.bex (tSucc #4) (.and (pairCode.app ![#3, tSucc #2, #0])
              (supportsCode.app ![#5, #6, #7, #8, #0, #10])))))))))))

/-- The exhaustive nine-way disjunction. -/
def clauseCode : Delta0Code 1 6 :=
  .or caseZeroCode (.or caseSuccCode (.or caseLeftCode (.or caseRightCode
    (.or caseOracleCode (.or casePairCode (.or caseCompCode
      (.or casePrecCode caseRfindCode)))))))

section layer3

variable {𝕊 : Set (Set ℕ)} {E : Fin 1 → Set ℕ}

theorem evalN_caseZeroCode (S i k c n x : ℕ) :
    EvalN 𝕊 caseZeroCode.toFormula E ![S, i, k, c, n, x] ↔ c = 0 ∧ x = 0 := Iff.rfl

theorem evalN_caseSuccCode (S i k c n x : ℕ) :
    EvalN 𝕊 caseSuccCode.toFormula E ![S, i, k, c, n, x] ↔ c = 1 ∧ x = n + 1 := Iff.rfl

theorem evalN_caseLeftCode (S i k c n x : ℕ) :
    EvalN 𝕊 caseLeftCode.toFormula E ![S, i, k, c, n, x] ↔ c = 2 ∧ x = n.unpair.1 := by
  simp only [caseLeftCode, Delta0Code.toFormula, evalN_and, Delta0Code.evalN_app,
    tval_vecCons, tval_vecEmpty, evalN_fstCode]
  exact Iff.rfl

theorem evalN_caseRightCode (S i k c n x : ℕ) :
    EvalN 𝕊 caseRightCode.toFormula E ![S, i, k, c, n, x] ↔ c = 3 ∧ x = n.unpair.2 := by
  simp only [caseRightCode, Delta0Code.toFormula, evalN_and, Delta0Code.evalN_app,
    tval_vecCons, tval_vecEmpty, evalN_sndCode]
  exact Iff.rfl

theorem evalN_caseOracleCode (S i k c n x : ℕ) :
    EvalN 𝕊 caseOracleCode.toFormula E ![S, i, k, c, n, x] ↔
      c = 4 ∧ x = oracleOf (E 0) n := by
  change (c = 4 ∧ ((x = 1 ∧ n ∈ E 0) ∨ (x = 0 ∧ ¬ n ∈ E 0))) ↔ _
  refine and_congr Iff.rfl ?_
  by_cases hn : n ∈ E 0 <;> simp [oracleOf, hn]

theorem evalN_casePairCode (S i k c n x : ℕ) :
    EvalN 𝕊 casePairCode.toFormula E ![S, i, k, c, n, x] ↔
      ∃ m, c = 2 * (2 * m) + 5 ∧ ∃ y z, SupportsAt S i ⟨k + 1, m.unpair.1, n, y⟩ ∧
        SupportsAt S i ⟨k + 1, m.unpair.2, n, z⟩ ∧ x = Nat.pair y z := by
  simp only [casePairCode, Delta0Code.toFormula, evalN_bexLT, evalN_and,
    Delta0Code.evalN_app, tval_vecCons, tval_vecEmpty, evalN_supportsCode, evalN_pairCode]
  change (∃ m, m < c + 1 ∧ (c = 2 * (2 * m) + 5 ∧ ∃ cf, cf < m + 1 ∧ ∃ cg, cg < m + 1 ∧
    (m = Nat.pair cf cg ∧ ∃ y, y < S + 1 ∧ ∃ z, z < S + 1 ∧
      (SupportsAt S i ⟨k + 1, cf, n, y⟩ ∧ SupportsAt S i ⟨k + 1, cg, n, z⟩ ∧
        x = Nat.pair y z)))) ↔ _
  constructor
  · rintro ⟨m, -, hc, cf, -, cg, -, rfl, y, -, z, -, hy, hz, hx⟩
    exact ⟨_, hc, y, z, by rwa [Nat.unpair_pair], by rwa [Nat.unpair_pair], hx⟩
  · rintro ⟨m, hc, y, z, hy, hz, hx⟩
    exact ⟨m, by omega, hc, m.unpair.1, Nat.lt_succ_of_le (Nat.unpair_left_le m),
      m.unpair.2, Nat.lt_succ_of_le (Nat.unpair_right_le m), (Nat.pair_unpair m).symm,
      y, Nat.lt_succ_of_le hy.output_le, z, Nat.lt_succ_of_le hz.output_le, hy, hz, hx⟩

theorem evalN_caseCompCode (S i k c n x : ℕ) :
    EvalN 𝕊 caseCompCode.toFormula E ![S, i, k, c, n, x] ↔
      ∃ m, c = 2 * (2 * m + 1) + 5 ∧ ∃ y, SupportsAt S i ⟨k + 1, m.unpair.2, n, y⟩ ∧
        SupportsAt S i ⟨k + 1, m.unpair.1, y, x⟩ := by
  simp only [caseCompCode, Delta0Code.toFormula, evalN_bexLT, evalN_and,
    Delta0Code.evalN_app, tval_vecCons, tval_vecEmpty, evalN_supportsCode, evalN_pairCode]
  change (∃ m, m < c + 1 ∧ (c = 2 * (2 * m + 1) + 5 ∧ ∃ cf, cf < m + 1 ∧
    ∃ cg, cg < m + 1 ∧ (m = Nat.pair cf cg ∧ ∃ y, y < S + 1 ∧
      (SupportsAt S i ⟨k + 1, cg, n, y⟩ ∧ SupportsAt S i ⟨k + 1, cf, y, x⟩)))) ↔ _
  constructor
  · rintro ⟨m, -, hc, cf, -, cg, -, rfl, y, -, hy, hx⟩
    exact ⟨_, hc, y, by rwa [Nat.unpair_pair], by rwa [Nat.unpair_pair]⟩
  · rintro ⟨m, hc, y, hy, hx⟩
    exact ⟨m, by omega, hc, m.unpair.1, Nat.lt_succ_of_le (Nat.unpair_left_le m),
      m.unpair.2, Nat.lt_succ_of_le (Nat.unpair_right_le m), (Nat.pair_unpair m).symm,
      y, Nat.lt_succ_of_le hy.output_le, hy, hx⟩

theorem evalN_casePrecCode (S i k c n x : ℕ) :
    EvalN 𝕊 casePrecCode.toFormula E ![S, i, k, c, n, x] ↔
      ∃ m, c = 2 * (2 * m) + 1 + 5 ∧
        ((n.unpair.2 = 0 ∧ SupportsAt S i ⟨k + 1, m.unpair.1, n.unpair.1, x⟩) ∨
         (∃ m' i', n.unpair.2 = m' + 1 ∧
            SupportsAt S i ⟨k, c, Nat.pair n.unpair.1 m', i'⟩ ∧
            SupportsAt S i ⟨k + 1, m.unpair.2, Nat.pair n.unpair.1 (Nat.pair m' i'), x⟩)) := by
  simp only [casePrecCode, Delta0Code.toFormula, evalN_bexLT, evalN_and, evalN_or,
    Delta0Code.evalN_app, tval_vecCons, tval_vecEmpty, evalN_supportsCode, evalN_pairCode]
  constructor
  · rintro ⟨m, -, hc, cf, -, cg, -, hm, a, -, b, -, hn, h⟩
    have hc' : c = 2 * (2 * m) + 1 + 5 := hc
    have hm' : m = Nat.pair cf cg := hm
    have hn' : n = Nat.pair a b := hn
    subst hm' hn'
    refine ⟨_, hc', ?_⟩
    rw [Nat.unpair_pair, Nat.unpair_pair]
    rcases h with ⟨hb, hs⟩ | ⟨m', -, hb, i', -, p, -, hp, hs, r, -, hr, q, -, hq, hg⟩
    · have hb' : b = 0 := hb
      exact Or.inl ⟨hb', hs⟩
    · have hb' : b = m' + 1 := hb
      have hp' : p = Nat.pair a m' := hp
      have hr' : r = Nat.pair m' i' := hr
      have hq' : q = Nat.pair a r := hq
      subst hp' hr' hq'
      exact Or.inr ⟨m', i', hb', hs, hg⟩
  · rintro ⟨m, hc, h⟩
    refine ⟨m, show m < c + 1 by omega, hc, m.unpair.1,
      Nat.lt_succ_of_le (Nat.unpair_left_le m),
      m.unpair.2, Nat.lt_succ_of_le (Nat.unpair_right_le m),
      show m = Nat.pair m.unpair.1 m.unpair.2 from (Nat.pair_unpair m).symm,
      n.unpair.1, Nat.lt_succ_of_le (Nat.unpair_left_le n),
      n.unpair.2, Nat.lt_succ_of_le (Nat.unpair_right_le n),
      show n = Nat.pair n.unpair.1 n.unpair.2 from (Nat.pair_unpair n).symm, ?_⟩
    rcases h with ⟨hb, hs⟩ | ⟨m', i', hb, hs, hg⟩
    · exact Or.inl ⟨hb, hs⟩
    · exact Or.inr ⟨m', show m' < n.unpair.2 by omega, hb, i', Nat.lt_succ_of_le hs.output_le,
        _, Nat.lt_succ_of_le hs.input_le, rfl, hs,
        Nat.pair m' i', Nat.lt_succ_of_le (le_trans (Nat.right_le_pair _ _) hg.input_le),
        rfl, _, Nat.lt_succ_of_le hg.input_le, rfl, hg⟩

theorem evalN_caseRfindCode (S i k c n x : ℕ) :
    EvalN 𝕊 caseRfindCode.toFormula E ![S, i, k, c, n, x] ↔
      ∃ m, c = 2 * (2 * m + 1) + 1 + 5 ∧
        ∃ y, SupportsAt S i ⟨k + 1, m, Nat.pair n.unpair.1 n.unpair.2, y⟩ ∧
          ((y = 0 ∧ x = n.unpair.2) ∨
           (y ≠ 0 ∧ SupportsAt S i ⟨k, c, Nat.pair n.unpair.1 (n.unpair.2 + 1), x⟩)) := by
  simp only [caseRfindCode, Delta0Code.toFormula, evalN_bexLT, evalN_and, evalN_or,
    Delta0Code.evalN_app, tval_vecCons, tval_vecEmpty, evalN_supportsCode, evalN_pairCode]
  constructor
  · rintro ⟨m, -, hc, a, -, b, -, hn, y, -, hy, h⟩
    have hc' : c = 2 * (2 * m + 1) + 1 + 5 := hc
    have hn' : n = Nat.pair a b := hn
    subst hn'
    refine ⟨_, hc', y, by rw [Nat.unpair_pair]; exact hy, ?_⟩
    rw [Nat.unpair_pair]
    rcases h with ⟨hy0, hx⟩ | ⟨hy0, p, -, hp, hs⟩
    · exact Or.inl ⟨hy0, hx⟩
    · have hp' : p = Nat.pair a (b + 1) := hp
      subst hp'
      exact Or.inr ⟨hy0, hs⟩
  · rintro ⟨m, hc, y, hy, h⟩
    rw [Nat.pair_unpair] at hy
    refine ⟨m, show m < c + 1 by omega, hc, n.unpair.1,
      Nat.lt_succ_of_le (Nat.unpair_left_le n),
      n.unpair.2, Nat.lt_succ_of_le (Nat.unpair_right_le n),
      show n = Nat.pair n.unpair.1 n.unpair.2 from (Nat.pair_unpair n).symm,
      y, Nat.lt_succ_of_le hy.output_le, hy, ?_⟩
    rcases h with ⟨hy0, hx⟩ | ⟨hy0, hs⟩
    · exact Or.inl ⟨hy0, hx⟩
    · exact Or.inr ⟨hy0, _, Nat.lt_succ_of_le hs.input_le, rfl, hs⟩

/-- **The clause agreement**: the nine-way disjunction evaluates to exactly the C1
`Clause` at the decoded code, with seed support. Proved shape by shape: the matching
disjunct survives, every other is refuted arithmetically, and the decoder agrees with
the arithmetic branch through the shape lemmas. -/
theorem evalN_clauseCode (S i k c n x : ℕ) :
    EvalN 𝕊 clauseCode.toFormula E ![S, i, k, c, n, x] ↔
      Clause (E 0) (SupportsAt S i) k (OracleCode.ofNatCode c) n x := by
  rw [show clauseCode.toFormula = caseZeroCode.toFormula ⋎ (caseSuccCode.toFormula ⋎
    (caseLeftCode.toFormula ⋎ (caseRightCode.toFormula ⋎ (caseOracleCode.toFormula ⋎
    (casePairCode.toFormula ⋎ (caseCompCode.toFormula ⋎
    (casePrecCode.toFormula ⋎ caseRfindCode.toFormula))))))) from rfl]
  simp only [evalN_or, evalN_caseZeroCode, evalN_caseSuccCode, evalN_caseLeftCode,
    evalN_caseRightCode, evalN_caseOracleCode, evalN_casePairCode, evalN_caseCompCode,
    evalN_casePrecCode, evalN_caseRfindCode]
  rcases codeShape c with _ | _ | _ | _ | _ | m | m | m | m
  · simp only [OracleCode.ofNatCode, Clause]
    constructor
    · rintro (⟨-, h⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨m', hc, -⟩ | ⟨m', hc, -⟩ |
        ⟨m', hc, -⟩ | ⟨m', hc, -⟩) <;> first | exact h | omega
    · exact fun h => Or.inl ⟨trivial, h⟩
  · simp only [OracleCode.ofNatCode, Clause]
    constructor
    · rintro (⟨hc, -⟩ | ⟨-, h⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨m', hc, -⟩ | ⟨m', hc, -⟩ |
        ⟨m', hc, -⟩ | ⟨m', hc, -⟩) <;> first | exact h | omega
    · exact fun h => Or.inr (Or.inl ⟨trivial, h⟩)
  · simp only [OracleCode.ofNatCode, Clause]
    constructor
    · rintro (⟨hc, -⟩ | ⟨hc, -⟩ | ⟨-, h⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨m', hc, -⟩ | ⟨m', hc, -⟩ |
        ⟨m', hc, -⟩ | ⟨m', hc, -⟩) <;> first | exact h | omega
    · exact fun h => Or.inr (Or.inr (Or.inl ⟨trivial, h⟩))
  · simp only [OracleCode.ofNatCode, Clause]
    constructor
    · rintro (⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨-, h⟩ | ⟨hc, -⟩ | ⟨m', hc, -⟩ | ⟨m', hc, -⟩ |
        ⟨m', hc, -⟩ | ⟨m', hc, -⟩) <;> first | exact h | omega
    · exact fun h => Or.inr (Or.inr (Or.inr (Or.inl ⟨trivial, h⟩)))
  · simp only [OracleCode.ofNatCode, Clause]
    constructor
    · rintro (⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨-, h⟩ | ⟨m', hc, -⟩ | ⟨m', hc, -⟩ |
        ⟨m', hc, -⟩ | ⟨m', hc, -⟩) <;> first | exact h | omega
    · exact fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨trivial, h⟩))))
  · rw [ofNatCode_pair_shape]
    simp only [Clause, encodeCode_ofNatCode]
    constructor
    · rintro (⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨m', hc, h⟩ | ⟨m', hc, -⟩ |
        ⟨m', hc, -⟩ | ⟨m', hc, -⟩) <;> first | omega | skip
      obtain rfl : m' = m := by omega
      exact h
    · exact fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl, h⟩)))))
  · rw [ofNatCode_comp_shape]
    simp only [Clause, encodeCode_ofNatCode]
    constructor
    · rintro (⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨m', hc, -⟩ | ⟨m', hc, h⟩ |
        ⟨m', hc, -⟩ | ⟨m', hc, -⟩) <;> first | omega | skip
      obtain rfl : m' = m := by omega
      exact h
    · exact fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl, h⟩))))))
  · rw [ofNatCode_prec_shape]
    simp only [Clause, encodeCode_ofNatCode, encodeCode_prec, Nat.pair_unpair]
    constructor
    · rintro (⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨m', hc, -⟩ | ⟨m', hc, -⟩ |
        ⟨m', hc, h⟩ | ⟨m', hc, -⟩) <;> first | omega | skip
      obtain rfl : m' = m := by omega
      exact h
    · exact fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨m, rfl, h⟩)))))))
  · rw [ofNatCode_rfind'_shape]
    simp only [Clause, encodeCode_ofNatCode, encodeCode_rfind']
    constructor
    · rintro (⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨m', hc, -⟩ | ⟨m', hc, -⟩ |
        ⟨m', hc, -⟩ | ⟨m', hc, h⟩) <;> first | omega | skip
      obtain rfl : m' = m := by omega
      exact h
    · exact fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨m, rfl, h⟩)))))))

end layer3

/-! ### Layer 4: one justified entry -/

/-- `justifiedCode (S, i, e)`: `e` decodes to `(K, c, n, x)` with each component bounded by
`e`, some `k < K` has `K = k + 1` and `n < K`, and the clause holds at `(S, i, k, c, n, x)`.
Beneath the binders `#0 = k`, `#1 = x`, `#2 = n`, `#3 = c`, `#4 = K`, `#5 = S`, `#6 = i`,
`#7 = e`. -/
def justifiedCode : Delta0Code 1 3 :=
  .bex (tSucc #2) (.bex (tSucc #3) (.bex (tSucc #4) (.bex (tSucc #5)
    (.and (decodeEntryCode.app ![#6, #3, #2, #1, #0])
      (.bex #3 (.and (.eq #4 (tSucc #0)) (.and (.lt #2 #4)
        (clauseCode.app ![#5, #6, #0, #3, #2, #1]))))))))

section layer4

variable {𝕊 : Set (Set ℕ)} {E : Fin 1 → Set ℕ}

theorem evalN_justifiedCode (S i e : ℕ) :
    EvalN 𝕊 justifiedCode.toFormula E ![S, i, e] ↔
      JustifiedBy (E 0) (SupportsAt S i) (Entry.ofNat e) := by
  simp only [justifiedCode, Delta0Code.toFormula, evalN_bexLT, evalN_and,
    Delta0Code.evalN_app, tval_vecCons, tval_vecEmpty, evalN_decodeEntryCode,
    evalN_clauseCode]
  constructor
  · rintro ⟨K, -, c, -, n, -, x, -, he, k, -, hK, hn, hc⟩
    have he' : e = Entry.toNat ⟨K, c, n, x⟩ := he
    have hK' : K = k + 1 := hK
    have hn' : n < K := hn
    subst he'
    rw [Entry.ofNat_toNat]
    exact ⟨k, hK', show n ≤ k by omega, hc⟩
  · rintro ⟨k, hK, hn, hc⟩
    refine ⟨(Entry.ofNat e).fuel, Nat.lt_succ_of_le (Entry.fuel_ofNat_le e),
      (Entry.ofNat e).code, Nat.lt_succ_of_le (Entry.code_ofNat_le e),
      (Entry.ofNat e).input, Nat.lt_succ_of_le (Entry.input_ofNat_le e),
      (Entry.ofNat e).output, Nat.lt_succ_of_le (Entry.output_ofNat_le e),
      show e = Entry.toNat (Entry.ofNat e) from (Entry.toNat_ofNat e).symm,
      k, show k < (Entry.ofNat e).fuel by omega, hK,
      show (Entry.ofNat e).input < (Entry.ofNat e).fuel by omega, hc⟩

end layer4

/-! ### Layer 5: the whole transcript -/

/-- `verifiedCode (T)`: `T = pair L S` with `L, S ≤ T`, and every `i < L` has an entry
`e = β S i ≤ S` justified at `(S, i, e)`. Beneath the binders `#0 = e`, `#1 = i`,
`#2 = S`, `#3 = L`, `#4 = T`. -/
def verifiedCode : Delta0Code 1 1 :=
  .bex (tSucc #0) (.bex (tSucc #1)
    (.and (pairCode.app ![#1, #0, #2])
      (.ball #1 (.bex (tSucc #1)
        (.and (betaCode.app ![#2, #1, #0]) (justifiedCode.app ![#2, #1, #0]))))))

/-- **The checker agreement**: the Δ⁰₀ checker's Tarski evaluation at set assignment
`![B]` and transcript code `T` is exactly `Verified B (tableOf T)`, for every standard-ℕ
set domain `𝕊`. -/
theorem evalN_verifiedCode {𝕊 : Set (Set ℕ)} (B : Set ℕ) (T : ℕ) :
    EvalN 𝕊 verifiedCode.toFormula ![B] ![T] ↔ Verified B (tableOf T) := by
  simp only [verifiedCode, Delta0Code.toFormula, evalN_bexLT, evalN_ballLT, evalN_and,
    Delta0Code.evalN_app, tval_vecCons, tval_vecEmpty, evalN_pairCode, evalN_betaCode,
    evalN_justifiedCode]
  constructor
  · rintro ⟨L, -, S, -, hT, h⟩
    have hT' : T = Nat.pair L S := hT
    subst hT'
    intro i e hie
    rw [tableOf_getElem?, Nat.unpair_pair] at hie
    simp only at hie
    split_ifs at hie with hi
    · obtain ⟨e', -, he', hj⟩ := h i hi
      have he'' : e' = Nat.beta S i := he'
      subst he''
      rw [Option.some.injEq] at hie
      subst hie
      refine hj.mono fun e'' he'' => ?_
      exact (supportsAt_iff_supports (T := Nat.pair L S) (by rw [Nat.unpair_pair]; exact hi.le)
        e'').mp (by rw [Nat.unpair_pair]; exact he'')
  · intro h
    refine ⟨T.unpair.1, Nat.lt_succ_of_le (Nat.unpair_left_le T),
      T.unpair.2, Nat.lt_succ_of_le (Nat.unpair_right_le T),
      show T = Nat.pair T.unpair.1 T.unpair.2 from (Nat.pair_unpair T).symm, ?_⟩
    intro i hi
    have hi' : i < T.unpair.1 := hi
    refine ⟨Nat.beta T.unpair.2 i, Nat.lt_succ_of_le (Nat.beta_le _ _), rfl, ?_⟩
    have hie : getElem? (tableOf T) i = some (Entry.ofNat (Nat.beta T.unpair.2 i)) := by
      rw [tableOf_getElem?, if_pos hi']
    exact (h i _ hie).mono fun e'' he'' => (supportsAt_iff_supports hi'.le e'').mpr he''


end RMFoundationBridge
