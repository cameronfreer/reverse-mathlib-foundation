/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Omega.OracleCode
import ReverseMathlib.Omega.Computability

/-!
# Converse adequacy, Slice C1: semantic computation transcripts

The downward-closure clause of the converse needs a Σ⁰₁ definition, with the oracle set
as its only set parameter, of "the coded oracle computation halts with output `x`". The
route is a **transcript**: a finite list of entries, each asserting one fact
`evaln χ K c n = some x` about the frozen step-bounded evaluator, in which every entry
is *justified* — its guard holds and its recursive calls occur as earlier entries with
exactly the fuel the evaluator uses. This module is the purely semantic half: transcripts
are lists, justification is a Lean predicate, and the three principal theorems relate
verified transcripts to the frozen `evaln` with no syntax anywhere.

**Pinned conventions.**

* The oracle is the bridge-local total binary oracle `oracleOf B` (`1` on members, `0`
  off), with `charFn B = ↑(oracleOf B)` proved here; `Omega/Jump.lean` is not imported.
* An entry stores a **natural** code. The division of responsibility is: soundness
  interprets the stored natural through `OracleCode.ofNatCode`; completeness stores
  `encodeCode` of the typed code and relies on the round trip `ofNatCode_encodeCode`
  (audit-gated) to make that target denote the original code.
* The stored fuel is the actual fuel `K`. Every justified entry witnesses `K = k + 1`
  and requires `input ≤ k` (the evaluator's guard), so `0 < K` and `input < K` hold. The
  recursive support then reproduces the frozen evaluator exactly: `pair`/`comp` subcalls,
  the `prec` base, the `prec` step-code call, and the `rfind'` test at fuel `K`; the
  `prec` self-call and the `rfind'` continuation at the predecessor `k`, named through
  the witness rather than truncated subtraction.
* Recursive support must occur at a **strictly earlier index**; duplicates are harmless.

**Principal theorems.** `verified_sound` (every entry of a verified transcript is a true
`evaln` fact), `verified_complete` (every true `evaln` fact occurs in some verified
transcript — the target is appended last, after its sub-transcripts), and
`verified_deterministic` (verified entries with the same code and input agree on the
output, across two transcripts — soundness twice, then `evaln_mono`; the same-transcript
form is a corollary).

The set `A` being reduced never appears here; only the oracle set `B`.
-/

namespace RMFoundationBridge

open ReverseMathlib.Omega

/-! ### The total binary oracle -/

open Classical in
/-- The total binary oracle of a set: `1` on members, `0` off. Bridge-local, so the
downward-closure route acquires no dependency on the jump module. -/
noncomputable def oracleOf (B : Set ℕ) : ℕ → ℕ := fun n => if n ∈ B then 1 else 0

/-- The frozen partial characteristic function is the coercion of the total oracle. -/
theorem charFn_eq_coe_oracleOf (B : Set ℕ) : charFn B = ↑(oracleOf B) := by
  funext n
  simp [charFn, oracleOf, PFun.coe_val]

theorem oracleOf_eq_one_iff {B : Set ℕ} {n : ℕ} : oracleOf B n = 1 ↔ n ∈ B := by
  simp [oracleOf]

theorem oracleOf_eq_zero_iff {B : Set ℕ} {n : ℕ} : oracleOf B n = 0 ↔ n ∉ B := by
  simp [oracleOf]

/-! ### Entries and their numeric convention -/

/-- One transcript entry: the assertion `evaln χ fuel (ofNatCode code) input = some output`.
The code is stored as a natural. -/
structure Entry where
  fuel : ℕ
  code : ℕ
  input : ℕ
  output : ℕ
  deriving DecidableEq

namespace Entry

/-- The pinned numeric convention for an entry: `pair fuel (pair code (pair input output))`.
Consumed by the syntactic half; fixed here so the convention is semantic. -/
def toNat (e : Entry) : ℕ := Nat.pair e.fuel (Nat.pair e.code (Nat.pair e.input e.output))

/-- Decoding under the same convention. -/
def ofNat (m : ℕ) : Entry :=
  ⟨m.unpair.1, m.unpair.2.unpair.1, m.unpair.2.unpair.2.unpair.1,
    m.unpair.2.unpair.2.unpair.2⟩

@[simp] theorem ofNat_toNat (e : Entry) : ofNat e.toNat = e := by
  cases e
  simp [ofNat, toNat]

@[simp] theorem toNat_ofNat (m : ℕ) : (ofNat m).toNat = m := by
  simp [ofNat, toNat]

/-- The semantic interpretation of the stored code. -/
def oracleCode (e : Entry) : OracleCode := OracleCode.ofNatCode e.code

/-- The `evaln` fact an entry asserts, against the oracle of `B`. -/
def Holds (B : Set ℕ) (e : Entry) : Prop :=
  OracleCode.evaln (oracleOf B) e.fuel e.oracleCode e.input = some e.output

end Entry

/-! ### Justification against a support predicate -/

/-- The clause condition for an entry `(k + 1, c, n, x)` whose recursive calls must be
supplied by the support predicate `S`: the exact recursive shape of the frozen `evaln`
at fuel `k + 1`. Subcalls carry the **encoded** code of the sub-code. -/
def Clause (B : Set ℕ) (S : Entry → Prop) (k : ℕ) : OracleCode → ℕ → ℕ → Prop
  | .zero, _, x => x = 0
  | .succ, n, x => x = n + 1
  | .left, n, x => x = n.unpair.1
  | .right, n, x => x = n.unpair.2
  | .oracle, n, x => x = oracleOf B n
  | .pair cf cg, n, x => ∃ y z, S ⟨k + 1, cf.encodeCode, n, y⟩ ∧
      S ⟨k + 1, cg.encodeCode, n, z⟩ ∧ x = Nat.pair y z
  | .comp cf cg, n, x => ∃ y, S ⟨k + 1, cg.encodeCode, n, y⟩ ∧
      S ⟨k + 1, cf.encodeCode, y, x⟩
  | .prec cf cg, n, x =>
      (n.unpair.2 = 0 ∧ S ⟨k + 1, cf.encodeCode, n.unpair.1, x⟩) ∨
      (∃ m i, n.unpair.2 = m + 1 ∧
        S ⟨k, (OracleCode.prec cf cg).encodeCode, Nat.pair n.unpair.1 m, i⟩ ∧
        S ⟨k + 1, cg.encodeCode, Nat.pair n.unpair.1 (Nat.pair m i), x⟩)
  | .rfind' cf, n, x => ∃ y, S ⟨k + 1, cf.encodeCode, Nat.pair n.unpair.1 n.unpair.2, y⟩ ∧
      ((y = 0 ∧ x = n.unpair.2) ∨
       (y ≠ 0 ∧ S ⟨k, (OracleCode.rfind' cf).encodeCode,
          Nat.pair n.unpair.1 (n.unpair.2 + 1), x⟩))

/-- An entry is justified by the support `S`: its fuel is a witnessed successor `k + 1`,
its input passes the guard `input ≤ k`, and its clause holds with recursive calls
supplied by `S`. -/
def JustifiedBy (B : Set ℕ) (S : Entry → Prop) (e : Entry) : Prop :=
  ∃ k, e.fuel = k + 1 ∧ e.input ≤ k ∧ Clause B S k e.oracleCode e.input e.output

theorem Clause.mono {B : Set ℕ} {S S' : Entry → Prop} (h : ∀ e, S e → S' e) {k : ℕ} :
    ∀ {c : OracleCode} {n x : ℕ}, Clause B S k c n x → Clause B S' k c n x
  | .zero, _, _, hc => hc
  | .succ, _, _, hc => hc
  | .left, _, _, hc => hc
  | .right, _, _, hc => hc
  | .oracle, _, _, hc => hc
  | .pair _ _, _, _, ⟨y, z, h₁, h₂, hx⟩ => ⟨y, z, h _ h₁, h _ h₂, hx⟩
  | .comp _ _, _, _, ⟨y, h₁, h₂⟩ => ⟨y, h _ h₁, h _ h₂⟩
  | .prec _ _, _, _, Or.inl ⟨hm, h₁⟩ => Or.inl ⟨hm, h _ h₁⟩
  | .prec _ _, _, _, Or.inr ⟨m, i, hm, h₁, h₂⟩ => Or.inr ⟨m, i, hm, h _ h₁, h _ h₂⟩
  | .rfind' _, _, _, ⟨y, h₁, Or.inl hz⟩ => ⟨y, h _ h₁, Or.inl hz⟩
  | .rfind' _, _, _, ⟨y, h₁, Or.inr ⟨hy, h₂⟩⟩ => ⟨y, h _ h₁, Or.inr ⟨hy, h _ h₂⟩⟩

theorem JustifiedBy.mono {B : Set ℕ} {S S' : Entry → Prop} (h : ∀ e, S e → S' e)
    {e : Entry} : JustifiedBy B S e → JustifiedBy B S' e
  | ⟨k, hk, hn, hc⟩ => ⟨k, hk, hn, hc.mono h⟩

/-! ### Transcripts: support at strictly earlier indices -/

/-- `Supports L i e`: the entry `e` occurs in `L` at some index strictly below `i`. -/
def Supports (L : List Entry) (i : ℕ) (e : Entry) : Prop := ∃ j < i, L[j]? = some e

/-- A verified transcript: every entry is justified by the entries strictly before it. -/
def Verified (B : Set ℕ) (L : List Entry) : Prop :=
  ∀ i (e : Entry), L[i]? = some e → JustifiedBy B (Supports L i) e

theorem Supports.mono_index {L : List Entry} {i i' : ℕ} {e : Entry} (h : i ≤ i')
    (hs : Supports L i e) : Supports L i' e :=
  let ⟨j, hj, hje⟩ := hs
  ⟨j, lt_of_lt_of_le hj h, hje⟩

theorem Supports.append_left {L L' : List Entry} {i : ℕ} {e : Entry}
    (hs : Supports L i e) : Supports (L ++ L') i e := by
  obtain ⟨j, hj, hje⟩ := hs
  refine ⟨j, hj, ?_⟩
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hje).1]
  exact hje

theorem Supports.append_right {L L' : List Entry} {i : ℕ} {e : Entry}
    (hs : Supports L' i e) : Supports (L ++ L') (L.length + i) e := by
  obtain ⟨j, hj, hje⟩ := hs
  refine ⟨L.length + j, by omega, ?_⟩
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact hje

/-- Membership is support at the length. -/
theorem supports_length_iff {L : List Entry} {e : Entry} :
    Supports L L.length e ↔ e ∈ L := by
  constructor
  · rintro ⟨j, -, hje⟩
    exact List.mem_of_getElem? hje
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
    exact ⟨j, hj, List.getElem?_eq_getElem hj⟩

theorem Verified.append {B : Set ℕ} {L L' : List Entry} (h : Verified B L)
    (h' : Verified B L') : Verified B (L ++ L') := by
  intro i e hie
  by_cases hi : i < L.length
  · rw [List.getElem?_append_left hi] at hie
    exact (h i e hie).mono fun _ => Supports.append_left
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hie
    have := (h' (i - L.length) e hie).mono fun _ => Supports.append_right (L := L)
    rwa [Nat.add_sub_cancel' (Nat.le_of_not_lt hi)] at this

/-- Appending one entry justified by the whole transcript. -/
theorem Verified.snoc {B : Set ℕ} {L : List Entry} (h : Verified B L) {e : Entry}
    (he : JustifiedBy B (· ∈ L) e) : Verified B (L ++ [e]) := by
  intro i e' hie
  have hlen := (List.getElem?_eq_some_iff.mp hie).1
  simp only [List.length_append, List.length_singleton] at hlen
  by_cases hi : i < L.length
  · rw [List.getElem?_append_left hi] at hie
    exact (h i e' hie).mono fun _ => Supports.append_left
  · have hi' : i = L.length := by omega
    subst hi'
    rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hie
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hie
    subst hie
    exact he.mono fun e'' he'' => (supports_length_iff.mpr he'').append_left

/-! ### The frozen evaluator at successor fuel, clause by clause -/

theorem ofNatCode_encodeCode (c : OracleCode) : OracleCode.ofNatCode c.encodeCode = c := by
  rw [← OracleCode.ofNatCode_eq, ← OracleCode.encodeCode_eq]
  exact Denumerable.ofNat_encode c

@[simp] theorem Entry.holds_mk_encode {B : Set ℕ} {K n x : ℕ} {c : OracleCode} :
    Entry.Holds B ⟨K, c.encodeCode, n, x⟩ ↔
      OracleCode.evaln (oracleOf B) K c n = some x := by
  simp [Entry.Holds, Entry.oracleCode, ofNatCode_encodeCode]

/-- **The evaluator's own clause structure**: at fuel `k + 1`, `evaln` returns `x` iff
the guard passes and the clause holds with every recursive call a true `evaln` fact. This
is the single point of contact between `Clause` and the frozen definition. -/
theorem evaln_succ_iff_clause {B : Set ℕ} {k : ℕ} {c : OracleCode} {n x : ℕ} :
    OracleCode.evaln (oracleOf B) (k + 1) c n = some x ↔
      n ≤ k ∧ Clause B (Entry.Holds B) k c n x := by
  cases c with
  | zero =>
    simp only [OracleCode.evaln, Clause, bind, Option.bind_eq_some_iff,
      Option.guard_eq_some', exists_and_left, exists_const, Option.pure_def,
      Option.some.injEq]
    exact and_congr Iff.rfl eq_comm
  | succ =>
    simp only [OracleCode.evaln, Clause, bind, Option.bind_eq_some_iff,
      Option.guard_eq_some', exists_and_left, exists_const, Option.pure_def,
      Option.some.injEq]
    exact and_congr Iff.rfl eq_comm
  | left =>
    simp only [OracleCode.evaln, Clause, bind, Option.bind_eq_some_iff,
      Option.guard_eq_some', exists_and_left, exists_const, Option.pure_def,
      Option.some.injEq]
    exact and_congr Iff.rfl eq_comm
  | right =>
    simp only [OracleCode.evaln, Clause, bind, Option.bind_eq_some_iff,
      Option.guard_eq_some', exists_and_left, exists_const, Option.pure_def,
      Option.some.injEq]
    exact and_congr Iff.rfl eq_comm
  | oracle =>
    simp only [OracleCode.evaln, Clause, bind, Option.bind_eq_some_iff,
      Option.guard_eq_some', exists_and_left, exists_const, Option.pure_def,
      Option.some.injEq]
    exact and_congr Iff.rfl eq_comm
  | pair cf cg =>
    simp [OracleCode.evaln, Clause, Option.bind_eq_some_iff, Seq.seq]
    intro _
    exact exists_congr fun y => and_congr Iff.rfl (exists_congr fun z =>
      and_congr Iff.rfl eq_comm)
  | comp cf cg =>
    simp [OracleCode.evaln, Clause, Option.bind_eq_some_iff]
  | prec cf cg =>
    simp only [OracleCode.evaln, Clause, Entry.holds_mk_encode, bind, Nat.unpaired,
      Option.bind_eq_some_iff, Option.guard_eq_some', exists_and_left, exists_const]
    refine and_congr Iff.rfl ?_
    rcases hm : n.unpair.2 with _ | m
    · simp
    · simp only [Nat.succ_ne_zero, false_and, false_or, Nat.succ.injEq, exists_eq_left']
      exact Option.bind_eq_some_iff
  | rfind' cf =>
    simp only [OracleCode.evaln, Clause, Entry.holds_mk_encode, bind, Nat.unpaired,
      Option.bind_eq_some_iff, Option.guard_eq_some', exists_and_left, exists_const]
    refine and_congr Iff.rfl (exists_congr fun y => and_congr Iff.rfl ?_)
    by_cases hy : y = 0 <;> simp [hy, eq_comm]

/-! ### Soundness -/

/-- **Soundness**: every entry of a verified transcript is a true `evaln` fact about the
frozen evaluator, at the entry's stored fuel, against the oracle of `B`, with the stored
code interpreted through `OracleCode.ofNatCode`. -/
theorem verified_sound {B : Set ℕ} {L : List Entry} (h : Verified B L) {e : Entry}
    (he : e ∈ L) :
    OracleCode.evaln (oracleOf B) e.fuel (OracleCode.ofNatCode e.code) e.input =
      some e.output := by
  suffices ∀ i (e : Entry), L[i]? = some e → Entry.Holds B e by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    exact this j _ (List.getElem?_eq_getElem hj)
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro e hie
    obtain ⟨k, hk, hn, hc⟩ := h i e hie
    have hc' : Clause B (Entry.Holds B) k e.oracleCode e.input e.output :=
      hc.mono fun e' ⟨j, hj, hje⟩ => ih j hj e' hje
    show OracleCode.evaln (oracleOf B) e.fuel e.oracleCode e.input = some e.output
    rw [hk]
    exact evaln_succ_iff_clause.mpr ⟨hn, hc'⟩

/-! ### Completeness -/

/-- A one-entry transcript whose entry needs no support. -/
theorem Verified.singleton {B : Set ℕ} {e : Entry} (he : JustifiedBy B (fun _ => False) e) :
    Verified B [e] :=
  Verified.snoc (L := []) (fun _ _ h => by simp at h) (he.mono fun _ h => h.elim)

/-- The target entry of a computation, under the pinned convention. -/
def targetEntry (K : ℕ) (c : OracleCode) (n x : ℕ) : Entry := ⟨K, c.encodeCode, n, x⟩

private theorem mem_snoc {L : List Entry} (e : Entry) : e ∈ L ++ [e] :=
  List.mem_append_right _ (List.mem_singleton_self _)

/-- A target entry is justified by `S` once its guard and clause are. -/
theorem justified_target {B : Set ℕ} (S : Entry → Prop) {k : ℕ} (c : OracleCode) {n : ℕ}
    (x : ℕ) (hn : n ≤ k) (hc : Clause B S k c n x) :
    JustifiedBy B S (targetEntry (k + 1) c n x) :=
  ⟨k, rfl, hn, by
    show Clause B S k (OracleCode.ofNatCode c.encodeCode) n x
    rw [ofNatCode_encodeCode]
    exact hc⟩

/-- Completeness at successor fuel, by structural recursion on the code, given
completeness at the predecessor fuel for every code (the `prec` self-call and the
`rfind'` continuation). -/
theorem complete_succ {B : Set ℕ} {k : ℕ}
    (ih : ∀ (c : OracleCode) {n x : ℕ}, OracleCode.evaln (oracleOf B) k c n = some x →
      ∃ L, Verified B L ∧ targetEntry k c n x ∈ L) :
    ∀ (c : OracleCode) {n x : ℕ}, OracleCode.evaln (oracleOf B) (k + 1) c n = some x →
      ∃ L, Verified B L ∧ targetEntry (k + 1) c n x ∈ L
  | .zero, n, x, h =>
    let ⟨hn, hc⟩ := evaln_succ_iff_clause.mp h
    ⟨_, Verified.singleton (justified_target (fun _ => False) .zero x hn hc),
      List.mem_singleton_self _⟩
  | .succ, n, x, h =>
    let ⟨hn, hc⟩ := evaln_succ_iff_clause.mp h
    ⟨_, Verified.singleton (justified_target (fun _ => False) .succ x hn hc),
      List.mem_singleton_self _⟩
  | .left, n, x, h =>
    let ⟨hn, hc⟩ := evaln_succ_iff_clause.mp h
    ⟨_, Verified.singleton (justified_target (fun _ => False) .left x hn hc),
      List.mem_singleton_self _⟩
  | .right, n, x, h =>
    let ⟨hn, hc⟩ := evaln_succ_iff_clause.mp h
    ⟨_, Verified.singleton (justified_target (fun _ => False) .right x hn hc),
      List.mem_singleton_self _⟩
  | .oracle, n, x, h =>
    let ⟨hn, hc⟩ := evaln_succ_iff_clause.mp h
    ⟨_, Verified.singleton (justified_target (fun _ => False) .oracle x hn hc),
      List.mem_singleton_self _⟩
  | .pair cf cg, n, x, h => by
    obtain ⟨hn, y, z, hy, hz, rfl⟩ := evaln_succ_iff_clause.mp h
    obtain ⟨L₁, hL₁, hm₁⟩ := complete_succ ih cf (Entry.holds_mk_encode.mp hy)
    obtain ⟨L₂, hL₂, hm₂⟩ := complete_succ ih cg (Entry.holds_mk_encode.mp hz)
    exact ⟨_, (hL₁.append hL₂).snoc (justified_target (· ∈ L₁ ++ L₂) (.pair cf cg) _ hn
      ⟨y, z, List.mem_append_left _ hm₁,
      List.mem_append_right _ hm₂, rfl⟩), mem_snoc _⟩
  | .comp cf cg, n, x, h => by
    obtain ⟨hn, y, hy, hx⟩ := evaln_succ_iff_clause.mp h
    obtain ⟨L₁, hL₁, hm₁⟩ := complete_succ ih cg (Entry.holds_mk_encode.mp hy)
    obtain ⟨L₂, hL₂, hm₂⟩ := complete_succ ih cf (Entry.holds_mk_encode.mp hx)
    exact ⟨_, (hL₁.append hL₂).snoc (justified_target (· ∈ L₁ ++ L₂) (.comp cf cg) x hn
      ⟨y, List.mem_append_left _ hm₁, List.mem_append_right _ hm₂⟩), mem_snoc _⟩
  | .prec cf cg, n, x, h => by
    obtain ⟨hn, hc⟩ := evaln_succ_iff_clause.mp h
    rcases hc with ⟨hm, hb⟩ | ⟨m, i, hm, hs, hg⟩
    · obtain ⟨L₁, hL₁, hm₁⟩ := complete_succ ih cf (Entry.holds_mk_encode.mp hb)
      exact ⟨_, hL₁.snoc (justified_target (· ∈ L₁) (.prec cf cg) x hn (Or.inl ⟨hm, hm₁⟩)),
        mem_snoc _⟩
    · obtain ⟨L₁, hL₁, hm₁⟩ := ih (.prec cf cg) (Entry.holds_mk_encode.mp hs)
      obtain ⟨L₂, hL₂, hm₂⟩ := complete_succ ih cg (Entry.holds_mk_encode.mp hg)
      exact ⟨_, (hL₁.append hL₂).snoc (justified_target (· ∈ L₁ ++ L₂) (.prec cf cg) x hn
        (Or.inr ⟨m, i, hm,
        List.mem_append_left _ hm₁, List.mem_append_right _ hm₂⟩)), mem_snoc _⟩
  | .rfind' cf, n, x, h => by
    obtain ⟨hn, y, hy, hc⟩ := evaln_succ_iff_clause.mp h
    obtain ⟨L₁, hL₁, hm₁⟩ := complete_succ ih cf (Entry.holds_mk_encode.mp hy)
    rcases hc with ⟨hy0, hx⟩ | ⟨hy0, hs⟩
    · exact ⟨_, hL₁.snoc (justified_target (· ∈ L₁) (.rfind' cf) x hn
        ⟨y, hm₁, Or.inl ⟨hy0, hx⟩⟩), mem_snoc _⟩
    · obtain ⟨L₂, hL₂, hm₂⟩ := ih (.rfind' cf) (Entry.holds_mk_encode.mp hs)
      exact ⟨_, (hL₁.append hL₂).snoc (justified_target (· ∈ L₁ ++ L₂) (.rfind' cf) x hn
        ⟨y, List.mem_append_left _ hm₁, Or.inr ⟨hy0, List.mem_append_right _ hm₂⟩⟩), mem_snoc _⟩

/-- **Completeness**: every true `evaln` fact about the frozen evaluator, at any fuel,
occurs in some verified transcript — its target entry, appended after the
sub-transcripts it depends on, stores that fuel and the encoded code. -/
theorem verified_complete {B : Set ℕ} :
    ∀ (K : ℕ) (c : OracleCode) {n x : ℕ}, OracleCode.evaln (oracleOf B) K c n = some x →
      ∃ L, Verified B L ∧ targetEntry K c n x ∈ L
  | 0, c, n, x, h => by simp [OracleCode.evaln] at h
  | k + 1, c, n, x, h => complete_succ (fun c' _ _ h' => verified_complete k c' h') c h

/-! ### Determinism -/

/-- **Determinism, across transcripts**: entries of two verified transcripts with the
same code and input have the same output — soundness in each transcript, then
`evaln_mono` to the larger fuel. -/
theorem verified_deterministic₂ {B : Set ℕ} {L₁ L₂ : List Entry} (h₁ : Verified B L₁)
    (h₂ : Verified B L₂) {e₁ e₂ : Entry} (m₁ : e₁ ∈ L₁) (m₂ : e₂ ∈ L₂)
    (hc : e₁.code = e₂.code) (hn : e₁.input = e₂.input) : e₁.output = e₂.output := by
  have s₁ := verified_sound h₁ m₁
  have s₂ := verified_sound h₂ m₂
  rw [hc, hn] at s₁
  have k₁ : e₁.output ∈ OracleCode.evaln (oracleOf B) (max e₁.fuel e₂.fuel)
      (OracleCode.ofNatCode e₂.code) e₂.input :=
    OracleCode.evaln_mono (le_max_left _ _) s₁
  have k₂ : e₂.output ∈ OracleCode.evaln (oracleOf B) (max e₁.fuel e₂.fuel)
      (OracleCode.ofNatCode e₂.code) e₂.input :=
    OracleCode.evaln_mono (le_max_right _ _) s₂
  exact Option.mem_unique k₁ k₂

/-- **Determinism within one transcript**, as a corollary. -/
theorem verified_deterministic {B : Set ℕ} {L : List Entry} (h : Verified B L)
    {e₁ e₂ : Entry} (h₁ : e₁ ∈ L) (h₂ : e₂ ∈ L) (hc : e₁.code = e₂.code)
    (hn : e₁.input = e₂.input) : e₁.output = e₂.output :=
  verified_deterministic₂ h h h₁ h₂ hc hn

end RMFoundationBridge
