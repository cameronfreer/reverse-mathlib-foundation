/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.ParamOracle
import RMFoundationBridge.Delta0Eval

/-!
# F1 item 5, second layer (third slice): relative computability of the evaluator

**Bounded oracle recursion** — the same finite-query discipline as a transcript, but the
artifact is an interleaved recursion, nothing is materialized. Import boundary: the
executable layer only, never `Delta0Agreement` — relative computability is independent of
semantic correctness; the two results compose later.

Review pins: the result is stated at the **exact Boolean-as-ℕ normalization used by
`charFn`** (`bif b then 1 else 0`, agreeing with `if P then 1 else 0` at
`b = decide P`), so composition with `beval_agrees` needs no coercion archaeology.
Bounded recursion keeps its invariant explicit: the universal starts at `1` and
multiplies, the existential starts at `0` and takes the `{0,1}`-max (as
`a + b - a * b`), every intermediate stays in `{0, 1}`. Exactly **one oracle query per
evaluated signed membership atom**, at the `paramQuery` code; negation is pure
postprocessing. Generic in the oracle set `O`; `finiteParamOracle A` appears only in
later specialization. Short decoded environments stay total through `getD`. No
`OmegaPart`, `IsTuringIdeal`, semantic evaluation, hierarchy premise, or internal
packaging.
-/

namespace RMFoundationBridge

open ReverseMathlib.Omega

open Classical in
/-- The oracle answer function for an arbitrary oracle set (definitionally
`membershipOracle A` at `O := finiteParamOracle A`). -/
noncomputable def oracleAnswers (O : Set ℕ) : ℕ → Bool :=
  fun q => decide (q ∈ O)

/-- The evaluator at a coded environment, in `charFn`'s exact Boolean-as-ℕ
normalization. -/
noncomputable def bevalNat (O : Set ℕ) {N n : ℕ} (c : Delta0Code N n) (ec : ℕ) : ℕ :=
  bif Delta0Code.beval (oracleAnswers O) c (decodeSeq ec) then 1 else 0

/-! ### Named helpers: environment consing and bounded iteration -/

/-- Environment consing on codes is primitive recursive. -/
theorem primrec_consCode : Primrec₂ fun x ec => seqCode (x :: decodeSeq ec) :=
  (primrec_seqCode.comp
    (Primrec.list_cons.comp Primrec.fst (primrec_decodeSeq.comp Primrec.snd))).to₂

/-- The bounded universal as an explicit `{0,1}`-product recursion: start at `1`,
multiply. -/
theorem ballProd_eq_nat_rec (O : Set ℕ) {N n : ℕ} (c : Delta0Code N (n + 1)) (ec : ℕ) :
    ∀ k : ℕ,
      (Nat.rec (motive := fun _ => ℕ) 1
        (fun y ih => ih * bevalNat O c (seqCode (y :: decodeSeq ec))) k) =
      (bif (List.range k).all
          (fun x => Delta0Code.beval (oracleAnswers O) c (x :: decodeSeq ec))
        then 1 else 0)
  | 0 => rfl
  | k + 1 => by
      rw [show (Nat.rec (motive := fun _ => ℕ) 1
            (fun y ih => ih * bevalNat O c (seqCode (y :: decodeSeq ec))) (k + 1)) =
          (Nat.rec (motive := fun _ => ℕ) 1
            (fun y ih => ih * bevalNat O c (seqCode (y :: decodeSeq ec))) k) *
            bevalNat O c (seqCode (k :: decodeSeq ec)) from rfl,
        ballProd_eq_nat_rec O c ec k, List.range_succ, List.all_append, bevalNat,
        decodeSeq_seqCode]
      cases hall : (List.range k).all
          (fun x => Delta0Code.beval (oracleAnswers O) c (x :: decodeSeq ec)) <;>
        cases hch : Delta0Code.beval (oracleAnswers O) c (k :: decodeSeq ec) <;>
        simp [hch]

/-- The bounded existential as an explicit `{0,1}`-max recursion: start at `0`, combine
by `a + b - a * b`. -/
theorem bexMax_eq_nat_rec (O : Set ℕ) {N n : ℕ} (c : Delta0Code N (n + 1)) (ec : ℕ) :
    ∀ k : ℕ,
      (Nat.rec (motive := fun _ => ℕ) 0
        (fun y ih => ih + bevalNat O c (seqCode (y :: decodeSeq ec)) -
          ih * bevalNat O c (seqCode (y :: decodeSeq ec))) k) =
      (bif (List.range k).any
          (fun x => Delta0Code.beval (oracleAnswers O) c (x :: decodeSeq ec))
        then 1 else 0)
  | 0 => rfl
  | k + 1 => by
      rw [show (Nat.rec (motive := fun _ => ℕ) 0
            (fun y ih => ih + bevalNat O c (seqCode (y :: decodeSeq ec)) -
              ih * bevalNat O c (seqCode (y :: decodeSeq ec))) (k + 1)) =
          (Nat.rec (motive := fun _ => ℕ) 0
            (fun y ih => ih + bevalNat O c (seqCode (y :: decodeSeq ec)) -
              ih * bevalNat O c (seqCode (y :: decodeSeq ec))) k) +
            bevalNat O c (seqCode (k :: decodeSeq ec)) -
            (Nat.rec (motive := fun _ => ℕ) 0
              (fun y ih => ih + bevalNat O c (seqCode (y :: decodeSeq ec)) -
                ih * bevalNat O c (seqCode (y :: decodeSeq ec))) k) *
              bevalNat O c (seqCode (k :: decodeSeq ec)) from rfl,
        bexMax_eq_nat_rec O c ec k, List.range_succ, List.any_append, bevalNat,
        decodeSeq_seqCode]
      cases hany : (List.range k).any
          (fun x => Delta0Code.beval (oracleAnswers O) c (x :: decodeSeq ec)) <;>
        cases hch : Delta0Code.beval (oracleAnswers O) c (k :: decodeSeq ec) <;>
        simp [hch]

/-! ### The theorem -/

open Classical in
/-- **Relative computability of the evaluator**: for a fixed code, evaluation at a coded
environment is recursive in the oracle's characteristic function — one oracle query per
signed membership atom, bounded oracle recursion for the bounded quantifiers. Stated at
`charFn`'s Boolean-as-ℕ normalization for direct later composition with the agreement
theorem. -/
theorem recursiveIn_bevalNat (O : Set ℕ) :
    ∀ {N n : ℕ} (c : Delta0Code N n),
      Nat.RecursiveIn {charFn O} fun ec => Part.some (bevalNat O c ec)
  | _, _, .eq t s =>
      (recursiveIn_of_primrec (Primrec.ite
        (Primrec.eq.comp (primrec_termValEnv t)
          (primrec_termValEnv s))
        (Primrec.const 1) (Primrec.const 0))).of_eq fun ec => by
      by_cases h : termValEnv t (decodeSeq ec) = termValEnv s (decodeSeq ec) <;>
        simp [bevalNat, Delta0Code.beval, beq_eq_decide, h]
  | _, _, .neq t s =>
      (recursiveIn_of_primrec (Primrec.ite
        (Primrec.eq.comp (primrec_termValEnv t)
          (primrec_termValEnv s))
        (Primrec.const 0) (Primrec.const 1))).of_eq fun ec => by
      by_cases h : termValEnv t (decodeSeq ec) = termValEnv s (decodeSeq ec) <;>
        simp [bevalNat, Delta0Code.beval, beq_eq_decide, h]
  | _, _, .lt t s =>
      (recursiveIn_of_primrec (Primrec.ite
        (Primrec.nat_lt.comp (primrec_termValEnv t)
          (primrec_termValEnv s))
        (Primrec.const 1) (Primrec.const 0))).of_eq fun ec => by
      by_cases h : termValEnv t (decodeSeq ec) < termValEnv s (decodeSeq ec) <;>
        simp [bevalNat, Delta0Code.beval, h]
  | _, _, .nlt t s =>
      (recursiveIn_of_primrec (Primrec.ite
        (Primrec.nat_lt.comp (primrec_termValEnv t)
          (primrec_termValEnv s))
        (Primrec.const 0) (Primrec.const 1))).of_eq fun ec => by
      by_cases h : termValEnv t (decodeSeq ec) < termValEnv s (decodeSeq ec) <;>
        simp [bevalNat, Delta0Code.beval, h]
  | _, _, .mem X t =>
      (recursiveIn_comp_primrec
        ((Nat.RecursiveIn.oracle _ rfl : Nat.RecursiveIn {charFn O} (charFn O)))
        ((primrec_paramQuery X).comp (primrec_termValEnv t))).of_eq fun ec => by
      by_cases h : paramQuery X (termValEnv t (decodeSeq ec)) ∈ O <;>
        simp [bevalNat, Delta0Code.beval, oracleAnswers, charFn, h]
  | _, _, .notMem X t => by
      have hbase : Nat.RecursiveIn {charFn O} fun ec =>
          Part.some (if paramQuery X (termValEnv t (decodeSeq ec)) ∈ O
            then 1 else 0) :=
        (recursiveIn_comp_primrec
        ((Nat.RecursiveIn.oracle _ rfl : Nat.RecursiveIn {charFn O} (charFn O)))
          ((primrec_paramQuery X).comp (primrec_termValEnv t))).of_eq fun ec => rfl
      exact (recursiveIn_comp_total
        (recursiveIn_of_primrec
          (Primrec.nat_sub.comp (Primrec.const 1) Primrec.id)) hbase).of_eq fun ec => by
        by_cases h : paramQuery X (termValEnv t (decodeSeq ec)) ∈ O <;>
          simp [bevalNat, Delta0Code.beval, oracleAnswers, h]
  | _, _, .verum =>
      (recursiveIn_of_primrec (Primrec.const 1)).of_eq fun ec => by
        simp [bevalNat, Delta0Code.beval]
  | _, _, .falsum =>
      (recursiveIn_of_primrec (Primrec.const 0)).of_eq fun ec => by
        simp [bevalNat, Delta0Code.beval]
  | _, _, .and c d => by
      have h1 := recursiveIn_bevalNat O c
      have h2 := recursiveIn_bevalNat O d
      exact (recursiveIn_comp_total
        (recursiveIn_of_primrec (Primrec.nat_mul.comp
          (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))
        (recursiveIn_pair_total h1 h2)).of_eq fun ec => by
        cases hb : Delta0Code.beval (oracleAnswers O) c (decodeSeq ec) <;>
          cases hd : Delta0Code.beval (oracleAnswers O) d (decodeSeq ec) <;>
          simp [bevalNat, Delta0Code.beval, hb, hd, Nat.unpair_pair]
  | _, _, .or c d => by
      have h1 := recursiveIn_bevalNat O c
      have h2 := recursiveIn_bevalNat O d
      exact (recursiveIn_comp_total
        (recursiveIn_of_primrec
          (Primrec.nat_sub.comp
            (Primrec.nat_add.comp (Primrec.fst.comp Primrec.unpair)
              (Primrec.snd.comp Primrec.unpair))
            (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.unpair)
              (Primrec.snd.comp Primrec.unpair))))
        (recursiveIn_pair_total h1 h2)).of_eq fun ec => by
        cases hb : Delta0Code.beval (oracleAnswers O) c (decodeSeq ec) <;>
          cases hd : Delta0Code.beval (oracleAnswers O) d (decodeSeq ec) <;>
          simp [bevalNat, Delta0Code.beval, hb, hd, Nat.unpair_pair]
  | _, _, .ball t c => by
      have hchild := recursiveIn_bevalNat O c
      have hstep : Nat.RecursiveIn {charFn O} fun m =>
          Part.some (m.unpair.2.unpair.2 *
            bevalNat O c (seqCode (m.unpair.2.unpair.1 :: decodeSeq m.unpair.1))) := by
        have hc : Nat.RecursiveIn {charFn O} fun m =>
            Part.some (bevalNat O c
              (seqCode (m.unpair.2.unpair.1 :: decodeSeq m.unpair.1))) :=
          recursiveIn_comp_primrec hchild
            (Primrec₂.comp (f := fun x ec => seqCode (x :: decodeSeq ec)) primrec_consCode
              (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
              (Primrec.fst.comp Primrec.unpair))
        have hih : Nat.RecursiveIn {charFn O} fun m =>
            Part.some m.unpair.2.unpair.2 :=
          recursiveIn_of_primrec
            (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
        exact (recursiveIn_comp_total
          (recursiveIn_of_primrec (Primrec.nat_mul.comp
            (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))
          (recursiveIn_pair_total hih hc)).of_eq fun m => by
          simp [Nat.unpair_pair]
      have hrec := recursiveIn_nat_rec_param (base := fun _ : ℕ => 1)
        (step := fun a y ih => ih * bevalNat O c (seqCode (y :: decodeSeq a)))
        (recursiveIn_of_primrec (Primrec.const 1)) hstep
      exact (recursiveIn_comp_primrec hrec
        (Primrec₂.comp (f := Nat.pair) Primrec₂.natPair Primrec.id
          (primrec_termValEnv t))).of_eq fun ec => by
        rw [Nat.unpair_pair]
        exact congrArg Part.some
          ((ballProd_eq_nat_rec O c ec (termValEnv t (decodeSeq ec))).trans (by
            simp [bevalNat, Delta0Code.beval]))
  | _, _, .bex t c => by
      have hchild := recursiveIn_bevalNat O c
      have hstep : Nat.RecursiveIn {charFn O} fun m =>
          Part.some (m.unpair.2.unpair.2 +
            bevalNat O c (seqCode (m.unpair.2.unpair.1 :: decodeSeq m.unpair.1)) -
            m.unpair.2.unpair.2 *
              bevalNat O c (seqCode (m.unpair.2.unpair.1 :: decodeSeq m.unpair.1))) := by
        have hc : Nat.RecursiveIn {charFn O} fun m =>
            Part.some (bevalNat O c
              (seqCode (m.unpair.2.unpair.1 :: decodeSeq m.unpair.1))) :=
          recursiveIn_comp_primrec hchild
            (Primrec₂.comp (f := fun x ec => seqCode (x :: decodeSeq ec)) primrec_consCode
              (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
              (Primrec.fst.comp Primrec.unpair))
        have hih : Nat.RecursiveIn {charFn O} fun m =>
            Part.some m.unpair.2.unpair.2 :=
          recursiveIn_of_primrec
            (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
        exact (recursiveIn_comp_total
          (recursiveIn_of_primrec
            (Primrec.nat_sub.comp
              (Primrec.nat_add.comp (Primrec.fst.comp Primrec.unpair)
                (Primrec.snd.comp Primrec.unpair))
              (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.unpair)
                (Primrec.snd.comp Primrec.unpair))))
          (recursiveIn_pair_total hih hc)).of_eq fun m => by
          simp [Nat.unpair_pair]
      have hrec := recursiveIn_nat_rec_param (base := fun _ : ℕ => 0)
        (step := fun a y ih => ih + bevalNat O c (seqCode (y :: decodeSeq a)) -
          ih * bevalNat O c (seqCode (y :: decodeSeq a)))
        (recursiveIn_of_primrec (Primrec.const 0)) hstep
      exact (recursiveIn_comp_primrec hrec
        (Primrec₂.comp (f := Nat.pair) Primrec₂.natPair Primrec.id
          (primrec_termValEnv t))).of_eq fun ec => by
        rw [Nat.unpair_pair]
        exact congrArg Part.some
          ((bexMax_eq_nat_rec O c ec (termValEnv t (decodeSeq ec))).trans (by
            simp [bevalNat, Delta0Code.beval]))

end RMFoundationBridge
