/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.ConverseDownward
import RMFoundationBridge.ForwardAdequacy

/-!
# Converse adequacy, Slice D (bridge half): the converse and the context equivalence

The three clauses of `IsTuringIdeal` have been recovered from satisfaction of
`Rca0Theory` on canonical ω-structures — nonemptiness and the join in Slice A,
downward closure in Slice C3. This module bundles them:

* `isTuringIdeal_of_models_rca0` — **the converse**: every canonical ω-structure
  satisfying the theory is a Turing ideal;
* `models_rca0_iff_isTuringIdeal` — **the context equivalence**: together with
  `forward_adequacy`, the canonical ω-structures satisfying `Rca0Theory` are exactly the
  Turing ideals.

**What this does and does not say.** It concerns the canonical ω-structures
`Ω.toFoundation` (number sort standard ℕ under the explicitly supplied interpretation,
set sort exactly `Ω.sets`) and the named bridge theory `Rca0Theory`. Consequently every
registered theorem over all Turing ideals holds over every canonical ω-model of that
exact theory. It does **not** identify `Rca0Theory` unqualifiedly with conventional
RCA₀ (axiomatization faithfulness is a separate obligation, still documented as claimed
and unverified against a pinned source), it transports nothing to arbitrary Henkin or
nonstandard models, it claims no object-calculus derivability, it does not reinterpret
the calculus-relative nonderivability as conventional-RCA₀ nonderivability, and it turns
no typed ω-capability into an L₂ theorem without that capability's own statement adapter.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-- **The converse**: every canonical ω-structure satisfying `Rca0Theory` is a Turing
ideal — nonemptiness from comprehension on `⊥`, downward closure from comprehension on
the Σ⁰₁ output predicate and its Π⁰₁ complement, join closure from comprehension on the
bounded even/odd matrix. -/
theorem isTuringIdeal_of_models_rca0 {Ω : OmegaPart} (h : Ω.toFoundation ⊧* Rca0Theory) :
    IsTuringIdeal Ω where
  nonempty := nonempty_of_models_rca0 h
  downward := fun hB hAB => mem_of_reducible_of_models_rca0 h hB hAB
  join := fun hA hB => joinSet_mem_of_models_rca0 h hA hB

/-- **Context equivalence** on canonical ω-structures: `Ω.toFoundation` satisfies the
named theory iff `Ω` is a Turing ideal. -/
theorem models_rca0_iff_isTuringIdeal (Ω : OmegaPart) :
    Ω.toFoundation ⊧* Rca0Theory ↔ IsTuringIdeal Ω :=
  ⟨isTuringIdeal_of_models_rca0, fun h => ⟨fun _ hσ => forward_adequacy h hσ⟩⟩

/-- The recursive part, both ways: a Turing ideal, hence a model; a model, hence a
Turing ideal (the converse instantiated at REC). -/
example : recursivePart.toFoundation ⊧* Rca0Theory :=
  (models_rca0_iff_isTuringIdeal _).mpr recursivePart_isTuringIdeal

example : IsTuringIdeal recursivePart :=
  isTuringIdeal_of_models_rca0 ⟨fun _ hσ => recursivePart_models_rca0 hσ⟩

end RMFoundationBridge
