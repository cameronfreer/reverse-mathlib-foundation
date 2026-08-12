/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.SentenceTransfer
import RMFoundationBridge.Turnstile

/-!
# The bridge export surface

The **typed** export records downstream consumers (eventually reverse-mathlib, as
external checked backend evidence) may cite — nothing else in the bridge is part of the
export contract. Every record carries its meaning in its type and its provenance in a
single named theorem; no export reproves anything inline, and the audit's dependency
gates check that each export genuinely reaches its named theorem — and that no export
leaf reaches the derived ŴKL → Hall composition.

Epistemic boundary, restated as types:

* **Context realization is one-way** (`RealizationDirection.forward`,
  `RealizationStatus.realizationOnly`): every Turing ideal realizes semantic RCA₀ on
  ω-structures. No converse-adequacy claim exists anywhere in the bridge.
* **Statement adapters are unconditional** (`AdapterStatus.unconditional`): each ties
  one closed sentence to one frozen capability, for arbitrary `Ω`.
* **The calculus is bridge-local** (`BridgeCalculusId.henkinSafeV1`,
  `CalculusComparisonStatus.pending`): no equivalence with a pinned standard proof
  system is claimed.
* **Nonderivability is calculus-relative**: the record type is indexed by the calculus
  identifier, so it cannot render as a generic RCA₀ ⊬ WKL.

* **The semantic countermodel is scope-tagged** (`SemanticScopeTag.allModels`,
  `ModelClassTag.foundationStruc2General`): the all-model nonconsequence over general
  `Struc₂` structures, witnessed by an ω-structure (provenance, not scope).

No local certified fact is added: these are evidence records about theorems the
bridge already owns. The consumer may count the validated semantic-countermodel
record in its explicitly backend-qualified scoped-results scoreboard.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-! ### Status vocabularies -/

/-- Direction of a context-realization record. Only `forward` exists: the bridge proves
that ideals realize the theory, never that realizers are ideals. -/
inductive RealizationDirection
  | forward
  deriving DecidableEq, Repr

/-- Strength of a context-realization record. Only `realizationOnly` exists: this is
one-way realization evidence, not context equivalence. -/
inductive RealizationStatus
  | realizationOnly
  deriving DecidableEq, Repr

/-- Status of a statement adapter. Only `unconditional` exists: every exported adapter
holds for an arbitrary second-order part. -/
inductive AdapterStatus
  | unconditional
  deriving DecidableEq, Repr

/-- Stable bridge-local calculus identifiers. -/
inductive BridgeCalculusId
  | henkinSafeV1
  deriving DecidableEq, Repr

/-- Comparison of a bridge-local calculus against a pinned standard proof system.
`pending` records the proof-system-adequacy debt: neither an embedding of a standard
calculus nor direct soundness for one has been proved. -/
inductive CalculusComparisonStatus
  | pending
  deriving DecidableEq, Repr

/-! ### Record types -/

/-- **Context realization**: every Turing ideal satisfies every sentence of the theory,
on ω-structures. The direction and status fields pin the one-way reading in the data. -/
structure ContextRealizationCertificate (theory : Set (SecondOrder.Sentence ℒₒᵣ)) where
  direction : RealizationDirection
  status : RealizationStatus
  realizes : ∀ Ω : OmegaPart, IsTuringIdeal Ω → Ω.toFoundation ⊧* theory

/-- **Exact statement adapter**: one closed sentence tied to one frozen capability,
for an arbitrary second-order part. -/
structure StatementAdapterCertificate (sentence : SecondOrder.Sentence ℒₒᵣ)
    (capability : OmegaPart → Prop) where
  status : AdapterStatus
  adequate : ∀ Ω : OmegaPart, (Ω.toFoundation ⊧ sentence ↔ capability Ω)

/-- **Calculus identity**: the bridge-local calculus with its soundness theorem and its
standard-calculus comparison status. -/
structure CalculusRecord where
  id : BridgeCalculusId
  comparison : CalculusComparisonStatus
  sound : ∀ {Γ : Set (SecondOrder.Sentence ℒₒᵣ)} {σ : SecondOrder.Sentence ℒₒᵣ},
    Derivable Γ σ → ∀ M : Struc₂.{0, 0} ℒₒᵣ, (∀ τ ∈ Γ, M ⊧ τ) → M ⊧ σ

/-- **Calculus-relative nonderivability**, structurally keyed to a calculus identifier:
the type says *in which* calculus the sentence is underivable, so the record cannot
render as a generic turnstile claim. -/
structure NonderivabilityCertificate (id : BridgeCalculusId)
    (theory : Set (SecondOrder.Sentence ℒₒᵣ))
    (sentence : SecondOrder.Sentence ℒₒᵣ) where
  underivable_in_bridge_calculus : ¬ Derivable theory sentence

/-- **Scope vocabulary for semantic nonconsequence records**: the general L₂
model class. Closed tag; explanatory prose is generated at render time. -/
inductive SemanticScopeTag
  | allModels
  deriving DecidableEq, Repr

/-- **Model-class vocabulary**: Foundation's `Struc₂` — general (Henkin-style)
second-order structures, the standard model class for subsystems of Z₂. -/
inductive ModelClassTag
  | foundationStruc2General
  deriving DecidableEq, Repr

/-- **Semantic countermodel**, structurally keyed to scope and model class: the
theory does not semantically imply the sentence over the general `Struc₂` class.
The witness (an ω-structure) is provenance, not the scope — an ω-countermodel is
in particular an L₂ countermodel. -/
structure SemanticCountermodelCertificate
    (theory : Set (SecondOrder.Sentence ℒₒᵣ))
    (sentence : SecondOrder.Sentence ℒₒᵣ) where
  scope : SemanticScopeTag
  modelClass : ModelClassTag
  countermodel : ∃ M : Struc₂.{0, 0} ℒₒᵣ, (∀ σ ∈ theory, M ⊧ σ) ∧ ¬ M ⊧ sentence

/-! ### The export records -/

/-- Export 1 — the one-way context realization: `forward_adequacy`, in `⊧*` form. -/
def rca0RealizationExport : ContextRealizationCertificate Rca0Theory where
  direction := .forward
  status := .realizationOnly
  realizes := fun _ h => ⟨fun _ hσ => forward_adequacy h hσ⟩

/-- Export 2a — the exact ŴKL statement adapter: `models_wklSentence_iff`. -/
def wklAdapterExport : StatementAdapterCertificate wklSentence WeakKonigAt where
  status := .unconditional
  adequate := fun _ => models_wklSentence_iff

/-- Export 2b — the exact EFILC statement adapter: `models_efilcSentence_iff`. -/
def efilcAdapterExport : StatementAdapterCertificate efilcSentence EFILCAt where
  status := .unconditional
  adequate := fun _ => models_efilcSentence_iff

/-- Export 2c — the exact one-sided Hall statement adapter:
`models_hallSentence_iff`. -/
def hallAdapterExport : StatementAdapterCertificate hallSentence CountableHallAt where
  status := .unconditional
  adequate := fun _ => models_hallSentence_iff

/-- Export 3 — the calculus identity: `Derivable` with `soundness_sentence`,
standard-calculus comparison pending. -/
def bridgeCalculusExport : CalculusRecord where
  id := .henkinSafeV1
  comparison := .pending
  sound := fun h M hΓ => soundness_sentence h M hΓ

/-- Export 4 — the calculus-relative nonderivability: `rca0_not_derives_wkl`, keyed to
`henkinSafeV1`. -/
theorem wklNonderivabilityExport :
    NonderivabilityCertificate .henkinSafeV1 Rca0Theory wklSentence :=
  ⟨rca0_not_derives_wkl⟩

/-- Export 5 — the all-model semantic countermodel:
`rca0_not_semantically_implies_wkl`, keyed to scope `allModels` over the general
`Struc₂` class. -/
def wklCountermodelExport :
    SemanticCountermodelCertificate Rca0Theory wklSentence where
  scope := .allModels
  modelClass := .foundationStruc2General
  countermodel := rca0_not_semantically_implies_wkl

end RMFoundationBridge
