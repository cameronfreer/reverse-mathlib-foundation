/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.SentenceTransfer
import RMFoundationBridge.Turnstile
import RMFoundationBridge.StandardTurnstile

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
* **The Henkin-safe calculus is bridge-local** (`BridgeCalculusId.henkinSafeV1`); the
  **pinned standard calculus** (`BridgeCalculusId.l2VarWitnessLKv1`) is the bridge's
  fully specified LK presentation of the conventional two-sorted logic *assumed* in
  Simpson [Sim09] §I.2, carrying its nonempty-sort assumption as a closed tag and its
  **direct** theory-level soundness. Their typed comparison record
  (`CalculusRelationTag.independentDirectSoundness`) states exactly that both are
  independently sound; **it carries no embedding and licenses no derivability
  transfer** in either direction. (The checked ∃X⊤ contrast refutes the
  identity-preserving embedding of the standard calculus into the Henkin-safe one;
  no claim is made about the reverse direction.)
* **Nonderivability is calculus-relative**: each record type is indexed by the calculus
  identifier, so it cannot render as a generic RCA₀ ⊬ WKL. The standard-calculus
  record renders as `Rca0Theory ⊬ wklSentence in l2VarWitnessLK.v1` — the
  identification of the pinned calculus with Simpson's prose logic is a documented
  reading, never a checked claim.

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

/-- Stable calculus identifiers: the bridge-local Henkin-safe calculus and the pinned
standard calculus `l2VarWitnessLK.v1`. -/
inductive BridgeCalculusId
  | henkinSafeV1
  | l2VarWitnessLKv1
  deriving DecidableEq, Repr

/-- Comparison of a bridge-local calculus against a pinned standard proof system.
`recorded` means a typed calculus-comparison record exists naming the exact relation;
it never asserts an embedding. (`pending` recorded the earlier
proof-system-adequacy debt and is retained for the tag vocabulary's history.) -/
inductive CalculusComparisonStatus
  | pending
  | recorded
  deriving DecidableEq, Repr

/-- Sort assumption a calculus's theory-level soundness consumes. Only
`nonemptySetSort` exists: the pinned standard calculus needs a nonempty designated
part (Simpson [Sim09] §I.2 assumes both sorts nonempty). -/
inductive SortAssumptionTag
  | nonemptySetSort
  deriving DecidableEq, Repr

/-- Equality rules a calculus carries. Only `reflAndSubstitution` exists: Simpson's
"usual logical axioms, including equality" — reflexivity and the substitution schema,
sound against equality-correct structures (`EqCorrect`, an explicit hypothesis of
soundness). -/
inductive EqualityRulesTag
  | reflAndSubstitution
  deriving DecidableEq, Repr

/-- Relation carried by a calculus-comparison record. Only
`independentDirectSoundness` exists: both calculi are independently sound over
`Struc₂` semantics (the Henkin-safe one for every designated part, the pinned
standard one for nonempty equality-correct parts); the record carries no embedding
and licenses no derivability transfer in either direction. The checked ∃X⊤ contrast
refutes the identity-preserving embedding of the standard calculus into the
Henkin-safe one; no claim is made about the reverse direction. -/
inductive CalculusRelationTag
  | independentDirectSoundness
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

/-- **Pinned standard calculus identity**: the fully specified LK presentation of the
conventional two-sorted logic assumed in Simpson [Sim09] §I.2, with its **direct**
theory-level soundness — consuming the nonempty-sort assumption as an explicit
hypothesis — and no completeness claim. -/
structure StandardCalculusRecord where
  id : BridgeCalculusId
  sortAssumption : SortAssumptionTag
  equalityRules : EqualityRulesTag
  sound : ∀ {Γ : Set (SecondOrder.Sentence ℒₒᵣ)} {σ : SecondOrder.Sentence ℒₒᵣ},
    StdLKProvable Γ σ → ∀ M : Struc₂.{0, 0} ℒₒᵣ, M.sets.Nonempty → EqCorrect M →
      (∀ τ ∈ Γ, M ⊧ τ) → M ⊧ σ

/-- **Calculus comparison**, typed: the pinned standard calculus and the Henkin-safe
calculus are independently sound — the record carries both soundness theorems and the
closed relation tag, and **deliberately has no embedding field**: it carries no
embedding and licenses no derivability transfer in either direction. -/
structure CalculusComparisonCertificate where
  standard : BridgeCalculusId
  compared : BridgeCalculusId
  relation : CalculusRelationTag
  standardSound : ∀ {Γ : Set (SecondOrder.Sentence ℒₒᵣ)} {σ : SecondOrder.Sentence ℒₒᵣ},
    StdLKProvable Γ σ → ∀ M : Struc₂.{0, 0} ℒₒᵣ, M.sets.Nonempty → EqCorrect M →
      (∀ τ ∈ Γ, M ⊧ τ) → M ⊧ σ
  comparedSound : ∀ {Γ : Set (SecondOrder.Sentence ℒₒᵣ)} {σ : SecondOrder.Sentence ℒₒᵣ},
    Derivable Γ σ → ∀ M : Struc₂.{0, 0} ℒₒᵣ, (∀ τ ∈ Γ, M ⊧ τ) → M ⊧ σ

/-- **Standard-calculus nonprovability**, structurally keyed to a calculus identifier:
the type says the sentence is unprovable *in the pinned standard calculus*, so the
record cannot render as a generic turnstile claim. -/
structure StandardNonprovabilityCertificate (id : BridgeCalculusId)
    (theory : Set (SecondOrder.Sentence ℒₒᵣ))
    (sentence : SecondOrder.Sentence ℒₒᵣ) where
  unprovable_in_pinned_standard_calculus : ¬ StdLKProvable theory sentence

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

/-- Export 3 — the calculus identity: `Derivable` with `soundness_sentence`; the
standard-calculus comparison is now `recorded` (see `calculusComparisonExport` for the
exact — embedding-free — relation). -/
def bridgeCalculusExport : CalculusRecord where
  id := .henkinSafeV1
  comparison := .recorded
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

/-- Export 6 — the pinned standard calculus identity: `StdLKProvable` with its direct
theory-level soundness `StdLKProvable.soundness`, keyed to `l2VarWitnessLK.v1` with the
nonempty-sort assumption as a closed tag. -/
def stdCalculusExport : StandardCalculusRecord where
  id := .l2VarWitnessLKv1
  sortAssumption := .nonemptySetSort
  equalityRules := .reflAndSubstitution
  sound := fun h M hne heq hΓ => h.soundness M hne heq hΓ

/-- Export 7 — the typed calculus comparison: both calculi independently sound; the
record carries no embedding and licenses no derivability transfer. -/
def calculusComparisonExport : CalculusComparisonCertificate where
  standard := .l2VarWitnessLKv1
  compared := .henkinSafeV1
  relation := .independentDirectSoundness
  standardSound := fun h M hne heq hΓ => h.soundness M hne heq hΓ
  comparedSound := fun h M hΓ => soundness_sentence h M hΓ

/-- Export 8 — the standard-calculus nonprovability: `rca0_not_stdLK_proves_wkl`,
keyed to `l2VarWitnessLK.v1`. -/
theorem wklStandardNonprovabilityExport :
    StandardNonprovabilityCertificate .l2VarWitnessLKv1 Rca0Theory wklSentence :=
  ⟨rca0_not_stdLK_proves_wkl⟩

end RMFoundationBridge
