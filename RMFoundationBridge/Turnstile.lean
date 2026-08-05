/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import RMFoundationBridge.HenkinCalculus
import RMFoundationBridge.WklRegression

/-!
# F3, second layer: the negative turnstile

Soundness composed with the semantic countermodel: the ŴKL sentence is not derivable
from `Rca0Theory` in the Henkin-safe calculus. The witness structure is
`recursivePart.toFoundation` — context adequacy at REC supplies the axioms, the
unconditional statement adapter composed with the Kleene tree refutes the conclusion.

**Scope**: this is nonderivability in the bridge's Henkin-safe calculus, from the
semantic `Rca0Theory` axiom set, over the canonical coding — with **no completeness
claim**: derivability is not asserted to exhaust semantic consequence, and no positive
derivability facts are claimed at all.
-/

namespace RMFoundationBridge

open LO LO.FirstOrder LO.SecondOrder
open ReverseMathlib.Omega

/-- **The negative turnstile**: `Rca0Theory ⊬ ŴKL` in the Henkin-safe calculus —
soundness instantiated at the REC structure, refuted by the Kleene tree through the
unconditional adapter. -/
theorem rca0_not_derives_wkl : ¬ Derivable Rca0Theory wklSentence := fun h =>
  recursivePart_not_models_wklSentence
    (soundness_sentence h recursivePart.toFoundation
      (fun _ hτ => recursivePart_models_rca0 hτ))

end RMFoundationBridge
