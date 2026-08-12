# Backend-evidence interchange: `rmlib-bridge-evidence/2`

The versioned canonical JSON contract by which reverse-mathlib ingests this bridge's
export surface as **backend evidence** — a fourth evidence grade, stored apart from
certified facts, imported reductions, and reported corpus findings. The certified
scoreboard is structurally out of reach. Schema review precedes implementation; the
fingerprint encoder is spiked with regression fixtures before either the emitter or the
importer lands.

## Envelope

```json
{ "schema": "rmlib-bridge-evidence/2",
  "fingerprintSchema": "lean-interface-expr/1",
  "source": {
    "repository": "cameronfreer/reverse-mathlib-foundation",
    "revision": "<40-hex bridge commit>",
    "toolchain": "leanprover/lean4:v4.32.2",
    "dependencies": {
      "reverse-mathlib": "<40-hex checked revision>",
      "Foundation":      "<40-hex>",
      "mathlib":         "<40-hex>" } },
  "namespace": "rmFoundationBridge",
  "checking": {
    "mechanism": "leanKernel",
    "allowedAxioms": ["Classical.choice", "Quot.sound", "propext"],
    "audit": "lake env lean scripts/Audit.lean" },
  "fingerprints": [
    { "name": "<fully qualified reverse-mathlib declaration>",
      "canonicalInterface": "<lean-interface-expr/1 payload>" }, … ],
  "records": [ … ] }
```

The `dependencies.reverse-mathlib` revision is the revision the bridge **checked**
against, truthfully — later reverse-mathlib commits remain compatible exactly when the
interface fingerprints still match (see *Trust*).

**Revision provenance**: the emitter takes only the bridge export revision as explicit
input; the three dependency revisions are derived from `lake-manifest.json` and the
toolchain from the workspace's `lean-toolchain` file. Every derived revision is
validated as full lowercase 40-hex.

All **closed status, direction, calculus, and comparison tags** in `records` are
produced by the emitter **pattern-matching the typed export-surface constructors** into
explicit schema tags (`.forward ↦ "forward"`, `.realizationOnly ↦ "realizationOnly"`,
`.unconditional ↦ "unconditional"`, `.henkinSafeV1 ↦ "henkinSafeV1"`,
`.pending ↦ "pending"`) — never `Repr` output, never hand-written strings. Record ids,
theorem names, and external keys necessarily come from the explicit emitter manifest;
they are not recoverable from the typed records alone.

## Record kinds

Five kinds, one record per typed export. (Schema `/1` had four kinds and treated the
semantic countermodels as deliberately not records; `/1` is intentionally retired — the
sole consumer pins exact artifact revisions, and no `/1` artifact remains referenced.)
Every record carries `"status": "backendChecked"` as emitted; the importer
may downgrade (see *Trust*).

```json
{ "kind": "contextRealization", "id": "realization.rca0.turingIdeal",
  "status": "backendChecked",
  "export": "RMFoundationBridge.rca0RealizationExport",
  "theorem": "RMFoundationBridge.forward_adequacy",
  "theory": "RMFoundationBridge.Rca0Theory",
  "contextKey": "rca0/turingIdealOmega",
  "context": "ReverseMathlib.Omega.IsTuringIdeal",
  "direction": "forward", "realizationStatus": "realizationOnly" }

{ "kind": "statementAdapter", "id": "adapter.wkl.binaryTree.foundationL2",
  "status": "backendChecked",
  "export": "RMFoundationBridge.wklAdapterExport",
  "theorem": "RMFoundationBridge.models_wklSentence_iff",
  "sentence": "RMFoundationBridge.wklSentence",
  "capability": "ReverseMathlib.Omega.WeakKonigAt",
  "variantKey": "wkl/binaryTree.turingIdealOmega",
  "adapterStatus": "unconditional" }
// likewise, following the family/presentation convention (presentation-explicit,
// never pretending the bridge sentence is itself the alias target):
//   adapter.efilc.explicitSequential.enumeratedFibers.foundationL2
//     with variantKey "efilc/explicitSequential.enumeratedFibers.turingIdealOmega"
//   adapter.countableHall.oneSidedInjective.enumeratedCandidates.foundationL2
//     with variantKey
//     "countableHall/oneSidedInjective.enumeratedCandidates.turingIdealOmega"

{ "kind": "calculusIdentity", "id": "calculus.henkinSafeV1",
  "status": "backendChecked",
  "export": "RMFoundationBridge.bridgeCalculusExport",
  "calculusId": "henkinSafeV1",
  "derivability": "RMFoundationBridge.Derivable",
  "soundness": "RMFoundationBridge.soundness_sentence",
  "standardComparison": "pending" }

{ "kind": "calculusNonderivability", "id": "nonderivability.rca0.wkl.henkinSafeV1",
  "status": "backendChecked",
  "export": "RMFoundationBridge.wklNonderivabilityExport",
  "theorem": "RMFoundationBridge.rca0_not_derives_wkl",
  "calculusRecord": "calculus.henkinSafeV1",
  "sentenceAdapter": "adapter.wkl.binaryTree.foundationL2",
  "theory": "RMFoundationBridge.Rca0Theory",
  "sentence": "RMFoundationBridge.wklSentence" }
```

**Typed record references**: `calculusRecord` and `sentenceAdapter` are record ids in
this file, not correlate strings. The importer verifies referential integrity: the
referenced calculus record's `calculusId` and the referenced adapter's `sentence` must
agree with the nonderivability record's own view of them.

## Crosswalk semantics

Kinds resolve to **different** local object kinds, each through a registered
`exactAlias` in the `rmFoundationBridge` namespace:

- `contextRealization.contextKey` `rca0/turingIdealOmega` → the registered
  **SemanticContext** `rca0.turingIdealOmega` (requires extending `CatalogObjectRef`
  with a `semanticContext` kind on the reverse-mathlib side, or a backend-specific
  context crosswalk);
- `statementAdapter.variantKey` → the registered **StatementVariant** for the exact
  Turing-ideal presentation (e.g. `wkl/binaryTree.turingIdealOmega` → `WeakKonigAt`'s
  exact Turing-ideal variant). The bridge-side `sentence` is **never** an alias of that
  variant: the adapter theorem exists precisely because the L₂ syntax and the
  model-facing capability are distinct artifacts;
- calculus records are **bridge-local** and carry no catalog alias at all.

After resolution the importer verifies the semantic anchors by exact declaration
identity: the resolved variant's registered `interface` must be exactly the record's
declared `capability`, and the resolved context's `contextDecl` must be exactly the
record's declared `context` predicate.
Backend records may *reference* contexts and variants; they are simply *stored* outside
those families.

## Fingerprints: `lean-interface-expr/1`

**Roots, per record, after crosswalk resolution** (so coverage is anchored in what the
records actually mean locally):

- context realization: the resolved `SemanticContextEntry.contextDecl`;
- statement adapter: the resolved `StatementVariantEntry.interface`;
- calculus nonderivability: the roots of its referenced adapter;
- calculus identity: no reverse-mathlib root.

**Closure** — the recursive semantic-interface closure from the roots:

- always include a declaration's **type**;
- include **bodies** of definitions, abbreviations, and **opaque definitions** (an
  owned opaque can carry semantic meaning);
- include **constructor types** of inductives and structures (constructors are
  attributed to their inductive; a recursor enqueues **every** inductive of its
  possibly-mutual group — never silently only the first);
- recursively follow **reverse-mathlib-owned** dependencies of the included
  components;
- **never** include theorem proof bodies or other proof-only dependencies —
  theorems contribute their statements only.

Non-reverse-mathlib constants (mathlib, core) contribute their fully qualified *names*
inside payloads but are not expanded; their meaning is pinned by the `mathlib` and
toolchain revisions instead (see *Trust*).

**Encoding** — `Expr` constructors encoded directly; no pretty-printing, no
`toString`:

- `mdata` stripped (encode the body); binder **names ignored**, binder info kept;
- universe parameters normalized **by position**; level expressions encoded
  structurally (`0`, `s _`, `max _ _`, `imax _ _`, positional params);
- names encoded component-wise with explicit escaping (`"` and `\` backslash-escaped;
  numeric components tagged); literals encoded explicitly (decimal naturals, escaped
  strings);
- free variables and metavariables are hard errors (only closed declarations are
  encoded);
- per-declaration payload: kind tag, universe-parameter count, then the included
  components in fixed order.

**Comparison**: the importer recomputes payloads from its own elaborated environment
and requires **exact equality of the covered-name set and of every payload** — an
under-covered manifest is rejected, not partially accepted. The canonical payloads are
carried verbatim in the JSON (`canonicalInterface`); a cryptographic digest is an
optional future display convenience, not the comparand.

**Pinned regression fixtures** (`scripts/FingerprintSpike.lean`; must stay green
before ingestion is wired):

1. checked revision vs. a docs-only later revision: equal;
2. a semantic definition-body change: mismatch;
3. a theorem proof-body change: still equal;
4. a metadata or binder-name-only change: still equal;
5. an **opaque body change**: mismatch;
6. a **mutual recursor**: covers every inductive of its group;
7. a missing or extra covered declaration: hard failure.

## Trust and fail-closed discipline

- `backendChecked` requires: repository, 40-hex bridge revision, all three dependency
  revisions, toolchain, structured `checking` block, per-record theorem name, and a
  **validating** fingerprint block.
- Missing theorem/checking trust fields → ingested as `reported`, downgrade reason
  displayed.
- **Lean or mathlib pin mismatch** with the importing workspace → downgraded to
  `reported` with reason (the closure deliberately excludes mathlib bodies, so
  `backendChecked` is not available across a toolchain gap; a future upgrade does not
  hard-fail the repository).
- **reverse-mathlib revision drift is allowed** while the covered-name set and all
  interface payloads match exactly.
- Hard errors, never downgrades: unknown schema or fingerprint-schema version,
  unregistered namespace, unresolvable or wrong-kind alias, failed semantic-anchor
  verification, malformed or mismatched or under-covering fingerprints, broken record
  references, unknown kind/status tags, duplicate ids, malformed JSON.

## Rendering discipline

- Backend evidence renders as **its own section** initially. No legend arrow and no
  projection into the existing concept-strength graph until a separate backend-evidence
  graph with typed node and edge meanings is designed.
- A `realizationOnly` record licenses per-ideal ω-model readings only; renderers must
  never present positive ω-facts as unrestricted semantic RCA₀ claims.
- The nonderivability record renders solely as
  `Rca0Theory ⊬ wklSentence in henkinSafeV1 (standard-calculus comparison pending)`,
  generated from the typed `calculusId` and `standardComparison` fields — the
  qualifier cannot be dropped without changing the data.


### `semanticCountermodel`

The all-model semantic nonconsequence: the theory does not semantically imply
the sentence over the general `Struc₂` class. One record:
`countermodel.rca0.wkl.allModels`.

- `export`, `theorem` — the typed export record and the named theorem
  (`rca0_not_semantically_implies_wkl`).
- `contextRealization`, `sentenceAdapter` — typed references, **identity checks
  only**: the referenced realization record must name exactly this record's
  `theory`, and the referenced adapter exactly this record's `sentence`.
  Neither reference licenses an all-model adapter to any local capability —
  the adapters characterize satisfaction over ω-structures only.
- `theory`, `sentence` — the exact Foundation-side identities.
- `scope` — closed tag, `allModels`.
- `modelClass` — closed tag, `foundationStruc2General`: Foundation's `Struc₂`
  (general/Henkin-style second-order structures at universe `{0, 0}`), the
  standard model class for subsystems of Z₂. Explanatory prose is generated at
  render time, never stored.
- `witnessProvenance`/`witnessBase` — provenance, not scope: the countermodel
  witness is the ω-structure over `ReverseMathlib.Omega.recursivePart`; an
  ω-countermodel is in particular an L₂ countermodel.
