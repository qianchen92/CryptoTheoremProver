# Project Conventions

## Lean Module Names

- Prefer domain-specific top-level names over broad containers. Use names such
  as `Assumption`, `Primitive`, and `Protocol` for first-level cryptographic
  domains.
- Put reusable infrastructure under `Crypto.Infrastructure`, using submodules
  such as `Asymptotic`, `Computation`, `Complexity`, `GameBased`, and
  `UC`, and `ProofPattern` when they describe the actual role of the
  declarations.
- Avoid adding new broad namespaces such as `Foundation`, `Core`, `Security`,
  or `Proof` unless the module has a precisely documented scope that cannot be
  expressed with a narrower name.
- Aggregation modules should be named `Basic.lean`; implementation modules
  should describe the concepts they export, such as `Randomized`, `Oracle`, or
  `Advantage`.

## Library Layer Boundaries

- Keep reusable infrastructure, assumptions, abstract primitive/protocol
  syntax, generic security definitions, and generic properties in `Crypto`.
- Put the trusted first-order language, interpreter, validation, bounds,
  Builder surface, and reusable native-algebra bridges in the separate
  `CryptoFirstOrder` library. It contains no construction algorithms,
  assembled schemes, security definitions, complexity certificates, or
  concrete backend choices.
- `CryptoFirstOrder.Core` aggregates only `Type`, `Signature`, `Algebra`,
  `Syntax`, `Builder`, `Semantics`, `Execution`, `Operation`, `Validation`, and
  `Bounds`. Core modules may depend only on lower `Crypto` cost/probability
  infrastructure. Adapter modules may additionally depend on the abstract
  algebra or assumption definition they adapt.
- Put parameterized algorithms that construct abstract primitives or protocols
  in the separate `CryptoConstruction` library. It may depend on `Crypto` and
  `CryptoFirstOrder` but must not depend on a concrete backend instantiation.
- Within each named construction, keep parameter and algebra definitions in
  `Construction.lean`, executable algorithm `Program`s and their assembled
  abstract object in `Scheme.lean`, and budgets, bounded/timed wrappers, exact
  cost results, and efficiency certificates in `Complexity.lean`.
- `Scheme.lean` must not import `Complexity.lean`; complexity evidence depends
  on the algorithm, never the reverse.
- Put cost-erasure and value-distribution theorems in
  `Properties/Semantics.lean`. Correctness and security properties should
  depend on this semantic layer, not on `Complexity.lean`.
- Reserve a future `CryptoInstantiation` library for fixed representations,
  implementation backends, and their instance-specific cost certificates.
- The only permitted direct `Crypto -> CryptoFirstOrder` import is
  `Crypto.Infrastructure.Complexity.Operational -> CryptoFirstOrder.Core`.
  This preserves the closed internally validated `ValidCode` constructor;
  it must never import `CryptoFirstOrder.Basic` or an adapter subtree.
- `CryptoFirstOrder` must not import `CryptoConstruction` or
  `CryptoInstantiation`; `CryptoConstruction` must not import
  `CryptoInstantiation`.
- Each library's `Basic.lean` aggregates only that library. Import
  `CryptoFirstOrder.Core` for only the trusted language,
  `CryptoFirstOrder.Basic` for all adapters, and
  `CryptoConstruction.Basic` explicitly for parameterized constructions.

## Lean Universe Names

- Use meaningful universe names that describe the role of the corresponding type parameter.
- Avoid bare `u`, `v`, or `w` in project code except for very small local experiments that are not committed.
- Reuse established role names where applicable:
  - `uIn`, `uOut` for input/output types.
  - `uQuery`, `uResponse` for oracle query/response types.
  - `uValue`, `uMapped` for value and mapped-value types.
  - `uScalar`, `uModule`, `uGroup` for algebraic scalar/module/group types.
- When adding a new polymorphic definition, choose universe names from the domain vocabulary of that definition and keep them consistent across the declaration, namespace variables, and related theorems.

## Lean Declaration Names

- Use fixed suffixes for game-based declarations.
- Oracle specifications use lower-camel-case property names ending in
  `OracleSpec`, such as `oneTimeOracleSpec` and `indCPAOracleSpec`.
- Security games use lower-camel-case property names ending in `SecurityGame`,
  such as `oneTimeSecurityGame` and `indCPASecurityGame`. Generic infrastructure
  combinators use `securityGame`, `leftSecurityGame`, and `rightSecurityGame`.
- Advantages use upper-camel-case property names ending in `Advantage`, such as
  `OneTimeAdvantage` and `INDCPAAdvantage`.
- Reusable problem instances use lower-camel-case property names ending in
  `Problem`, such as `oneTimeProblem`, `indCPAProblem`, `dLogProblem`, and
  `ddhProblem`.
- Security predicates should use the established cryptographic notion name,
  such as `OneTimeSecure`, `INDCPASecure`, or `Assumption` inside a specific
  assumption namespace.
- Keep the generic computation type named `Game`; reserve the `SecurityGame`
  suffix for concrete or template game-based security experiments.

## Lean Variables and Namespace Qualification

- Put parameters repeated by several declarations in the nearest namespace- or
  section-level `variable` block. This includes cost models, public parameters,
  construction families, measures, certificates, and genuinely polymorphic
  input or output types.
- Use a shared variable only for a real parameter. Never turn a
  construction-fixed identity into a free variable merely to shorten a type.
  For example, keep the ElGamal public-key role definitionally equal to the
  group carrier selected by its public parameter.
- Preserve public binder order, binder explicitness, universe roles,
  declaration types, and theorem behavior during cleanup. When one declaration
  needs different binder explicitness, delimit that case with a small
  `section` or a separate variable declaration instead of changing the whole
  namespace.
- Keep import paths fully qualified.
- Avoid ordinary broad `open` declarations in `CryptoConstruction`, especially
  in `Scheme.lean`. Remove unused ordinary opens. Prefer qualification at the
  declaration boundary and narrow `open scoped` declarations for DSL notation
  or scoped algebra/parameter instances.
- `variable` declarations do not perform namespace resolution. A proof-heavy
  file may retain a narrow ordinary `open` when repeated qualification would
  materially obscure the proof. Do not introduce a private namespace alias
  merely to relocate the same verbosity.
- Where cost-layer names recur in a primitive or proof file, narrowly open
  `Crypto.Infrastructure.Computation.Cost` and use `CostModel`, `RandCosted`,
  and `NatMeasure`. In a construction `Scheme.lean`, prefer one fully qualified
  `CostModel` in the shared variable block rather than a broad ordinary open or
  repeated fully qualified binders.

## Lean Abbreviations and Role Types

- Do not create one-use chains of `private abbrev` declarations merely to
  shorten a file.
- Use `abbrev` when it names a stable semantic/domain role or reusable
  interface and definitional transparency is intended.
- Put construction-specific object-language role abbreviations in the
  authoritative `Construction.Language` namespace. Use role names such as
  `keyTy`, `publicKeyTy`, `secretKeyTy`, `messageTy`, and `ciphertextTy`, even
  when multiple roles reduce to the same carrier type.
- Keep public-key and secret-key roles distinct. ElGamal key generation may
  structurally return a pair, but its interface must list `publicKeyTy` and
  `secretKeyTy` separately; do not introduce a construction-level `keyPairTy`.
- In ElGamal algorithm and proof-local variables, write the public key as `pk`,
  the secret key as `sk`, and fresh encryption randomness as `r`. Keep semantic
  interface names such as `PublicKey`, `SecretKey`, `publicKeyTy`, and
  `secretKeyTy` unabbreviated.
- Put reusable program-arity encoding in `CryptoFirstOrder`.
  New construction declarations use `CryptoFirstOrder.Program.NAry` with a
  static list of logical input roles, and `CryptoFirstOrder.Program.NAryPair`
  for a result containing two distinct roles. Treat `Nullary`, `Unary`, `Binary`, `Ternary`,
  and `NullaryPair` as compatibility abbreviations rather than the primary
  construction style.
- Use `Ty.tuple` as the sole compilation from a static input list to the trusted
  structural input. Its encoding is `unit` for `[]`, the type itself for a
  singleton, and a right-associated product for a longer list. Do not introduce
  a second n-ary AST or runtime-variable arity for this purpose.

## First-Order Construction Surface

- Activate construction syntax with
  `open scoped CryptoFirstOrder`.
- Define straight-line construction algorithms with
  `first_order input do ...`. The Builder layer must lower immediately to the
  trusted `CryptoFirstOrder.Code`; do not add a second algorithm AST or
  semantics.
- Match an `NAry` input list with Builder typed-context syntax. Use
  `first_order () do` for an empty list, `first_order input do` or
  `first_order (input) do` for a singleton, and
  `first_order (x, y, z) do` for multiple inputs. Input names must compile to
  projections from the one `Ty.tuple` value rather than becoming a second core
  context representation.
- In new construction code, prefer Unicode smart-operation forms: `x • y`,
  `x + y`, `x - y`, `-x`, and `x * y`. The named forms `smul`, `add`, `sub`,
  `neg`, and `mul` remain accepted only as compatibility forms.
- Permit nested smart operations such as `message + (r • pk)` at the Builder
  surface. Compile them left to right into fresh internal bindings before
  producing `Code`; do not add effectful `Expr` constructors, a second AST, or
  a duplicated algorithm in `Complexity.lean`.
- Keep fixed-generator representation notation in the DDH adapter, not in the
  generic Builder. Open the separate `DDHGroup` scope and write `⦋x⦌` for
  `x • pp.generator`; it must lower to the existing scalar-action call and add
  no core operation. In Lean's Unicode input mode, type `\s[]` or `\simplex`
  to insert the delimiter pair, and open this scope narrowly.
- Use bound names, `unit`, booleans, pairs, `value(...)`, `fst(...)`, and
  `snd(...)` in Builder expressions. Reserve
  `call operation with arguments` for primitives with no smart surface form.
- Do not expose `Signature.inject`, `.inl`, `.inr`, or `ULift` manipulation in
  a `Scheme.lean` algorithm body. Put reusable typed signature embeddings and
  lift/projection boundaries in `CryptoFirstOrder`; let smart constructors lower
  to `Code.call`; and use `Builder.runCosted`, `ValueRepresentation`, and
  `ValueProjection` at the host-facing boundary.
- Use the scoped notation `A ×ₜ B` for genuine object-language product types.
  Keep `.prod` as the trusted structural representation in generic core code.
  Do not expose a product solely because a program has several logical inputs;
  list those roles in `Program.NAry` instead.

## First-Order Sampling

- Write general sampling as `sample sampleTy sampler`. Both arguments are
  required: `sampleTy` is the sampled object-language type, and
  `sampler : Sampler S sampleTy` selects the sampler operation or distribution
  descriptor embedded in the current signature.
- Write uniform sampling as `unifSamp sampleTy`. Uniformity fixes the
  distribution, so the surface form has only the explicit object-language type
  and obtains its operation through `Signature.Embedding`.
- Keep sampler descriptors inside the typed signature. Do not embed arbitrary
  host `PMF` callbacks into first-order program syntax. The exact algebra and
  its laws supply the operation's distributional semantics.

## Construction File Style

- In `CryptoFirstOrder`, define reusable object-language bases,
  interpretations, signatures, typed operation embeddings, host-value
  lift/projection boundaries, exact handler bridges, and bridge-specific
  semantic lemmas. Do not put construction algorithms or certificates there.
- In `Construction.lean`, define construction-specific mathematical parameters
  and the authoritative exact algebra. Its `Language` namespace should reuse a
  `CryptoFirstOrder` adapter and add only construction-specific semantic role
  names and bindings. Add a reusable adapter instead of copying base,
  interpretation, signature, embedding, or handler wiring into a construction.
- In `Scheme.lean`, define each executable algorithm exactly once with the
  first-order Builder surface and assemble the abstract primitive or protocol
  from those programs. Keep the file free of hand-written signature injection,
  explicit universe lifting, cost proofs, and imports of `Complexity.lean`.
- In `Complexity.lean`, prove budgets, bounds, exact costs, timed wrappers, and
  efficiency certificates for the already compiled first-order program,
  normally its existing `.body`. Never duplicate or restate an algorithm there.
- In `Properties/Semantics.lean`, prove cost erasure and value-distribution
  theorems for the same program. Correctness and security properties depend on
  this semantic layer rather than on complexity evidence.
- Pass host-facing scheme values through the shared first-order representation
  boundary. Do not add an alternate execution path merely to avoid
  `ValueRepresentation` or `ValueProjection`.

## Verification of Style Refactors

- Treat source-style cleanup as an API-preserving refactor unless the task
  explicitly requests an API change.
- Review the diff for changed binders, declaration types, namespace exposure,
  and duplicated algorithms.
- Build the smallest affected targets first. Run the full `lake build` whenever
  the change crosses an interface or library boundary.
- Require `git diff --check` to pass, and do not introduce `sorry` or `admit` in
  committed project code.
