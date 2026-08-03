# Crypto

`Crypto` is an experimental Lean library for building reusable, machine-checked
cryptographic security proofs. The project aims to provide a small but coherent
foundation for defining cryptographic schemes, security games, oracle access,
semantic PPT-machine interfaces, asymptotic bounds, assumptions, reductions,
and proof patterns.

The library is organized around game-based security proofs, with a growing UC
layer for interactive protocols. Shared computation semantics such as
randomized computations, games, oracles, cost models, and algebraic operations
live in reusable lower layers. Cryptographic primitives, protocols, and
assumptions build on those layers without duplicating the common machinery.
This keeps primitive-specific definitions local while still allowing different
constructions to share the same vocabulary for games, complexity, advantages,
and UC executions.

The current codebase is intentionally minimal. It prioritizes stable boundaries
and clear interfaces over a large catalog of primitives. The symmetric
encryption hierarchy already includes syntax, correctness, one-time
left-or-right security, and a group-based one-time pad with correctness and
perfect one-time security proofs. The asymmetric hierarchy includes ElGamal
syntax and correctness, while DLog and DDH provide the corresponding
game-based problems. Schemes and DL assumption families are cost-annotated
directly and connect to the algebraic program and machine layers without
introducing parallel uncosted structures.

## Build and verification

The repository pins its Lean toolchain in `lean-toolchain`. With `elan` and
Lake available, build the library and all compile-time proof tests with:

```shell
lake build
```

The default targets are `Crypto` and `CryptoTest`. To check them separately,
use `lake build Crypto` or `lake build CryptoTest`. The files under
`CryptoTest/` are theorem-level regression and smoke tests; a successful build
is the test result.

## Organization

The project is intentionally layered. Lower layers contain general semantic
infrastructure; higher layers define cryptographic objects, assumptions,
protocols, and proof organization.

```text
Crypto/
  Basic.lean
  Infrastructure/
    Basic.lean
    Asymptotic/
      SecurityParameter.lean
      Bounds.lean
    Computation/
      Cost/
      Algebra/
      Oracle/
      Distribution.lean
      Randomized.lean
      Program.lean
      Game.lean
    Complexity/
      Machine.lean
      CostBound.lean
      ProgramMachine.lean
    GameBased/
      Advantage.lean
      Indistinguishability.lean
      Search.lean
      Hybrid.lean
      Reduction.lean
    UC/
      Execution.lean
      Protocol.lean
      Layered.lean
    ProofPattern/
  Assumption/
    DL/
  Primitive/
    Encryption/
      AsymmetricEncryption/
      SymmetricEncryption/
  Protocol/
CryptoTest/
  Assumption/
  Infrastructure/
  Primitive/
```

### `Crypto.Infrastructure`

Reusable infrastructure shared by assumptions, primitives, and protocols.
This layer contains asymptotic vocabulary, randomized computations, games,
oracles, cost models, machine models, and generic game-based proof concepts.

### `Crypto.Infrastructure.Asymptotic`

Asymptotic vocabulary with minimal project dependencies.

- `SecPar` is the shared security parameter.
- `IsPolyBounded` and `IsNegligible` define the asymptotic vocabulary used by
  complexity and security definitions.

Files in this layer should not depend on cryptographic primitives,
game-based security definitions, or machine models.

### `Crypto.Infrastructure.Computation`

Reusable semantic infrastructure for cryptographic formalization.

- `Computation.Cost` defines the `Costed` writer computation and `RandCosted`
  randomized paths. Their bind operations add the local costs of sequential
  steps exactly once.
- `Computation.Algebra` separates mathematical structures from explicit
  operation backends, operand-dependent local costs, uniform operation bounds,
  and costed samplers. Backend operations return `Costed` values directly, and
  a `UniformSampler` carries its full `RandCosted` execution distribution, so
  values and costs cannot be paired by unrelated downstream code. Group and
  module cost conventions are explicit named models rather than global
  instances, so selecting an implementation is a local and visible choice.
- `Algebra.Costed` is the small typeclass-based compatibility layer.
  `AdditiveBackend` and `MultiplicativeBackend` remain Nat-facing handler
  constructors, and `AdditiveBackend.ofCostModel` bridges the old operation
  typeclasses. The selected `CostedAlgebra.exec` is the authoritative primitive
  interpreter; `AlgebraLaws` and `OperationBounds` are independent evidence.
- `Program A Input Output` is a typed heterogeneous algebraic program language.
  `runCosted` is its only execution semantics, and ordinary probability
  semantics is defined by erasing the exact path cost. `BoundedProgram` stores
  that same program together with an input-dependent certificate: sequencing
  uses the selected cost monoid, while branches use either an explicit common
  upper bound or a model-provided supremum.
- `Computation.Oracle` defines oracle interfaces, stateful environments, and
  adaptive oracle-program syntax. `CostedOracleEnv` is the implementation
  interface for reductions that must account for work performed inside oracle
  calls; erasing it recovers an ordinary `OracleEnv` with the same value
  semantics.
- `Randomized` packages security-parameter-indexed randomized computations
  with cost information. The generic `CostedT`/`RandCostedT` layer supports
  ordered additive resource models, while `Costed`/`RandCosted` remain the
  backwards-compatible natural-number specializations.
- `Game` packages security experiments as security-parameter-indexed
  distributions.

This layer should remain primitive-agnostic. It is the shared substrate for
security games, reductions, and construction-specific definitions.

### `Crypto.Infrastructure.Complexity`

Semantic complexity notions used by constructions and security games.

- `Machine` defines deterministic, probabilistic, timed, PPT, oracle, and
  oracle PPT machine interfaces.
- `CostBound` connects core costed computations to polynomial bounds.
- `ProgramMachine` constructs timed and PPT machines from statically bounded
  generic programs. An explicit monotone additive `NatMeasure` projects their
  resource costs to the legacy natural-number runtime without changing the
  value distribution.
- Timed machines prove that their runtime bounds cover every explicitly costed
  execution path; PPT machines additionally prove those bounds polynomial.
- Oracle programs record annotated local cost and the exact query trace.
  The legacy `OracleProgram` retains exactly its original unit-cost `query`
  constructor, so runtime still bounds total query count and the
  `PPTOracleMachine` adversary domain is unchanged. Explicit caller-side query
  costs, including zero, exist only in `OracleProgramT`; Nat callers use
  `OracleProgramT natCostModel`.
  Timed oracle machines prove runtime and per-oracle query bounds for every
  structural execution path, and the profiled interpreter is proved to follow
  those paths. An optional `TotalQueryBoundCertificate` can record a dedicated
  or tighter total-query bound for composition without adding a field to the
  existing machine interfaces. The ordinary interpreter still excludes the
  internal implementation cost of its supplied `OracleEnv`. For implemented
  reductions, the generic costed-oracle interpreter preserves the exact
  sequential total cost and separately records local and oracle costs for
  analysis. With an explicit exchange law for regrouping noncommutative costs,
  it derives `localBudget + totalQueryBound • envBudget`; the Nat compatibility
  theorem is `localBudget + totalQueryBound * envBudget`. Polynomial closure
  lemmas discharge the corresponding PPT bound.

This layer may depend on `Crypto.Infrastructure.Asymptotic` and
`Crypto.Infrastructure.Computation`, but should not depend on specific
primitives or assumptions. The current model is an explicit, trusted path-cost
semantics: runtime and query certificates are now connected to the annotated
computation and oracle-program execution, rather than being unrelated metadata.
For `Program` computations, costs are generated by the selected algebra handler
and sampler and accumulated by the interpreter; callers do not attach a total
cost after defining the algorithm. Exact handlers, cost-erased algebra laws,
and operation bounds are separate records. A `BoundedProgram` derives an
input-dependent bound compositionally from the primitive bounds; the machine
constructor statically relates its runtime field to the measured budget. It
does not synthesize a closed-form security-parameter bound independently of the
supplied program family.

The current program language is nevertheless an engineering-level higher-order
syntax: values passed to `pure`, continuation functions, and branch conditions
remain Lean terms. It therefore measures all explicit program primitives but is
not yet a first-order Turing/RAM semantics that prevents hidden host
computation. A concrete interpretation must justify the primitive backend and
sampler costs, and a fully non-bypassable model would additionally replace the
higher-order boundaries with first-order typed syntax.

### `Crypto.Infrastructure.GameBased`

Generic security notions that are not tied to one primitive.

- `Advantage` defines acceptance probability and distinguishing advantage for
  boolean games.
- `Indistinguishability` states negligible distinguishing advantage and
  provides reusable distinguishing and oracle-distinguishing problem templates.
- `Search` defines reusable search-problem security games and hardness.
- `Hybrid` records finite hybrid sequences.
- `Reduction` records transformations between machine families or other
  proof-relevant types.

Primitive-specific games should live under the corresponding primitive; shared
game combinators and proof patterns belong here.

### `Crypto.Infrastructure.UC`

Reusable universal-composability vocabulary for interactive protocols. This
layer currently sits above the computation, complexity, and game-based
infrastructure: UC environments, adversaries, and simulators are first expressed
as semantic oracle machines, with PPT aliases used by computational UC
emulation. The real and ideal executions are packaged as boolean `Game`s whose
indistinguishability is stated with the generic game-based vocabulary.

- `Execution` defines semantic interactive systems, UC experiments, real and
  ideal executions, computational UC emulation, controlled-environment UC
  emulation, perfect UC emulation, and the coercion lemmas from perfect to
  computational emulation.
- `Protocol` defines generic UC protocols as indexed families of interactive
  machines, together with corruption modes and corruption policies.
- `Layered` provides the layered/YOSO MPC template: layered party identifiers,
  trusted and boundary roles, per-layer corruption eligibility, the standard
  local party-step shape, and a generic MPC ideal functionality skeleton.

This layer is still a framework, not a collection of completed protocol
proofs. Concrete UC statements should instantiate these templates with explicit
message syntax, schedulers, ideal functionalities, and simulators.

### `Crypto.Assumption`

Computational assumptions, organized by family.

Discrete logarithm and DDH live directly in `Assumption.DL.DLog` and
`Assumption.DL.DDH`; there are no companion `Costed` submodules. They share a
cyclic-action parameter layer, while the decisional layer adds exactly the
stronger commutative multiplication/action capabilities. Public parameters
carry the exact typed algebra handlers and samplers used by the native
programs, while each family has a native `RandCosted` setup. Search and
distinguishing distributions are obtained only by erasing costs from those
computations.

DLog and DDH separate exact execution from efficiency evidence explicitly.
Their public parameters contain exact algebra backends and samplers, but no
local algebraic bounds. A `ParamEfficiencyCertificate` supplies the backend
bounds used to derive fixed-parameter challenge and sampling bounds. Each
`Family` stores its native costed setup computation; family-level typed
signatures and handlers dispatch setup and the parameter-dependent operations
selected by that result. DLog's complete sample and DDH's complete real and
random samples are `Program`s over those dependent handlers. A family-level
`EfficiencyCertificate` supplies global setup and sampling `CostBound` proofs.
Consequently, both assumptions and exact constructions such as the ElGamal
`scheme` depend on native families but not on either efficiency certificate.
Certificates prove upper bounds on already-derived path costs; they are not a
second source of runtime. These modules state the assumptions; they do not
prove them.

### `Crypto.Primitive`

Cryptographic primitives and their primitive-specific syntax, correctness, and
security definitions.

The current encryption hierarchy contains:

- `Primitive.Encryption.AsymmetricEncryption.Syntax`
- `Primitive.Encryption.AsymmetricEncryption.UC`
- `Primitive.Encryption.AsymmetricEncryption.Properties`
- `Primitive.Encryption.SymmetricEncryption.Syntax`
- `Primitive.Encryption.SymmetricEncryption.UC`
- `Primitive.Encryption.SymmetricEncryption.Properties`
- `Primitive.Encryption.SymmetricEncryption.Instantiations`

The main symmetric-encryption interface is
`Crypto.Primitive.Encryption.SymmetricEncryption.Scheme SecPar Param Key Message Ciphertext`.
It is the only scheme interface: `setup`, `keygen`, and `encrypt` return
`RandCosted`, while `decrypt` returns `Costed`. `Key`, `Message`, and
`Ciphertext` are indexed by the sampled public parameters. Correctness and
security notions observe ordinary values through `setupDist`, `keygenDist`,
`encryptDist`, and `decryptValue`; they do not convert to a second scheme
structure. `OneTimeSecure` is the PPT notion, while `PerfectOneTimeSecure`
quantifies over unbounded oracle machines and requires exact zero advantage.

The main asymmetric-encryption interface is
`Crypto.Primitive.Encryption.AsymmetricEncryption.Scheme SecPar Param PublicKey SecretKey Message Ciphertext`.
It follows the same cost-annotated design for public parameters, key
generation, public-key encryption, and secret-key decryption. Its IND-CPA
definition is expressed as an `Infrastructure.GameBased.OracleDistinguishing`
problem over the observed value distributions.

The current instantiations include a group-based one-time pad and ElGamal. The
one-time pad exposes the finite nonempty additive group chosen for the security
parameter, encrypts by addition, and decrypts by negation followed by addition.
The library proves both correctness and perfect one-time security for this
construction, and derives PPT one-time security from the perfect theorem.
ElGamal has a correctness proof under the scalar-action laws carried by its
public parameters; an IND-CPA-from-DDH reduction remains future work.

Both construction-level `scheme` definitions directly inhabit the costed
interface. Their setup/sampling and algebraic programs obtain path costs from
explicit parameter-local backends and have value-distribution equations used
by correctness and security. OTP uses typed key-generation, encryption, and
decryption programs without a dummy scalar capability. ElGamal reuses the DDH
family setup program and has typed key-generation, encryption, and decryption
programs; its bounded wrappers pair those same programs with proofs instead of
copying their syntax. In particular, the exact DDH-based ElGamal scheme depends
only on `DDH.Family`, not on a DDH efficiency certificate. Separate local and
global certificates can supply verified uniform bounds when constructing timed
or PPT machines.

The primitive-level `UC.lean` files are reserved for primitive-specific UC
formulations, such as ideal functionalities or emulation statements for the
corresponding primitive. The reusable UC execution and protocol machinery
belongs in `Crypto.Infrastructure.UC`; primitive-level files should import and
instantiate that machinery only when they introduce concrete UC definitions.

### `Crypto.Protocol`

Protocol-level definitions that compose primitives or model interactive
protocols. This namespace is currently reserved for future protocol
formalizations. Protocol code may depend on primitives, assumptions,
game-based security, complexity, and computation infrastructure as needed.

### `Crypto.Infrastructure.ProofPattern`

Reusable proof infrastructure and proof organization. This namespace is
currently reserved for shared proof patterns, automation, and library-level
proof utilities that do not naturally belong to one primitive or assumption.

## Import Policy

`Basic.lean` files are aggregation modules. Import them when a caller wants a
whole layer; otherwise prefer importing the narrow file that provides the needed
definition.

The intended dependency direction is:

```text
Infrastructure.Asymptotic
  -> Infrastructure.Computation
  -> Infrastructure.Complexity / Infrastructure.GameBased
  -> Infrastructure.UC
  -> Assumption / Primitive
  -> Protocol / Infrastructure.ProofPattern
```

This is a guideline rather than a total order. For example,
`Infrastructure.GameBased` and `Infrastructure.Complexity` both depend on
`Infrastructure.Computation`, `Infrastructure.UC` uses both machine and
game-based vocabulary, and primitive-specific security games may depend on both
game-based and complexity infrastructure. Avoid dependencies from lower layers
back into higher layers.

## Adding New Material

- Put infrastructure code under `Infrastructure`.
- Put security-parameter and asymptotic vocabulary in `Infrastructure.Asymptotic`.
- Put reusable game, oracle, computation, cost, or algebra semantics in
  `Infrastructure.Computation`.
- Put machine models, including PPT, oracle, and oracle PPT machines, in
  `Infrastructure.Complexity`.
- Put generic advantage, indistinguishability, hybrid, and reduction notions in
  `Infrastructure.GameBased`.
- Put reusable UC experiment, execution, protocol, corruption, and layered MPC
  templates in `Infrastructure.UC`.
- Put assumption families in `Assumption/<family>/`.
- Put primitive-specific syntax, correctness, and security games in
  `Primitive/<kind>/<primitive>/`, with `Syntax.lean` and `UC.lean` as direct
  files and `Properties/` and `Instantiations/` as subdirectories.
- Put composed or interactive protocols in `Protocol`.
- Put shared proof utilities in `Infrastructure.ProofPattern`.

When adding polymorphic Lean declarations, use descriptive universe names such
as `uIn`, `uOut`, `uQuery`, `uResponse`, `uValue`, `uMapped`, `uScalar`,
`uModule`, and `uGroup`, rather than bare `u`, `v`, or `w`.

## Naming Conventions

Use a fixed suffix vocabulary for game-based declarations.

- Oracle specifications use lower-camel-case property names with the suffix
  `OracleSpec`, for example `oneTimeOracleSpec` and `indCPAOracleSpec`.
- Security games use lower-camel-case property names with the suffix
  `SecurityGame`, for example `oneTimeSecurityGame` and
  `indCPASecurityGame`. Generic infrastructure combinators use
  `securityGame`, `leftSecurityGame`, and `rightSecurityGame`.
- Advantages use upper-camel-case property names with the suffix `Advantage`,
  for example `OneTimeAdvantage` and `INDCPAAdvantage`.
- Reusable game-based problem instances use lower-camel-case property names
  with the suffix `Problem`, for example `oneTimeProblem`, `indCPAProblem`,
  `dLogProblem`, and `ddhProblem`.
- Security predicates should use the established cryptographic notion name,
  such as `OneTimeSecure`, `INDCPASecure`, or `Assumption` inside a specific
  assumption namespace.

The generic type `Crypto.Infrastructure.Computation.Game` remains named `Game`;
the `SecurityGame` suffix is for concrete or template security experiments
that instantiate a game-based notion.

## Status

The library is early-stage. The current hierarchy is sound as a working
architecture, but several namespaces are intentionally sparse. Ordinary,
dependent-output, and oracle machines now share the explicit path-cost model;
oracle runtime and query bounds are tied to structural executions and to the
profiled interpreter. OTP, ElGamal, DLog, and DDH now exercise the
typed-algebra-to-costed-computation path, with efficiency bounds treated as
certificates over those exact executions; all four use the same typed
`Program` layer. The next useful refinements are to choose a
first-order operational machine model when host-independent PPT soundness is
required, complete reusable reduction and hybrid infrastructure, prove ElGamal
IND-CPA security from DDH, and move common proof patterns into
`Crypto.Infrastructure.GameBased` or `Crypto.Infrastructure.ProofPattern` once
they repeat across multiple constructions.
