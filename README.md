# Crypto

`Crypto` is an experimental Lean library for building reusable, machine-checked
cryptographic security proofs. The project aims to provide a small but coherent
foundation for defining cryptographic schemes, security games, oracle access,
exact cost semantics, certificate-backed PPT-machine interfaces, asymptotic
bounds, assumptions, and typed UC executions.

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

The default targets are `Crypto`, `CryptoFirstOrder`, `CryptoConstruction`, and
`CryptoTest`. To check the layers separately, use `lake build Crypto`,
`lake build CryptoFirstOrder`, `lake build CryptoConstruction`, or
`lake build CryptoTest`. The files under `CryptoTest/` are theorem-level
regression and smoke tests; a successful build is the test result.

## Organization

The project is intentionally layered. Lower layers contain general semantic
infrastructure; higher layers define cryptographic objects, assumptions,
protocols, and proof organization.

```text
Crypto/
  Basic.lean
  Infrastructure/
    Basic.lean
    SecurityParameter.lean
    Probability/
      Uniform.lean
      Basic.lean
    Asymptotic/
      Bounds.lean
      Basic.lean
    Computation/
      Cost/          # Model -> Writer -> Randomized -> PathBound
                     # Model -> Measure; PathBound + Measure -> Projection
      Algebra/       # Signature -> Handler -> Laws / Bounds -> Operation
      Program/       # Syntax -> Semantics -> Execution / Bounds
      Oracle/        # Spec -> Trace -> Program -> Handler -> Interpreter
                     #      -> Bounds -> Composition
      Randomized.lean
      Game.lean
      Basic.lean
    Complexity/
      CostBound.lean
      Machine.lean
      ProgramMachine.lean
      OracleImplementation.lean
      OracleMachine.lean
      Basic.lean
    GameBased/
      Advantage.lean
      Indistinguishability.lean
      Distinguishing.lean
      OracleDistinguishing.lean
      Search.lean
      Hybrid.lean
      Basic.lean
    UC/
      Session.lean
      Port.lean
      Message.lean
      ITM.lean
      Corruption.lean
      Configuration.lean
      Kernel.lean
      Complexity.lean
      Protocol.lean
      Functionality.lean
      Composition.lean
      Execution.lean
      Security.lean
      Context.lean
      Layered.lean
      Basic.lean
  Assumption/
    DL/
  Primitive/
    Encryption/
      AsymmetricEncryption/
        Syntax.lean
        UC.lean
        Properties/
      SymmetricEncryption/
        Syntax.lean
        UC.lean
        Properties/
CryptoFirstOrder/
  Basic.lean
  Core.lean
  Type.lean
  Signature.lean
  Algebra.lean
  Syntax.lean
  Builder.lean
  Semantics.lean
  Execution.lean
  Operation.lean
  Validation.lean
  Bounds.lean
  Algebra/
    AdditiveGroup.lean
    ScalarAction.lean
  Assumption/
    DL/
      DDH.lean
CryptoConstruction/
  Basic.lean
  Primitive/
    Encryption/
      AsymmetricEncryption/
        ElGamal/
      SymmetricEncryption/
        OneTimePad/
CryptoTest/
  FirstOrder.lean
  Assumption/
  Infrastructure/
  Primitive/
```

### `Crypto.Infrastructure`

Reusable infrastructure shared by assumptions, primitives, and protocols.
This layer contains asymptotic vocabulary, randomized computations, games,
oracles, cost models, machine models, and generic game-based proof concepts.

### `Crypto.Infrastructure.SecurityParameter`

`Crypto.SecPar` is defined at the root of Infrastructure. Computation, oracle,
UC-session, and asymptotic modules may depend on it directly; none must import
the asymptotic layer merely to name a security parameter.

### `Crypto.Infrastructure.Probability`

Probability constructions that do not depend on costs, machines, or
asymptotics live in an independent root layer. `Uniform.uniformPMF` is the
current reusable construction. Algebra laws and cryptographic constructions
may use this layer without pulling in a cost or complexity API.

### `Crypto.Infrastructure.Asymptotic`

Asymptotic vocabulary depending only on the root security parameter.

- `IsPolyBounded` and `IsNegligible` define the asymptotic vocabulary used by
  complexity and security definitions. Negligibility constrains `|f n|`, so a
  negative function is not accepted merely because it lies below a positive
  threshold.

Files in this layer do not depend on probability, computation, cryptographic
primitives, game-based security definitions, or machine models.

### `Crypto.Infrastructure.Computation`

Reusable semantic infrastructure for cryptographic formalization.

- `Computation.Cost` follows the dependency chain
  `Model -> Writer -> Randomized -> PathBound`, with `Measure` depending only
  on `Model` and `Projection` joining measurement with path bounds. A
  `CostModel` is an ordered, potentially noncommutative additive monoid;
  `WorstCaseCostModel` adds a supremum using that same order. `Costed M` and
  `RandCosted M` preserve exact sequential order, and
  `RandCosted.CostBound` is the sole path-bound predicate. `NatMeasure` is a
  monotone additive projection, including addition and `nsmul` laws, and its
  projections preserve value distributions. `CostModel.nat` and
  `NatMeasure.nat` are ordinary concrete choices, not compatibility aliases or
  a second API.
- `Computation.Algebra` defines result-indexed `Signature`s and
  `CostedAlgebra M S` in the order
  `Signature -> Handler -> Laws / Bounds -> Operation`. Pure signatures do not
  depend on PMFs or costs. `CostedAlgebra.exec` is the sole exact primitive
  interpreter; `AlgebraLaws` specify cost-erased mathematics and distributions,
  while `OperationBounds` independently certifies upper bounds. Typed signature
  sums and result indices support heterogeneous and dependent operations.
  Sampling likewise has one exact handler, a separate uniformity law, and a
  separate bound. No operation-cost typeclass supplies a second exact cost.
- `Program A Input Output` is a typed heterogeneous algebraic program language.
  Its modules are `Syntax`, `Semantics`, `Execution`, and `Bounds`.
  `runCosted` is the only execution semantics and `valueDist` only erases that
  result. Structural `Execution` is proved equivalent to membership in
  `runCosted.support`. `BoundedProgram` stores the same `Program` plus an
  input-dependent certificate; sequencing uses ordered addition and a branch
  uses either an explicit common upper bound or `WorstCaseCostModel.sup`.
- `Computation.Oracle` follows
  `Spec -> Trace -> Program -> Handler -> Interpreter -> Bounds -> Composition`.
  `Program` contains only syntax: a query constructor carries no cost. Exact
  `QueryIssue` constructors and `CostedOracleEnv` live in `Handler`, while path
  certificates first appear in `Bounds`. The result-indexed issue algebra is
  the sole source of caller-side issue cost, while `CostedOracleEnv` is the sole
  exact implemented-oracle handler. `Program.runExact` is the only structural
  interpreter. Exact cost, local cost, implemented-oracle cost, and query trace
  are separate projections; `runCosted`, ordinary `runWithEnv`, and trace views
  are maps or erasures of that run. Ordinary environments enter through a
  named zero-cost lift. `PossibleExecution` deliberately overapproximates
  responses, and only interpreter support implies a possible execution.
- `Randomized` packages security-parameter-indexed `RandCosted M`
  computations. Probability semantics is always obtained by erasing the exact
  cost from that same computation.
- `Game` packages security experiments as security-parameter-indexed
  distributions.

This layer remains primitive-agnostic. It is the shared substrate for security
games and construction-specific definitions.

### `Crypto.Infrastructure.Complexity`

Semantic complexity notions used by constructions and security games.

- `CostBound` defines the certificate chain over one dependent,
  security-parameter-indexed run:

  ```text
  RandCosted.CostBound
    -> ExactCostCertificate
    -> RuntimeCertificate (NatMeasure and a uniform Nat runtime)
    -> PolyRuntimeCertificate
    +  PPTAdmissible (same run and claimed runtime)
    -> PPTMachine
  ```

- `Operational` defines `OperationalModel` and `OperationalRealization`.
  A realization identifies a validated code object, its denoted semantic
  artifact, and its resource claim. `PPTAdmissible`,
  `PPTOracleAdmissible`, and `PPTAddressedITMAdmissible` are transparent
  specializations of this common boundary. `OperationalModel.ValidCode` is now
  structural: canonical `FirstOrderOperationalCode` is validated internally,
  while `ExternalValidCode` is the named opaque trust anchor for other
  backends. `PPTMachine.ofFirstOrderCode` derives admission directly from the
  reified program, structural primitive-algebra witness, exact path bound, and
  measured runtime.
- `Machine` has one fully dependent core. `ProbabilisticMachine` stores the
  sole exact run; `TimedMachine` attaches annotation-level path and runtime
  certificates, while `PPTMachine` additionally requires `PPTAdmissible` for
  that exact run and claimed runtime. Ordinary inputs or outputs are constant
  families. Value-only `map` and pure-function constructors remain available
  below the PPT boundary, but cannot preserve or manufacture operational
  admission; there is no parallel ordinary/dependent or deterministic/decider
  hierarchy.
- `ProgramMachine` retains the program's native cost model. `NatMeasure` is
  used only to prove a uniform runtime and never rewrites the exact result into
  a natural-cost computation. Because the current program syntax is
  higher-order, `PPTMachine.ofBoundedProgram` also requires independent
  admission for its exact run.
- `OracleImplementation -> TimedOracleImplementation ->
  PPTOracleImplementation` certifies the authoritative `CostedOracleEnv`, its
  input-dependent query budget, measured uniform query runtime, repeat-cost
  monotonicity, and polynomiality.
- `OracleMachine -> TimedOracleMachine -> PPTOracleMachine` stores one oracle
  program and independently certifies input-dependent local work, per-name
  query counts, total query count, uniform local runtime, and uniform total
  query runtime. Composition constructs one ordinary machine with exact budget
  `localBudget + repeatCost totalQueryBudget envBudget` and runtime
  `localRuntime + totalQueryRuntime * envRuntime`. `CostExchange` is requested
  only by the exact theorem that regroups interleaved work;
  `NatMeasure.map_nsmul` proves the measured theorem, and the PPT constructor
  requires both polynomial closure and independent admission of the closed
  run. `PPTOracleMachine` itself likewise carries caller admission. Query
  counts are never inferred from cost or runtime.

This layer may depend on `Crypto.Infrastructure.Asymptotic` and
`Crypto.Infrastructure.Computation`, but should not depend on specific
primitives or assumptions. The current annotation model is an explicit,
trusted path-cost semantics: runtime and query certificates are connected to
the annotated computation and oracle-program execution, rather than being
unrelated metadata. Entry into cryptographic PPT quantification is a separate
operational boundary: each admission exposes a model, validated code object,
denotation equation, and claim equation indexed by the same execution and
claimed runtime. Internal `ValidCode` constructors are restricted to the
canonical first-order interpreter; the generic library provides no constructor
for arbitrary host functions.
For `Program` computations, costs are generated by the selected algebra handler
and accumulated by the interpreter; callers do not attach a total
cost after defining the algorithm. Exact handlers, cost-erased algebra laws,
and operation bounds are separate records. A `BoundedProgram` derives an
input-dependent bound compositionally from the primitive bounds; the machine
constructor statically relates its runtime field to the measured budget. It
does not synthesize a closed-form security-parameter bound independently of the
supplied program family.

The general `Program` language remains an engineering-level higher-order
syntax: values passed to `pure`, continuation functions, and branch conditions
remain Lean terms, so `PPTMachine.ofBoundedProgram` still needs independent
admission. The separate `CryptoFirstOrder` core removes those host
continuations and derives operational admission internally for a fixed reified
program. It is deliberately straight-line and has no recursion, loops, RAM, or
encoded bit-level representation. A concrete interpretation must still justify
that its bottom algebra operations and declared primitive costs adequately
model the intended platform; external backends use the explicit
`ExternalValidCode` boundary.

### `Crypto.Infrastructure.GameBased`

Generic security notions that are not tied to one primitive.

- `Advantage` defines acceptance probability and distinguishing advantage for
  boolean games.
- `Indistinguishability` contains only the cost-erased negligible-advantage
  boundary.
- `Distinguishing` and `OracleDistinguishing` separately define ordinary and
  oracle challenge problems. Their `Hard` predicates explicitly select an
  adversary `CostModel` and `NatMeasure`, then quantify all corresponding PPT
  machines rather than only program-derived adversaries.
- `Search` uses the same explicit adversary model and the unified dependent
  machine core, so witness types may depend on the sampled instance.
- `Hybrid` records finite hybrid sequences.

Primitive-specific games live under the corresponding primitive. This layer
contains only shared, semantically meaningful game boundaries.

### `Crypto.Infrastructure.UC`

The UC layer is an exact, typed ITM execution stack rather than a wrapper around
oracle games:

```text
Session -> Port -> Message -> ITM -> Corruption -> Configuration
        -> Kernel -> Complexity
        -> Protocol / Functionality -> Composition -> Execution -> Security -> Context
                                            `-> Layered
```

- `Session` gives `SID` a root and child path, and addresses pair a session with
  a machine name. `Port` and `Message` use result-indexed payloads, typed
  endpoints, proof-carrying `CanConnect` capabilities, and routing policies
  whose projections explicitly state observation, delay/delivery authority,
  forgery, and broadcast permission. `CanSendAs controller claimedSource`
  separately limits address impersonation after corruption. Broadcast is an
  ordinary manager component that serializes deliveries, not hidden kernel
  fanout.
- `ITMFamily` supplies address-indexed state, leakage, erasure requests, output,
  and exact `init`, `activate`, `applyErasure`, and `leak` handlers. One
  activation produces one `LocalAction`; multi-message work is serialized by
  queued resume activations.
- `Corruption` keeps policy separate from state semantics. `Configuration` is a
  dependently typed cell store with a global FIFO of activation and corruption
  events, audit trace, output, and corrupted-address set. A dynamic-corruption
  action only appends a request; a later kernel step checks the policy, passes
  the current state (including all previously committed erasures) to the exact
  leakage handler, removes honest state, marks the address corrupted, and
  queues a typed leakage activation for adversarial control.
- `Kernel` charges dequeue, initialization, state access, routing, enqueue,
  erasure, corruption, and finish through a typed `KernelAlgebra`. Its sole
  fuel-bounded `runCosted` activates at most one ITM per step and returns
  output, timeout, or deadlock. Timeout and deadlock map to `false`; neither a
  cost certificate nor a fuel certificate is inspected by the runner.
- `Complexity` attaches component-handler, one-step, repeated-activation,
  measurement, and polynomial certificates to that exact runner. Independent
  `FuelCertificate` proofs are indexed by the closed world's actual initial
  configuration and establish no-timeout and erased-distribution stability.
  Certified real and ideal worlds use the pointwise maximum of their
  polynomial activation limits as a common fuel; formal independence theorems
  show that this choice cannot make the real game depend on the simulator or
  the ideal game depend on the adversary.
- `Protocol` and `IdealFunctionality` are distinct wrappers. `Environment`,
  `Adversary`, `Simulator`, and `Network` are also distinct addressed ITMs.
  `Composition` dispatches their address spaces into one dependent family;
  `composeReal` installs environment, protocol, adversary, and network, while
  `composeIdeal` installs the same environment and network with functionality
  and simulator. One experiment supplies one corruption policy, and both
  execution-data families are indexed by that exact policy rather than storing
  independently selectable copies.
- `Execution` erases and maps `RealWorld.runCosted` and
  `IdealWorld.runCosted` directly. An environment's output family is
  intrinsically Boolean (represented universe-polymorphically as
  `ULift Bool`); the closed-world observation reads only an
  environment-owned terminal value. System, adversarial, and network terminal
  values cannot be reinterpreted by an uncharged post-processing function.
  `Security` provides PPT-certified role wrappers and restores the standard
  quantifier order
  `forall PPT adversary, exists PPT simulator, forall PPT environment` before
  applying game indistinguishability. Perfect equality implies computational
  emulation.
- `Context` provides a typed system hole, role-preserving injective address and
  port transport, PPT-preserving environment/adversary/simulator transforms,
  identity and associative plugging, and `uc_compose`. A single
  `SystemHole.fill` owns the plugged system, `ContextBuilder` constructs the
  surrounding world without accepting an unrelated outer system, and one
  `plugPolicy` transformation is shared by the real and ideal executions. Its
  premise is an erased one-step kernel commuting square over the dependent
  configuration; arbitrary finite runs, both sides' pointwise-maximum fuel,
  and the final real/ideal game equalities are derived theorems. The plugged
  simulator has no environment argument, while the same transformed
  environment is used on both inner worlds. `Layered` installs party steps and
  MPC functionalities as actual ITMs,
  includes explicit broadcast/corruption managers and boundary components in a
  total role dispatcher, and enforces corruption eligibility separately for
  each session and layer. `ExecutableLayered` connects that dispatcher, the MPC
  functionality, network, initial configurations, and both PPT certificates to
  the same layered policy before packaging the generic executable experiment.

This remains infrastructure rather than a catalog of completed UC protocols.
Concrete statements must instantiate the port schema, components, policy,
initial configuration, exact kernel algebra, complexity certificates, and
operational context simulations.

### `Crypto.Assumption`

Computational assumptions, organized by family.

Discrete logarithm and DDH live directly in `Assumption.DL.DLog` and
`Assumption.DL.DDH`. They share a cyclic-action parameter layer, while the
decisional layer adds exactly the stronger commutative multiplication/action
capabilities. For a chosen cost model `M`, each public parameter carries one
typed algebra implementing every operation used by its programs. Each family
has one `RandCosted M` setup, and search or distinguishing distributions are
obtained only by erasing costs from those computations.

DLog and DDH separate exact execution from efficiency evidence explicitly.
Their exact algebras contain no local upper bounds. A
`ParamEfficiencyCertificate` packages `OperationBounds` for the same algebra
and derives fixed-parameter challenge and sampling bounds. Family-level typed
signatures dispatch setup and parameter-dependent operations selected by its
result. DLog's complete sample and DDH's real and random samples are `Program`s
over those handlers. A family-level `EfficiencyCertificate` supplies global
setup and sampling `CostBound` proofs. Consequently, assumptions and exact
constructions such as ElGamal depend on the same native family algebra, while
efficiency certificates only bound already-defined execution paths. These
modules state the assumptions; they do not prove them.

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

The main symmetric-encryption interface is
`Crypto.Primitive.Encryption.SymmetricEncryption.Scheme M SecPar Param Key Message Ciphertext`.
It is generic in its `CostModel`; `setup`, `keygen`, `encrypt`, and `decrypt`
all return `RandCosted M`. `Key`, `Message`, and `Ciphertext` are indexed by
the sampled public parameters. Correctness and security notions observe
ordinary values through `setupDist`, `keygenDist`, `encryptDist`, and
`decryptDist`; they do not convert to a second scheme structure.
`OneTimeSecure` keeps its arbitrary PPT-machine quantification, while
`PerfectOneTimeSecure` quantifies over unbounded oracle machines and requires
exact zero advantage.

The main asymmetric-encryption interface is
`Crypto.Primitive.Encryption.AsymmetricEncryption.Scheme M SecPar Param PublicKey SecretKey Message Ciphertext`.
It follows the same `RandCosted M` design for public parameters, key
generation, public-key encryption, and secret-key decryption. Its IND-CPA
definition remains an `Infrastructure.GameBased.OracleDistinguishing` problem
over the cost-erased value distributions and keeps the same arbitrary PPT
adversary domain.

### `CryptoFirstOrder`

The trusted first-order language and its reusable algebra adapters live
together in the separate `CryptoFirstOrder` library. The core modules are
`Type`, `Signature`, `Algebra`, `Syntax`, `Builder`, `Semantics`, `Execution`,
`Operation`, `Validation`, and `Bounds`; `CryptoFirstOrder.Core` aggregates
exactly those modules. `Ty` contains base carriers, unit, booleans, and
products; `Expr`, `Var`, and `Env` give a typed de Bruijn representation; and
`Code` contains only return, pure let, primitive call, and represented branch
nodes. Code stores neither Lean continuations nor function-valued syntax.

The adapter subtrees own generic object-language bases, interpretations,
signatures, smart-operation embeddings, host-value lift/projection boundaries,
and exact handler bridges. Assumption-specific modules such as
`CryptoFirstOrder.Assumption.DL.DDH` may package reusable cost-erasure facts.
`ValidAlgebra` exposes the bottom operations as the primitive boundary while
preventing an arbitrary sampler distribution from entering internal
validation.

Core modules depend only on lower `Crypto` cost and probability infrastructure;
adapter modules may additionally depend on the corresponding abstract algebra
or assumption definitions. The sole direct import in the other direction is
`Crypto.Infrastructure.Complexity.Operational -> CryptoFirstOrder.Core`, which
keeps internally validated first-order admission as a closed `ValidCode`
constructor without importing adapters. `CryptoFirstOrder` contains no
construction algorithms, assembled schemes, security definitions, complexity
certificates, or concrete backend choices. Import `CryptoFirstOrder.Core` for
only the trusted language, `CryptoFirstOrder.Basic` for the core plus all
current adapters, or a narrow module when defining a construction.

### `CryptoConstruction`

Parameterized algorithms and protocol constructions live in the separate
`CryptoConstruction` library. It depends on `Crypto` and `CryptoFirstOrder`;
neither lower library imports it. The current constructions include a
group-based one-time pad and ElGamal. They work over abstract cost-aware
parameter families; the production package does not yet choose a concrete
group representation or implementation backend. A future
`CryptoInstantiation` library is reserved for such concrete choices.
The one-time pad exposes the finite nonempty additive group chosen for the
security parameter, encrypts by addition, and decrypts by negation followed by
addition.
The library proves both correctness and perfect one-time security for this
construction, and derives PPT one-time security from the perfect theorem.
ElGamal has a correctness proof under the scalar-action laws carried by its
public parameters; an IND-CPA-from-DDH reduction remains future work.

Import `CryptoConstruction.Basic` to obtain all current parameterized
constructions. Importing `Crypto` or `Crypto.Primitive.Basic` exposes only the
core definitions, assumptions, infrastructure, and generic properties;
`CryptoFirstOrder.Basic` exposes adapters but no schemes.

Both construction-level `scheme` definitions directly inhabit this generic
interface. OTP, DLog, DDH, and ElGamal each use one typed algebra as the only
primitive execution source. Their decomposed algorithm bodies are `Program`s;
scheme fields run those programs directly, while an exact family setup is the
primitive called by the family-level setup program where one is needed.
Value-distribution equations used by correctness and security erase costs from
that execution. OTP has no dummy scalar capability. ElGamal reuses the DDH
family algebra and setup rather than defining a second arithmetic
implementation. Bounded wrappers pair the same programs with proofs instead of
copying their syntax. Separate local and family certificates supply verified
upper bounds when constructing timed or PPT machines; they never define
another cost semantics.

The primitive-level `UC.lean` files are reserved for primitive-specific UC
formulations, such as ideal functionalities or emulation statements for the
corresponding primitive. The reusable UC execution and protocol machinery
belongs in `Crypto.Infrastructure.UC`; primitive-level files should import and
instantiate that machinery only when they introduce concrete UC definitions.

## Import Policy

`Basic.lean` files are aggregation modules for their own library layer. Import
them when a caller wants that layer; otherwise prefer the narrow file that
provides the needed definition. `Crypto.Basic` does not aggregate
`CryptoFirstOrder.Basic` or its adapters; its operational-admission layer
imports only `CryptoFirstOrder.Core`. `CryptoFirstOrder.Basic` never aggregates
constructions.

The enforced dependency direction is:

```text
SecurityParameter -> Asymptotic
SecurityParameter -> security-parameter-indexed Computation / UC modules

Cost.Model -> Cost.Writer -> Cost.Randomized -> Cost.PathBound
Cost.Model -> Cost.Measure
Cost.PathBound + Cost.Measure -> Cost.Projection

Cost -> Algebra -> Program
SecurityParameter + Cost + Algebra -> Oracle
Asymptotic + Computation -> Complexity -> GameBased -> UC

Probability ---------------------------------------> Assumption / Primitive
Program / Oracle / GameBased / UC -----------------> Assumption / Primitive

Crypto Cost / Probability -> CryptoFirstOrder core
CryptoFirstOrder core -> Crypto Complexity.Operational
Crypto definitions + CryptoFirstOrder core -> CryptoFirstOrder adapters
  -> CryptoConstruction -> future CryptoInstantiation
```

`SecurityParameter` and `Probability` are independent roots; in particular,
neither imports asymptotics or computation. `scripts/check_infrastructure_imports.py`
checks exact project-module resolution, the Infrastructure hierarchy, the
first-order core order, the core-only operational bridge, and the
`CryptoFirstOrder`/`CryptoConstruction`/`CryptoInstantiation` boundary; CI runs
it before Lean builds. Infrastructure subsystems additionally enforce their
file-local orders, including Algebra, Program, Oracle, Complexity, GameBased,
and the UC kernel stack.

## Adding New Material

- Put infrastructure code under `Infrastructure`.
- Put only `SecPar` in `Infrastructure.SecurityParameter`; put polynomial and
  negligible predicates in `Infrastructure.Asymptotic`.
- Put cost-independent PMF constructions in `Infrastructure.Probability`.
- Put reusable game, oracle, computation, cost, or algebra semantics in
  the corresponding ordered sublayer of `Infrastructure.Computation`.
- Put exact/runtime/polynomial certificates, unified dependent machines,
  program-to-machine adapters, and oracle implementation/machine certificates
  in `Infrastructure.Complexity`.
- Put generic advantage, indistinguishability, hybrid, distinguishing, oracle
  distinguishing, and search notions in `Infrastructure.GameBased`.
- Put reusable typed ITM, corruption, FIFO-kernel, closed-world, UC-security,
  context-composition, and layered-MPC definitions in `Infrastructure.UC`.
- Put assumption families in `Assumption/<family>/`.
- Put primitive-specific abstract syntax, correctness, and security games in
  `Primitive/<kind>/<primitive>/`, with `Syntax.lean` and `UC.lean` as direct
  files and generic theorems under `Properties/`.
- Put the trusted first-order AST, interpreter, validation, bounds, Builder
  surface, reusable bases, signatures, operation embeddings, lift/projection
  boundaries, and exact-algebra bridges under `CryptoFirstOrder/`. Do not put
  schemes, security properties, complexity certificates, or concrete backends
  there.
- Put algorithms that construct abstract primitives or protocols over
  parameterized mathematical and cost-aware backends under
  `CryptoConstruction/`.
- Within a named construction, use `Construction.lean` for its parameters and
  algebra, `Scheme.lean` for the executable algorithm `Program`s and assembled
  scheme, and `Complexity.lean` for budgets, bounded/timed wrappers, exact-cost
  results, and efficiency certificates. `Scheme.lean` must not import
  `Complexity.lean`. Put cost-erasure and value-distribution theorems in
  `Properties/Semantics.lean`; correctness and security properties depend on
  semantics rather than complexity evidence.
- Reserve a future `CryptoInstantiation/` library for fixed representations,
  implementation backends, and their instance-specific cost certificates.
- Use `CryptoFirstOrder.Core` when only the trusted language is required and
  `CryptoFirstOrder.Basic` when all adapters are required. Import
  `CryptoConstruction.Basic` explicitly for parameterized algorithms.

When adding polymorphic Lean declarations, use descriptive universe names such
as `uIn`, `uOut`, `uQuery`, `uResponse`, `uValue`, `uMapped`, `uScalar`,
`uModule`, and `uGroup`, rather than bare `u`, `v`, or `w`.

## Lean Source Style

The following rules are part of the project interface, not merely formatting
preferences. They keep construction files readable without hiding the exact
first-order program whose semantics and cost are proved later.

### Variables and namespace qualification

- Put parameters repeated by several declarations in the nearest namespace- or
  section-level `variable` block. This applies to cost models, public
  parameters, construction families, measures, certificates, and genuinely
  polymorphic input or output types.
- A shared variable must remain a real parameter. Do not replace a
  construction-fixed identity, such as an ElGamal public key being a group
  carrier, with a free type variable merely to shorten a declaration.
- A cleanup must preserve public binder order, explicitness, universe roles,
  declaration types, and theorem behavior. Use a small `section` or a new
  variable declaration when one declaration needs different binder
  explicitness.
- Keep imports fully qualified. In `CryptoConstruction` algorithm files, avoid
  ordinary broad `open` declarations; activate notation and scoped instances
  with narrow `open scoped` declarations instead. A proof-heavy file may use a
  narrow ordinary `open` when repeated qualification would obscure the proof.
  Do not introduce a private namespace alias merely to move the same verbosity
  elsewhere.
- When cost-layer names recur in a primitive or proof file, a narrow
  `open Crypto.Infrastructure.Computation.Cost` permits `CostModel`,
  `RandCosted`, and `NatMeasure`. In a construction `Scheme.lean`, prefer one
  fully qualified `CostModel` in the shared `variable` block over a broad
  namespace opening or repeated fully qualified binders.

### Abbreviations and cryptographic roles

- Avoid chains of one-use `private abbrev` declarations whose only purpose is
  shortening the current file. Use `abbrev` when it publicly names a stable
  semantic role or a reusable interface and definitional transparency is
  intended.
- A construction's object-language roles belong in its authoritative
  `Construction.Language` namespace. Use names such as `keyTy`, `publicKeyTy`,
  `secretKeyTy`, `messageTy`, and `ciphertextTy`, even when several roles are
  definitionally the same carrier.
- Keep public and secret keys as distinct roles. ElGamal key generation returns
  a structural pair, but the interface lists `publicKeyTy` and `secretKeyTy`
  separately rather than introducing a `keyPairTy` role.
- Put reusable arity encoding in `CryptoFirstOrder`. New construction
  declarations use `CryptoFirstOrder.Program.NAry` with a static list of
  logical input roles, and `CryptoFirstOrder.Program.NAryPair` when the result
  contains two distinct roles. `Nullary`, `Unary`, `Binary`, `Ternary`, and `NullaryPair`
  remain compatibility abbreviations over this layer.
- `Ty.tuple` compiles the static input list to the existing structural input:
  `[]` becomes `unit`, a singleton remains unchanged, and larger lists become
  right-associated products. Every instantiated program therefore still has a
  fixed, fully typed input at the trusted core boundary.

### First-order construction syntax

Construction algorithms use the scoped `CryptoFirstOrder.Builder` surface and
compile immediately to the trusted `CryptoFirstOrder.Code` syntax. A typical
declaration has this shape:

```lean
open scoped CryptoFirstOrder DDHGroup

variable
  {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
  (pp : PublicParam.{uCost, uScalar, uGroup} M)

def keygenProgram :
    CryptoFirstOrder.Program.NAryPair
      (Language.interpret pp) Language.signature
      []
      Language.publicKeyTy Language.secretKeyTy where
  body := first_order () do
    let sk ← unifSamp Language.scalarTy
    let pk ← ⦋sk⦌
    return (pk, sk)
```

- Match the `NAry` input list with a Builder typed context: use
  `first_order () do` for no logical inputs, `first_order input do` or
  `first_order (input) do` for one, and `first_order (x, y, z) do` for several.
  These names compile to projections from `Ty.tuple`; they do not add variables
  or a second context representation to the trusted AST.
- Inside `first_order`, prefer `•`, `+`, binary `-`, unary `-`, and `*`.
  The named forms `smul`, `add`, `sub`, `neg`, and `mul` remain compatibility
  forms, not the default style for new construction code.
- Smart operations may be nested, for example `message + (r • pk)`. Builder
  A-normalizes nested calls from left to right into fresh internal bindings, so
  the trusted core and `Complexity.lean` still see ordinary sequential
  `Code.call` nodes rather than a second expression or algorithm AST.
- Importing the first-order DDH adapter makes the separate `DDHGroup` scope
  available. With that scope open, `⦋x⦌` denotes `x • pp.generator`; type
  `\s[]` (or `\simplex`) in Lean's Unicode input mode to insert the pair. The
  current DDH parameter is inferred from the program's carrier type. The
  notation lowers to the existing scalar-action call and adds no core AST node.
  Open `DDHGroup` only where this notation is used.
- Use bound names, `unit`, booleans, pairs, `value(...)`, `fst(...)`, and
  `snd(...)` for expressions. Use `call operation with arguments` only as an
  escape hatch for a primitive that has no smart surface form.
- Algorithm bodies must not expose `Signature.inject`, sum injections such as
  `.inl` or `.inr`, or `ULift` conversions. Signature embeddings and smart
  constructors lower those details to raw `Code.call`; host-boundary conversion
  belongs in `Builder.runCosted`, `ValueRepresentation`, and
  `ValueProjection`.
- Write object-language products as `A ×ₜ B` in surface type declarations.
  The trusted structural core remains `Ty.prod`. Do not write a product merely
  because a `Program` accepts several logical inputs; list their roles in
  `Program.NAry`. A genuine value product, such as an ElGamal ciphertext, still
  uses `×ₜ`.

### Sampling syntax

- General sampling has two explicit conceptual inputs and is written
  `sample sampleTy sampler`: the object-language type being sampled and a
  `Sampler S sampleTy` selecting the corresponding operation or distribution
  descriptor in the current signature.
- Uniform sampling is the convenience form `unifSamp sampleTy`. Its distribution
  is fixed to uniform, so only the object-language type is written explicitly;
  the required operation is found through a signature embedding.
- A sampler descriptor belongs to the typed signature. It does not embed an
  arbitrary host `PMF` callback in first-order syntax. Distributional meaning
  is supplied by the selected algebra and its laws.

### Construction and proof boundaries

- `Construction.lean` owns construction-specific mathematical parameters and
  the authoritative exact algebra. Reusable base types, interpretations,
  signatures, operation embeddings, lift/projection boundaries, and handler
  bridges belong in `CryptoFirstOrder`; `Construction.Language` should alias an
  existing adapter and add only construction-specific semantic role names and
  bindings. Add a new reusable adapter instead of copying this wiring into a
  construction.
- `Scheme.lean` is the single source of each executable algorithm and assembles
  the abstract primitive or protocol from those programs. It uses the Builder
  surface, contains no hand-written signature injection or universe lifting,
  and never imports `Complexity.lean`.
- `Complexity.lean` proves budgets, bounds, exact costs, timed wrappers, and
  efficiency certificates for the compiled first-order program, normally its
  existing `.body`. It must not restate or copy the algorithm.
- `Properties/Semantics.lean` proves cost erasure and value-distribution facts
  for the same program. Correctness and security depend on that semantic layer,
  not on `Complexity.lean`.
- Scheme-facing host values enter and leave through the shared first-order
  representation boundary. Do not create a second execution path solely to
  avoid a representation conversion.

Style refactors must be checked as API-preserving changes: inspect the diff for
binder and declaration changes, build the smallest affected targets, then run
the full `lake build` when an interface or cross-library boundary changed.
`git diff --check` must pass, and committed project code must not introduce
`sorry` or `admit`.

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

The library is early-stage, but Infrastructure now follows one strict semantic
and certificate hierarchy. There is one dependent machine core, one exact
Program interpreter, and one structural Oracle interpreter. Oracle local cost,
per-name queries, total queries, implementation cost, measured runtime, and
polynomial closure form one certificate chain. The UC layer has a typed FIFO
kernel, exact kernel algebra, dynamic corruption, real/ideal world wiring,
PPT-certified roles, common-fuel execution, standard UC quantifiers, and an
operationally certified context-composition theorem. Its public Boolean game
is fixed by the typed environment output, real and ideal executions share one
corruption policy, and layered systems are connected through a total executable
dispatcher rather than metadata-only components.

OTP, ElGamal, DLog, and DDH use the generic typed-algebra-to-`RandCosted`
path, with efficiency bounds treated as certificates over those exact
executions. All four use the same typed `Program` layer and none has an
alternate fixed-natural-cost API. The minimal first-order operational model now
covers straight-line algebraic code and finite uniform sampling. The next
useful refinements are iteration and representation-level machine costs,
concrete protocol instantiations of the UC kernel and context interface, and an
ElGamal IND-CPA proof from DDH.
