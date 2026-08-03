# Cost-aware algebra and generic `Program` migration

This document is the implementation ledger for the repository-wide migration
from a fixed natural-number cost model and a fixed additive `Program` syntax to
generic resource models and typed heterogeneous primitive operations.  It is
intended to be updated at each buildable milestone.  It is not evidence that a
milestone has been completed unless the corresponding verification commands
and status are recorded below.

## Baseline

- Date recorded: 2026-08-03.
- Branch: `main`.
- Baseline commit: `d8ba0802be01` (`rebuild the entire project`).
- Toolchain: Lean `v4.29.0-rc1`; Lake `5.0.0`; Mathlib pinned by the current
  manifest.
- Baseline verification: `lake build` completed successfully (1812 jobs).
- Source inventory: 81 Lean files including the two root aggregation modules.
- Trust audit: no `sorry`, `admit`, `axiom`, or `unsafe` declaration was found.
- No commit or push is part of this migration unless explicitly requested.

The following user-owned changes existed before this document was created and
are migration inputs.  They must not be discarded or overwritten:

| Status | Path | Existing intent |
| --- | --- | --- |
| modified | `Crypto/Infrastructure/Asymptotic/Bounds.lean` | polynomial closure lemmas used by composed resource bounds |
| modified | `Crypto/Infrastructure/Complexity/Machine.lean` | cost-aware oracle-machine integration |
| modified | `Crypto/Infrastructure/Computation/Oracle/Basic.lean` | profiled and costed oracle execution |
| modified | `README.md` | documentation for the in-progress oracle work |
| untracked | `Crypto/Infrastructure/Computation/Oracle/Costed.lean` | exact-cost oracle environment and erasure bridge |
| untracked | `CryptoTest/Infrastructure/Computation/CostedOracle.lean` | oracle composition regression tests |

The semantic `OracleEnv` remains the cost-erased API used by games.  The
cost-aware environment is an implementation layer with a proved erasure map;
it must not replace or weaken the semantic interface.

## Architectural invariants

1. There is one authoritative exact interpreter for every primitive.  Value
   semantics are obtained by erasing its cost, never by maintaining a second
   evaluator whose behavior may drift.
2. Exact execution costs, finite upper-bound certificates, and asymptotic
   bounds are separate layers.
3. Sequential resource composition need not be commutative.  The core assumes
   an ordered additive monoid; automatic worst-case branch bounds require an
   additional join capability.
4. Random computations retain the joint distribution of values and path
   costs.  This migration does not introduce expected-cost or tail-bound
   semantics.
5. Existing cost-erased games, advantages, correctness statements, `Hard`,
   DLog/DDH `Assumption`, `OneTimeSecure`, `INDCPASecure`, and UC semantics keep
   their current names, quantification domains, and theorem strength.
6. Global projection instances are avoided.  Algebra bundles expose explicit
   projections and scoped/local instances so that concrete Mathlib instances
   cannot form diamonds.
7. `Nat` remains a compatibility model while internal algorithms migrate to
   generic resources.

## Target dependency structure

```text
CostModel ------------------------------+
  |                                     |
  +--> CostedT / RandCostedT             +--> NatMeasure
               |                                  |
Signature ---> CostedAlgebra                      |
  |            |                                  |
  |            +--> AlgebraLaws                   |
  |            +--> OperationBounds               |
  |                     |                          |
  +-----------> Program.Code                      |
                        |                          |
                        +--> Program A Input Output|
                                  |                |
                                  +--> CostBound   |
                                  +--> BoundedProgram
                                           |
                                           +------> ProgramMachine
                                                      |
                                                      +--> existing Nat
                                                           Timed/PPT machines
                                                               |
                                                               +--> existing
                                                                    games and
                                                                    security
                                                                    predicates
```

### Generic cost model

The cost layer will provide the following roles (exact field names may be
adjusted only to match available Mathlib typeclasses without changing their
meaning):

```lean
structure CostModel where
  Cost : Type uCost
  instAddMonoid : AddMonoid Cost
  instPartialOrder : PartialOrder Cost
  addLeftMono : AddLeftMono Cost
  addRightMono : AddRightMono Cost

structure WorstCaseCostModel extends CostModel where
  instSemilatticeSup : SemilatticeSup Cost

structure NatMeasure (M : CostModel) where
  toNat : M.Cost ->+ Nat
  monotone_toNat : Monotone toNat
```

- `CostedT M Value` is the deterministic writer value.
- `RandCostedT M Value := PMF (CostedT M Value)` retains exact path costs.
- `Costed` and `RandCosted` remain aliases for `natCostModel`.
- Cost mapping through `NatMeasure` must preserve `valueDist`.
- A componentwise `Steps x Queries` test model will demonstrate that the
  abstraction is genuinely multi-resource rather than a renamed `Nat` API.
- Parallel composition is not part of the initial model; it can be added later
  as an independent capability.

### Typed primitive signatures

The program algebra is based on an operation family indexed by result type:

```lean
structure Signature where
  Op : (Result : Type uResult) -> Type uOp

structure CostedAlgebra (M : CostModel) (S : Signature) where
  exec : forall {Result}, S.Op Result -> RandCostedT M Result
```

`Signature.Sum` combines independent capabilities.  Deterministic arithmetic
operations, sampling, and family-dependent operations are represented as
typed constructors.  In particular, a family signature may contain operations
such as `sampleScalar pp : Op pp.Scalar`; no dummy scalar type or optional
backend field is required.

`AlgebraLaws` relates the erasure of `exec` to Mathlib operations or a uniform
distribution.  `OperationBounds` proves local upper bounds separately.  The
existing `AdditiveBackend` and `MultiplicativeBackend` become compatibility
constructors for handlers, while the current operation-cost typeclasses remain
temporary adapters until repository users have been migrated.

The shared mathematical parameter hierarchy is intentionally capability-based:

- a finite additive parameter for one-time pad;
- a cyclic-action parameter for discrete logarithm;
- a stronger DDH parameter extending cyclic action with the commutative
  multiplicative/action structure used by DDH;
- ElGamal continues to reuse DDH parameters rather than restating the laws.

The current `UniformSampler` is split into exact sampling, its uniformity law,
and a separate bound certificate.

### Generic program

The fixed `Scalar`/`Carrier`/`Sample` syntax is replaced by a generic typed
program:

```lean
inductive Program.Code (A : CostedAlgebra M S) : Type uResult -> Type _
  | pure
  | bind
  | call
  | branch

structure Program (A : CostedAlgebra M S)
    (Input : Type uIn) (Output : Type uOut) where
  body : Input -> Program.Code A Output
```

- `runCosted` is the only interpreter and `valueDist` is its erasure.
- `Execution` records the selected structural path and exact model cost.
- `Program.CostBound` accepts an input-dependent budget
  `Input -> M.Cost`.
- `BoundedProgram` contains one `Program` plus a proof; concrete algorithms do
  not duplicate bounded and unbounded syntax trees.
- Structural bound derivation uses operation certificates, sequential addition,
  and either a worst-case join or an explicitly supplied common branch bound.
- `ProgramMachine` maps generic costs through `NatMeasure` before constructing
  the existing `TimedMachine` or `PPTMachine`, with a theorem that the value
  distribution is unchanged.

The existing `Hard` predicate continues to quantify over arbitrary legacy
`PPTMachine` values.  Program-derived machines form a source of such machines,
not a replacement adversary class.  Any program-restricted hardness notion
must use a distinct name and may receive only the sound one-way implication
from existing hardness.

## Declaration migration map

| Existing declaration | Target role | Compatibility policy |
| --- | --- | --- |
| `Cost := Nat` | `natCostModel.Cost` | retain the public alias |
| `Costed`, `RandCosted` | `CostedT natCostModel`, `RandCostedT natCostModel` | retain namespaces and existing theorem names where practical |
| `AddCost`, `MulCost`, `NegCost`, `SubCost`, `SMulCost` | adapters that construct exact handlers | do not use as the new source of truth |
| `AdditiveBackend`, `MultiplicativeBackend` | typed-operation handler constructors | retain Nat-facing constructors during migration |
| `UniformSampler` | exact sampler plus uniformity law and independent bounds | provide a wrapper for existing constructors |
| fixed-parameter `Program` | `Program A Input Output` | migrate all concrete programs before retiring the old shape |
| current `BoundedProgram` combinator trees | a single program paired with `CostBound` | no duplicated algorithm bodies |
| `ProgramMachine` | generic program plus bounds and `NatMeasure` | resulting legacy machine preserves value semantics |
| OTP `UnusedScalar` | no declaration | OTP signature contains only sample/add/neg operations |
| repeated DLog/DDH parameter shells | cyclic-action base and DDH extension | preserve old projection names through adapters where needed |
| legacy `OracleProgram.query` and `OracleProfile.ofQuery` | original unit-cost syntax and profile | retain exactly; explicit costs exist only in `OracleProgramT` |
| runtime-derived legacy query count | retain, plus optional `TotalQueryBoundCertificate` | runtime remains a polynomial query bound; the certificate supplies composition-specific bounds |
| existing security predicates | unchanged semantic boundary | never replace by program-restricted quantification |

## Ordered milestones

| Milestone | Work | Exit criterion | Status |
| --- | --- | --- | --- |
| 1. Lock the baseline | Record this plan and import `CostedOracle` from the root test module. | Direct CostedOracle build and `lake build CryptoTest` pass without changing pre-existing files. | complete; regression imported |
| 2. Generic cost foundation | Add `CostModel`, worst-case capability, `NatMeasure`, `CostedT`, `RandCostedT`, Nat aliases, cost mapping, and resource-pair tests. | Foundation modules, compatibility tests, `Crypto`, and `CryptoTest` build. | implemented; focused tests pass |
| 3. Typed algebra | Add `Signature`, sums, handlers, laws, operation bounds, sampler split, and old-backend adapters. | Deterministic, sampling, dependent-operation, and multi-resource tests pass. | implemented; focused tests pass |
| 4. Generic Program | Replace the fixed AST, implement exact semantics/executions and input-dependent bounds, and adapt `ProgramMachine`. | Program tests cover erasure, exact paths, sequencing, branching, and measured machine conversion. | implemented; focused tests pass |
| 5. Concrete algorithms | Migrate ElGamal, then OTP, then DLog and DDH; introduce the shared parameter hierarchy only after the representative slices build. | Existing correctness/security theorem statements and concrete cost regressions pass. | implemented; focused tests pass |
| 6. Oracle composition | Finish costed environments, explicit query cost, independent total-query bounds, and corrected composed bounds. | Exact erasure and internal-cost tests plus generic and Nat coarse bounds pass. | implemented; focused tests pass |
| 7. Compatibility cleanup | Remove internal obsolete uses, retain public Nat wrappers, update imports/README, and run the final audit. | Full build and trust/diff audits pass with no orphaned tests. | complete; full repository verified |

Each milestone is landed as a buildable workspace state.  A later milestone may
not weaken or delete the tests established by an earlier one.

## Per-file ledger

The status column is updated before a file is edited.  `verify only` means the
file is a semantic compatibility boundary and is not expected to change unless
an import or explicit adapter is required.

| Area | Files | Planned action | Status |
| --- | --- | --- | --- |
| Cost foundation | `Crypto/Infrastructure/Computation/Cost/Model.lean` | define the generic model and Nat instance | implemented; focused build passed |
| Cost foundation | `Crypto/Infrastructure/Computation/Cost/Projection.lean` | add monotone additive Nat measurements | new; implemented and tested |
| Cost foundation | `Crypto/Infrastructure/Computation/Cost/Costed.lean` | generalize the writer and retain the Nat alias | implemented; monad laws tested |
| Cost foundation | `Crypto/Infrastructure/Computation/Cost/Distribution.lean` | generalize random costed computations and erasure | implemented; joint distribution tested |
| Cost foundation | `Crypto/Infrastructure/Computation/Cost/Basic.lean` | export the new cost modules | complete |
| Cost foundation | `Crypto/Infrastructure/Computation/Randomized.lean` | connect randomized computations to the Nat compatibility layer/generic family | complete |
| Algebra | `Crypto/Infrastructure/Computation/Algebra/Signature.lean` | add typed signatures, sums, handlers, laws, and operation bounds | new; implemented and tested |
| Algebra | `Crypto/Infrastructure/Computation/Algebra/Operation.lean` | provide typed arithmetic and sampling capabilities plus Nat adapters | new; implemented and tested |
| Algebra | `Crypto/Infrastructure/Computation/Algebra/Backend.lean` | adapt backends and split sampler bounds | complete |
| Algebra | `Crypto/Infrastructure/Computation/Algebra/Costed.lean` | retain legacy operation-cost adapters | compatibility boundary; unchanged |
| Algebra | `Crypto/Infrastructure/Computation/Algebra/Group.lean` | introduce/reuse the finite additive parameter base | `AdditiveGroupParam` complete; `CyclicAction` and `DecisionalCyclicAction` extend it in `DL/Parameter.lean` |
| Algebra | `Crypto/Infrastructure/Computation/Algebra/Module.lean` | align scalar-action capabilities and legacy cost-model bridge | compatibility boundary; unchanged |
| Algebra | `Crypto/Infrastructure/Computation/Algebra/Basic.lean` | export the typed algebra API | complete |
| Program | `Crypto/Infrastructure/Computation/Program.lean` | implement `Program A Input Output`, exact execution, and nonduplicated bounds | implemented and tested |
| Complexity | `Crypto/Infrastructure/Complexity/CostBound.lean` | connect generic exact bounds to Nat asymptotic bounds | compatibility boundary; reused through `NatMeasure` |
| Complexity | `Crypto/Infrastructure/Complexity/ProgramMachine.lean` | add measured generic-program machine adapters | implemented; erasure theorem tested |
| Complexity | `Crypto/Infrastructure/Complexity/Machine.lean` | add independent total-query bounds while preserving legacy machines | original unconditional runtime-query lemmas and optional certificates tested |
| Asymptotic | `Crypto/Infrastructure/Asymptotic/Bounds.lean` | retain and validate closure lemmas needed by composed bounds | polynomial closure lemmas implemented |
| Oracle | `Crypto/Infrastructure/Computation/Oracle/Interface.lean` | separate explicit query cost from trace/count resources | complete; generic explicit-cost core and exact legacy unit-cost syntax tested |
| Oracle | `Crypto/Infrastructure/Computation/Oracle/Costed.lean` | integrate exact environment costs and erasure | complete; generic exact interpreter and bounds tested |
| Oracle | `Crypto/Infrastructure/Computation/Oracle/Basic.lean` | correct exact/coarse composition interpreters and bounds | complete; aggregation build passed |
| Assumptions | `Crypto/Assumption/DL/Parameter.lean` | share cyclic-action and decisional parameter hierarchy | new; implemented and tested |
| Assumptions | `Crypto/Assumption/DL/DLog.lean` | migrate setup and complete sampling/search to dependent typed operations | family-level setup/sample programs and assumption bridges implemented; test build passed |
| Assumptions | `Crypto/Assumption/DL/DDH.lean` | migrate setup plus real/random sampling and preserve assumptions | family-level setup/real/random programs and assumption bridges implemented; test build passed |
| Assumptions | `Crypto/Assumption/DL/Basic.lean` | update aggregation import only if needed | complete |
| OTP | `Crypto/Primitive/Encryption/SymmetricEncryption/Instantiations/OneTimePad/Construction.lean` | remove dummy scalar and define one program body | implemented; no dummy scalar remains |
| OTP | `Crypto/Primitive/Encryption/SymmetricEncryption/Instantiations/OneTimePad/Scheme.lean` | expose the erased/timed adapters from that program | implemented; focused tests passed |
| ElGamal | `Crypto/Primitive/Encryption/AsymmetricEncryption/Instantiations/ElGamal/Construction.lean` | adapt shared DDH parameters | verified through shared parameter alias |
| ElGamal | `Crypto/Primitive/Encryption/AsymmetricEncryption/Instantiations/ElGamal/Scheme.lean` | migrate setup, key generation, encryption, decryption, and bounds | implemented using the DDH setup program plus local typed programs; exact-cost/correctness tests passed |
| Tests | `CryptoTest/Infrastructure/Computation/CostedOracle.lean` | preserve existing exact/erasure tests and update corrected query bounds | Nat, vector, noncommutative exact-order, erasure, and coarse-bound cases pass |
| Tests | `CryptoTest/Infrastructure/Computation/GenericCost.lean` | test vector costs, laws, projection, machine erasure, and value/cost correlation | new; multi-outcome joint-distribution regression passes |
| Tests | `CryptoTest/Infrastructure/Computation/CostComposition.lean` | retain Nat compatibility composition cases | unchanged compatibility test |
| Tests | `CryptoTest/Infrastructure/Computation/Program.lean` | migrate to typed signatures and input-dependent bounds | complete; passes |
| Tests | `CryptoTest/Infrastructure/Complexity/ResourceBounds.lean` | test total-query certificates and polynomial transfer | unconditional legacy runtime-query and optional-certificate cases pass |
| Tests | `CryptoTest/Primitive/Encryption/AsymmetricEncryption/ElGamal.lean` | retain exact bound, erasure, timed, and correctness regression | complete; passes |
| Tests | `CryptoTest/Primitive/Encryption/SymmetricEncryption/OneTimePad.lean` | verify no dummy algebra and retain perfect security | complete; focused build passed |
| Tests | `CryptoTest/Assumption/DL/DLog.lean` | retain search/sample semantics and costs | complete; passes |
| Tests | `CryptoTest/Assumption/DL/DDH.lean` | retain real/random distributions and exact operation costs | complete; passes |
| Tests | `CryptoTest.lean` | import all regression modules, beginning with `CostedOracle` | complete; both new suites imported |
| Documentation | `README.md` | describe only completed, verified architecture | complete; pre-existing Oracle documentation integrated and corrected |
| Documentation | `docs/refactor/cost-aware-algebra-plan.md` | maintain decisions, status, and verification evidence | complete; final evidence recorded below |

The symmetric/asymmetric syntax modules, their general security-property
modules, `Crypto/Infrastructure/GameBased/**`, and
`Crypto/Infrastructure/UC/**` are verification-only boundaries.  If an adapter
edit becomes necessary, it must preserve theorem statements and be entered in
this ledger before modification.

## Oracle correction contract

- `CostedOracleEnv.erase` recovers the existing stateful semantic environment.
- Local machine work and query trace/count are independent resources.
- A generic `OracleProgramT` query receives its cost explicitly. The legacy
  `OracleProgram` retains only its original unit-cost `query` constructor;
  explicit-cost Nat callers use `OracleProgramT natCostModel`.
- `TimedOracleMachine` and `PPTOracleMachine` retain their original fields and
  adversary domain. Legacy runtime therefore still bounds total and per-name
  query counts. A separate optional `TotalQueryBoundCertificate` can provide a
  dedicated bound for composed-oracle accounting.
- `PolyTotalQueryBoundCertificate` adds polynomial boundedness of that
  independent total-query certificate.
- The exact interpreter accumulates the actual returned internal environment
  costs in sequential order for every `CostModel`.
- A uniform environment bound yields
  `localBudget + totalQueryBound • envBudget` when an explicit exchange law
  permits local and oracle contributions to be regrouped; the Nat compatibility
  theorem is `localBudget + totalQueryBound * envBudget`.
- Runtime-derived query bounds remain unconditional for the legacy unit-cost
  syntax, but do not transfer to generic explicit-cost programs.

## Verification matrix

Run the narrowest relevant target after each edit, followed at every milestone
by:

```text
lake build Crypto
lake build CryptoTest
lake build
```

Required behavioral tests:

- ordered sequential monoid laws, monotonicity, Nat compatibility, and optional
  worst-case join;
- a componentwise `Steps x Queries` model and its Nat projection;
- writer bind charging each component once and random computations retaining
  the value/path-cost joint distribution;
- typed signature sums, dependent result types, handler dispatch, erasure laws,
  and independent operation bounds;
- exact `Program.Execution`, input-dependent bounds, sequential addition,
  branch join, and value-preserving machine conversion;
- ElGamal's sampler, two scalar multiplications, addition, exact path formula,
  existing numerical upper bound, erased PMF, timed adapter, and correctness;
- OTP construction without `UnusedScalar`, including its perfect one-time
  security theorem;
- DLog/DDH sampling erasure, exact primitive costs, and unchanged assumption
  declarations;
- oracle erasure, traces, per-name and total-query bounds, exact internal cost,
  and corrected coarse composition;
- unchanged adversary domain for legacy `Hard` and related security predicates.

Final static checks:

```text
rg -n '\b(sorry|admit)\b|^\s*axiom\b|\bunsafe\b' Crypto CryptoTest
git diff --check
git status --short
```

### Final verification evidence

The completed workspace was checked in increasing scope:

| Command | Result |
| --- | --- |
| focused generic-cost, Program, Oracle, resource-bound, OTP, DLog, DDH, and ElGamal targets | passed (3190 jobs) |
| `lake build Crypto` | passed (1778 jobs, no warnings) |
| `lake build CryptoTest` | passed (3193 jobs, no warnings) |
| `lake build` | passed (3223 jobs, no warnings) |
| trust-marker scan over `Crypto` and `CryptoTest` | no `sorry`, `admit`, `axiom`, or `unsafe` hits |
| `git diff --check` | passed |
| root test-import audit | every regression file is imported by `CryptoTest.lean` |

The stable GameBased, Advantage, correctness/security-property, and UC files
were audited against `d8ba0802be01`. Their security predicates and arbitrary
legacy PPT-machine quantification domains are unchanged. DLog/DDH assumption
definitions and OTP/ElGamal correctness conclusions retain their original
strength; adapter and scoped-instance changes only connect them to the new
exact interpreters.

### Compatibility and deferred work

- `Cost`, `Costed`, and `RandCosted` remain the Nat specializations, and the
  old operation-cost typeclasses and backend constructors remain as one-stage
  compatibility adapters. Repository algorithms take exact costs from
  `CostedAlgebra.exec`; there are no remaining concrete internal users that
  treat the legacy classes as a second authoritative cost source.
- Legacy `OracleProgram` remains unit-cost. Generic explicit query costs use
  `OracleProgramT`; optional total-query certificates are analysis data and do
  not narrow the legacy adversary structures.
- Expected cost, tail bounds, parallel-resource composition, first-order
  machine syntax, and an IND-CPA-from-DDH reduction are intentionally deferred.
  The current higher-order `Program` accounts for all explicit calls but does
  not attempt to cost arbitrary host-language computation inside continuations.
- New `noncomputable` declarations are limited to PMF/finite-distribution
  constructions, lifted handlers, or proof-carrying bound packages; none is a
  trust escape hatch.

Review the final diff for duplicate cost sources, `Program.cost` drift, dummy
types, blanket global instances, typeclass diamonds, changed probabilities,
weakened theorem statements, simp loops, dead imports, and unreferenced tests.
Any newly necessary `noncomputable` declaration must be attributable to PMF or
finite-distribution construction and documented in the milestone report.

## Risks and mitigations

| Risk | Consequence | Mitigation |
| --- | --- | --- |
| Repacking DLog/DDH parameters changes dependent projections | casts replace formerly definitional equalities | migrate ElGamal first through adapters; introduce the shared hierarchy only after exact erasure tests pass |
| A generic cost model accidentally assumes commutativity | invalid model for ordered sequential resources | require only `AddMonoid`; test a deliberately componentwise resource model |
| Two evaluators become independent | value semantics may silently differ from exact semantics | define `valueDist` exclusively as cost erasure and prove adapter erasure theorems |
| Program-derived machines replace arbitrary PPT adversaries | security definitions become weaker | preserve legacy machine types and security predicate bodies; provide embeddings only |
| Runtime is reused as a query bound for generic explicit-cost programs | zero-cost queries invalidate the bound and could expand an adversary domain | keep explicit costs out of legacy machine syntax; use an independent total-query certificate in coarse composition |
| Global algebra instances overlap Mathlib instances | elaboration ambiguity or proof instability | use explicit projections and local/scoped instances |
| Old `rfl` proofs cease to elaborate | tempting but invalid theorem weakening | replace them with explicit erasure/adapter equivalences and preserve conclusions |
| Compatibility wrappers remain indefinitely | duplicate APIs and sources of truth | track every wrapper here and remove internal uses once `rg` reports none |
| Existing dirty work is overwritten | loss of user work and misleading validation | inspect the targeted diff before every milestone and never reset/revert it |

## Decision log

| Date | Decision | Reason |
| --- | --- | --- |
| 2026-08-03 | Treat the current costed-oracle changes as part of the migration baseline. | They are user-owned work already present in the checkout. |
| 2026-08-03 | Generalize the exact cost core while retaining Nat compatibility. | This supports resource vectors without breaking current machines and APIs. |
| 2026-08-03 | Use typed heterogeneous primitive signatures for `Program`. | Algorithms need capability-specific and dependent operations without dummy types. |
| 2026-08-03 | Execute a full-repository migration through buildable milestones. | All concrete algorithms should converge on one architecture while keeping failures localized. |
| 2026-08-03 | Keep existing semantic security predicates and arbitrary PPT quantification unchanged. | Replacing them by program-derived machines would weaken theorem strength. |
| 2026-08-03 | Keep probability semantics orthogonal to exact resource and asymptotic layers. | Joint path costs are useful, while expected/tail complexity is outside this migration. |
| 2026-08-03 | Do not add parallel-cost semantics in this migration. | It is not required by current algorithms; the generic core leaves room for a later capability. |
| 2026-08-03 | Keep total-query evidence in a separate certificate rather than adding fields to legacy oracle machines. | The machine types are part of the security adversary domain; changing their required fields would narrow that domain. |
| 2026-08-03 | Preserve exact Oracle total cost in execution order and require an explicit exchange law only for grouped coarse bounds. | A noncommutative sequential monoid does not justify moving all local work before all oracle work. |
| 2026-08-04 | Keep legacy `OracleProgram` exactly unit-cost and place explicit costs only in `OracleProgramT`. | Adding zero-cost calls to legacy syntax would make polynomial runtime insufficient to bound queries and would expand the `PPTOracleMachine` adversary domain. |

## Completion report requirements

The final implementation report must include:

1. the final architecture and declaration migration map;
2. exact files changed, including which pre-existing edits were preserved;
3. reused, adapted, deprecated, and removed declarations;
4. narrow and full build commands with their outcomes;
5. confirmation that security predicate statements and adversary domains did
   not change;
6. trust audit results and any justified `noncomputable` additions;
7. remaining compatibility wrappers, technical debt, and intentionally
   deferred resource notions.
