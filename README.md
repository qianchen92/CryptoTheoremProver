# Crypto

`Crypto` is an experimental Lean library for building reusable, machine-checked
cryptographic security proofs. The project aims to provide a small but coherent
foundation for defining cryptographic schemes, security games, oracle access,
PPT machines, asymptotic bounds, assumptions, reductions, and proof patterns.

The library is organized around game-based security proofs. Core semantic
notions such as randomized computations, games, oracles, cost models, and
algebraic operations live in reusable lower layers. Cryptographic primitives,
protocols, and assumptions build on those layers without duplicating the common
machinery. This keeps primitive-specific definitions local while still allowing
different constructions to share the same vocabulary for games, complexity, and
advantages.

The current codebase is intentionally minimal. It prioritizes stable boundaries
and clear interfaces over a large catalog of primitives. The symmetric
encryption hierarchy already includes syntax, correctness, and a one-time
left-or-right security game; additional primitives and proof libraries can be
added on top of the same framework.

## Organization

The project is intentionally layered. Lower layers contain general semantic
infrastructure; higher layers define cryptographic objects, assumptions,
protocols, and proof organization.

```text
Crypto/
  Basic.lean
  Foundation/
    SecurityParameter.lean
    Asymptotics.lean
  Core/
    Cost/
    Algebra/
    Oracle/
    Computation.lean
    Game.lean
  Complexity/
    Machine.lean
    CostBound.lean
    PPT.lean
  Security/
    Advantage.lean
    Indistinguishability.lean
    Hybrid.lean
    Reduction.lean
  Assumption/
    DL/
  Primitive/
    Encryption/
      SymmetricEncryption/
  Protocol/
  Proof/
```

### `Crypto.Foundation`

Foundational definitions with minimal project dependencies.

- `SecPar` is the shared security parameter.
- `IsPolyBounded` and `IsNegligible` define the asymptotic vocabulary used by
  complexity and security definitions.

Files in this layer should not depend on cryptographic primitives, security
games, or machine models.

### `Crypto.Core`

Reusable semantic infrastructure for cryptographic formalization.

- `Core.Cost` defines cost models and costed randomized computations.
- `Core.Algebra` contains algebraic structures and costed algebraic operations.
- `Core.Oracle` defines oracle interfaces and stateful oracle environments.
- `Computation` packages security-parameter-indexed randomized computations
  with cost information.
- `Game` packages security experiments as security-parameter-indexed
  distributions.

This layer should remain primitive-agnostic. It is the shared substrate for
security games, reductions, and construction-specific definitions.

### `Crypto.Complexity`

Semantic complexity notions used by constructions and security games.

- `Machine` defines deterministic, probabilistic, timed, and PPT machines.
- `CostBound` connects core costed computations to polynomial bounds.
- `PPT` adds oracle PPT machines with security-parameter-indexed oracle specs,
  polynomial runtime, and uniform polynomial query bounds.

This layer may depend on `Foundation` and `Core`, but should not depend on
specific primitives or assumptions.

### `Crypto.Security`

Generic security notions that are not tied to one primitive.

- `Advantage` defines acceptance probability and distinguishing advantage for
  boolean games.
- `Indistinguishability` states negligible distinguishing advantage.
- `Hybrid` records finite hybrid sequences.
- `Reduction` records transformations between machine families or other
  proof-relevant types.

Primitive-specific games should live under the corresponding primitive; shared
game combinators and proof patterns belong here.

### `Crypto.Assumption`

Computational assumptions, organized by family.

For example, discrete-logarithm assumptions belong under `Assumption.DL`. This
area is currently skeletal, but it is the right place for assumption statements
and their associated machine/game interfaces.

### `Crypto.Primitive`

Cryptographic primitives and their primitive-specific syntax, correctness, and
security definitions.

The current encryption hierarchy contains:

- `Primitive.Encryption.SymmetricEncryption.Syntax`
- `Primitive.Encryption.SymmetricEncryption.UC`
- `Primitive.Encryption.SymmetricEncryption.Properties`
- `Primitive.Encryption.SymmetricEncryption.Instantiations`

The main interface is
`Crypto.Primitive.Encryption.SymmetricEncryption.Scheme Param Key Message Ciphertext`.
`setup` samples public parameters from the security parameter; `Key`, `Message`,
and `Ciphertext` are then indexed by those public parameters. Correctness and
one-time left-or-right security live in the same namespace because they are
definitions about symmetric-encryption schemes. The generic notions they use
remain in `Core`, `Complexity`, and `Security`. The current instantiations
include a group-based one-time pad whose setup exposes the finite nonempty
additive group chosen for the security parameter.

### `Crypto.Protocol`

Protocol-level definitions that compose primitives or model interactive
protocols. This namespace is currently reserved for future protocol
formalizations. Protocol code may depend on primitives, assumptions, security,
complexity, and core infrastructure as needed.

### `Crypto.Proof`

Reusable proof infrastructure and proof organization. This namespace is
currently reserved for shared proof patterns, automation, and library-level
proof utilities that do not naturally belong to one primitive or assumption.

## Import Policy

`Basic.lean` files are aggregation modules. Import them when a caller wants a
whole layer; otherwise prefer importing the narrow file that provides the needed
definition.

The intended dependency direction is:

```text
Foundation
  -> Core
  -> Complexity / Security
  -> Assumption / Primitive
  -> Protocol / Proof
```

This is a guideline rather than a total order. For example, `Security` and
`Complexity` both depend on `Core`, and primitive-specific security games may
depend on both `Security` and `Complexity`. Avoid dependencies from lower layers
back into higher layers.

## Adding New Material

- Put universal mathematical or asymptotic vocabulary in `Foundation`.
- Put reusable game, oracle, computation, cost, or algebra semantics in `Core`.
- Put machine models, including PPT and oracle PPT machines, in `Complexity`.
- Put generic advantage, indistinguishability, hybrid, and reduction notions in
  `Security`.
- Put assumption families in `Assumption/<family>/`.
- Put primitive-specific syntax, correctness, and security games in
  `Primitive/<kind>/<primitive>/`, with `Syntax.lean` and `UC.lean` as direct
  files and `Properties/` and `Instantiations/` as subdirectories.
- Put composed or interactive protocols in `Protocol`.
- Put shared proof utilities in `Proof`.

When adding polymorphic Lean declarations, use descriptive universe names such
as `uIn`, `uOut`, `uQuery`, `uResponse`, `uValue`, `uMapped`, `uScalar`,
`uModule`, and `uGroup`, rather than bare `u`, `v`, or `w`.

## Status

The library is early-stage. The current hierarchy is sound as a working
architecture, but several namespaces are intentionally sparse. The next useful
refinements are to fill out assumption interfaces, add more primitive families,
and move common proof patterns into `Crypto.Security` or `Crypto.Proof` once
they repeat across multiple constructions.
