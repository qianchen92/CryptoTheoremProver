# Crypto

`Crypto` is an experimental Lean library for formalizing cryptographic
constructions, security games, complexity bounds, assumptions, and reductions.

The current organization is intentionally layered. Lower layers contain general
semantic infrastructure; higher layers define cryptographic objects and their
security notions. This keeps primitive-specific definitions from leaking into
the reusable core, while still allowing concrete constructions to share one
game, oracle, cost, and asymptotic vocabulary.

## Organization

The overall architecture is reasonable for the library's current stage: it
separates foundational notions, executable/game semantics, complexity models,
security notions, assumptions, primitives, protocols, and proof organization.
Some top-level areas are still placeholders, but the boundaries are useful and
should be preserved as the library grows.

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

Semantic complexity notions used by adversaries and constructions.

- `Machine` defines deterministic, probabilistic, timed, and PPT machines.
- `CostBound` connects core costed computations to polynomial bounds.
- `PPT` adds oracle PPT machines with polynomial runtime and query bounds.

This layer may depend on `Foundation` and `Core`, but should not depend on
specific primitives or assumptions.

### `Crypto.Security`

Generic security notions that are not tied to one primitive.

- `Advantage` defines acceptance probability and distinguishing advantage for
  boolean games.
- `Indistinguishability` states negligible distinguishing advantage.
- `Hybrid` records finite hybrid sequences.
- `Reduction` records adversary transformations.

Primitive-specific games should live under the corresponding primitive; shared
game combinators and proof patterns belong here.

### `Crypto.Assumption`

Computational assumptions, organized by family.

For example, discrete-logarithm assumptions belong under `Assumption.DL`. This
area is currently skeletal, but it is the right place for assumption statements
and their associated adversary/game interfaces.

### `Crypto.Primitive`

Cryptographic primitives and their primitive-specific syntax, correctness, and
security definitions.

The current encryption hierarchy contains:

- `Primitive.Encryption.SymmetricEncryption.Syntax`
- `Primitive.Encryption.SymmetricEncryption.Correctness`
- `Primitive.Encryption.SymmetricEncryption.OneTime`

This placement is appropriate: the symmetric-encryption interface and one-time
left-or-right security game are specific to that primitive, while the generic
notions they use remain in `Core`, `Complexity`, and `Security`.

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
- Put adversary and machine models in `Complexity`.
- Put generic advantage, indistinguishability, hybrid, and reduction notions in
  `Security`.
- Put assumption families in `Assumption/<family>/`.
- Put primitive-specific syntax, correctness, and security games in
  `Primitive/<kind>/<primitive>/`.
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
