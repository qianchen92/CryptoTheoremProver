# Crypto

`Crypto` is an experimental Lean library for building reusable, machine-checked
cryptographic security proofs. The project aims to provide a small but coherent
foundation for defining cryptographic schemes, security games, oracle access,
PPT machines, asymptotic bounds, assumptions, reductions, and proof patterns.

The library is organized around game-based security proofs. Shared computation
semantics such as randomized computations, games, oracles, cost models, and
algebraic operations live in reusable lower layers. Cryptographic primitives,
protocols, and assumptions build on those layers without duplicating the common
machinery. This keeps primitive-specific definitions local while still allowing
different constructions to share the same vocabulary for games, complexity, and
advantages.

The current codebase is intentionally minimal. It prioritizes stable boundaries
and clear interfaces over a large catalog of primitives. The symmetric
encryption hierarchy already includes syntax, correctness, one-time
left-or-right security, and a group-based one-time pad with correctness and
perfect one-time security proofs. Additional primitives and proof libraries can
be added on top of the same framework.

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
      Game.lean
    Complexity/
      Machine.lean
      CostBound.lean
    GameBased/
      Advantage.lean
      Indistinguishability.lean
      Hybrid.lean
      Reduction.lean
    ProofPattern/
  Assumption/
    DL/
  Primitive/
    Encryption/
      SymmetricEncryption/
  Protocol/
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

- `Computation.Cost` defines cost models and costed randomized computations.
- `Computation.Algebra` contains algebraic structures and costed operations.
- `Computation.Oracle` defines oracle interfaces and stateful environments.
- `Randomized` packages security-parameter-indexed randomized computations
  with cost information.
- `Game` packages security experiments as security-parameter-indexed
  distributions.

This layer should remain primitive-agnostic. It is the shared substrate for
security games, reductions, and construction-specific definitions.

### `Crypto.Infrastructure.Complexity`

Semantic complexity notions used by constructions and security games.

- `Machine` defines deterministic, probabilistic, timed, PPT, oracle, and
  oracle PPT machines.
- `CostBound` connects core costed computations to polynomial bounds.
- Oracle PPT machines carry security-parameter-indexed oracle specs,
  polynomial runtime, and uniform polynomial query bounds.

This layer may depend on `Crypto.Infrastructure.Asymptotic` and
`Crypto.Infrastructure.Computation`, but should not depend on specific
primitives or assumptions.

### `Crypto.Infrastructure.GameBased`

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
definitions about symmetric-encryption schemes. `OneTimeSecure` is the PPT
notion, while `PerfectOneTimeSecure` quantifies over unbounded oracle machines
and requires exact zero advantage. The generic notions they use remain in
`Infrastructure.Computation`, `Infrastructure.Complexity`, and
`Infrastructure.GameBased`.

The current instantiations include a group-based one-time pad. Its setup
exposes the finite nonempty additive group chosen for the security parameter;
the construction encrypts by addition and decrypts by subtraction. The library
proves both correctness and perfect one-time security for this construction,
and derives PPT one-time security from the perfect theorem.

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
  -> Assumption / Primitive
  -> Protocol / Infrastructure.ProofPattern
```

This is a guideline rather than a total order. For example,
`Infrastructure.GameBased` and `Infrastructure.Complexity` both depend on
`Infrastructure.Computation`, and primitive-specific security games may depend
on both game-based and complexity infrastructure. Avoid dependencies from lower
layers back into higher layers.

## Adding New Material

- Put infrastructure code under `Infrastructure`.
- Put security-parameter and asymptotic vocabulary in `Infrastructure.Asymptotic`.
- Put reusable game, oracle, computation, cost, or algebra semantics in
  `Infrastructure.Computation`.
- Put machine models, including PPT, oracle, and oracle PPT machines, in
  `Infrastructure.Complexity`.
- Put generic advantage, indistinguishability, hybrid, and reduction notions in
  `Infrastructure.GameBased`.
- Put assumption families in `Assumption/<family>/`.
- Put primitive-specific syntax, correctness, and security games in
  `Primitive/<kind>/<primitive>/`, with `Syntax.lean` and `UC.lean` as direct
  files and `Properties/` and `Instantiations/` as subdirectories.
- Put composed or interactive protocols in `Protocol`.
- Put shared proof utilities in `Infrastructure.ProofPattern`.

When adding polymorphic Lean declarations, use descriptive universe names such
as `uIn`, `uOut`, `uQuery`, `uResponse`, `uValue`, `uMapped`, `uScalar`,
`uModule`, and `uGroup`, rather than bare `u`, `v`, or `w`.

## Status

The library is early-stage. The current hierarchy is sound as a working
architecture, but several namespaces are intentionally sparse. The next useful
refinements are to fill out assumption interfaces, add more primitive families,
connect costed implementations to concrete constructions, and move common proof
patterns into `Crypto.Infrastructure.GameBased` or
`Crypto.Infrastructure.ProofPattern` once they repeat across multiple
constructions.
