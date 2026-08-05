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
- Put parameterized algorithms that construct abstract primitives or protocols
  in the separate `CryptoConstruction` library. It may depend on `Crypto` but
  must not depend on a concrete backend instantiation.
- Reserve a future `CryptoInstantiation` library for fixed representations,
  implementation backends, and their instance-specific cost certificates.
- `Crypto` must not import `CryptoConstruction` or `CryptoInstantiation`.
  `CryptoConstruction` must not import `CryptoInstantiation`.
- Each library's `Basic.lean` aggregates only that library. Import
  `CryptoConstruction.Basic` explicitly when parameterized constructions are
  required.

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
