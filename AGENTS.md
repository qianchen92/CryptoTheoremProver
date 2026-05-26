# Project Conventions

## Lean Module Names

- Prefer domain-specific top-level names over broad containers. Use names such
  as `Assumption`, `Primitive`, and `Protocol` for first-level cryptographic
  domains.
- Put reusable infrastructure under `Crypto.Infrastructure`, using submodules
  such as `Asymptotic`, `Computation`, `Complexity`, `GameBased`, and
  `ProofPattern` when they describe the actual role of the declarations.
- Avoid adding new broad namespaces such as `Foundation`, `Core`, `Security`,
  or `Proof` unless the module has a precisely documented scope that cannot be
  expressed with a narrower name.
- Aggregation modules should be named `Basic.lean`; implementation modules
  should describe the concepts they export, such as `Randomized`, `Oracle`, or
  `Advantage`.

## Lean Universe Names

- Use meaningful universe names that describe the role of the corresponding type parameter.
- Avoid bare `u`, `v`, or `w` in project code except for very small local experiments that are not committed.
- Reuse established role names where applicable:
  - `uIn`, `uOut` for input/output types.
  - `uQuery`, `uResponse` for oracle query/response types.
  - `uValue`, `uMapped` for value and mapped-value types.
  - `uScalar`, `uModule`, `uGroup` for algebraic scalar/module/group types.
- When adding a new polymorphic definition, choose universe names from the domain vocabulary of that definition and keep them consistent across the declaration, namespace variables, and related theorems.
