# Project Conventions

## Lean Universe Names

- Use meaningful universe names that describe the role of the corresponding type parameter.
- Avoid bare `u`, `v`, or `w` in project code except for very small local experiments that are not committed.
- Reuse established role names where applicable:
  - `uIn`, `uOut` for input/output types.
  - `uQuery`, `uResponse` for oracle query/response types.
  - `uValue`, `uMapped` for value and mapped-value types.
  - `uScalar`, `uModule`, `uGroup` for algebraic scalar/module/group types.
- When adding a new polymorphic definition, choose universe names from the domain vocabulary of that definition and keep them consistent across the declaration, namespace variables, and related theorems.
