#!/usr/bin/env python3
"""Reject unresolved imports and violations of the project import hierarchy.

This check is intentionally independent of Lean's build graph. It enforces the
Infrastructure hierarchy, the trusted `CryptoLib.Program` core order, and the
package direction from `CryptoLib.Core` definitions through the sibling
`CryptoLib.Algebra`, `CryptoLib.Program`, `CryptoLib.Oracle`, `CryptoLib.UC`,
`CryptoLib.Assumption`, `CryptoLib.Primitive`, and `CryptoLib.Protocol` layers
to `CryptoLib.Instantiation` realizations. `CryptoLib.Backend` remains a
reserved future layer and is intentionally not part of the current default
target set.
Exact module-name membership additionally catches case mismatches that can pass
on a case-insensitive macOS checkout but fail on GitHub's Linux runners.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
INFRA_ROOT = ROOT / "CryptoLib" / "Core" / "Infrastructure"
IMPORT_RE = re.compile(r"^(?:public\s+)?import\s+(.+?)\s*$")
MODULE_RE = re.compile(r"^[A-Za-z0-9_.'-]+$")
PREFIX = "CryptoLib.Core.Infrastructure."
PROJECT_PACKAGES = (
    "CryptoLib.Core",
    "CryptoLib.Algebra",
    "CryptoLib.Program",
    "CryptoLib.Oracle",
    "CryptoLib.UC",
    "CryptoLib.Assumption",
    "CryptoLib.Primitive",
    "CryptoLib.Protocol",
    "CryptoLib.Instantiation",
    "CryptoLib.Backend",
    "CryptoLib.Test",
)

PRODUCTION_PACKAGE_LEVEL = {
    "CryptoLib.Core": 0,
    "CryptoLib.Algebra": 1,
    "CryptoLib.Program": 2,
    # These are sibling post-Program layers. UC and Protocol intentionally
    # share a level because protocol components are built on UC ITMs while UC
    # composition consumes those components.
    "CryptoLib.Oracle": 3,
    "CryptoLib.UC": 3,
    "CryptoLib.Assumption": 3,
    "CryptoLib.Primitive": 3,
    "CryptoLib.Protocol": 3,
    "CryptoLib.Instantiation": 4,
    "CryptoLib.Backend": 5,
}

# The operational-admission layer consumes the trusted first-order core so that
# internally validated reified code remains a closed constructor of `ValidCode`.
ALLOWED_CROSS_PACKAGE_IMPORTS = {
    ("CryptoLib.Core.Infrastructure.Complexity.Operational", "CryptoLib.Program.Core"),
    # Narrow complexity adapter/aggregation bridges. The generic machine core
    # remains in Core, while oracle refinements live in Oracle.
    ("CryptoLib.Core.Infrastructure.Complexity.Basic", "CryptoLib.Oracle.Complexity.Implementation"),
    ("CryptoLib.Core.Infrastructure.Complexity.Basic", "CryptoLib.Oracle.Complexity.Machine"),
    ("CryptoLib.Core.Infrastructure.Complexity.Operational", "CryptoLib.Oracle.Complexity.MachineCore"),
    ("CryptoLib.Core.Infrastructure.GameBased.OracleDistinguishing", "CryptoLib.Oracle.Complexity.Machine"),
}


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def strip_lean_comments(source: str) -> str:
    """Remove nested block comments and line comments, preserving newlines."""

    result: list[str] = []
    index = 0
    block_depth = 0
    while index < len(source):
        if block_depth == 0 and source.startswith("--", index):
            newline = source.find("\n", index)
            if newline == -1:
                break
            result.append("\n")
            index = newline + 1
        elif source.startswith("/-", index):
            block_depth += 1
            index += 2
        elif block_depth > 0 and source.startswith("-/", index):
            block_depth -= 1
            index += 2
        elif block_depth > 0:
            if source[index] == "\n":
                result.append("\n")
            index += 1
        else:
            result.append(source[index])
            index += 1
    return "".join(result)


def imports_from_text(source: str) -> list[str]:
    """Parse every module named by Lean `import` or `public import` commands."""

    result: list[str] = []
    for line in strip_lean_comments(source).splitlines():
        match = IMPORT_RE.match(line.strip())
        if match:
            modules = match.group(1).split()
            result.extend(module for module in modules if MODULE_RE.fullmatch(module))
    return result


def imports(path: Path) -> list[str]:
    return imports_from_text(path.read_text(encoding="utf-8"))


def project_package(module: str) -> str | None:
    """Return the project package owning a module name, including future roots."""

    for package in PROJECT_PACKAGES:
        if module == package or module.startswith(package + "."):
            return package
    return None


def is_project_module(module: str) -> bool:
    return project_package(module) is not None


def is_higher_level_project_import(module: str) -> bool:
    """Infrastructure may depend only on other CryptoLib.Core.Infrastructure modules."""

    is_infrastructure = (
        module == "CryptoLib.Core.Infrastructure" or module.startswith(PREFIX)
    )
    return is_project_module(module) and not is_infrastructure


def is_allowed_cross_package_import(source: str, target: str) -> bool:
    if (source, target) in ALLOWED_CROSS_PACKAGE_IMPORTS:
        return True
    return False


def project_import_hierarchy_error(source: str, target: str) -> str | None:
    """Enforce package order plus the one core-only operational bridge."""

    source_package = project_package(source)
    target_package = project_package(target)
    if is_allowed_cross_package_import(source, target):
        return None
    if source_package in PRODUCTION_PACKAGE_LEVEL and target_package == "CryptoLib.Test":
        return f"production package imports CryptoLib.Test: {source} -> {target}"
    if (
        source_package in PRODUCTION_PACKAGE_LEVEL
        and target_package in PRODUCTION_PACKAGE_LEVEL
        and PRODUCTION_PACKAGE_LEVEL[target_package]
          > PRODUCTION_PACKAGE_LEVEL[source_package]
    ):
        return f"lower package imports higher package: {source} -> {target}"
    return None


def parser_regression_errors() -> list[str]:
    """Keep the accepted Lean import forms and project boundary under test."""

    fixture = """\
/- import CryptoLib.Assumption.Hidden
   /- nested import CryptoLib.Test.Hidden -/
-/
public import CryptoLib.Core.Infrastructure.SecurityParameter CryptoLib.Primitive.Bad CryptoLib.Program.Algebra.Bad CryptoLib.Instantiation.Primitive.Bad -- tail
import Mathlib.Data.Nat.Basic
"""
    expected = [
        "CryptoLib.Core.Infrastructure.SecurityParameter",
        "CryptoLib.Primitive.Bad",
        "CryptoLib.Program.Algebra.Bad",
        "CryptoLib.Instantiation.Primitive.Bad",
        "Mathlib.Data.Nat.Basic",
    ]
    errors: list[str] = []
    parsed = imports_from_text(fixture)
    if parsed != expected:
        errors.append(f"internal import-parser regression: {parsed!r}")
    if not is_higher_level_project_import("CryptoLib.Primitive.Bad"):
        errors.append("internal boundary regression: CryptoLib.Primitive.Bad accepted")
    if not is_higher_level_project_import("CryptoLib.Test.Bad"):
        errors.append("internal boundary regression: CryptoLib.Test.Bad accepted")
    if not is_higher_level_project_import("CryptoLib.Instantiation.Primitive.Bad"):
        errors.append("internal boundary regression: CryptoLib.Instantiation accepted")
    if not is_higher_level_project_import("CryptoLib.Program.Algebra.Bad"):
        errors.append("internal boundary regression: CryptoLib.Program accepted")
    if is_higher_level_project_import("CryptoLib.Core.Infrastructure.Computation.Basic"):
        errors.append("internal boundary regression: Infrastructure rejected")
    if project_package("CryptoLib.Instantiation.Primitive.Basic") != "CryptoLib.Instantiation":
        errors.append("internal boundary regression: CryptoLib.Instantiation not recognized")
    if project_package("CryptoLib.Program.Algebra.Basic") != "CryptoLib.Program":
        errors.append("internal boundary regression: CryptoLib.Program not recognized")
    if project_package("CryptoLib.Assumption.DL.DDH") != "CryptoLib.Assumption":
        errors.append("internal boundary regression: CryptoLib.Assumption not recognized")
    if project_package("CryptoLib.Backend.Basic") != "CryptoLib.Backend":
        errors.append("internal boundary regression: CryptoLib.Backend not recognized")
    if project_import_hierarchy_error(
        "CryptoLib.Core.Infrastructure.Computation.Basic",
        "CryptoLib.Program.Core",
    ) is None:
        errors.append("internal boundary regression: core-to-program accepted")
    if project_import_hierarchy_error(
        "CryptoLib.Core.Infrastructure.Complexity.Operational",
        "CryptoLib.Program.Core",
    ) is not None:
        errors.append("internal boundary regression: operational-to-core rejected")
    if project_import_hierarchy_error(
        "CryptoLib.Core.Infrastructure.Complexity.Machine",
        "CryptoLib.Program.Core",
    ) is None:
        errors.append("internal boundary regression: broad core-to-program-core accepted")
    if project_import_hierarchy_error(
        "CryptoLib.Program.Algebra.Basic",
        "CryptoLib.Instantiation.Primitive.Encryption.Basic",
    ) is None:
        errors.append("internal boundary regression: program-to-instantiation accepted")
    if project_import_hierarchy_error(
        "CryptoLib.Program.Algebra.Basic",
        "CryptoLib.Assumption.DL.DDH",
    ) is None:
        errors.append("internal boundary regression: program-to-assumption accepted")
    if project_import_hierarchy_error(
        "CryptoLib.Assumption.Program.DL.DDH",
        "CryptoLib.Program.Algebra.ScalarAction",
    ) is not None:
        errors.append("internal boundary regression: assumption-to-program rejected")
    if project_import_hierarchy_error(
        "CryptoLib.Core.Infrastructure.Computation.Basic",
        "CryptoLib.Instantiation.Primitive.Basic",
    ) is None:
        errors.append("internal boundary regression: Infrastructure-to-instantiation accepted")
    if project_import_hierarchy_error(
        "CryptoLib.Instantiation.Primitive.Basic",
        "CryptoLib.Backend.Basic",
    ) is None:
        errors.append("internal boundary regression: instantiation-to-backend accepted")
    if project_import_hierarchy_error(
        "CryptoLib.Instantiation.Primitive.Basic",
        "CryptoLib.Program.Algebra.Basic",
    ) is not None:
        errors.append("internal boundary regression: instantiation-to-program rejected")
    if project_import_hierarchy_error(
        "CryptoLib.Program.Algebra.Basic",
        "CryptoLib.Primitive.Basic",
    ) is None:
        errors.append("internal boundary regression: program-to-primitive accepted")
    if first_order_core_import_error(
        "CryptoLib.Program.Type", "CryptoLib.Program.Signature"
    ) is None:
        errors.append("internal boundary regression: first-order upward import accepted")
    if first_order_core_import_error(
        "CryptoLib.Program.Bounds", "CryptoLib.Program.Type"
    ) is not None:
        errors.append("internal boundary regression: first-order downward import rejected")
    if first_order_core_part("CryptoLib.Program.Algebra.AdditiveGroup") is not None:
        errors.append("internal boundary regression: adapter mistaken for core module")
    return errors


def top_layer(module: str) -> str:
    suffix = module.removeprefix(PREFIX)
    return suffix.split(".", 1)[0]


FORBIDDEN_TOP_IMPORTS = {
    "SecurityParameter": {
        "Probability", "Computation", "Asymptotic", "Complexity", "GameBased", "UC"
    },
    "Probability": {
        "SecurityParameter", "Computation", "Asymptotic", "Complexity", "GameBased", "UC"
    },
    "Computation": {"Asymptotic", "Complexity", "GameBased", "UC"},
    "Asymptotic": {"Probability", "Computation", "Complexity", "GameBased", "UC"},
    "Complexity": {"GameBased", "UC"},
    "GameBased": {"UC"},
    "UC": set(),
}


SUBSYSTEM_ORDER = {
    "Probability": {
        "Uniform": 0,
        "Basic": 99,
    },
    "Computation.Cost": {
        "Model": 0,
        "Writer": 1,
        "Randomized": 2,
        "PathBound": 3,
        "Measure": 1,
        "Projection": 3,
        "Basic": 99,
    },
    "Computation.Oracle": {
        "Spec": 0,
        "Trace": 1,
        "Program": 2,
        "Handler": 3,
        "Interpreter": 4,
        "Bounds": 5,
        "Composition": 6,
        "Basic": 99,
    },
    "Complexity": {
        "CostBound": 0,
        "Operational": 1,
        "Machine": 2,
        "OracleImplementation": 3,
        "OracleMachine": 4,
        "Basic": 99,
    },
    "GameBased": {
        "Advantage": 0,
        "Indistinguishability": 1,
        "Hybrid": 1,
        "Distinguishing": 2,
        "Search": 2,
        "OracleDistinguishing": 3,
        "Basic": 99,
    },
    "UC": {
        "Session": 0,
        "Port": 1,
        "Message": 2,
        "ITM": 3,
        "Corruption": 4,
        "Configuration": 5,
        "Kernel": 6,
        "Complexity": 7,
        "Protocol": 8,
        "Functionality": 8,
        "Composition": 9,
        "Execution": 10,
        "Security": 11,
        "Context": 12,
        "Layered": 13,
        "Basic": 99,
    },
}


COMPUTATION_ALLOWED_IMPORTS = {
    "Cost": {"Cost"},
    "Oracle": {"Cost", "Oracle"},
    "Randomized": {"Cost"},
    "Game": set(),
    "Basic": {
        "Cost", "Oracle",
        "Randomized", "Game", "Basic",
    },
}


def computation_part(module: str) -> str | None:
    prefix = PREFIX + "Computation."
    if not module.startswith(prefix):
        return None
    return module.removeprefix(prefix).split(".", 1)[0]


def subsystem_part(module: str, subsystem: str) -> str | None:
    prefix = PREFIX + subsystem + "."
    if not module.startswith(prefix):
        return None
    return module.removeprefix(prefix).split(".", 1)[0]


FIRST_ORDER_CORE_ORDER = {
    "Type": 0,
    "Signature": 1,
    "Algebra": 2,
    "Syntax": 3,
    "Operation": 3,
    "Builder": 4,
    "Semantics": 4,
    "Validation": 4,
    "Execution": 5,
    "Bounds": 5,
    "Core": 99,
}


def first_order_core_part(module: str) -> str | None:
    prefix = "CryptoLib.Program."
    if not module.startswith(prefix):
        return None
    suffix = module.removeprefix(prefix)
    if "." in suffix or suffix not in FIRST_ORDER_CORE_ORDER:
        return None
    return suffix


def first_order_core_import_error(source: str, target: str) -> str | None:
    source_core = first_order_core_part(source)
    target_core = first_order_core_part(target)
    if source_core is None or target_core is None:
        return None
    if (
        FIRST_ORDER_CORE_ORDER[target_core] > FIRST_ORDER_CORE_ORDER[source_core]
        and source_core != "Core"
    ):
        return f"first-order core upward import: {source} -> {target}"
    return None


def project_source_files() -> list[Path]:
    """Collect every currently present project root and package source tree."""

    source_root = ROOT / "CryptoLib"
    return sorted(source_root.rglob("*.lean"))


def main() -> int:
    infrastructure_files = sorted(INFRA_ROOT.rglob("*.lean"))
    infrastructure_graph = {
        module_name(path): imports(path) for path in infrastructure_files
    }
    errors = parser_regression_errors()

    project_files = project_source_files()
    project_graph = {module_name(path): imports(path) for path in project_files}
    project_modules = {module_name(path) for path in project_files}
    for source, targets in project_graph.items():
        for target in targets:
            if is_project_module(target) and target not in project_modules:
                errors.append(
                    f"missing or case-mismatched project import: {source} -> {target}"
                )
            hierarchy_error = project_import_hierarchy_error(source, target)
            if hierarchy_error is not None:
                errors.append(hierarchy_error)
            core_error = first_order_core_import_error(source, target)
            if core_error is not None:
                errors.append(core_error)

    for source, targets in infrastructure_graph.items():
        source_layer = top_layer(source)
        forbidden = FORBIDDEN_TOP_IMPORTS.get(source_layer, set())
        for target in targets:
            if (
                is_higher_level_project_import(target)
                and not is_allowed_cross_package_import(source, target)
            ):
                errors.append(f"higher-level project import: {source} -> {target}")

            if not target.startswith(PREFIX):
                continue

            target_layer = top_layer(target)
            if target_layer in forbidden:
                errors.append(f"upward import: {source} -> {target}")

            source_computation = computation_part(source)
            target_computation = computation_part(target)
            if source_computation is not None and target_computation is not None:
                allowed = COMPUTATION_ALLOWED_IMPORTS.get(source_computation, set())
                if target_computation not in allowed:
                    errors.append(
                        f"computation layer import: {source} -> {target}"
                    )

            for subsystem, order in SUBSYSTEM_ORDER.items():
                source_part = subsystem_part(source, subsystem)
                target_part = subsystem_part(target, subsystem)
                if source_part is None or target_part is None:
                    continue
                if source_part not in order or target_part not in order:
                    continue
                if order[target_part] > order[source_part] and source_part != "Basic":
                    errors.append(f"subsystem upward import: {source} -> {target}")

    visiting: set[str] = set()
    visited: set[str] = set()
    stack: list[str] = []

    def visit(node: str) -> None:
        if node in visited:
            return
        if node in visiting:
            start = stack.index(node)
            errors.append("cycle: " + " -> ".join(stack[start:] + [node]))
            return
        visiting.add(node)
        stack.append(node)
        for target in project_graph.get(node, []):
            if target in project_graph:
                visit(target)
        stack.pop()
        visiting.remove(node)
        visited.add(node)

    for module in project_graph:
        visit(module)

    if errors:
        for error in sorted(set(errors)):
            print(error, file=sys.stderr)
        return 1

    print(
        "Project imports resolve exactly; Project import hierarchy OK "
        f"({len(infrastructure_graph)} Infrastructure modules, "
        f"{len(project_modules)} project modules)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
