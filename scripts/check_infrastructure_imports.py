#!/usr/bin/env python3
"""Reject unresolved imports and violations of the project import hierarchy.

This check is intentionally independent of Lean's build graph. It enforces the
Infrastructure hierarchy and the package direction from `Crypto` definitions to
`CryptoConstruction` realizations and future `CryptoInstantiation` backends.
Exact module-name membership additionally catches case mismatches that can pass
on a case-insensitive macOS checkout but fail on GitHub's Linux runners.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
INFRA_ROOT = ROOT / "Crypto" / "Infrastructure"
IMPORT_RE = re.compile(r"^(?:public\s+)?import\s+(.+?)\s*$")
MODULE_RE = re.compile(r"^[A-Za-z0-9_.'-]+$")
PREFIX = "Crypto.Infrastructure."
PROJECT_PACKAGES = (
    "Crypto",
    "CryptoConstruction",
    "CryptoInstantiation",
    "CryptoTest",
)


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
    """Infrastructure may depend only on other Crypto.Infrastructure modules."""

    is_infrastructure = (
        module == "Crypto.Infrastructure" or module.startswith(PREFIX)
    )
    return is_project_module(module) and not is_infrastructure


def project_import_hierarchy_error(source: str, target: str) -> str | None:
    """Enforce Crypto <- CryptoConstruction <- CryptoInstantiation."""

    source_package = project_package(source)
    target_package = project_package(target)
    if source_package == "Crypto" and target_package in {
        "CryptoConstruction",
        "CryptoInstantiation",
    }:
        return f"Crypto imports higher package: {source} -> {target}"
    if (
        source_package == "CryptoConstruction"
        and target_package == "CryptoInstantiation"
    ):
        return f"CryptoConstruction imports CryptoInstantiation: {source} -> {target}"
    return None


def parser_regression_errors() -> list[str]:
    """Keep the accepted Lean import forms and project boundary under test."""

    fixture = """\
/- import Crypto.Assumption.Hidden
   /- nested import CryptoTest.Hidden -/
-/
public import Crypto.Infrastructure.SecurityParameter Crypto.Primitive.Bad CryptoConstruction.Primitive.Bad -- tail
import Mathlib.Data.Nat.Basic
"""
    expected = [
        "Crypto.Infrastructure.SecurityParameter",
        "Crypto.Primitive.Bad",
        "CryptoConstruction.Primitive.Bad",
        "Mathlib.Data.Nat.Basic",
    ]
    errors: list[str] = []
    parsed = imports_from_text(fixture)
    if parsed != expected:
        errors.append(f"internal import-parser regression: {parsed!r}")
    if not is_higher_level_project_import("Crypto.Primitive.Bad"):
        errors.append("internal boundary regression: Crypto.Primitive.Bad accepted")
    if not is_higher_level_project_import("CryptoTest.Bad"):
        errors.append("internal boundary regression: CryptoTest.Bad accepted")
    if not is_higher_level_project_import("CryptoConstruction.Primitive.Bad"):
        errors.append("internal boundary regression: CryptoConstruction accepted")
    if is_higher_level_project_import("Crypto.Infrastructure.UC.Kernel"):
        errors.append("internal boundary regression: Infrastructure rejected")
    if project_package("CryptoConstruction.Primitive.Basic") != "CryptoConstruction":
        errors.append("internal boundary regression: CryptoConstruction not recognized")
    if project_package("CryptoInstantiation.Backend.Basic") != "CryptoInstantiation":
        errors.append("internal boundary regression: CryptoInstantiation not recognized")
    if project_import_hierarchy_error(
        "Crypto.Primitive.Encryption.Basic",
        "CryptoConstruction.Primitive.Encryption.Basic",
    ) is None:
        errors.append("internal boundary regression: Crypto-to-construction accepted")
    if project_import_hierarchy_error(
        "Crypto.Infrastructure.Computation.Basic",
        "CryptoConstruction.Primitive.Basic",
    ) is None:
        errors.append("internal boundary regression: Infrastructure-to-construction accepted")
    if project_import_hierarchy_error(
        "CryptoConstruction.Primitive.Basic",
        "CryptoInstantiation.Backend.Basic",
    ) is None:
        errors.append("internal boundary regression: construction-to-instantiation accepted")
    if project_import_hierarchy_error(
        "CryptoConstruction.Primitive.Basic",
        "Crypto.Primitive.Basic",
    ) is not None:
        errors.append("internal boundary regression: construction-to-Crypto rejected")
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
    "Computation.Algebra": {
        "Signature": 0,
        "Handler": 1,
        "Laws": 2,
        "Bounds": 2,
        "Parameter": 2,
        "Operation": 3,
        "Basic": 99,
    },
    "Computation.Program": {
        "Syntax": 0,
        "Semantics": 1,
        "Execution": 2,
        "Bounds": 2,
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
        "Machine": 1,
        "ProgramMachine": 2,
        "OracleImplementation": 2,
        "OracleMachine": 3,
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
    "Algebra": {"Cost", "Algebra"},
    "Program": {"Cost", "Algebra", "Program"},
    "Oracle": {"Cost", "Algebra", "Oracle"},
    "Randomized": {"Cost"},
    "Game": set(),
    "Basic": {"Cost", "Algebra", "Program", "Oracle", "Randomized", "Game", "Basic"},
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


def project_source_files() -> list[Path]:
    """Collect every currently present project root and package source tree."""

    files: set[Path] = set()
    for package in PROJECT_PACKAGES:
        root_module = ROOT / f"{package}.lean"
        package_root = ROOT / package
        if root_module.is_file():
            files.add(root_module)
        if package_root.is_dir():
            files.update(package_root.rglob("*.lean"))
    return sorted(files)


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

    for source, targets in infrastructure_graph.items():
        source_layer = top_layer(source)
        forbidden = FORBIDDEN_TOP_IMPORTS.get(source_layer, set())
        for target in targets:
            if is_higher_level_project_import(target):
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
