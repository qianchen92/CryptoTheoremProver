#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/build-docs.sh [options]

Generate HTML documentation for this Lean project using doc-gen4.

Options:
  --serve          Serve generated docs over HTTP after building.
  --port PORT     Port used with --serve. Default: 8000.
  --skip-update   Do not run lake update before building.
  -h, --help      Show this help text.

Environment:
  LIB_NAME        Lean library target to document. Default: Crypto.
  DOCGEN_REV      doc-gen4 revision/tag. Default: version from lean-toolchain.
EOF
}

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd -- "$SCRIPT_DIR/.." && pwd)"

LIB_NAME="${LIB_NAME:-Crypto}"
TOOLCHAIN="$(sed -E 's#^leanprover/lean4:##' "$REPO_ROOT/lean-toolchain")"
DOCGEN_REV="${DOCGEN_REV:-$TOOLCHAIN}"
DOCBUILD_DIR="$REPO_ROOT/docbuild"
DOCROOT="$DOCBUILD_DIR/.lake/build/doc"
PORT="8000"
SERVE=0
RUN_UPDATE=1

export MATHLIB_NO_CACHE_ON_UPDATE="${MATHLIB_NO_CACHE_ON_UPDATE:-1}"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --serve)
      SERVE=1
      shift
      ;;
    --port)
      if [[ $# -lt 2 ]]; then
        echo "error: --port requires a value" >&2
        exit 2
      fi
      PORT="$2"
      shift 2
      ;;
    --skip-update)
      RUN_UPDATE=0
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if ! command -v lake >/dev/null 2>&1; then
  echo "error: lake was not found in PATH" >&2
  exit 1
fi

mkdir -p "$DOCBUILD_DIR"

cat > "$DOCBUILD_DIR/lakefile.toml" <<EOF
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "$DOCGEN_REV"

[[require]]
name = "$LIB_NAME"
path = "../"
EOF

cd "$DOCBUILD_DIR"

if [[ "$RUN_UPDATE" -eq 1 ]]; then
  lake update doc-gen4
  lake update "$LIB_NAME"
fi

lake build "$LIB_NAME:docs"

echo "Documentation generated at: $DOCROOT/index.html"

if [[ "$SERVE" -eq 1 ]]; then
  if command -v python3 >/dev/null 2>&1; then
    PYTHON=python3
  elif command -v python >/dev/null 2>&1; then
    PYTHON=python
  else
    echo "error: Python was not found; cannot serve docs" >&2
    exit 1
  fi

  echo "Serving documentation at: http://localhost:$PORT"
  cd "$DOCROOT"
  "$PYTHON" -m http.server "$PORT"
fi
