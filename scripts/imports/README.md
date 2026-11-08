# Import and module tools

## Matroid import list

Keeps `Matroid.lean` synchronized with the `.lean` modules under the `Matroid/` directory.

What it does:

- Scans `Matroid/` recursively for all `.lean` files and computes their module names `Matroid.<path.with.dots>`.
- Parses `Matroid.lean` for existing lines of the form `public import Matroid.xxx` and `-- public import Matroid.xxx`.
- Adds missing modules as enabled `public import Matroid.xxx` lines.
- Rewrites `Matroid.lean` as a sorted list by module name, preserving any pre-existing comment markers (i.e. lines starting with `-- public import`).

### Usage

From the repo root:

```bash
uv run --no-project python scripts/imports/update_matroid_imports.py --dry-run
uv run --no-project python scripts/imports/update_matroid_imports.py
uv run --no-project python scripts/imports/update_matroid_imports.py --comment
uv run --no-project python scripts/imports/update_matroid_imports.py --all --dry-run
```

Options:

- `--root <path>`: explicitly set the repo root (defaults to the repository root).
- `--matroid-dir <path>`: path to the `Matroid/` directory (defaults to `<root>/Matroid`).
- `--matroid-file <path>`: path to `Matroid.lean` (defaults to `<root>/Matroid.lean`).
- `--dry-run`: show what would change without modifying files.
- `--comment`: when adding missing modules, write them as commented imports (`-- public import ...`).
- `--all`: include all discovered modules (opt-out of ignore rules).

Notes:

- Existing commented imports such as `-- public import Matroid.GraphTheory.Graph.Bipartite` are kept commented.
- New entries are added as enabled `public import ...` lines by default; you can use `--comment` to add them commented out instead.
- By default, modules matching any regex in `.matroidignore` (in `scripts/imports`) are ignored; use `--all` to include them.

### Ignore rules (`.matroidignore`)

Place a `.matroidignore` file next to this script (`scripts/imports/.matroidignore`). Each non-empty, non-comment line is a Python regular expression tested against full module names like `Matroid.GraphTheory.Graph.Basic`.

Example patterns:

```
# Ignore experimental or WIP modules
^Matroid\.Experiments\.
^Matroid\.Exercises\.
^Matroid\.WIP\.

# Ignore any module with 'scratch' in the path
scratch
```

---

## Import minimization

Detects and marks inefficient Mathlib imports that could be replaced with more direct imports.

What it does:

- Scans all `.lean` files in the project (excluding `.lake` and hidden directories).
- For each Mathlib import, checks if the file still compiles when the import is replaced with its transitive imports.
- If compilation succeeds, the import is inefficient (more direct imports are available).
- Marks inefficient imports with a `-- inefficient import` comment.

### Usage

From the repo root:

```bash
uv run --no-project python scripts/imports/detect_inefficient_imports.py
```

Configuration:

- `MATHLIB_PATH`: Path to mathlib (defaults to `.lake/packages/mathlib`).
- `TARGET_DIR`: Directory to scan for `.lean` files (defaults to `.`).

Notes:

- The script modifies files in place, adding `-- inefficient import` comments to imports that can be improved.
- Already marked imports (containing `-- inefficient`) are skipped.
- The script compiles each test case using `lake env lean` to verify changes.
- Headers may contain `module`, `prelude`, nested comments, and `public`, `meta`,
  or `all` import modifiers. Replacement imports respect visibility through both
  import steps. The scanner supports complete single-line imports with ASCII
  module names; other layouts end the scan. Imports with trailing multiline
  block comments are left untouched.
- Compilation checks the current file, not compatibility with downstream users
  of its exported API. Interrupted compilation restores the source file.

Run the regression tests, including Lean checks of import visibility and `meta`
evaluation, from the repository root:

```bash
uv run --no-project python -m unittest scripts.imports.test_detect_inefficient_imports -v
```

---


## Lean module headers

`Modulize.lean` adds module headers and public sections to the supplied files:

```sh
lake env lean --run scripts/imports/Modulize.lean file1.lean file2.lean
```

Pass `--meta` before the file names for meta imports and sections. The command edits those files.
