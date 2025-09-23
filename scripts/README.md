# Matroid import updater

This small utility keeps `Matroid.lean` synchronized with the `.lean` modules under the `Matroid/` directory.

What it does:
- Scans `Matroid/` recursively for all `.lean` files and computes their module names `Matroid.<path.with.dots>`.
- Parses `Matroid.lean` for existing lines of the form `import Matroid.xxx` and `-- import Matroid.xxx`.
- Adds missing modules as active `import Matroid.xxx` lines.
- Rewrites `Matroid.lean` as a sorted list by module name, preserving any pre-existing comment markers (i.e. lines starting with `-- import`).

## Usage

From the repo root:

```bash
python3 scripts/update_matroid_imports.py --dry-run
python3 scripts/update_matroid_imports.py
python3 scripts/update_matroid_imports.py --comment-new
python3 scripts/update_matroid_imports.py --all --dry-run
```

Options:
- `--root <path>`: explicitly set the repo root (defaults to the parent of `scripts/`).
- `--matroid-dir <path>`: path to the `Matroid/` directory (defaults to `<root>/Matroid`).
- `--matroid-file <path>`: path to `Matroid.lean` (defaults to `<root>/Matroid.lean`).
- `--dry-run`: show what would change without modifying files.
- `--comment-new`: when adding missing modules, write them as commented imports (`-- import ...`).
- `--all`: include all discovered modules (opt-out of ignore rules).

Notes:
- Existing commented imports such as `-- import Matroid.Graph.Bipartite` are kept commented.
- New entries are added as active `import ...` lines by default; you can use `--comment-new` to add them commented out instead.
- By default, modules matching any regex in `.matroidignore` (in the `scripts/` directory) are ignored; use `--all` to include them.

### Ignore rules (`.matroidignore`)

Place a `.matroidignore` file next to this script (`scripts/.matroidignore`). Each non-empty, non-comment line is a Python regular expression tested against full module names like `Matroid.Graph.Basic`.

Example patterns:

```
# Ignore experimental or WIP modules
^Matroid\.Experiments\.
^Matroid\.Exercises\.
^Matroid\.WIP\.

# Ignore any module with 'scratch' in the path
scratch
```
