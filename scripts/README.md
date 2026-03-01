# Scripts

This folder contains utility scripts for the Matroid project:

1. **update_matroid_imports.py** - Synchronizes `Matroid.lean` with module files
2. **detect_inefficient_imports.py** - Identifies inefficient Mathlib imports
3. **canvas_to_pdf.py** - Converts Obsidian canvas files to PDF visualizations

---

## 1. Matroid Import Updater (`update_matroid_imports.py`)

Keeps `Matroid.lean` synchronized with the `.lean` modules under the `Matroid/` directory.

What it does:
- Scans `Matroid/` recursively for all `.lean` files and computes their module names `Matroid.<path.with.dots>`.
- Parses `Matroid.lean` for existing lines of the form `import Matroid.xxx` and `-- import Matroid.xxx`.
- Adds missing modules as active `import Matroid.xxx` lines.
- Rewrites `Matroid.lean` as a sorted list by module name, preserving any pre-existing comment markers (i.e. lines starting with `-- import`).

### Usage

From the repo root:

```bash
uv run scripts/update_matroid_imports.py --dry-run
uv run scripts/update_matroid_imports.py
uv run scripts/update_matroid_imports.py --comment
uv run scripts/update_matroid_imports.py --all --dry-run
```

Options:
- `--root <path>`: explicitly set the repo root (defaults to the parent of `scripts/`).
- `--matroid-dir <path>`: path to the `Matroid/` directory (defaults to `<root>/Matroid`).
- `--matroid-file <path>`: path to `Matroid.lean` (defaults to `<root>/Matroid.lean`).
- `--dry-run`: show what would change without modifying files.
- `--comment`: when adding missing modules, write them as commented imports (`-- import ...`).
- `--all`: include all discovered modules (opt-out of ignore rules).

Notes:
- Existing commented imports such as `-- import Matroid.Graph.Bipartite` are kept commented.
- New entries are added as active `import ...` lines by default; you can use `--comment` to add them commented out instead.
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

---

## 2. Inefficient Import Detector (`detect_inefficient_imports.py`)

Detects and marks inefficient Mathlib imports that could be replaced with more direct imports.

What it does:
- Scans all `.lean` files in the project (excluding `.lake` and hidden directories).
- For each Mathlib import, checks if the file still compiles when the import is replaced with its transitive imports.
- If compilation succeeds, the import is inefficient (more direct imports are available).
- Marks inefficient imports with a `-- inefficient import` comment.

### Usage

From the repo root:

```bash
uv run scripts/detect_inefficient_imports.py
```

Configuration:
- `MATHLIB_PATH`: Path to mathlib (defaults to `.lake/packages/mathlib`).
- `TARGET_DIR`: Directory to scan for `.lean` files (defaults to `.`).

Notes:
- The script modifies files in place, adding `-- inefficient import` comments to imports that can be improved.
- Already marked imports (containing `-- inefficient`) are skipped.
- The script compiles each test case using `lake env lean` to verify changes.

---

## 3. Canvas to PDF Converter (`canvas_to_pdf.py`)

Converts Obsidian canvas files (`.canvas`) to PDF visualizations.

What it does:
- Reads `.canvas` files (JSON format) from the `ToDo/` directory.
- Generates PDF visualizations showing node layouts and connections.
- Preserves node colors, text content, and edge relationships.
- Uses landscape A4 format with automatic scaling to fit content.

### Usage

From the repo root:

```bash
cd scripts && uv run canvas_to_pdf.py
```

Requirements:
- `reportlab` library (`uv` handles dependencies automatically via `pyproject.toml`)

Output:
- For each `.canvas` file in `ToDo/`, creates a corresponding `.pdf` file in the same directory.
- Example: `ToDo/DiGraph.canvas` → `ToDo/DiGraph.pdf`

Notes:
- Node colors are preserved from the Obsidian canvas (red, orange, yellow, green, blue, purple).
- Both file nodes and text nodes are rendered with their content.
- Edges are drawn with arrows indicating direction.
- Content is automatically scaled to fit on the page.
