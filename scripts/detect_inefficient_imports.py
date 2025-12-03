#!/usr/bin/env python3
import os
import re
import subprocess
import sys

# Configuration
MATHLIB_PATH = ".lake/packages/mathlib"
TARGET_DIR = "."

def find_lean_files(root_dir):
    lean_files = []
    for root, dirs, files in os.walk(root_dir):
        # Skip .lake and hidden directories
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        
        for file in files:
            if file.endswith(".lean"):
                lean_files.append(os.path.join(root, file))
    return lean_files

def get_imports(file_path):
    """
    Returns a list of (line_index, import_name, full_line_content)
    """
    imports = []
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
            for i, line in enumerate(lines):
                stripped = line.strip()
                if not stripped or stripped.startswith("--") or stripped.startswith("/-"):
                    continue
                
                # Match "import X" or "public import X"
                match = re.match(r"^(?:public\s+)?import\s+([a-zA-Z0-9_\.]+)", stripped)
                if match:
                    import_name = match.group(1)
                    imports.append((i, import_name, line))
                else:
                    # Stop at first non-import line (unless prelude)
                    if stripped == "prelude":
                        continue
                    break
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
    return imports

def resolve_mathlib_import(import_name):
    # import_name: Mathlib.Data.Set.Basic
    parts = import_name.split('.')
    rel_path = os.path.join(*parts) + ".lean"
    full_path = os.path.join(MATHLIB_PATH, rel_path)
    
    if os.path.exists(full_path):
        return full_path
    return None

def get_transitive_imports(lean_file_path):
    imports = []
    try:
        with open(lean_file_path, 'r', encoding='utf-8') as f:
            for line in f:
                stripped = line.strip()
                match = re.match(r"^(?:public\s+)?import\s+([a-zA-Z0-9_\.]+)", stripped)
                if match:
                    imp = match.group(1)
                    imports.append(f"import {imp}")
    except Exception as e:
        print(f"Error reading imported file {lean_file_path}: {e}")
    return imports

def check_compilation(file_path):
    try:
        result = subprocess.run(
            ["lake", "env", "lean", file_path],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL
        )
        return result.returncode == 0
    except Exception as e:
        print(f"Error running compiler: {e}")
        return False

def process_file(file_path):
    print(f"Processing {file_path}...")
    
    with open(file_path, 'r', encoding='utf-8') as f:
        original_lines = f.readlines()
        
    current_lines = list(original_lines)
    imports_to_check = get_imports(file_path)
    
    # Filter for Mathlib imports
    mathlib_imports = [x for x in imports_to_check if x[1].startswith("Mathlib")]
    
    changes_made = False
    
    for line_idx, import_name, _ in mathlib_imports:
        # Check if already marked
        if "-- inefficient" in current_lines[line_idx]:
             continue

        imported_file_path = resolve_mathlib_import(import_name)
        if not imported_file_path:
            continue
            
        transitive = get_transitive_imports(imported_file_path)
        
        # Prepare test content
        test_lines = list(current_lines)
        replacement_block = "\n".join(transitive) + "\n"
        test_lines[line_idx] = replacement_block
        
        # Write test content
        with open(file_path, 'w', encoding='utf-8') as f:
            f.writelines(test_lines)
            
        print(f"  Testing {import_name}...")
        if check_compilation(file_path):
            print(f"  -> Inefficient: {import_name}")
            # Revert and add comment
            stripped = current_lines[line_idx].rstrip()
            current_lines[line_idx] = f"{stripped} -- inefficient import\n"
            changes_made = True
        
        # Revert to current state (modified or original)
        with open(file_path, 'w', encoding='utf-8') as f:
            f.writelines(current_lines)
            
    if changes_made:
        print(f"Updated {file_path}")

if __name__ == "__main__":
    lean_files = find_lean_files(TARGET_DIR)
    print(f"Found {len(lean_files)} lean files.")
    for f in lean_files:
        process_file(f)

