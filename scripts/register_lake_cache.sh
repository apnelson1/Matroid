#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/register_lake_cache.sh [--set-default] [CONFIG_PATH]

Register Matroid's public R2 Lake cache in a Lake config file.

Arguments:
  CONFIG_PATH     Lake config path to update. Defaults to ~/.lake/config.toml.

Options:
  --set-default   Also set cache.defaultService = "matroid-r2-public".

After registration, run:
  lake cache get --repo=apnelson1/Matroid

If this script reports that another default cache service is already configured,
run either:
  lake cache get --service=matroid-r2-public --repo=apnelson1/Matroid

or rerun this script with --set-default.
EOF
}

set_default=false
config_path="${HOME}/.lake/config.toml"

while (($#)); do
  case "$1" in
    --help|-h)
      usage
      exit 0
      ;;
    --set-default)
      set_default=true
      shift
      ;;
    -*)
      echo "unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
    *)
      config_path="$1"
      shift
      ;;
  esac
done

CONFIG_PATH="$config_path" SET_DEFAULT="$set_default" python3 - <<'PY'
import os
import re
from pathlib import Path

service_name = "matroid-r2-public"
repo = "apnelson1/Matroid"
config_path = Path(os.environ["CONFIG_PATH"]).expanduser()
set_default = os.environ["SET_DEFAULT"] == "true"

service_block = f'''
[[cache.service]]
name = "{service_name}"
kind = "s3"
artifactEndpoint = "https://pub-8410780127634ed2b09f7b7f09c7f4e5.r2.dev/artifacts"
revisionEndpoint = "https://pub-8410780127634ed2b09f7b7f09c7f4e5.r2.dev/revisions"
'''.lstrip()

config_path.parent.mkdir(parents=True, exist_ok=True)
text = config_path.read_text() if config_path.exists() else ""
changed = False

default_re = re.compile(r'^cache\.defaultService\s*=\s*"([^"]+)"\s*$', re.MULTILINE)
default_match = default_re.search(text)

if default_match is None:
    text = f'cache.defaultService = "{service_name}"\n' + text
    changed = True
    print(f"Set cache.defaultService to {service_name}.")
elif default_match.group(1) != service_name:
    if set_default:
        text = default_re.sub(f'cache.defaultService = "{service_name}"', text, count=1)
        changed = True
        print(f"Changed cache.defaultService from {default_match.group(1)} to {service_name}.")
    else:
        print(
            f"Existing cache.defaultService is {default_match.group(1)}; leaving it unchanged.\n"
            f"Use --set-default to make `lake cache get --repo={repo}` use {service_name}."
        )
else:
    print(f"cache.defaultService is already {service_name}.")

if f'name = "{service_name}"' not in text:
    if text and not text.endswith("\n"):
        text += "\n"
    text += "\n" + service_block
    changed = True
    print(f"Registered cache service {service_name}.")
else:
    print(f"Cache service {service_name} is already registered.")

if changed:
    config_path.write_text(text)
    print(f"Updated {config_path}.")
else:
    print(f"No changes needed in {config_path}.")

print("\nNext commands:")
if default_match is not None and default_match.group(1) != service_name and not set_default:
    print(f"  lake cache get --service={service_name} --repo={repo}")
else:
    print(f"  lake cache get --repo={repo}")
print("  lake build")
PY
