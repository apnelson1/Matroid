#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/register_lake_cache.sh [--set-default] [CONFIG_PATH]

Register Matroid's public R2 Lake cache in a Lake config file.
Requires Python 3.11+ and tomlkit (see CACHE.md).

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
import fcntl
import os
import stat
import sys
import tempfile
import tomllib
from collections.abc import Mapping
from pathlib import Path

try:
    import tomlkit
except ImportError:
    sys.exit("tomlkit is required; install it for python3 (see CACHE.md).")

service_name = "matroid-r2-public"
repo = "apnelson1/Matroid"
# Follow symlinks so atomic replacement updates their target, not the link.
config_path = Path(os.environ["CONFIG_PATH"]).expanduser().resolve()
set_default = os.environ["SET_DEFAULT"] == "true"
endpoint = "https://pub-8410780127634ed2b09f7b7f09c7f4e5.r2.dev"
service = {
    "name": service_name,
    "kind": "s3",
    "artifactEndpoint": endpoint + "/artifacts",
    "revisionEndpoint": endpoint + "/revisions",
}

try:
    config_path.parent.mkdir(parents=True, exist_ok=True)
    # Lock a stable sidecar: locking the config inode would not survive replace.
    # Keep the sidecar in place so waiting invocations share the same lock.
    lock_fd = os.open(str(config_path) + ".lock", os.O_CREAT | os.O_RDWR, 0o600)
    with os.fdopen(lock_fd, "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        original = config_path.read_bytes() if config_path.exists() else None
        text = original.decode("utf-8") if original is not None else ""
        tomllib.loads(text)
        doc = tomlkit.parse(text)
        if "cache" not in doc:
            doc["cache"] = tomlkit.table()
        cache = doc["cache"]
        if not isinstance(cache, Mapping):
            raise ValueError("cache must be a TOML table")
        if "defaultService" in cache and not isinstance(cache["defaultService"], str):
            raise ValueError("cache.defaultService must be a string")
        if "service" not in cache:
            cache["service"] = tomlkit.aot()
        services = cache["service"]
        if not isinstance(services, list) or any(
            not isinstance(s, Mapping) or not isinstance(s.get("name"), str)
            for s in services
        ):
            raise ValueError("cache.service must be an array of named tables")
        names = [s["name"] for s in services]
        if len(names) != len(set(names)):
            raise ValueError("duplicate cache service names")

        if "defaultService" not in cache or set_default:
            cache["defaultService"] = service_name
        if service_name not in names:
            services.append(service)
        default = cache["defaultService"]
        updated = tomlkit.dumps(doc).encode("utf-8")
        # Validate the complete candidate independently before touching the file.
        tomllib.loads(updated.decode("utf-8"))
        if updated != original:
            temp_path = None
            try:
                with tempfile.NamedTemporaryFile(
                    dir=config_path.parent, prefix="." + config_path.name + ".",
                    delete=False,
                ) as temp:
                    temp_path = Path(temp.name)
                    if original is not None:
                        os.fchmod(temp.fileno(), stat.S_IMODE(config_path.stat().st_mode))
                    temp.write(updated)
                    temp.flush()
                    os.fsync(temp.fileno())
                # Also detect edits by programs that do not use our sidecar lock.
                current = config_path.read_bytes() if config_path.exists() else None
                if current != original:
                    raise ValueError("config changed during registration; rerun the script")
                os.replace(temp_path, config_path)
            finally:
                if temp_path is not None:
                    temp_path.unlink(missing_ok=True)
            print(f"Updated {config_path}.")
        else:
            print(f"No changes needed in {config_path}.")
except (OSError, ValueError, tomlkit.exceptions.TOMLKitError) as error:
    sys.exit(f"Could not register cache in {config_path}: {error}")

if default != service_name:
    print(f"Existing cache.defaultService is {default}; leaving it unchanged.")
    print("Use --set-default to make Matroid's cache the default.")
print("\nNext commands:")
print(f"  lake cache get --service={service_name} --repo={repo}")
print("  lake build")
PY
