# Matroid build cache

Matroid publishes prebuilt build artifacts for its own library, so you can start working on the repository without compiling the whole library locally. The idea matches the Mathlib cache, but it is built on Lake's remote artifact cache, so the commands are `lake cache ...` rather than `lake exe cache ...`.

The cache covers the `Matroid` library. Dependencies such as Mathlib and loogle are handled by Lake as usual.

## One-time setup

```bash
scripts/register_lake_cache.sh
```

Before using the cache, we first need to tell the computer where to find the cache. `scripts/register_lake_cache.sh` registers the public cache service `matroid-r2-public` in `~/.lake/config.toml`, the per-user Lake configuration file read by every Lake workspace on the machine. It also makes that service the default unless another default is already configured, in which case it leaves the existing default in place.

## Everyday use

If `matroid-r2-public` is the default service (i.e. the only one in `~/.lake/config.toml`), we can just run:

```bash
lake cache get --repo=apnelson1/Matroid
lake build
```

If another default is already configured, select Matroid's cache explicitly on every fetch:

```bash
lake cache get --service=matroid-r2-public --repo=apnelson1/Matroid
```

I suggest adding an alias to your shell config file (e.g. `~/.zshrc` or `~/.bashrc`) to make this easier.

Options of `lake cache get` worth knowing (`lake cache get --help` lists all of them):

| Option | Effect |
| --- | --- |
| `--max-revs=<n>` | how many revisions back from `HEAD` to search (default 100) |
| `--rev=<commit>` | look up artifacts for exactly that commit |
| `--mappings-only` | download the input-to-output index without the artifacts |
| `--force-download` | re-download files that are already in the local cache |
| `-v` | print the cache service URLs that are actually queried |

## What the cache contains

Lake tracks build products per module: each `.olean`, object file, and intermediate product is stored under a hash of the inputs that produced it. A commit's cache entry is therefore keyed by the commit, the Lean toolchain named in `lean-toolchain`, and the platform, and it exists only for commits that CI has built.

Artifacts fetched by `lake cache get` land in the local Lake cache (`~/.cache/lake` on Linux, or the directory named by `LAKE_CACHE_DIR`). Matroid's `lakefile.toml` sets `restoreAllArtifacts = true`, so Lake also copies them into `.lake/build`, where the language server and `lake env` find them.

Because artifacts are keyed by exact input hashes, they are reused only where your sources match the ones that were built. Editing a module means that module and its dependents are rebuilt; everything else is restored from the cache.

## Troubleshooting

### `error: apnelson1/Matroid: no outputs found in 100 revisions from HEAD`

Lake fell back to its default service, Reservoir, which holds no Matroid artifacts. The `matroid-r2-public` service is either not registered or not the default. Pass `--service=matroid-r2-public`, or rerun the registration script with `--set-default`. Adding `-v` shows which endpoint was queried: a working run reports a `https://pub-...r2.dev/revisions/...` URL, a broken one reports `reservoir.lean-lang.org`.

### `warning: Matroid: package has changes; only artifacts for committed code will be downloaded`

  The working tree has uncommitted changes. Lake looks artifacts up by the committed revision, so commit or stash if you want the cache to line up with your sources.

### Nothing has been published for your commit

Artifacts are uploaded for commits on `main`. A local commit, a side branch, or a commit whose CI run failed has no published artifacts, and that code is compiled locally instead. `--rev` fetches a neighbouring published commit if one helps.

### The build became slow again after `lake update`

The `lean-toolchain` or the Mathlib revision changed, and artifacts for the new toolchain exist only after CI has built it.

### `lake cache services`

Lists the cache services configured for your user, one per line; `matroid-r2-public` should appear among them.

Note that `lake cache clean` deletes the whole local Lake cache directory served by your toolchain, which other projects on the machine also use. It is rarely what you want when a single commit fails to restore.
