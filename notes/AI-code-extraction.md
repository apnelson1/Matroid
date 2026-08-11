# Extracting lemmas from AI-written proofs

A method note, written from a worked example: `Matroid/Graph/Planarity/StarLemma.lean`, 1692 lines
of freshly AI-generated Lean, reduced to 1469 by extraction alone — no change to any statement, no
change to what the file proves.

The point is not the 13% line count. It is that AI-written Lean **duplicates where a human would
abstract**, and the duplication is mechanically findable. A model writing a 400-line proof has no
pressure to notice that it just wrote the same forty lines two hundred lines earlier; it re-derives
instead of naming. So the extraction work is largely a search problem, and the search can be
automated even though the extraction cannot.

> **Order matters.** Do this *before* running `golf_rules.py` (`../leangolf`). The mechanical
> golfer rewrites each copy of a duplicated block independently — the rewrites it accepts in one
> copy are not the ones it accepts in another. That destroys the textual duplication which is the
> cheapest signal you have. Extract first, golf second.

---

## How to find it

### 1. The rolling-hash duplicate scan

This is the highest-yield tool and it takes ten seconds. Hash every window of six consecutive
non-blank stripped lines and report the windows that occur more than once:

```python
import hashlib, collections
f = 'Matroid/Graph/Planarity/StarLemma.lean'
L = [l.rstrip('\n') for l in open(f)]
W = 6
seen = collections.defaultdict(list)
for i in range(len(L) - W):
    blk = [x.strip() for x in L[i:i+W]]
    if sum(1 for b in blk if b) < W:      # skip windows containing blank lines
        continue
    seen[hashlib.md5('\n'.join(blk).encode()).hexdigest()].append(i + 1)
for h, v in seen.items():
    if len(v) > 1:
        print(f'lines {v}: {L[v[0]-1].strip()[:78]}')
```

Stripping indentation is what makes it work: the same argument at two different nesting depths
still matches. On `StarLemma.lean` this immediately surfaced a **25-line block occurring three
times** and a 16-line block occurring twice — neither of which I would reliably have spotted by
reading 1692 lines, because the copies were 200 and 300 lines apart.

Read the hits as *seeds*, not as the extraction boundary. The true shared unit is usually larger
than the matching window: the ×3 hit above was the tail of a 50-line argument whose head differed
only in a type ascription, so a strict textual scan under-reports it.

### 2. Tactic frequency against the house style

```bash
grep -oE "\b(grind|rcases|constructor|by_cases|subst|have|simp_all|aesop)\b" file.lean \
  | sort | uniq -c | sort -rn
```

`StarLemma.lean` had 382 `have`, 48 `rcases`, 15 `constructor`, and **zero `grind`** in 1692 lines.
That profile alone identifies a file as machine-written. High `have` density in particular is the
signature of an extraction opportunity: a proof that names forty intermediate facts is a proof that
has an unnamed lemma inside it.

### 3. The `.1`/`.2` smell

Grep for facts stated about both components of a pair. Four separate blocks here iterated over
`s : V × V` and did the identical thing to `s.1` and then to `s.2`, complete with duplicated
`split_ifs` / `Finset.notMem_empty` boilerplate. This is not a duplicated *block* — the two halves
are adjacent and interleaved, so the hash scan misses it. It is a duplicated *shape*, and the fix
is a data-structure change, not a lemma.

### 4. Lemmas the file proves and then ignores

Check whether the general lemmas at the top of the file are actually used further down. Here,
`ne_of_mem_openSegment_left`/`_right` were proved at lines 316/324 and then re-derived by hand,
twice, three hundred lines later. A model that proves a helper does not reliably remember it
exists. Grep each private lemma name and count the call sites; one call site (or zero) is a smell.

---

## The six extractions

Each was verified by a full `lake build` before moving to the next. Rebuild cost on this file is
about six seconds, which makes one-extraction-per-build entirely practical.

### 1. `exists_sector_subset_faceSet` — the ×3 block

**Found by:** the hash scan (three hits, 200+ lines apart).

Roughly 50 lines appearing verbatim in `ncard_facesAt_le_two`, `facesAt_eq_image_sectors` and
`facesAt_eq_of_mem_star_ball`: given the star equality, pull a support-free point out of the ball,
take its connected component in `diskMinusRadii`, and show that component's image lies in the face.

The interesting part was that the three copies were *not* identical. Two were centred at `p`
itself; the third was centred at a different point `q ∈ ball p ρ`, and reached its neighbourhood
via `IsOpen.mem_nhds isOpen_ball hqball` rather than `ball_mem_nhds _ hρ`. The argument never looks
at which, so the extracted lemma takes `q` and `hqball : q ∈ ball p ρ` as parameters, and the two
`p`-centred call sites pass `mem_ball_self hρ`. **Generalising was what made the three copies
collapse into one** — a strict "find identical text" approach would have merged two and left the
third. The hypothesis `hρ : 0 < ρ` then became unnecessary and was dropped from the signature.

Net: ~150 lines to ~60, and the three call sites are now one line each.

### 2. `exists_pos_le_dist_of_notMem` — the `δ` gadget

**Found by:** the hash scan (`have hnotK` bodies byte-identical at two sites).

Both `exists_radius` and `exists_radius_edgeInterior` opened with:

```lean
let δ : ℝ := if hKne : K.Nonempty then infDist p K else 1
have hδpos : 0 < δ := by
  dsimp [δ]; split_ifs with hKne
  · exact (hKclosed.notMem_iff_infDist_pos hKne).mp hpK
  · norm_num
```

and later re-derived `δ ≤ dist p x` by repeating the same `split_ifs`.

The `if K.Nonempty` exists for exactly one reason: `infDist p ∅ = 0`, so the `infDist` formulation
is false when `K` is empty. State the conclusion pointwise instead and the empty case becomes
vacuous:

```lean
private lemma exists_pos_le_dist_of_notMem {K : Set V} (hK : IsClosed K) {p : V} (hp : p ∉ K) :
    ∃ δ > 0, ∀ x ∈ K, δ ≤ Dist.dist p x
```

Both sites are now `obtain ⟨δ, hδpos, hδle⟩ := exists_pos_le_dist_of_notMem hKclosed hpK`, and
`hnotK` drops from eight lines to three. **This is the generalisable lesson**: when a definition
needs a case split to be well-behaved, the case split usually belongs to the *statement*, not the
proof. Choosing a formulation whose degenerate case is vacuous removes it everywhere at once.

### 3. The endpoint restructure in `exists_radius`

**Found by:** the `.1`/`.2` smell. The hash scan does not see this one.

`Sp` ranged over segments `s : V × V`, so `dists`, `Y`, `hdists_pos`, `hρ_le_end` and `hYsphere`
each had to say everything twice, once per component, with `Finset.union` of two `dite`s to build
the sets and `split_ifs` plus `Finset.notMem_empty` to take them apart. Ranging over *endpoints*
instead:

```lean
let ends : Finset V := hSpfin.toFinset.biUnion fun s ↦ ({s.1, s.2} : Finset V).erase p
let dists : Finset ℝ := ends.image (Dist.dist p ·)
let Y : Finset V := ends.image (radialPoint p · ρ)
```

`hdists_pos` went 12 lines → 4, `hρ_le_end` 17 → 6, `hYsphere` 10 → 4, and the backward half of the
main `subset_antisymm` 34 → 12. Every `split_ifs` in the file (10 of them) disappeared with this
change, since they existed only to take apart the `dite`s.

The `erase p` in `ends` carries what the `if _ ≠ p` guards used to: an endpoint equal to `p`
contributes no radius. Two small helpers (`hends_ne`, `hends_seg`) recover the facts the pair
structure used to supply directly, and `hmem_ends` goes the other way.

This was the highest-risk edit — `Y` is what `exists_radius` *returns*, so a wrong move breaks
every downstream consumer. It was done last, deliberately, so that a failure here would not have
cost the other five.

### 4. The mirrored branches in `hneY`

**Found by:** reading, after the hash scan flagged a 6-line hit inside it (`hab'` at two sites).

`exists_radius_edgeInterior` case-split on `t ≤ 1` and then wrote two ~40-line branches related by
`a ↔ b`, `A ↔ B`, `t ↔ t⁻¹`. A `wlog` is the textbook move, but the two sides are not symmetric in
the ambient context (`A` ends at `p`, `B` starts at it), so setting up the symmetry costs more than
it saves.

The better factorisation is not symmetry but a shared conclusion. Both branches, once they have
produced a point `c ≠ p` whose segment from `p` lies in both `A` and `B`, run the identical
midpoint argument against `hinter`. So:

```lean
have key {c : V} (hne_c : c ≠ p) (hA : segment ℝ p c ⊆ A.toSet)
    (hB : segment ℝ p c ⊆ B.toSet) : False
```

and each branch shrinks to deriving its segment inclusion and calling `key`. 90 lines → 40.

**Lesson:** when two branches look symmetric, check whether they share a *conclusion* before
reaching for `wlog`. Factoring the common tail is often easier than establishing the symmetry, and
it does not require the context to be symmetric at all.

### 5. Reusing `ne_of_mem_openSegment_left`/`_right`

**Found by:** noticing the file's own helper lemmas were unused.

Sixteen lines of `congrArg`/`smul_eq_zero` at each of two sites, proving that the midpoint of
`p`–`c` differs from `p` and from `c`. The file already had both facts as general lemmas. Each site
became two lines:

```lean
have hz_ne_p : z ≠ p := (ne_of_mem_openSegment_left hne_a.symm hz_open).symm
have hz_ne_a : z ≠ a := (ne_of_mem_openSegment_right hne_a.symm hz_open).symm
```

The instantiation is a three-way renaming (`a := p`, `b := a`, `p := z`), which is exactly the kind
of thing a model will not spot and will re-derive from scratch instead.

### 6. `hYunion`, and the lints

A ten-line hand-rolled proof, twice, that `⋃ y ∈ ({ya, yb} : Finset V), segment ℝ p y` splits as a
union. `simp [Y]` closes it. Not an extraction — just a reminder to try the one-liner before
believing the file needs a lemma.

Also fixed from build warnings: `haveI` → `have` (×2, style linter) and the deprecated
`Set.mem_diff` → `Set.mem_sdiff`.

---

## Results

| | before | after |
|---|---|---|
| lines | 1692 | 1469 |
| `have` | 382 | 305 |
| `rcases` | 48 | 36 |
| `constructor` | 15 | 13 |
| `by_cases` | 12 | 9 |
| `split_ifs` | 10 | **0** |
| `subst` | 11 | 11 |

Two new private lemmas: `exists_pos_le_dist_of_notMem`, `exists_sector_subset_faceSet`.

Of the 223 lines, **about 207 are extraction**; the other 16 are the `hYunion` → `simp [Y]`
collapse (#6), which is golf, not extraction. The lint fixes changed no line counts.

`subst` is unchanged, and not because of any swap: all ten sites are the *same* sites, carried
through untouched. By the house rule of thumb (a surviving `subst` means something was not golfed)
there is real work left there — but it is tactic-level work for the golfer, not extraction.

Every step was verified by `lake build Matroid.Graph.Planarity.StarLemma`. Only one step failed on
first attempt, and for an unrelated reason: `le_or_lt` has been renamed `le_or_gt` in the pinned
Mathlib.

---

---

# Level 2: private lemma → public lemma in its natural file

The first pass above moves code *within* a file: inline block → standalone lemma. There is a second
axis, and AI-written files are just as bad at it: a lemma can be perfectly well factored and still
be **in the wrong place**, marked `private` in a planarity file when it is a fact about normed
spaces that four other files would want.

The two axes are independent. Level 1 asks "is this argument named?". Level 2 asks "is the name
visible from where it is needed?". A file can pass level 1 completely and fail level 2 entirely —
which is roughly what `StarLemma.lean` does after the first pass.

There is also a **level 0** worth checking first: *should this lemma exist at all?*

## Finding level-2 candidates

Tag each declaration by whether its statement mentions any domain vocabulary. Anything with no
domain tokens at all is a general fact wearing a planarity costume:

```python
import re
f = 'Matroid/Graph/Planarity/StarLemma.lean'
L = [l.rstrip('\n') for l in open(f)]
decl = re.compile(r'^(private |protected )*(noncomputable )?(theorem|lemma|def) (\S+)')
DOMAIN = re.compile(r'\b(Graph|PLDrawing|Drawing|PolygonalPath|Path|cell|edgeSource|edgeTarget'
                    r'|faceSet|Face|OnePoint|sectors|diskMinusRadii|facesAt)\b')
starts = [(i, m.group(4)) for i, l in enumerate(L) if (m := decl.match(l))] + [(len(L), '')]
for k in range(len(starts) - 1):
    i, name = starts[k]; j = starts[k + 1][0]
    hits = sorted(set(DOMAIN.findall('\n'.join(L[i:j]))))
    print(f"{i+1:5d} {j-i:4d}L {name:44s} {'PURE' if not hits else ','.join(hits[:4])}")
```

On `StarLemma.lean` this reports **16 declarations, ~273 lines, with no graph content whatsoever** —
about a fifth of the file. That is the level-2 backlog, and it is invisible to every technique in
the first pass, because none of those lemmas are duplicated. They are each used exactly once or
twice, correctly named, and sitting in a file no one would ever grep for them in.

## Level 0: `dist_lineMap_center` should not exist

Mathlib already has it. `Mathlib/Analysis/Normed/Affine/AddTorsor.lean:80` provides

```lean
@[simp] theorem dist_lineMap_left (p₁ p₂ : P) (c : 𝕜) : dist (lineMap p₁ p₂ c) p₁ = ‖c‖ * dist p₁ p₂
```

which is the file's seven-line `dist_lineMap_center` modulo `‖t‖ = t` for `0 ≤ t`. The module was
simply not imported. Adding `import Mathlib.Analysis.Normed.Affine.AddTorsor` reduces the proof to

```lean
rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ht]
```

**and costs one extra build job** (2651 vs 2650 — it was already almost entirely transitively
imported). *This edit has been applied.*

The lesson generalises: a model writing a proof will re-derive a Mathlib lemma rather than search
for it, and the re-derivation is invisible because it looks like ordinary work. Before promoting
any `PURE`-tagged lemma, grep Mathlib for it. The cheapest place to look is the module that already
provides the neighbouring lemmas you *are* using.

## Does `radialPoint` deserve its own home? Yes.

`radialPoint p z ρ = AffineMap.lineMap p z (ρ / dist p z)` — the point at distance `ρ` from `p`
along the ray towards `z`. Around it sit eight declarations, and the load-bearing one is

```lean
segment_inter_closedBall_eq_radial :
  closedBall p ρ ∩ segment ℝ p z = segment ℝ p (radialPoint p z ρ)
```

*Truncating a segment to a ball.* That is a statement about normed spaces with no planarity content
at all, and nobody looking for it would think to grep a file called `StarLemma.lean`. It is also
not in Mathlib (checked: Mathlib has `segment_subset_closedBall_left/right`, which are the easy
containments, not the equality).

So this is a genuine API, not a construction in passing — but the promotion should be **split**, not
wholesale:

| declaration | verdict |
|---|---|
| `dist_lineMap_center` | delete — use Mathlib's `dist_lineMap_left` |
| `radialPoint`, `dist_radialPoint`, `mem_sphere_radialPoint`, `radialPoint_mem_segment`, `segment_inter_closedBall_eq_radial` | **public**, coherent unit |
| `lineMap_eq_lineMap_radial` | stays `private` — an internal step of the above |
| `radialPoint_eq_iff_pos_parallel`, `radialPoint_ne_of_mem_openSegment`, `closedBall_inter_segment_eq_two_radii`, `closedBall_inter_two_segments_at_endpoint`, `two_radii_union_eq_star`, `coe_star_eq_sphere_inter_support` | the "star of two radii" facts — move *with* `radialPoint`, public |
| `ne_of_mem_openSegment_left`/`_right` | public; general `openSegment` facts, Mathlib has only the converse (`mem_openSegment_of_ne_left_right`) |

**Proposed home:** `Matroid/ForMathlib/Analysis/Convex/Segment.lean`, or a sibling
`ForMathlib/Analysis/Convex/RadialPoint.lean` if 200-odd lines is too much for one file. The
precedent is already set — that file holds `segment_union_eq_segment` and `isCompact_segment`,
*both of which `StarLemma.lean` already imports and uses*, so the import direction is proven
acyclic.

**The cost, stated honestly:** `private` → public is a maintenance commitment. You are promising a
name and an interface. `radialPoint` in particular is a definition, so its precise form (`lineMap`
with `ρ / dist p z`) becomes something downstream proofs will unfold. That is an argument for
promoting the *lemmas* eagerly and the *definition* deliberately.

## Who else wants this? `PLReduction.lean`, demonstrably

This is the question that decides whether level-2 work is worth doing, and here it has a concrete
answer. `Matroid/Graph/Planarity/PLReduction.lean` independently reinvents two of these.

**1. The same "clear a closed set" construction.** StarLemma builds

```lean
K := (range D.toDrawing.vertex \ {p}) ∪ ⋃ s ∈ Srest, segment ℝ s.1 s.2
```

PLReduction builds, per vertex `x`, the same set in disassembled form: `vertDists x` (distances to
all other vertices) and `edgeDists x` (`infDist` to each non-incident edge's range), then
`r x := (1/3) * min' (insert 1 (vertDists x ∪ edgeDists x))`. That is exactly
`(range D.vertex \ {D.vertex x}) ∪ ⋃ (e not incident to x), range (D.edgePath e)` — the *same
shape*, reached by taking a `Finset.min'` of per-object distances instead of one `infDist` of a
union.

It then needs `0 < r x`, which it gets by repeating
`(hrange_closed e).notMem_iff_infDist_pos (hrange_nonempty e) |>.mp …` — **including the explicit
nonemptiness argument that `exists_pos_le_dist_of_notMem` was written to eliminate** — and later
re-derives the "nothing in the set is within `r x`" contradiction through a
`lt_of_le_of_lt` / `mul_lt_iff_lt_one_left` chain, which is `hnotK` the long way round.

So `exists_pos_le_dist_of_notMem` **is** reusable here: all its hypotheses are already available
(`hrange_closed`, `D.vertex_injective`, `vertex_notMem_range_edgePath_of_not_inc`). The pairwise
ball-disjointness that motivates the `1/3` still goes through, since `δx/3 + δy/3 ≤ (2/3)·dist`.

> Verified to the level of *shape and available hypotheses*, not by performing the refactor. The
> ingredients are all present in PLReduction; nobody has typechecked the replacement.

**2. Radii meeting spheres.** `PLReduction.lean`'s own header says the construction makes arcs
"end on the two spheres", and that "two radii of the same ball ending at distinct points of its
sphere meet only [at the centre]". That is `radialPoint_ne_of_mem_openSegment` and
`radialPoint_eq_iff_pos_parallel`, stated informally in prose in one file while sitting proved and
`private` in another.

## The other misplaced clusters

- **The `PolygonalPath` block** — `exists_edge_ending_at_last`, `exists_edge_starting_at_first`,
  `isSimple_left_of_append_isSimpleArcOrLoop`, `isSimple_right_of_append_isSimpleArcOrLoop`,
  `toSet_inter_subset_of_append_isSimpleArcOrLoop`, `append_cast_right`, `cast_edges`,
  `IsSimpleLoop.hasNondegenerateEdges`, `eq_last_edge_of_mem_segment`,
  `eq_first_edge_of_mem_segment` — roughly 120 lines of general `PolygonalPath` API with an obvious
  existing home in `ForMathlib/Geometry/PolygonalPath/`. Same argument as `radialPoint`, different
  destination. These are the ones most likely to be re-proved by the next AI-written file, because
  they are exactly the lemmas you reach for when appending paths.
- **`pathInterior_subset_range`** — five lines, belongs wherever `pathInterior` is defined.
- **`faceSet_disjoint_of_ne`** — stated for a general `Drawing`, not a `PLDrawing`; belongs with the
  face API in `Graph/Planarity/Face.lean`.

## A rule of thumb

After level-1 extraction, run the domain-token scan and ask of each `PURE` hit: *if I needed this
in six months, where would I look for it?* If the answer is not the file it is in, it is misplaced.
If the answer is "Mathlib", check Mathlib first — it may already be there.

---

## Caveats for whoever picks this up

- **`exists_radius_vertex` still contains a `sorry`.** The degree conjunct
  `(Y.card : ℕ∞) = G.degree v.1` is unproven. The module docstring advertises this theorem "with
  the number of radii identified"; that claim is not yet backed. `degree_eq_ncard_source_add_target`
  appears to exist to serve it. **Nothing in this refactor touched that proof**, deliberately: a
  `sorry`'d declaration builds trivially, so a build-based oracle — whether the golfer's or a
  human's — accepts *any* rewrite inside it regardless of soundness.
- The file is **not** in `Matroid.lean`, so it is not part of the default build. Build it explicitly.
- Seven `automatically included section variable` warnings are pre-existing (verified by building
  the pre-refactor file); they concern `[NormedAddCommGroup V]`/`[NormedSpace ℝ V]` on the small
  path helpers and are unrelated to this work.
- The file still has **zero `grind`**. Closing that gap is a rewriting job, not an extraction one,
  and no mechanical rule reaches it.
- **`Dist.dist` is written out 99 times** where `dist` would do — `open Metric` is in scope. Pure
  AI verbosity, zero proof risk to change, but it is a large mechanical diff and neither this
  extraction pass nor `golf_rules.py` touches notation. Left deliberately; worth a single
  find-and-replace once someone has read the file.
