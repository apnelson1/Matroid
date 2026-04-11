#!/usr/bin/env python3
"""
Best-effort auto-golf for Lean tactic proofs (single file).

Transforms are heuristic and assume standard indentation (focus bullets `·`).
Run after replacing `constructor` and goal `apply` with `refine` (see pre-check).

Golfed tactic lines longer than --max-line-width (default 100) are wrapped at
spaces, preferring lower bracket depth. Use --max-line-width 0 to disable.

`lemma` / `def` / … headers with `:= by` or trailing `where` are re-packed to that
width: binder groups `{…}` and `(…)` are filled on the first lines, with continuation
indent taken from the original continuation lines. Headers that already fit the
limit *and* use at most two physical lines are left unchanged (so compact lemmas
stay as written); longer multi-line headers are still re-packed.

If the whole proof (after golfing) is a single `exact t`, `by` and `exact` are
removed: the declaration line ends with `:=` and `t` is kept on the next line
with the same indent the tactic had.

Pattern alternatives `foo|bar` (including `_|h` in `rintro`) are normalized to spaced `|`
(not `||`, not `|>`), including lines kept as `Raw` inside nested `have … := by` proofs.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from typing import List, Optional, Tuple, Union

Stmt = Union["Raw", "Plain", "Focus"]


@dataclass
class Raw:
    """Preserves a line verbatim (blank, comment, or out-of-structure)."""

    text: str


@dataclass
class Plain:
    indent: int
    content: str  # text after leading spaces
    # If set, `content` still equals `frozen_merged` and every source line was ≤ width: emit as-is.
    original_physical_lines: Optional[List[str]] = None
    frozen_merged: Optional[str] = None

    def full(self) -> str:
        return " " * self.indent + self.content


@dataclass
class Focus:
    indent: int
    header: str  # text after `·` on the bullet line
    body: List[Stmt] = field(default_factory=list)

    def full_header_line(self) -> str:
        return " " * self.indent + "· " + self.header


def code_before_comment(s: str) -> str:
    """Strip end-of-line `--` comment (heuristic, ignores strings)."""
    if "--" not in s:
        return s
    i = 0
    while i < len(s):
        if s.startswith("--", i):
            return s[:i].rstrip()
        i += 1
    return s


def line_indent_and_rest(line: str) -> Tuple[int, str]:
    m = re.match(r"^(\s*)(.*)$", line.rstrip("\n"))
    if not m:
        return 0, line
    ws, rest = m.group(1), m.group(2)
    # Expand tabs to spaces for counting (Lean typically uses spaces)
    indent = len(ws.expandtabs(4))
    return indent, rest


def is_blank_or_comment_line(line: str) -> bool:
    _, rest = line_indent_and_rest(line)
    t = rest.strip()
    return t == "" or t.startswith("--")


def is_comment_line(raw: str) -> bool:
    """
    True for Lean line comments (`-- ...`), using text after indentation.
    Do not use `code_before_comment` here: it strips `--` and would make `  -- x`
    look like blank/whitespace-only, breaking classification.
    """
    _, rest = line_indent_and_rest(raw.rstrip("\n\r"))
    return rest.lstrip().startswith("--")


# Lines starting a new proof command at the *same* script level (not a wrapped term).
_TACTIC_HEAD = re.compile(
    r"^(have|obtain|refine|exact|apply|simp\b|rfl\b|norm_num|ring|linarith|grind\b|grw\b|"
    r"rw\b|erw\b|simpa\b|simp_rw\b|conv\b|calc\b|by_contra|intro\b|rintro\b|cases\b|"
    r"induction\b|specialize\b|contradiction\b|done\b|skip\b|repeat\b|try\b|first\b|"
    r"all_goals|on_goal|swap\b|pick_goal|clear\b|subst\b|change\b|show\b|suffices\b|"
    r"let\b|set\b|replace\b|fail_if_unsolved_goals)\b"
)


def looks_like_fresh_tactic(rest: str) -> bool:
    r = rest.lstrip()
    if r.startswith("·"):
        return True
    return bool(_TACTIC_HEAD.match(r))


def _continuation_parts_use_tac_semicolon(parts: List[str]) -> bool:
    """
    True if a merged tactic used `;<>` / `<;>` / `; exact …` / etc. on a following line.
    Those should print as one line when they fit, not preserve the line break via freeze.
    """
    for p in parts[1:]:
        t = p.lstrip()
        if t.startswith("<;"):  # `<;>`, `<;`, …
            return True
        if t.startswith(";") and not t.startswith(";;"):
            return True
    return False


def extend_plain_with_continuations(
    lines: List[str],
    start_i: int,
    base_ind: int,
    first_rest: str,
    max_line_width: Optional[int] = None,
) -> Tuple[str, int, Optional[List[str]], Optional[str]]:
    """
    `exact` / `refine` / … may continue on deeper-indented lines (term wrapping).
    Absorb following lines while indent > base_ind and they do not start a new tactic.
    Returns merged tactic text (after indent), next index, and optional frozen layout
    when every absorbed physical line already fits `max_line_width`.
    """
    parts = [first_rest.rstrip()]
    physical: List[str] = [lines[start_i].rstrip("\n\r")]
    n = len(lines)
    j = start_i + 1
    while j < n:
        raw = lines[j]
        if raw.strip() == "" or is_comment_line(raw):
            break
        ind, rest = line_indent_and_rest(code_before_comment(raw))
        if ind <= base_ind:
            break
        if looks_like_fresh_tactic(rest):
            break
        parts.append(rest.strip())
        physical.append(raw.rstrip("\n\r"))
        j += 1
    merged = " ".join(parts)
    frozen_lines: Optional[List[str]] = None
    frozen_merged: Optional[str] = None
    if (
        max_line_width is not None
        and max_line_width > 0
        and all(len(p) <= max_line_width for p in physical)
        and not _continuation_parts_use_tac_semicolon(parts)
    ):
        frozen_lines = physical
        frozen_merged = merged
    return merged, j, frozen_lines, frozen_merged


def pre_check(lines: List[str]) -> bool:
    """
    Return True if file passes pre-check (no blocking constructor / goal apply).
    """
    bad: List[Tuple[int, str]] = []
    for i, line in enumerate(lines, start=1):
        code = code_before_comment(line)
        ind, rest = line_indent_and_rest(code)
        if rest.strip() == "":
            continue
        # Only consider lines that look like tactic lines (indented), skip decl headers
        if ind == 0 and not rest.lstrip().startswith("·"):
            continue
        st = rest.lstrip()
        if st.startswith("constructor") and re.match(r"constructor\b", st):
            bad.append((i, line.rstrip()))
        elif st.startswith("apply ") or st == "apply":
            # Goal apply: not `apply ... at ...`
            if not re.search(r"\bat\s+\S", code):
                bad.append((i, line.rstrip()))
    if bad:
        print(
            "Friendly reminder: Please replace 'constructor' and 'apply' (to the goal) "
            "with 'refine' before running this script so the auto-golfer knows what it "
            "is dealing with.",
            file=sys.stderr,
        )
        print("Found:", file=sys.stderr)
        for ln, txt in bad[:20]:
            print(f"  line {ln}: {txt}", file=sys.stderr)
        if len(bad) > 20:
            print(f"  ... and {len(bad) - 20} more", file=sys.stderr)
        return False
    return True


def parse_inner(
    i: int, lines: List[str], gate: int, max_line_width: Optional[int] = None
) -> Tuple[List[Stmt], int]:
    """Parse statements while non-blank lines satisfy indent > gate (blanks pass through)."""
    items: List[Stmt] = []
    n = len(lines)
    while i < n:
        raw = lines[i]
        if raw.strip() == "" or is_comment_line(raw):
            items.append(Raw(raw))
            i += 1
            continue
        ind, rest = line_indent_and_rest(code_before_comment(raw))
        if ind <= gate:
            return items, i
        if rest.startswith("·"):
            hdr = rest[1:].lstrip()
            i += 1
            sub, i = parse_inner(i, lines, ind, max_line_width)
            items.append(Focus(ind, hdr, sub))
        else:
            merged, i, f_lines, f_merged = extend_plain_with_continuations(
                lines, i, ind, rest, max_line_width
            )
            items.append(Plain(ind, merged, f_lines, f_merged))
    return items, i


def parse_proof_body(
    lines: List[str], max_line_width: Optional[int] = None
) -> List[Stmt]:
    """Parse a proof script fragment (list of physical lines)."""
    if not lines:
        return []
    # First meaningful line sets sibling gate
    gate = -1
    for raw in lines:
        if raw.strip() == "" or is_comment_line(raw):
            continue
        ind, _ = line_indent_and_rest(code_before_comment(raw))
        gate = ind
        break
    if gate < 0:
        return [Raw(l) for l in lines]
    items: List[Stmt] = []
    i = 0
    n = len(lines)
    while i < n:
        raw = lines[i]
        if raw.strip() == "" or is_comment_line(raw):
            items.append(Raw(raw))
            i += 1
            continue
        ind, rest = line_indent_and_rest(code_before_comment(raw))
        if ind < gate:
            items.append(Raw(raw))
            i += 1
            continue
        if ind > gate:
            # Should not happen in well-formed scripts; keep as raw
            items.append(Raw(raw))
            i += 1
            continue
        if rest.startswith("·"):
            hdr = rest[1:].lstrip()
            i += 1
            sub, i = parse_inner(i, lines, ind, max_line_width)
            items.append(Focus(ind, hdr, sub))
        else:
            merged, i, f_lines, f_merged = extend_plain_with_continuations(
                lines, i, ind, rest, max_line_width
            )
            items.append(Plain(ind, merged, f_lines, f_merged))
    return items


def _prefix_bracket_depth(s: str, end: int) -> int:
    d = 0
    for i in range(min(end, len(s))):
        d += bracket_delta(s[i])
    return d


def find_zero_depth_at_space(s: str) -> int:
    """Index of ` at ` (space-at-space) at bracket depth 0, or -1."""
    depth = 0
    for i, c in enumerate(s):
        if depth == 0 and s.startswith(" at ", i):
            return i
        depth += bracket_delta(c)
    return -1


def _rw_list_comma_breaks(head: str) -> List[int]:
    """Indices of `,` at depth 1 inside the first `rw`/`erw`/`grw`/`simp`/`simp_rw` `[...]` span."""
    m = re.search(r"\b(?:rw|erw|grw|simp_rw|simp\??)\s+\[", head)
    if not m:
        return []
    lb = m.end() - 1
    depth = 0
    commas: List[int] = []
    i = lb
    while i < len(head):
        c = head[i]
        depth += bracket_delta(c)
        if c == "," and depth == 1:
            commas.append(i)
        if depth == 0 and i > lb:
            break
        i += 1
    return commas


def _break_rw_head_before_last_list_entry(head: str) -> int:
    """
    Return index in `head` to split so continuation starts after a space following
    a comma (before the last `rw` list entry), or -1.
    """
    commas = _rw_list_comma_breaks(head)
    if not commas:
        return -1
    if len(commas) >= 2:
        return commas[-2] + 1
    return commas[0] + 1


_RW_LIKE_HEAD = re.compile(
    r"^(\s*)((?:rw|erw|grw|simp_rw|simp\??)\s+\[)(.*)$"
)


def wrap_rw_like_or_physical(phys_line: str, max_col: int, cont_extra: int = 2) -> List[str]:
    """
    Never break between `rw`/`simp`… and `[`; only wrap inside the `[…]` list (commas / spaces).
    Falls back to `wrap_physical_line` if the line is not a single bracketed rewrite/simplicand list.
    """
    m = _RW_LIKE_HEAD.match(phys_line)
    if not m:
        return wrap_physical_line(phys_line, max_col, cont_extra)
    ind, pkw, tail = m.group(1), m.group(2), m.group(3)
    cont = ind + " " * cont_extra
    depth = 1
    close_idx = -1
    for i, c in enumerate(tail):
        depth += bracket_delta(c)
        if depth == 0:
            close_idx = i
            break
    if close_idx < 0:
        return wrap_physical_line(phys_line, max_col, cont_extra)
    inner_close = tail[: close_idx + 1]
    after = tail[close_idx + 1 :].strip()
    if after:
        return wrap_physical_line(phys_line, max_col, cont_extra)
    head = pkw + inner_close
    if len(ind + head) <= max_col:
        return [phys_line]
    out: List[str] = []
    rem = head
    first = True
    while rem:
        pref = ind if first else cont
        room = max_col - len(pref)
        if len(rem) <= room:
            out.append(pref + rem)
            return out
        room_break = room - 10
        if room_break < 10:
            room_break = max(10, room * 2 // 3)
        br = _break_rw_head_before_last_list_entry(rem)
        if br <= 0 or br >= len(rem):
            br = -1
        if br < 0 or br > room_break:
            br2 = _find_wrap_break(rem, room_break)
            br = br2 if br2 and br2 > 0 else min(room_break, max(1, len(rem) - 1))
        piece = rem[:br].rstrip()
        if not piece:
            br = min(room_break, max(1, len(rem) - 1))
            piece = rem[:br].rstrip()
        out.append(pref + piece)
        rem = rem[br:].lstrip()
        first = False
    return out if out else [phys_line]


def wrap_tactic_line_smart(phys_line: str, max_col: int, cont_extra: int = 2) -> List[str]:
    """
    Like wrap_physical_line, but never breaks inside the ` at …` clause (Lean parses
    `at` + locations as one unit). For `rw […] at h`, break inside `[…]` before the
    last top-level comma, or else use depth-aware spaces in the last entry.
    """
    if len(phys_line) <= max_col:
        return [phys_line]
    m = re.match(r"^(\s*)(.*)$", phys_line)
    if not m:
        return [phys_line]
    ind, text = m.group(1), m.group(2)
    cont = ind + " " * cont_extra
    at_i = find_zero_depth_at_space(text)
    if at_i < 0:
        return wrap_rw_like_or_physical(phys_line, max_col, cont_extra)
    head = text[:at_i].rstrip()
    tail_suffix = " " + text[at_i:].lstrip()  # " at h …"

    one = ind + head + tail_suffix
    if len(one) <= max_col:
        return [one]

    out: List[str] = []
    rem = head
    first = True
    while rem:
        pref = ind if first else cont
        room = max_col - len(pref)
        if len(rem) + len(tail_suffix) <= room:
            out.append(pref + rem + tail_suffix)
            return out
        room_break = room - len(tail_suffix)
        if room_break < 10:
            room_break = max(10, room * 2 // 3)
        br = _break_rw_head_before_last_list_entry(rem)
        if br <= 0 or br >= len(rem):
            br = -1
        if br < 0 or br > room_break:
            br2 = _find_wrap_break(rem, room_break)
            br = br2 if br2 and br2 > 0 else min(room_break, max(1, len(rem) - 1))
        piece = rem[:br].rstrip()
        if not piece:
            br = min(room_break, max(1, len(rem) - 1))
            piece = rem[:br].rstrip()
        out.append(pref + piece)
        rem = rem[br:].lstrip()
        first = False
    return out if out else [phys_line]


def _find_wrap_break(s: str, budget: int) -> Optional[int]:
    """
    Largest split point <= budget: split into s[:idx].rstrip() and s[idx:].lstrip()
    preferring spaces at low bracket depth (top-level, then deeper).
    """
    if budget <= 0 or len(s) <= budget:
        return None
    lim = min(budget, len(s))
    for max_depth in (0, 1, 2, 4, 8, 9999):
        j = lim - 1
        while j > 0:
            if s[j] == " " and _prefix_bracket_depth(s, j) <= max_depth:
                return j + 1
            j -= 1
    return None


def wrap_physical_line(line: str, max_col: int, cont_extra: int = 2) -> List[str]:
    """
    Wrap one logical line (no \\n) to at most `max_col` columns.
    Continuation lines use the same leading indent plus `cont_extra` spaces.
    """
    if len(line) <= max_col:
        return [line]
    m = re.match(r"^(\s*)(.*)$", line)
    if not m:
        return [line]
    ind, text = m.group(1), m.group(2)
    cont = ind + " " * cont_extra
    out: List[str] = []
    rem = text
    first = True
    while rem:
        pref = ind if first else cont
        budget = max_col - len(pref)
        if budget < 8:
            out.append(pref + rem)
            break
        if len(rem) <= budget:
            out.append(pref + rem)
            break
        br = _find_wrap_break(rem, budget)
        if br is None or br <= 0:
            br = min(budget, max(1, len(rem) - 1))
        piece = rem[:br].rstrip()
        if not piece:
            br = min(budget, max(1, len(rem) - 1))
            piece = rem[:br].rstrip()
        out.append(pref + piece)
        rem = rem[br:].lstrip()
        first = False
    return out


def serialize_stmts(stmts: List[Stmt], max_line_width: Optional[int] = None) -> List[str]:
    out: List[str] = []
    for s in stmts:
        if isinstance(s, Raw):
            out.append(s.text if s.text.endswith("\n") else s.text + "\n")
        elif isinstance(s, Plain):
            if (
                max_line_width is not None
                and max_line_width > 0
                and s.original_physical_lines is not None
                and s.frozen_merged is not None
                and s.content == s.frozen_merged
            ):
                for ln in s.original_physical_lines:
                    out.append(ln + "\n")
            else:
                phys = s.full()
                if max_line_width is not None and len(phys) > max_line_width:
                    for ln in wrap_tactic_line_smart(phys, max_line_width):
                        out.append(ln + "\n")
                else:
                    out.append(phys + "\n")
        elif isinstance(s, Focus):
            hdr = s.full_header_line().rstrip("\n")
            if max_line_width is not None and len(hdr) > max_line_width:
                for ln in wrap_tactic_line_smart(hdr, max_line_width):
                    out.append(ln + "\n")
            else:
                out.append(hdr + "\n")
            out.extend(serialize_stmts(s.body, max_line_width=max_line_width))
        else:
            raise TypeError(s)
    return out


def replace_first_hole(s: str, repl: str) -> str:
    idx = s.find("?_")
    if idx < 0:
        return s
    return s[:idx] + repl + s[idx + 2 :]


def bracket_delta(c: str) -> int:
    if c in "⟨([{":
        return 1
    if c in "⟩)]}":
        return -1
    return 0


def split_top_level_commas(s: str) -> List[str]:
    """Split `s` by commas at bracket depth 0 (Lean `⟨...⟩`, `()`, `[]`)."""
    parts: List[str] = []
    depth = 0
    start = 0
    for i, c in enumerate(s):
        depth += bracket_delta(c)
        if c == "," and depth == 0:
            parts.append(s[start:i])
            start = i + 1
    parts.append(s[start:])
    return parts


def join_top_level_commas(parts: List[str]) -> str:
    return ", ".join(parts)


def parse_refine_angle_tuple(content: str) -> Optional[Tuple[str, List[str], str]]:
    """
    If `content` is `refine ⟨inner⟩suffix` or `exact ⟨inner⟩suffix`, return
    (keyword + \" ⟨\", list of top-level comma components inside, \"⟩\"+suffix).
    """
    t = content.strip()
    m = re.match(r"^(refine|exact)\s+⟨", t)
    if not m:
        return None
    open_idx = m.end() - 1
    depth = 0
    j = open_idx
    while j < len(t):
        depth += bracket_delta(t[j])
        if depth == 0:
            inner = t[open_idx + 1 : j]
            suffix = t[j + 1 :]
            kw = m.group(1)
            return (f"{kw} ⟨", split_top_level_commas(inner), "⟩" + suffix)
        j += 1
    return None


def rebuild_refine_angle(prefix: str, components: List[str], tail: str) -> str:
    return prefix + join_top_level_commas(components) + tail


def focus_index_in_siblings(stmts: List[Stmt], refine_i: int, focus_j: int) -> int:
    """Which `·` block index (0-based) `focus_j` is among Focus nodes after `refine_i`."""
    c = 0
    for k in range(refine_i + 1, focus_j + 1):
        if isinstance(stmts[k], Focus):
            c += 1
    return c - 1


def replace_component_hole(components: List[str], comp_idx: int, replacement: str) -> bool:
    """Replace the first `?_` in components[comp_idx] with `replacement`. If the component
    is exactly `?_`, replace the whole component. Returns False if index out of range."""
    if comp_idx < 0 or comp_idx >= len(components):
        return False
    comp = components[comp_idx]
    if comp.strip() == "?_":
        components[comp_idx] = replacement
        return True
    if "?_" not in comp:
        return False
    components[comp_idx] = replace_first_hole(comp, replacement)
    return True


def merge_intro_vars_with_term(intro_vars: str, kw_line: str) -> str:
    """Build term `fun vars ↦ rhs` from `intro vars` + `refine|exact|apply rhs`."""
    m = REFINE_KW.match(kw_line.strip())
    if not m:
        return kw_line
    rest = m.group(2).lstrip()
    mfun = re.match(r"^fun\s+(.+?)\s*↦\s*(.*)$", rest)
    if mfun:
        exist, tail = mfun.group(1), mfun.group(2)
        return f"fun {intro_vars} {exist} ↦ {tail}"
    return f"fun {intro_vars} ↦ {rest}"


def next_stmt_index(stmts: List[Stmt], start: int) -> int:
    j = start + 1
    while j < len(stmts) and isinstance(stmts[j], Raw):
        j += 1
    return j


def try_merge_intro_refine_into_prior_tuple(stmts: List[Stmt], i_intro: int) -> bool:
    """
    When `intro` + `refine|exact|apply` are sibling Plains, merge into the last
    top-level tuple hole of an earlier `refine ⟨...⟩` / `exact ⟨...⟩` line.
    """
    # find refine line index (skip focus blocks and raw lines)
    j = i_intro - 1
    ref_i = -1
    while j >= 0:
        if isinstance(stmts[j], Raw):
            j -= 1
            continue
        if isinstance(stmts[j], Focus):
            j -= 1
            continue
        if isinstance(stmts[j], Plain):
            parsed = parse_refine_angle_tuple(stmts[j].content)
            if parsed and "?_" in stmts[j].content:
                ref_i = j
                break
        j -= 1
    if ref_i < 0:
        return False
    s_intro = stmts[i_intro]
    j_kw = next_stmt_index(stmts, i_intro)
    if j_kw >= len(stmts):
        return False
    s_kw = stmts[j_kw]
    if not isinstance(s_intro, Plain) or not isinstance(s_kw, Plain):
        return False
    iv = parse_intro_vars(s_intro.content)
    if iv is None:
        return False
    if not REFINE_KW.match(s_kw.content.strip()):
        return False
    parsed = parse_refine_angle_tuple(stmts[ref_i].content)
    if not parsed:
        return False
    prefix, components, tail = parsed
    # fill last component that still contains ?_
    filled = False
    for idx in range(len(components) - 1, -1, -1):
        if "?_" in components[idx]:
            term = merge_intro_vars_with_term(iv, s_kw.content)
            if components[idx].strip() == "?_":
                components[idx] = term
            else:
                components[idx] = replace_first_hole(components[idx], term)
            filled = True
            break
    if not filled:
        return False
    stmts[ref_i] = Plain(stmts[ref_i].indent, rebuild_refine_angle(prefix, components, tail))
    del stmts[j_kw]
    del stmts[i_intro]
    return True


def try_merge_refine_intro_into_angle_tuple(stmts: List[Stmt], i_refine: int) -> bool:
    """
    When `refine ⟨…⟩` / `exact ⟨…⟩` with a `?_` is immediately followed by `intro …`,
    fold the binders into the last tuple component: `…, fun vars ↦ ?_`, and drop `intro`.
    """
    s_ref = stmts[i_refine]
    j_intro = next_stmt_index(stmts, i_refine)
    if j_intro >= len(stmts):
        return False
    s_intro = stmts[j_intro]
    if not isinstance(s_ref, Plain) or not isinstance(s_intro, Plain):
        return False
    if s_ref.indent != s_intro.indent:
        return False
    iv = parse_intro_vars(s_intro.content)
    if iv is None:
        return False
    parsed = parse_refine_angle_tuple(s_ref.content)
    if not parsed:
        return False
    prefix, components, tail = parsed
    lam = f"fun {iv} ↦ ?_"
    filled = False
    for idx in range(len(components) - 1, -1, -1):
        if "?_" not in components[idx]:
            continue
        comp = components[idx]
        if comp.strip() == "?_":
            components[idx] = lam
        elif comp.count("?_") == 1:
            components[idx] = replace_first_hole(comp, lam)
        else:
            return False
        filled = True
        break
    if not filled:
        return False
    stmts[i_refine] = Plain(s_ref.indent, rebuild_refine_angle(prefix, components, tail))
    del stmts[j_intro]
    return True


INTRO_HDR = re.compile(r"^(intro|rintro)\s+(?!rfl\b)(.+)$")
REFINE_KW = re.compile(r"^(refine|exact|apply)\s+(.*)$")


def parse_intro_vars(hdr: str) -> Optional[str]:
    """
    Bindings after `intro` / `rintro` for merging into `fun … ↦ …`.
    Returns None for `intro rfl` / leading `rfl` (excluded by INTRO_HDR) and when
    the pattern contains `rfl` anywhere (e.g. `rintro _ ⟨M, hM, rfl⟩`).
    """
    m = INTRO_HDR.match(hdr.strip())
    if not m:
        return None
    rest = m.group(2).strip()
    if re.search(r"\brfl\b", rest):
        return None
    return rest


def merge_intro_into_kw_line(intro_vars: str, content: str) -> str:
    """content is full line after indent, e.g. `refine foo`."""
    m = REFINE_KW.match(content.strip())
    if not m:
        return content
    kw, rest = m.group(1), m.group(2)
    rest = rest.lstrip()
    mfun = re.match(r"^fun\s+(.+?)\s*↦\s*(.*)$", rest)
    if mfun:
        exist, tail = mfun.group(1), mfun.group(2)
        return f"{kw} fun {intro_vars} {exist} ↦ {tail}"
    return f"{kw} fun {intro_vars} ↦ {rest}"


def is_refine_exact_header(hdr: str) -> Optional[Tuple[str, str]]:
    """Return (refine|exact, rest) if header is refine/exact of an expression."""
    t = hdr.strip()
    m = re.match(r"^(refine|exact)\s+(.+)$", t)
    if not m:
        return None
    return m.group(1), m.group(2)


def _parenthesize_for_hole_splice(expr: str) -> str:
    """Wrap `expr` so it parses as one argument after replacing `?_` (e.g. `f ?_` + `g a b` → `f (g a b)`)."""
    e = expr.strip()
    if not e:
        return e
    if e.startswith("(") and e.endswith(")"):
        depth = 0
        ok = True
        for i, ch in enumerate(e):
            depth += bracket_delta(ch)
            if depth < 0:
                ok = False
                break
        if ok and depth == 0:
            return e
    return f"({e})"


def transform_refine_refine_exact_siblings(stmts: List[Stmt]) -> bool:
    """
    T3 (sibling): `refine … ?_ …` then same-indent `refine expr` or `exact expr`
    (no `·` required). Splices `expr` into the first remaining `?_` of the parent.
    """
    changed = False
    for s in stmts:
        if isinstance(s, Focus) and transform_refine_refine_exact_siblings(s.body):
            changed = True
    i = 0
    while i < len(stmts):
        if isinstance(stmts[i], Raw):
            i += 1
            continue
        j = next_stmt_index(stmts, i)
        if j >= len(stmts):
            break
        a, b = stmts[i], stmts[j]
        if not isinstance(a, Plain) or not isinstance(b, Plain):
            i += 1
            continue
        if a.indent != b.indent:
            i += 1
            continue
        code = a.content
        if not code.startswith("refine ") or "?_" not in code:
            i += 1
            continue
        re_child = is_refine_exact_header(b.content)
        if re_child is None:
            i += 1
            continue
        _, expr = re_child
        expr_w = _parenthesize_for_hole_splice(expr)
        parsed = parse_refine_angle_tuple(code)
        if parsed is not None:
            prefix, components, tail = parsed
            comps = list(components)
            if replace_component_hole(comps, 0, expr_w):
                new_code = rebuild_refine_angle(prefix, comps, tail)
            else:
                new_code = replace_first_hole(code, expr_w)
        else:
            new_code = replace_first_hole(code, expr_w)
        stmts[i] = Plain(a.indent, new_code)
        del stmts[j]
        changed = True
    return changed


def transform_refine_focus_chain(stmts: List[Stmt]) -> bool:
    """T2+T3: parent Plain refine with ?_ + Focus header intro or refine/exact."""
    changed = False
    i = 0
    while i < len(stmts) - 1:
        a, b = stmts[i], stmts[i + 1]
        if isinstance(a, Plain) and isinstance(b, Focus):
            code = a.content
            if (code.startswith("refine ") or code.startswith("exact ")) and "?_" in code:
                parsed = parse_refine_angle_tuple(code)
                fidx = focus_index_in_siblings(stmts, i, i + 1)
                vars_ = parse_intro_vars(b.header)
                re_info = is_refine_exact_header(b.header)
                if parsed is not None and vars_ is not None:
                    prefix, components, tail = parsed
                    repl = f"fun {vars_} ↦ ?_"
                    if replace_component_hole(components, fidx, repl):
                        stmts[i] = Plain(a.indent, rebuild_refine_angle(prefix, components, tail))
                        if b.body:
                            first = b.body[0]
                            if isinstance(first, Plain):
                                b.header = first.content
                                b.body = b.body[1:]
                            else:
                                b.header = ""
                        else:
                            b.header = ""
                        changed = True
                        continue
                if parsed is not None and re_info is not None:
                    _, expr = re_info
                    prefix, components, tail = parsed
                    if replace_component_hole(components, fidx, expr):
                        stmts[i] = Plain(a.indent, rebuild_refine_angle(prefix, components, tail))
                        if b.body:
                            first = b.body[0]
                            if isinstance(first, Plain):
                                b.header = first.content
                                b.body = b.body[1:]
                            else:
                                b.header = ""
                        else:
                            b.header = ""
                        changed = True
                        continue
                # Non-`⟨⟩` refine: fall back to first hole
                if parsed is None and code.startswith("refine ") and vars_ is not None:
                    new_code = replace_first_hole(code, f"fun {vars_} ↦ ?_")
                    stmts[i] = Plain(a.indent, new_code)
                    if b.body:
                        first = b.body[0]
                        if isinstance(first, Plain):
                            b.header = first.content
                            b.body = b.body[1:]
                        else:
                            b.header = ""
                    else:
                        b.header = ""
                    changed = True
                    continue
                if parsed is None and code.startswith("refine ") and re_info is not None:
                    _, expr = re_info
                    new_code = replace_first_hole(code, expr)
                    stmts[i] = Plain(a.indent, new_code)
                    if b.body:
                        first = b.body[0]
                        if isinstance(first, Plain):
                            b.header = first.content
                            b.body = b.body[1:]
                        else:
                            b.header = ""
                    else:
                        b.header = ""
                    changed = True
                    continue
        if isinstance(a, Focus) and transform_refine_focus_chain(a.body):
            changed = True
        i += 1
    for s in stmts:
        if isinstance(s, Focus) and transform_refine_focus_chain(s.body):
            changed = True
    return changed


def transform_intro_refine_siblings(stmts: List[Stmt]) -> bool:
    """T1: intro↔refine/exact/apply — merge adjacent lines or into `⟨⟩` tuple holes."""
    changed = False

    def scan_list(items: List[Stmt]) -> bool:
        i = 0
        while i < len(items):
            if isinstance(items[i], Raw):
                i += 1
                continue
            j = next_stmt_index(items, i)
            if j >= len(items):
                break
            s1, s2 = items[i], items[j]
            if isinstance(s1, Plain) and isinstance(s2, Plain) and s1.indent == s2.indent:
                # `refine ⟨…, ?_⟩` / `exact ⟨…⟩` then `intro …` → `…, fun … ↦ ?_`
                if (
                    parse_refine_angle_tuple(s1.content) is not None
                    and "?_" in s1.content
                    and parse_intro_vars(s2.content) is not None
                ):
                    if try_merge_refine_intro_into_angle_tuple(items, i):
                        return True
                v = parse_intro_vars(s1.content)
                if v is not None and REFINE_KW.match(s2.content.strip()):
                    if try_merge_intro_refine_into_prior_tuple(items, i):
                        return True
                    items[j] = Plain(s2.indent, merge_intro_into_kw_line(v, s2.content))
                    del items[i]
                    return True
            i += 1
        return False

    for s in stmts:
        if isinstance(s, Focus) and transform_intro_refine_siblings(s.body):
            changed = True
    while scan_list(stmts):
        changed = True
    return changed


def non_raw_stmts(items: List[Stmt]) -> List[Stmt]:
    return [s for s in items if not isinstance(s, Raw)]


def same_indent_plain_follows(items: List[Stmt], idx: int, base_indent: int) -> bool:
    """
    True if some later sibling is a Plain or Focus at `base_indent` (e.g. `wlog` / `cases` second branch).
    Skips deeper-indented noise so we do not treat a stray inner line as the only follower.
    """
    j = idx
    while j < len(items):
        s = items[j]
        if isinstance(s, Raw):
            j += 1
            continue
        if isinstance(s, Plain):
            if s.indent == base_indent:
                return True
            if s.indent < base_indent:
                return False
            j += 1
            continue
        if isinstance(s, Focus):
            if s.indent == base_indent:
                return True
            if s.indent < base_indent:
                return False
            j += 1
            continue
        j += 1
    return False


def transform_last_focus_dot(stmts: List[Stmt]) -> bool:
    """
    T6: among sibling Focus nodes, strip `·` from the last Focus and unindent its body,
    only when that block is the last subgoal at its indentation (no same-indent Plain / Focus
    follows). Skips the first `·` after `wlog`, which shares a level with the unfocused branch.
    """
    changed = False

    def shift_body(st: Stmt, d: int) -> Stmt:
        if isinstance(st, Plain):
            return Plain(max(0, st.indent - d), st.content)
        if isinstance(st, Focus):
            st.indent = max(0, st.indent - d)
            st.body = [shift_body(x, d) for x in st.body]
            return st
        if isinstance(st, Raw):
            return st
        raise TypeError(st)

    def work(items: List[Stmt]) -> None:
        nonlocal changed
        for s in items:
            if isinstance(s, Focus):
                work(s.body)
        i = 0
        while i < len(items):
            if not isinstance(items[i], Focus):
                i += 1
                continue
            run_start = i
            while i < len(items) and isinstance(items[i], Focus):
                i += 1
            run = items[run_start:i]
            last = run[-1]
            assert isinstance(last, Focus)
            # `wlog` first case is `· …`; the second case follows at the same indent without `·`.
            if run_start > 0:
                prev = items[run_start - 1]
                if isinstance(prev, Plain) and re.match(r"^\s*wlog\b", prev.content):
                    continue
            # If a same-indent Plain / Focus follows, this is not the last subgoal at this level.
            if same_indent_plain_follows(items, i, last.indent):
                continue
            # Header line keeps parent sibling indent; body lines shift up by 2
            header_plain = Plain(last.indent, last.header)
            new_body = [shift_body(x, 2) for x in last.body]
            repl: List[Stmt] = [header_plain] + new_body
            items[run_start:i] = run[:-1] + repl
            changed = True
            i = run_start + len(run[:-1]) + len(repl)

    work(stmts)
    return changed


def try_hole_notation(expr: str) -> Optional[str]:
    """
    T5: If expr is `fun x ↦ body` with x used once in body and no ?_, produce bracketed hole.
    """
    m = re.match(r"^fun\s+(\w+)\s*↦\s*(.+)$", expr.strip())
    if not m:
        return None
    var, body = m.group(1), m.group(2)
    if "?_" in body:
        return None
    # Count whole-word occurrences
    cnt = len(re.findall(rf"\b{re.escape(var)}\b", body))
    if cnt != 1:
        return None
    # Method: var.rest args
    mm = re.match(rf"^{re.escape(var)}\.(\w+)(.*)$", body.strip())
    if mm:
        method, tail = mm.group(1), mm.group(2)
        return f"(·.{method}{tail})"
    # Function call: f var tail  -> (f · tail)
    # Find first token as callee
    mc = re.match(r"^(\S+)\s+", body.strip())
    if mc:
        callee = mc.group(1)
        if callee == var:
            return None
        rest = body.strip()[len(callee) :].lstrip()
        # rest should be var possibly followed by more args
        if rest.startswith(var):
            tail = rest[len(var) :].lstrip()
            return f"({callee} · {tail})" if tail else f"({callee} ·)"
    return None


def transform_hole_notation_in_str(s: str) -> Tuple[str, bool]:
    """Replace eligible `fun x ↦ …` subexpressions with parenthesized hole syntax."""
    changed = False
    out: List[str] = []
    i = 0
    n = len(s)
    while i < n:
        j = s.find("fun ", i)
        if j < 0:
            out.append(s[i:])
            break
        out.append(s[i:j])
        m = re.match(r"fun\s+(\w+)\s*↦\s*", s[j:])
        if not m:
            out.append(s[j])
            i = j + 1
            continue
        start = j
        k = j + m.end()
        depth = 0
        end = k
        while end < n:
            c = s[end]
            if c in "\"'":
                q = c
                end += 1
                while end < n:
                    if s[end] == "\\":
                        end += 2
                        continue
                    if s[end] == q:
                        end += 1
                        break
                    end += 1
                continue
            if depth == 0 and end > k and c in ",⟩)":
                break
            depth += bracket_delta(c)
            end += 1
        fragment = s[start:end]
        cand = try_hole_notation(fragment.strip())
        if cand:
            out.append(cand)
            changed = True
            i = end
            continue
        out.append(fragment)
        i = end
    return "".join(out), changed


def transform_hole_notation_stmts(stmts: List[Stmt]) -> bool:
    ch = False
    for s in stmts:
        if isinstance(s, Plain):
            nc, c = transform_hole_notation_in_str(s.content)
            if c:
                s.content = nc
                ch = True
        elif isinstance(s, Focus):
            nh, c1 = transform_hole_notation_in_str(s.header)
            if c1:
                s.header = nh
                ch = True
            if transform_hole_notation_stmts(s.body):
                ch = True
    return ch


def is_have_obtain_one_liner(content: str) -> bool:
    c = content.strip()
    return bool(re.match(r"^(have|obtain)\b.*:=\s*by\s+simp\s*$", c))


# `simp` -> `simp?` but not `simp?`, not `simp only`, not `simp_rw` / `simple` / …
_SIMP_HEAD = re.compile(r"^(\s*)\bsimp\b(?!\?)(?!\s+only\b)")


# Tight `|` between pattern atoms: Unicode names or a lone `_` (e.g. `rintro (_|h)`); not `||`, not `|>`.
# Must not match `a | b` (already spaced) or the loop would never terminate.
_BAR_ATOM = r"(?:[^\W\d_][\w.']*|_)"
_PATTERN_BAR_TIGHT = re.compile(
    rf"(?<![\w.'])({_BAR_ATOM})\|(?!\|)(?!>)({_BAR_ATOM})(?![\w.'])"
)


def normalize_pattern_bar_spacing(s: str) -> Tuple[str, bool]:
    """
    Insert spaces around tight `|` between pattern atoms, e.g. `(hempty|hne)`, `(_|h)` -> spaced `|`.
    Repeats until stable so `a|b|c` becomes `a | b | c`.
    """
    changed = False
    while True:
        s2, n = _PATTERN_BAR_TIGHT.subn(r"\1 | \2", s)
        if n == 0:
            return s, changed
        changed = True
        s = s2


def transform_pattern_bar_spacing(stmts: List[Stmt]) -> bool:
    """Normalize tight `|` in Plain, Focus headers, and single-line Raw (nested `have` proof lines)."""

    def work(items: List[Stmt]) -> bool:
        ch = False
        for s in items:
            if isinstance(s, Plain):
                new_c, c = normalize_pattern_bar_spacing(s.content)
                if c:
                    s.content = new_c
                    ch = True
            elif isinstance(s, Raw):
                t = s.text
                core = t.rstrip("\n\r")
                if "\n" not in core:
                    new_c, c = normalize_pattern_bar_spacing(core)
                    if c:
                        s.text = new_c + ("\n" if t.endswith("\n") else "")
                        ch = True
            elif isinstance(s, Focus):
                new_h, c = normalize_pattern_bar_spacing(s.header)
                if c:
                    s.header = new_h
                    ch = True
                if work(s.body):
                    ch = True
        return ch

    return work(stmts)


def _try_simp_to_simpq_content(content: str) -> Optional[str]:
    if not _SIMP_HEAD.match(content):
        return None
    return _SIMP_HEAD.sub(r"\1simp?", content, count=1)


# Full physical line (indent + optional `· ` before `simp`, e.g. lines kept as `Raw` when `ind > gate`).
_SIMP_HEAD_PHYSICAL = re.compile(
    r"^(\s*)(·\s*)?(\bsimp\b)(?!\?)(?!\s+only\b)"
)


def _try_simp_to_simpq_physical_code(code: str) -> Optional[str]:
    m = _SIMP_HEAD_PHYSICAL.match(code)
    if not m:
        return None
    return m.group(1) + (m.group(2) or "") + "simp?" + code[m.end() :]


def _physical_line_has_following_same_indent_tactic(lines: List[str], i: int) -> bool:
    """
    True if some later non-blank line is a sibling tactic at the same indent as `lines[i]`
    (or a `·` line at that indent), mimicking `non_raw_stmts(tail)` for structured scripts.
    """
    code_i = code_before_comment(lines[i].rstrip("\n"))
    ind_i, _ = line_indent_and_rest(code_i)
    j = i + 1
    while j < len(lines):
        raw = lines[j]
        if raw.strip() == "" or is_comment_line(raw):
            j += 1
            continue
        code_j = code_before_comment(raw.rstrip("\n"))
        ind_j, rest_j = line_indent_and_rest(code_j)
        if ind_j < ind_i:
            return False
        if ind_j == ind_i:
            r = rest_j.lstrip()
            if r.startswith("·"):
                return True
            return looks_like_fresh_tactic(rest_j)
        j += 1
    return False


def _replace_simp_head_on_physical_line(line: str) -> Optional[str]:
    ends_nl = line.endswith("\n")
    raw = line.rstrip("\n\r")
    code, comment = split_lean_line_code_and_comment(raw)
    if is_have_obtain_one_liner(code.strip()):
        return None
    new_code = _try_simp_to_simpq_physical_code(code)
    if new_code is None:
        return None
    out = new_code + comment
    return out + ("\n" if ends_nl else "")


def transform_simp_to_simpq_physical(lines: List[str]) -> bool:
    """
    `simp` → `simp?` on physical lines missed by `transform_simp_to_simpq` (nested scripts
    parsed as `Raw` because `ind > gate` in `parse_proof_body`).
    """
    changed = False
    for i in range(len(lines)):
        raw = lines[i]
        if raw.strip() == "" or is_comment_line(raw):
            continue
        code = code_before_comment(raw.rstrip("\n"))
        if is_have_obtain_one_liner(code.strip()):
            continue
        if _SIMP_HEAD_PHYSICAL.match(code) is None:
            continue
        if not _physical_line_has_following_same_indent_tactic(lines, i):
            continue
        new_line = _replace_simp_head_on_physical_line(raw)
        if new_line is not None and new_line != raw:
            lines[i] = new_line
            changed = True
    return changed


def transform_simp_to_simpq(stmts: List[Stmt]) -> bool:
    """T4: `simp` / `simp at …` / `simp […]` on Plain lines and `· simp` headers (not `simp only`)."""
    changed = False

    def work(items: List[Stmt]) -> None:
        nonlocal changed
        for idx, s in enumerate(items):
            if isinstance(s, Plain):
                if is_have_obtain_one_liner(s.content):
                    continue
                # Do not use `non_raw_stmts(tail)`: after `have … := by` as one Plain line, the
                # indented proof (`change`, `simp`, …) is flattened as siblings; a following
                # less-indented `have` is not a continuation of `simp` (see `same_indent_plain_follows`).
                if not same_indent_plain_follows(items, idx + 1, s.indent):
                    continue
                new_c = _try_simp_to_simpq_content(s.content)
                if new_c is not None:
                    s.content = new_c
                    changed = True
            elif isinstance(s, Focus):
                # `· simp` lives in `Focus.header`, not a Plain line.
                body_tail = non_raw_stmts(s.body)
                if len(body_tail) > 0 or same_indent_plain_follows(items, idx + 1, s.indent):
                    new_h = _try_simp_to_simpq_content(s.header)
                    if new_h is not None:
                        s.header = new_h
                        changed = True
                work(s.body)

    work(stmts)
    return changed


def transform_refine_to_exact(stmts: List[Stmt]) -> bool:
    changed = False
    for s in stmts:
        if isinstance(s, Plain):
            if s.content.startswith("refine ") and "?_" not in s.content:
                s.content = "exact " + s.content[len("refine ") :]
                changed = True
        elif isinstance(s, Focus):
            nh = s.header
            if nh.startswith("refine ") and "?_" not in nh:
                s.header = "exact " + nh[len("refine ") :]
                changed = True
            if transform_refine_to_exact(s.body):
                changed = True
    return changed


def transform_all(stmts: List[Stmt]) -> None:
    """Fixed-point loop of transformations."""
    while True:
        c = False
        while transform_refine_focus_chain(stmts):
            c = True
        if transform_refine_refine_exact_siblings(stmts):
            c = True
        if transform_intro_refine_siblings(stmts):
            c = True
        if not c:
            break
    while True:
        c = False
        if transform_last_focus_dot(stmts):
            c = True
        if transform_hole_notation_stmts(stmts):
            c = True
        if transform_simp_to_simpq(stmts):
            c = True
        if transform_pattern_bar_spacing(stmts):
            c = True
        if transform_refine_to_exact(stmts):
            c = True
        # Second pass for chains enabled by focus-dot removal
        while transform_refine_focus_chain(stmts):
            c = True
        if transform_refine_refine_exact_siblings(stmts):
            c = True
        if transform_intro_refine_siblings(stmts):
            c = True
        if not c:
            break
    # Final hole / refine->exact sweep
    while transform_hole_notation_stmts(stmts):
        pass
    while transform_refine_to_exact(stmts):
        pass
    transform_pattern_bar_spacing(stmts)


DECL_START = re.compile(
    r"^(lemma|theorem|example|def|instance|axiom|structure|class|inductive|abbrev)\b"
)

def find_resulting_type_colon(sig: str) -> int:
    """Index of the `:` that separates binders from the result type (depth 0, not `::`)."""
    depth = 0
    i = 0
    while i < len(sig):
        c = sig[i]
        depth += bracket_delta(c)
        if depth == 0 and c == ":":
            if i + 1 < len(sig) and sig[i + 1] == ":":
                i += 1
            else:
                return i
        i += 1
    return -1


def parse_binder_chunks(binders: str) -> List[str]:
    """Top-level `{…}`, `(…)`, and `[…]` (instances) groups in a binder prefix."""
    chunks: List[str] = []
    i = 0
    n = len(binders)
    while i < n:
        while i < n and binders[i].isspace():
            i += 1
        if i >= n:
            break
        if binders[i] not in "{([":  # `[` = e.g. `[G.Loopless]`
            return []
        start = i
        depth = 0
        while i < n:
            depth += bracket_delta(binders[i])
            i += 1
            if depth == 0:
                chunks.append(binders[start : i].strip())
                break
        else:
            return []
    return chunks


def collect_declaration_block(lines: List[str], start: int) -> Optional[Tuple[int, List[str]]]:
    """Collect a `lemma`/`def`/… header: either through `:= by` or through a line ending in `where`."""
    if start >= len(lines):
        return None
    code0 = code_before_comment(lines[start].rstrip("\n"))
    if not re.match(r"^\s*(lemma|theorem|example|def|instance|abbrev)\s+\S", code0):
        return None
    parts: List[str] = [lines[start].rstrip("\n")]
    j = start + 1
    c0 = code_before_comment(parts[0])
    if ":= by" in c0:
        return j, parts
    if re.search(r"\bwhere\s*$", c0.rstrip()):
        return j, parts
    while j < len(lines):
        raw = lines[j]
        if raw.strip() == "" or is_comment_line(raw):
            break
        code = code_before_comment(raw.rstrip("\n"))
        lead = len(raw) - len(raw.lstrip(" \t"))
        if lead == 0 and re.match(
            r"^(lemma|theorem|example|def|instance|abbrev|axiom|structure|class|inductive)\s+\S",
            code.lstrip(),
        ):
            break
        parts.append(raw.rstrip("\n"))
        if ":= by" in code:
            j += 1
            break
        if re.search(r"\bwhere\s*$", code.rstrip()):
            j += 1
            break
        j += 1
    joined = parts[0] + " " + " ".join(p.lstrip() for p in parts[1:])
    jc = code_before_comment(joined)
    if ":= by" in jc:
        return j, parts
    last = code_before_comment(parts[-1]).rstrip()
    if re.search(r"\bwhere\s*$", last):
        return j, parts
    return None


HAVE_BY_START = re.compile(r"^\s*have\s+\S+\s+")


def collect_have_by_block(lines: List[str], start: int) -> Optional[Tuple[int, List[str]]]:
    """Collect a proof-local `have … : … := by` header split across physical lines."""
    if start >= len(lines):
        return None
    code0 = code_before_comment(lines[start].rstrip("\n"))
    if not HAVE_BY_START.match(code0):
        return None
    parts: List[str] = [lines[start].rstrip("\n")]
    base = len(lines[start]) - len(lines[start].lstrip(" \t"))
    j = start + 1
    if ":= by" in code0:
        return j, parts
    while j < len(lines):
        raw = lines[j]
        if raw.strip() == "" or is_comment_line(raw):
            break
        code = code_before_comment(raw.rstrip("\n"))
        lead = len(raw) - len(raw.lstrip(" \t"))
        if lead == 0 and re.match(
            r"^(lemma|theorem|example|def|instance|abbrev|axiom|structure|class|inductive)\s+\S",
            code.lstrip(),
        ):
            break
        if j > start:
            ind = lead
            if ind < base:
                break
            if ind == base and re.match(r"^\s*have\s+\S", code):
                break
        parts.append(raw.rstrip("\n"))
        if ":= by" in code:
            j += 1
            break
        j += 1
    joined = parts[0] + " " + " ".join(p.lstrip() for p in parts[1:])
    jc = code_before_comment(joined)
    if ":= by" not in jc:
        return None
    return j, parts


def flatten_decl_block(parts: List[str]) -> str:
    bits = [code_before_comment(parts[0]).strip()]
    for p in parts[1:]:
        bits.append(code_before_comment(p.lstrip()).strip())
    return " ".join(bits)


def flatten_have_by_block(parts: List[str]) -> str:
    """Like `flatten_decl_block` but keep the leading indent of the first physical line."""
    raw0 = parts[0].rstrip("\n")
    c0 = code_before_comment(raw0)
    ind = len(c0) - len(c0.lstrip(" \t"))
    lead = c0[:ind]
    bits = [c0[ind:].strip()]
    for p in parts[1:]:
        bits.append(code_before_comment(p.lstrip()).strip())
    return lead + " ".join(bits)


def continuation_indent_ws(parts: List[str]) -> str:
    if len(parts) < 2:
        return "    "
    inds = [len(p) - len(p.lstrip(" \t")) for p in parts[1:]]
    return " " * (min(inds) if inds else 4)


def parse_declaration_signature(flat: str) -> Optional[Tuple[str, List[str], str, bool]]:
    m2 = re.match(
        r"^(\s*(?:lemma|theorem|example|def|instance|abbrev)\s+)(\S+)\s+(.*)$",
        flat.strip(),
    )
    if not m2:
        return None
    prefix = m2.group(1) + m2.group(2) + " "
    sig = m2.group(3).strip()
    ci = find_resulting_type_colon(sig)
    if ci < 0:
        return None
    binders = sig[:ci].strip()
    typ = sig[ci + 1 :].strip()
    ends_where = False
    mwhere = re.match(r"^(.*?)\bwhere\s*$", typ)
    if mwhere:
        typ = mwhere.group(1).strip()
        ends_where = True
    chunks = parse_binder_chunks(binders)
    if not chunks:
        return None
    return prefix, chunks, ": " + typ, ends_where


def parse_have_by_signature(flat: str) -> Optional[Tuple[str, List[str], str]]:
    """Parse `have name <binders> : type := by` (single logical line, may include leading indent)."""
    c = code_before_comment(flat.rstrip("\n"))
    m2 = re.match(r"^(\s*)(have\s+)(\S+)\s+(.*)$", c, re.DOTALL)
    if not m2:
        return None
    prefix = m2.group(1) + m2.group(2) + m2.group(3) + " "
    sig = m2.group(4).strip()
    ci = find_resulting_type_colon(sig)
    if ci < 0:
        return None
    binders = sig[:ci].strip()
    typ = sig[ci + 1 :].strip()
    if ":= by" not in typ:
        return None
    chunks = parse_binder_chunks(binders)
    if not chunks:
        return None
    return prefix, chunks, ": " + typ


def _split_decl_physical_line(cur: str, max_col: int, cont: str, prefix: str) -> List[str]:
    """If `cur` is too long, put `lemma … name` on its own line and wrap the rest under `cont`."""
    if len(cur) <= max_col:
        return [cur]
    pl = prefix.rstrip()
    if not cur.startswith(pl):
        return wrap_physical_line(cur, max_col, 2)
    rest = cur[len(prefix) :].lstrip()
    if not rest:
        return [cur]
    if len(pl) > max_col:
        return wrap_physical_line(cur, max_col, 2)
    lines = [pl]
    body_prefix = cont
    for ln in wrap_physical_line(body_prefix + rest, max_col, 0):
        lines.append(ln)
    return lines


def format_decl_block(
    prefix: str,
    chunks: List[str],
    type_part: str,
    max_col: int,
    cont: str,
    ends_where: bool = False,
) -> List[str]:
    last_unit = chunks[-1] + " " + type_part
    units = chunks[:-1] + [last_unit]
    physical: List[str] = []
    cur = (prefix + units[0]).rstrip()
    for u in units[1:]:
        trial = cur + " " + u
        if len(trial) <= max_col:
            cur = trial
        else:
            physical.extend(_split_decl_physical_line(cur, max_col, cont, prefix))
            cur = (cont + u).rstrip()
    physical.extend(_split_decl_physical_line(cur, max_col, cont, prefix))
    if ends_where:
        suffix = " where"
        if physical and len(physical[-1]) + len(suffix) <= max_col:
            physical[-1] = (physical[-1] + suffix).rstrip()
        else:
            physical.append((cont + "where").rstrip())
    return [ln + "\n" for ln in physical]


def _declaration_header_skip_reformat(parts: List[str], max_col: int) -> bool:
    """
    Skip repacking when every line already fits the width limit *and* the header is
    compact (at most two physical lines). Longer headers that still fit per-line
    (e.g. one binder per line) are re-flowed to fill `max_col`.
    """
    if not all(len(p.rstrip("\n")) <= max_col for p in parts):
        return False
    return len(parts) <= 2


def try_reformat_declaration_at(
    lines: List[str], start: int, max_col: int
) -> Optional[Tuple[List[str], int]]:
    got = collect_declaration_block(lines, start)
    if got is None:
        return None
    end_ex, parts = got
    if _declaration_header_skip_reformat(parts, max_col):
        return None
    flat = flatten_decl_block(parts)
    parsed = parse_declaration_signature(flat)
    if parsed is None:
        return None
    prefix, chunks, type_part, ends_where = parsed
    cont = continuation_indent_ws(parts)
    new_block = format_decl_block(prefix, chunks, type_part, max_col, cont, ends_where)
    old_text = "".join(lines[start:end_ex])
    new_text = "".join(new_block)
    if old_text == new_text:
        return None
    return new_block, end_ex


def reformat_declaration_headers(lines: List[str], max_col: int) -> None:
    i = 0
    while i < len(lines):
        res = try_reformat_declaration_at(lines, i, max_col)
        if res is None:
            i += 1
            continue
        block, end_ex = res
        lines[i:end_ex] = block
        i += len(block)


def try_reformat_have_by_at(
    lines: List[str], start: int, max_col: int
) -> Optional[Tuple[List[str], int]]:
    got = collect_have_by_block(lines, start)
    if got is None:
        return None
    end_ex, parts = got
    if _declaration_header_skip_reformat(parts, max_col):
        return None
    flat = flatten_have_by_block(parts)
    parsed = parse_have_by_signature(flat)
    if parsed is None:
        return None
    prefix, chunks, type_part = parsed
    cont = continuation_indent_ws(parts)
    new_block = format_decl_block(prefix, chunks, type_part, max_col, cont, ends_where=False)
    old_text = "".join(lines[start:end_ex])
    new_text = "".join(new_block)
    if old_text == new_text:
        return None
    return new_block, end_ex


def reformat_have_by_headers(lines: List[str], max_col: int) -> None:
    i = 0
    while i < len(lines):
        res = try_reformat_have_by_at(lines, i, max_col)
        if res is None:
            i += 1
            continue
        block, end_ex = res
        lines[i:end_ex] = block
        i += len(block)


def split_lean_line_code_and_comment(line: str) -> Tuple[str, str]:
    """Split `code` from trailing ` -- comment` using the same `--` scan as `code_before_comment`."""
    raw = line.rstrip("\n\r")
    if "--" not in raw:
        return raw, ""
    i = 0
    while i < len(raw):
        if raw.startswith("--", i):
            return raw[:i].rstrip(), raw[i:]
        i += 1
    return raw, ""


def strip_trailing_by_from_decl_line(line: str) -> str:
    """
    Turn a declaration line ending in `:= by` into `:=`, preserving `--` comments and newline.
    """
    ends_nl = line.endswith("\n")
    code, comment = split_lean_line_code_and_comment(line)
    if not re.search(r":=\s*by\s*$", code.rstrip()):
        return line
    new_code = re.sub(r":=\s*by\s*$", ":=", code.rstrip())
    return new_code + comment + ("\n" if ends_nl else "")


def first_meaningful_proof_line_indent(chunk: List[str]) -> int:
    for raw in chunk:
        if raw.strip() == "" or is_comment_line(raw):
            continue
        ind, _ = line_indent_and_rest(code_before_comment(raw))
        return ind
    return 2


def proof_body_is_only_exact_term(stmts: List[Stmt]) -> Optional[str]:
    """
    If the proof is only `exact t` (optional blank lines and full-line `--` comments), return `t`.
    """
    saw = False
    term: Optional[str] = None
    for s in stmts:
        if isinstance(s, Raw):
            if s.text.strip() == "":
                continue
            if is_comment_line(s.text):
                continue
            return None
        if isinstance(s, Focus):
            return None
        if isinstance(s, Plain):
            if saw:
                return None
            c = s.content.strip()
            m = re.match(r"^exact\s+([\s\S]+)$", c)
            if not m:
                return None
            term = m.group(1).strip()
            if not term:
                return None
            saw = True
        else:
            return None
    if not saw:
        return None
    return term


def find_proof_spans(lines: List[str]) -> List[Tuple[int, int]]:
    """
    Return [start, end) line indices for tactic scripts after `:= by`.

    Blank lines and `--` lines are only part of the proof if indented at least
    `proof_base`; otherwise the span stops (so a blank line or top-level section
    comment before the next declaration is not eaten by `remove by exact` / edits).
    """
    spans: List[Tuple[int, int]] = []
    n = len(lines)
    i = 0
    while i < n:
        code = code_before_comment(lines[i])
        if re.search(r":=\s*by\s*$", code.rstrip()):
            start = i + 1
            j = start
            # Determine proof base indent
            proof_base: Optional[int] = None
            while j < n:
                if lines[j].strip() == "":
                    j += 1
                    continue
                if is_comment_line(lines[j]):
                    j += 1
                    continue
                c2 = code_before_comment(lines[j])
                proof_base, _ = line_indent_and_rest(c2)
                break
            if proof_base is None:
                i += 1
                continue
            j = start
            while j < n:
                raw = lines[j]
                if raw.strip() == "":
                    # Use physical leading whitespace; `code_before_comment` is empty on blank lines.
                    ind, _ = line_indent_and_rest(raw)
                    if ind < proof_base:
                        break
                    j += 1
                    continue
                if is_comment_line(raw):
                    # Full-line `--` comments: `code_before_comment` strips to "", yielding indent 0 and
                    # truncating the span early (e.g. before the rest of a `by` block after `wlog`).
                    ind, _ = line_indent_and_rest(raw)
                    if ind < proof_base:
                        break
                    j += 1
                    continue
                c2 = code_before_comment(raw)
                ind, rest = line_indent_and_rest(c2)
                if ind == 0 and DECL_START.match(rest.lstrip()):
                    break
                if ind < proof_base:
                    break
                j += 1
            spans.append((start, j))
            i = j
        else:
            i += 1
    return spans


def apply_auto_golf(lines: List[str], max_line_width: Optional[int] = 100) -> List[str]:
    out = list(lines)
    spans = find_proof_spans(out)
    offset = 0
    for st, en in spans:
        st += offset
        en += offset
        chunk = out[st:en]
        stmts = parse_proof_body(chunk, max_line_width=max_line_width)
        transform_all(stmts)
        term_only = proof_body_is_only_exact_term(stmts)
        if term_only is not None and st > 0:
            hi = st - 1
            new_header = strip_trailing_by_from_decl_line(out[hi])
            if new_header != out[hi]:
                ind = first_meaningful_proof_line_indent(chunk)
                new_proof = " " * ind + term_only + "\n"
                old_len = en - hi
                out[hi:en] = [new_header, new_proof]
                offset += 2 - old_len
                continue
        new_chunk = serialize_stmts(stmts, max_line_width=max_line_width)
        transform_simp_to_simpq_physical(new_chunk)
        norm = [x.rstrip("\n\r") for x in new_chunk]
        oldn = [x.rstrip("\n\r") for x in chunk]
        if norm != oldn:
            out[st:en] = new_chunk
            offset += len(new_chunk) - (en - st)
    if max_line_width:
        reformat_declaration_headers(out, max_line_width)
        reformat_have_by_headers(out, max_line_width)
    return out


def main() -> None:
    p = argparse.ArgumentParser(description="Auto-golf Lean tactic proofs in one file.")
    p.add_argument("path", help="Path to a .lean file")
    p.add_argument(
        "--write",
        action="store_true",
        help="Write changes in place (default: print to stdout)",
    )
    p.add_argument(
        "--max-line-width",
        type=int,
        default=100,
        metavar="N",
        help="Wrap golfed tactics and `lemma`/`def`/… / multi-line `have … := by` headers to N columns. 0 disables.",
    )
    args = p.parse_args()
    path = args.path
    with open(path, encoding="utf-8") as f:
        lines = f.readlines()
    if not pre_check(lines):
        sys.exit(1)
    max_w = None if args.max_line_width <= 0 else args.max_line_width
    new_lines = apply_auto_golf(lines, max_line_width=max_w)
    text = "".join(new_lines)
    if args.write:
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
