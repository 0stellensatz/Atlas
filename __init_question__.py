#!/usr/bin/env python3
"""__init_question__.py — pose a question in the Lake project this script sits in.

A day's questions are a unit: `<Project>/Questions/YYYYMMDD/Challenge.lean` states them
and leaves each one `sorry`, and `Development.lean` carries the identical declaration list
with the bodies filled in.  The two files are what `__check__.py` compares, and they are
only worth comparing if they started out agreeing — so this script is what writes to them,
rather than a pair of hand edits that have to be kept in step by attention alone.

Two modes:

    python3 __init_question__.py [YYYYMMDD]
        Scaffold the day: both files, with the same namespace and no declarations, plus
        the root module's `import ...Development` line placed in date order.  A file that
        already exists is never overwritten, with one exception: one that is empty (or
        only whitespace) is filled, since a `touch`ed placeholder holds nothing to lose.

    python3 __init_question__.py [YYYYMMDD] --append --doc "..." < signature
        Append one question to *both* files, identically: the docstring, the next free
        letter in `question_YYYYMMDD_<letter>`, the signature read from stdin, and a
        `sorry` body.  The signature is everything between the name and the `:=` —
        binders and the type — and may span lines.

Writing the same declaration into two files is precisely the operation `__check__.py`'s
fourth check exists to police, so doing it here turns a check-after-the-fact into a
can't-happen.  What the script cannot do is judge the statement: a question that does not
*elaborate* is not yet a question, and `sorry` closes a proof, never a hole in what is
being asked.  Build the day after appending.

    python3 __init_question__.py --selftest
"""

from __future__ import annotations

import argparse
import datetime
import re
import string
import sys
from pathlib import Path
from typing import NoReturn

PROJECT = Path(__file__).resolve().parent          # the project root
NAME = PROJECT.name                                # the Lake package / library name
LIB_DIR = PROJECT / NAME                           # the library source tree
QUESTIONS = LIB_DIR / "Questions"                  # one directory per day posed
ROOT_MODULE = PROJECT / f"{NAME}.lean"             # the root all-import module

# `20260813` is not an identifier, so a day is imported — and its namespace named — in
# French quotes.  The root module carries Development only: Challenge shares its namespace.
DEV_IMPORT_RE = re.compile(
    r"^import\s+" + re.escape(NAME) + r"\.Questions\.«(\d{8})»\.Development\s*$"
)


def die(msg) -> NoReturn:
    print(f"error: {msg}", file=sys.stderr)
    sys.exit(1)


def namespace(stem):
    """The comparator namespace of one day, shared by both its files.

    Per unit rather than one project-wide `<Project>Challenge`: the root module holds
    every `Development.lean` at once, so a shared namespace would make any two days that
    clone the same definition declare one name twice.
    """
    return f"{NAME}Challenge.«{stem}»"


def challenge_skeleton(stem, date_str):
    ns = namespace(stem)
    return f"""import Mathlib

/-!
# Questions posed on {date_str}

TODO: one paragraph on what is being asked and why.

## Implementation notes

TODO: the `{NAME}.Knowledge` items these questions are about, as backticked
fully-qualified names. That is the pointer whoever answers follows, and it costs nothing:
a docstring is not an import, so this file still stands alone against Mathlib.
-/

namespace {ns}

end {ns}
"""


def development_skeleton(stem, date_str):
    ns = namespace(stem)
    return f"""import Mathlib

/-!
# Questions posed on {date_str}, answered

The statements, what they are about, and the knowledge items they draw on are in
`Challenge.lean` and are not repeated here. This file carries the same declaration list
with the bodies filled in, and `__check__.py` is what keeps the two lists identical.
-/

namespace {ns}

end {ns}
"""


def header_end(lines):
    """Index one past the file's header — its leading comments, blank lines and imports.

    Lean allows comments before the `import` block but no command after it, so this is
    the last point at which an `import` line may still be inserted.
    """
    i, in_block = 0, False
    while i < len(lines):
        stripped = lines[i].strip()
        if in_block:
            if "-/" in stripped:
                in_block = False
            i += 1
        elif stripped.startswith("/-"):
            if "-/" not in stripped[2:]:
                in_block = True
            i += 1
        elif stripped == "" or stripped.startswith("--") or stripped.startswith("import "):
            i += 1
        else:
            break
    return i


def insert_dev_import(text, stem):
    """Return `text` with the day's Development import inserted, in date order.

    Returns the text unchanged when the line is already there.
    """
    lines = text.splitlines()
    days = [(i, m.group(1)) for i, m in ((i, DEV_IMPORT_RE.match(l)) for i, l in enumerate(lines)) if m]
    if any(existing == stem for _, existing in days):
        return text

    new_line = f"import {NAME}.Questions.«{stem}».Development"
    if days:
        later = [i for i, existing in days if existing > stem]
        at = later[0] if later else days[-1][0] + 1
    else:
        # The first day of the project. Questions sort after Knowledge, so the end of the
        # header is the right place, and a blank line keeps the two blocks apart.
        at = header_end(lines)
        if at > 0 and lines[at - 1].strip() != "":
            lines.insert(at, "")
            at += 1
    lines.insert(at, new_line)
    return "\n".join(lines) + "\n"


def next_letter(text, stem):
    """The next free letter of `question_<stem>_<letter>` in `text`.

    Lettered in the order posed, so this is one past the highest already used rather than
    the first gap: a letter is not reused once a question has carried it.
    """
    used = set(re.findall(r"\bquestion_" + re.escape(stem) + r"_([a-z])\b", text))
    if not used:
        return "a"
    nxt = string.ascii_lowercase.index(max(used)) + 1
    if nxt >= len(string.ascii_lowercase):
        die(f"the day {stem} already has 26 questions; start another day")
    return string.ascii_lowercase[nxt]


# A chunk is one wrappable unit. A code span is glued to whatever non-space touches it, so
# that neither the span nor its trailing punctuation is ever left across a line break --- the
# rule `__docs__/rules-comments.md` states as never breaking between a construct's delimiters.
CHUNK = re.compile(r"\S*`[^`]*`\S*|\S+")


def wrap_docstring(doc, width=100):
    """Render `doc` as a `/-- ... -/` docstring hard-wrapped to `width` columns.

    The delimiters hug the text---the docstring starts on the `/--` line and ends on the `-/`
    line---so the first line carries four extra columns and the last three.
    """
    chunks = CHUNK.findall(doc)
    lines, current = [], "/--"
    for chunk in chunks:
        # The last line has to fit ` -/` as well, and any line may turn out to be the last.
        if current != "/--" and len(current) + 1 + len(chunk) + 3 > width:
            lines.append(current)
            current = chunk
        else:
            current = f"{current} {chunk}" if current else chunk
    lines.append(f"{current} -/")
    return lines


def append_declaration(text, stem, letter, doc, signature):
    """Return `text` with one `sorry`ed target appended just before the closing `end`."""
    lines = text.splitlines()
    end_line = f"end {namespace(stem)}"
    at = next((i for i in range(len(lines) - 1, -1, -1) if lines[i].strip() == end_line), None)
    if at is None:
        die(f"no closing `{end_line}` to append before; was the file edited by hand?")

    block = wrap_docstring(doc) + [f"theorem question_{stem}_{letter} {signature} := sorry"]
    # A blank line separates this question from whatever precedes it, and the scaffold
    # already leaves one before the closing `end`.
    if at > 0 and lines[at - 1].strip() != "":
        block.insert(0, "")
    block.append("")
    lines[at:at] = block
    return "\n".join(lines) + "\n"


def write_if_absent(path, body):
    """Write `body` unless a non-empty file is already there. Returns a verb, or None."""
    if path.exists() and path.read_text(encoding="utf-8").strip():
        return None
    refilled = path.exists()
    path.write_text(body, encoding="utf-8")
    return "filled empty" if refilled else "created"


def do_scaffold(stem, date_str):
    unit = QUESTIONS / stem
    unit.mkdir(parents=True, exist_ok=True)

    wrote = False
    for fname, body in (("Challenge.lean", challenge_skeleton(stem, date_str)),
                        ("Development.lean", development_skeleton(stem, date_str))):
        verb = write_if_absent(unit / fname, body)
        print(f"  {unit.relative_to(PROJECT)}/{fname}: "
              + (f"{verb}" if verb else "already exists, left alone"))
        wrote = wrote or verb is not None

    before = ROOT_MODULE.read_text(encoding="utf-8")
    after = insert_dev_import(before, stem)
    if after != before:
        ROOT_MODULE.write_text(after, encoding="utf-8")
        print(f"  {ROOT_MODULE.name}: import {NAME}.Questions.«{stem}».Development added")
    else:
        print(f"  {ROOT_MODULE.name}: already imports the day")

    if wrote:
        print(f"\nNext: state the questions with --append, then build the day:\n"
              f"  lake build '{NAME}.Questions.«{stem}».Challenge'")
    return 0


def do_append(stem, doc, signature):
    unit = QUESTIONS / stem
    challenge, development = unit / "Challenge.lean", unit / "Development.lean"
    for path in (challenge, development):
        if not path.is_file():
            die(f"the day is not scaffolded yet: {path.relative_to(PROJECT)} is missing")

    letter = next_letter(challenge.read_text(encoding="utf-8"), stem)
    for path in (challenge, development):
        text = path.read_text(encoding="utf-8")
        path.write_text(append_declaration(text, stem, letter, doc, signature), encoding="utf-8")

    print(f"Appended question_{stem}_{letter} to both files of "
          f"{unit.relative_to(PROJECT)}.")
    print(f"\nIt will not elaborate until the statement is right, which is where the work "
          f"of posing\na question goes. Check it:\n"
          f"  lake build '{NAME}.Questions.«{stem}».Challenge'\n"
          f"  python3 __check__.py")
    return 0


def selftest():
    stem = "20260813"
    ns = namespace(stem)
    assert ns == f"{NAME}Challenge.«20260813»", ns

    # next_letter: empty, then one past the highest used, never filling a gap.
    assert next_letter("", stem) == "a"
    assert next_letter(f"theorem question_{stem}_a : True := sorry", stem) == "b"
    assert next_letter(f"question_{stem}_a question_{stem}_c", stem) == "d"
    # Another day's questions do not advance this one's letter.
    assert next_letter(f"question_20260101_f", stem) == "a"

    # Docstrings wrap to 100 columns and never break inside a code span.
    long_doc = ("Legendre's formula: `(p - 1)` times the `p`-adic valuation of `n !` is `n` "
                "less the sum of the base-`p` digits of `n`, which is the correction term.")
    wrapped = wrap_docstring(long_doc)
    assert len(wrapped) > 1, wrapped
    assert wrapped[0].startswith("/-- ") and wrapped[-1].endswith(" -/"), wrapped
    assert all(len(l) <= 100 for l in wrapped), [len(l) for l in wrapped]
    assert all(l.count("`") % 2 == 0 for l in wrapped), wrapped
    # A short docstring stays on one line, delimiters and all.
    assert wrap_docstring("A prime above every bound.") == ["/-- A prime above every bound. -/"]

    # append_declaration lands before the closing `end`, in both files identically.
    body = challenge_skeleton(stem, "August 13, 2026")
    out = append_declaration(body, stem, "a", "A prime above every bound.",
                             "(n : ℕ) : ∃ p, n < p ∧ Nat.Prime p")
    assert f"theorem question_{stem}_a (n : ℕ) : ∃ p, n < p ∧ Nat.Prime p := sorry" in out
    assert out.index("theorem question_") < out.index(f"end {ns}")
    assert out.rstrip().endswith(f"end {ns}")
    assert append_declaration(development_skeleton(stem, "August 13, 2026"), stem, "a",
                              "A prime above every bound.",
                              "(n : ℕ) : ∃ p, n < p ∧ Nat.Prime p").count("question_") == 1

    # A second question is separated from the first by a blank line.
    two = append_declaration(out, stem, "b", "Another.", "(n : ℕ) : n = n")
    lines_two = two.splitlines()
    at_b = next(i for i, l in enumerate(lines_two) if l.startswith("/-- Another."))
    assert lines_two[at_b - 1].strip() == "", lines_two[at_b - 3:at_b + 1]
    assert lines_two[at_b - 2].startswith(f"theorem question_{stem}_a"), lines_two[at_b - 2]

    # Root import: date order among days, idempotent, and after the Knowledge block.
    root = f"import {NAME}.Knowledge.JumpSet\nimport {NAME}.Questions.«20260101».Development\n"
    added = insert_dev_import(root, stem)
    assert added.splitlines()[-1] == f"import {NAME}.Questions.«{stem}».Development", added
    assert insert_dev_import(added, stem) == added
    earlier = insert_dev_import(f"import {NAME}.Questions.«20270101».Development\n", stem)
    assert earlier.splitlines()[0] == f"import {NAME}.Questions.«{stem}».Development", earlier
    fresh = insert_dev_import(f"import {NAME}.Knowledge.JumpSet\n", stem)
    assert fresh.splitlines() == [f"import {NAME}.Knowledge.JumpSet", "",
                                  f"import {NAME}.Questions.«{stem}».Development"], fresh

    print("selftest ok")
    return 0


def main(argv):
    parser = argparse.ArgumentParser(
        prog="__init_question__.py",
        description=f"Pose a question in the {NAME} project, writing to both files of its unit.",
    )
    parser.add_argument("date", nargs="?", help="YYYYMMDD; defaults to today")
    parser.add_argument("-a", "--append", action="store_true",
                        help="append one question, reading its signature from stdin")
    parser.add_argument("--doc", help="the appended question's docstring (required with --append)")
    parser.add_argument("--selftest", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args(argv[1:])

    if args.selftest:
        return selftest()

    if not LIB_DIR.is_dir():
        die(f"the library directory is missing: {LIB_DIR.name}/")
    if not ROOT_MODULE.is_file():
        die(f"the root module is missing: {ROOT_MODULE.name}")

    if args.date:
        try:
            day = datetime.datetime.strptime(args.date, "%Y%m%d").date()
        except ValueError:
            die(f"invalid date (expected YYYYMMDD): {args.date}")
    else:
        day = datetime.date.today()
    stem = day.strftime("%Y%m%d")
    date_str = day.strftime("%B %-d, %Y")

    if not args.append:
        print(f"Questions posed on {date_str}:")
        return do_scaffold(stem, date_str)

    if not args.doc:
        die("--append needs --doc: every question carries a docstring saying what it asks")
    signature = sys.stdin.read().strip()
    if not signature:
        die("--append reads the question's signature from stdin, and none was given")
    return do_append(stem, args.doc, signature)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
