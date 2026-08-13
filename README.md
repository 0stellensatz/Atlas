# Atlas

A place to pose formal mathematical questions and have agents answer them, together with the standing body of formalized mathematics the answers are built from.

Two layers:

- **`Atlas/Knowledge/`** — atomic, cross-linked, curated. One file states one thing and is named for it, so `ls Atlas/Knowledge/` is the index of everything Atlas knows. This is the layer an agent reads before it starts proving: mathematics autoformalized from the literature, each item citing where it came from. It is built ahead of the questions rather than only in response to them—a static layer is one you can already read—and it also takes in whatever answering turns out to need.
- **`Atlas/Questions/YYYYMMDD/`** — one directory per day questions were posed. `Challenge.lean` states them and leaves every one `sorry`; `Development.lean` carries the same declaration list, answered.

The pair is the point. `Challenge.lean` stands alone against Mathlib and never changes when an answer is found, and `__check__.py` verifies that the two files still declare the same things—same names, kinds, binders, types, attributes, order. An agent that quietly reshapes a question to fit the proof it happened to find fails that check. Nothing else catches it: a diff on the file the proof goes into is exactly what an answer is supposed to look like.

A question is therefore never restated in order to be proved, and what is still `sorry` in a `Challenge.lean` is not the record of anything—the record is which `Development.lean` bodies are filled.

## Asking and answering

```bash
python3 __init_question__.py                    # scaffold today's unit, both files
python3 __init_question__.py 20260813 --append  # add one question, written into both identically
```

Questions are stated in Mathlib's vocabulary: a `Knowledge/` notion the question is *about* is unfolded inline rather than named, so a `Challenge.lean` carries no copy of anything and the knowledge layer is never duplicated into a day. The knowledge layer is what an answer is built *from*, not what a question is phrased *in*. `__docs__/rules-comparator.md` gives the reasoning and the exception.

An answer edits `Development.lean` and only `Development.lean`. If it cannot be written without changing the statement, the statement was wrong: change `Challenge.lean` first, propagate, then prove—deliberately, and in one commit.

## Reading the knowledge layer

Nothing indexes it but the files themselves, which is why the naming is strict:

```bash
ls Atlas/Knowledge/                              # every term Atlas knows
grep -h '^# ' Atlas/Knowledge/*.lean             # the same list, annotated
grep -rl 'Atlas.Knowledge.JumpSet' Atlas/        # backlinks to one item
./__graph__.sh                                   # the web as a picture
```

A prerequisite is an `import`. A softer reference—an item mentioned rather than used—is a backticked fully-qualified name in a docstring, and it may name an item that has not been written yet. Those unwritten promises are the backlog: `__graph__.sh` draws them as red nodes, and nothing else tracks them. They are not dangling references to be repaired.

A `sorry` on a knowledge theorem is likewise deliberate—a claim recorded before its proof, reported by every build. Under a definition it is never allowed.

## Building

Mathlib is pinned in `lake-manifest.json`, and `elan` will fetch the toolchain named in `lean-toolchain`. From this directory:

```bash
lake exe cache get   # once, before the first build—otherwise Mathlib compiles from source
lake build           # everything the root all-import module reaches
python3 __check__.py
```

`Challenge.lean` is **not** among them: it shares `Development.lean`'s namespace, so the root module cannot import it and `lake build` does not compile it. Build the Challenges by name, or a question that fails to elaborate stays green:

```bash
find Atlas -name Challenge.lean | sed 's|^|lake build |; s|/|.|g; s|\.lean$||' | sh
```

The conventions this project follows are its own copies, in `__docs__/`.
