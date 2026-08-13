# Architecture: the knowledge layer and the question units

These rules govern the shape of this package: a standing body of formalized mathematics, and a run of dated question units stated against it.

**Atlas is bound to no source.** The questions are its own—posed rather than transcribed—so nothing here mirrors a paper's sectioning, and there is no exposition being worked through. A *unit* is one day's questions, in the directory `Atlas/Questions/YYYYMMDD/`, and the date is the only thing that groups its contents: questions posed on one day share a directory whether or not they share a subject. That a unit is a directory holding one comparator pair is what `__check__.py` fixes, since it pairs the files by the directory they share; that the directory is a date is this project's own choice.

Two things about that spelling are load-bearing. `20260813` is not an identifier, so the module `Atlas.Questions.«20260813».Challenge`, the namespace, and the root module's import line all need the French quotes. And targets are named `question_YYYYMMDD_a`, `_b`, … lettered in the order they were posed, so a name carries its own day and no two days collide.

Two companion documents carry the parts not repeated here: `./rules-comparator.md` (the Challenge / Development pair—the specification-versus-proof split that these rules assume throughout) and `./rules-documentation.md` (module and declaration docstrings, and citations).

## The project is a Lake package

Each project is a self-contained Lake package with its own `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, and (gitignored, machine-local) `.lake/`, held in a repository of its own. The sources sit in the library directory named after the project:

```
<Project>/
├── lakefile.toml   lean-toolchain   lake-manifest.json   .gitignore
├── README.md   CLAUDE.md   AGENTS.md → CLAUDE.md
├── __docs__/            the project's own copies of the rules it follows
├── __check__.py         the project's own copy of the structural checker
├── <Project>.lean       the root all-import module
└── <Project>/           the library source tree
```

The `__docs__/` copies and `__check__.py` arrive with the template repository the project is generated from, and are the project's own from then on: they are fine-tuned in place to fit it, and a project keeps only the rules that apply to it, deleting the rest.

Module names mirror file paths under the package root: `<Project>/<Unit>/Foo.lean` is the module `<Project>.<Unit>.Foo`.

**The root module `<Project>.lean` directly imports every module of the project**, so a plain `lake build` cannot silently omit a new file. Keep the import list sorted, and add to it whenever a module is added or renamed. The exceptions are `Challenge.lean` and `CompareMathlib.lean`, which declare the same names in the same namespace as `Development.lean` and so cannot enter the same environment; the root module imports Development, and the other two are built by name.

## What a unit holds

A unit is two files and nothing else.

- **`Challenge.lean` — the frozen statement of the day's questions**, one declaration per question, each proved by `sorry`, and stated in Mathlib's vocabulary (`./rules-comparator.md`). It imports only Mathlib, and it is the file that does *not* change when an answer is found. A `sorry` here is permanent: it is the question, not a gap.
- **`Development.lean` — the same declarations, answered**, by importing what the answer needs from `Atlas.Knowledge` and delegating to it. This is where an agent works, and the only file of the two it may edit.

**There is no per-unit production code, no `Defs.lean`, and no per-unit proof file.** The template puts the definitions and proofs a unit is stated over beside that unit; here they sit in one project-wide layer that every unit draws on, because a day is a bad place to leave anything meant to be reused, and reuse is the point.

## The knowledge layer

`Atlas/Knowledge/` is that layer: the standing, curated body of mathematics **autoformalized from the literature**, which answers are built from. It is production code in the sense the comparator discipline means, and it is the reason an agent handed a question is not starting from Mathlib and a blank file.

**It is built ahead of the questions.** A layer that only accumulated what past answers happened to need would be a cache, and a cache is no use the first time a question is asked. Formalizing a source before anything asks for it is the normal way this layer grows, and the volume of work that takes is expected rather than a sign something has been mis-scoped.

- **One file states one thing**, and the file is named for that thing in UpperCamelCase: `Knowledge/JumpSet.lean`, `Knowledge/HigherUnitGroup.lean`. One definition, one statement with its proof, one construction, one worked example. A file wanting a second principal declaration is two files.
- **The file name is the index entry.** `ls Atlas/Knowledge/` is the index of everything Atlas knows, `grep -h '^# ' Atlas/Knowledge/*.lean` is that index annotated, and the root module is the same list again, complete because `__check__.py` says so. Nothing else indexes the layer, and nothing else needs to—a written index would be a second copy of a list already derivable three ways.
- **An item is referred to by its module name**, `Atlas.Knowledge.<Item>`, whether by an `import` or by a backticked mention in a docstring. Module components are UpperCamelCase, so a module name equals its file stem exactly, and that exactness is what lets `./__graph__.sh` resolve a reference without guessing. The declarations *inside* an item are named by Mathlib's own convention for their kind—`digitSum` for a `def` returning data, `sub_one_mul_padicValNat_factorial` for a theorem—and are written in prose as usual; they are not what the graph tracks, and the lowercase initial is what tells the two apart.
- **A prerequisite is an `import`. A soft or forward reference is a backticked module name in a docstring** (`./rules-documentation.md`), and it may name an item not written yet. That is the backlog, it is not an error, and it is not to be "fixed."
- **Every item cites where it came from.** An item with no source in its docstring is not usable later; see `./rules-documentation.md`.
- **A `sorry` on a theorem is a claim recorded before its proof**, and is allowed. Under a definition it never is (`./rules-comparator.md`).

### Taking a source into the layer

A paper or a chapter enters as *items*, not as a transcription of itself.

- **Atomize, and name for the mathematics rather than for the source's numbering.** A paper's Definition 2.3 becomes `Knowledge/JumpSet.lean` and not `Knowledge/Pagano2022_2_3.lean`; a term's name is what someone will look for, and a source's numbering is an accident of that source. The pinpoint is not lost—it goes in the docstring citation, which is where it belongs.
- **Take what is worth reusing, not everything.** A source contributes the notions and results that later questions will be stated against or answered from. Its scaffolding lemmas come along only where an item cannot elaborate without them.
- **Two sources may supply one item.** An item is about a piece of mathematics, so where two papers state the same notion it is one item citing both, not two items racing to own the name. Where they state it *differently*, the difference is itself worth an item, and the modeling decision is recorded in `## Implementation notes`.
- **The boundary with a source-formalization project.** A source being worked through unit by unit—its own numbered claims frozen in comparator files, its sectioning mirrored on disk, the goal being fidelity to that source—is a project of its own, and this is not it. Here a source is a supplier: what it supplies is chosen, atomized, and answerable to the vocabulary of the layer rather than to the paper's exposition. The two are different jobs on the same PDF, and neither is a substitute for the other.

## Import discipline

Lean's import graph is acyclic, and everything here flows one way:

```
Mathlib  ←  Knowledge/  ←  Development.lean

Mathlib  ←  Challenge.lean
```

- **A `Knowledge/` file imports Mathlib and other `Knowledge/` files, and nothing else.** It never imports a question, in either direction and at any remove. A genuine mutual dependency between two items is resolved by demoting one direction to a docstring reference, which is what the soft link is for.
- **`Challenge.lean` sits outside the graph entirely**—Mathlib alone (`./rules-comparator.md`).
- **No `Questions/` directory imports another.** Days are independent, and a day is finished when it is. **What a second day also wants moves up into `Knowledge/`** rather than being reached for sideways—that rule is what makes the knowledge layer grow from use instead of becoming a place things are filed.
- When a `Knowledge/` definition carries a proof obligation, prove the obligation in place when it is short; if it grows, split it into a prerequisite item imported *by* the one holding the definition. Never leave a `sorry` underneath a definition—a definition that does not elaborate takes everything downstream of it with it.

## Workflow

1. **Pose.** Scaffold the day with `__init_question__.py`, then add each question with its `--append` mode, which writes the identical declaration into both files so the two cannot start out of step. State it in Mathlib's vocabulary, unfolding any `Knowledge/` notion it is about. **A statement that will not elaborate is not yet a question**—`sorry` closes a proof, never a hole in what is being asked, so getting the statement to elaborate is where most of the work of posing one goes. Name in the Challenge's `## Implementation notes` the `Knowledge/` items the question is about, as backticked fully-qualified names; that is the pointer an agent follows, and it costs nothing, being a docstring rather than an import.
2. **Answer.** In `Development.lean` only, replace a `sorry` with a proof, importing from `Atlas.Knowledge` whatever it draws on. **The statement never changes at this step, only its body**, and `Challenge.lean` is not touched at all.
3. **Promote.** Anything the answer needed that a second question would also want—a definition, a lemma worth a name—moves into `Knowledge/` as an item of its own rather than staying inline in a body. This is the step that is easy to skip and the one that makes the layer worth having.

If step 2 cannot be carried out without changing the statement, the statement was wrong. Fix it in `Challenge.lean` first, copy the changed declaration verbatim into `Development.lean`, restore its body, and only then adjust the proof—in that order, and in one commit. Weakening a statement to fit the proof that turned out to be reachable is the single failure this whole architecture exists to catch, and `__check__.py` catches it only if the Challenge is edited deliberately rather than drifted into.

## Namespaces and naming

- Knowledge items live in `Atlas.Knowledge`, flat: `Knowledge/JumpSet.lean` declares `Atlas.Knowledge.JumpSet` and puts what supports it in a nested `namespace JumpSet`, for dot notation. The comparator files of a unit share a namespace of their own (`./rules-comparator.md`). Helpers not meant for use outside their file are `private`.
- Knowledge items are named in descriptive Mathlib style, and a name is chosen as the name of the *term*, since it is also the file name and the index entry.
- Docstrings on knowledge items cite where the item comes from, by numbering and page—see `./rules-documentation.md`.
- Modeling decisions (how an object is encoded—e.g., `ℤ_{≥1}` as `ℕ+`) are recorded once, in the `## Implementation notes` of the item that introduces them, and stay consistent across the layer.
- When a declaration's natural name collides with the Mathlib lemma it mirrors, the Mathlib one is reachable as `_root_.<name>`; prefer a distinct descriptive name when the collision would confuse.

## File layout

Every `.lean` file starts with `import Mathlib`, then the project-local imports (each on its own line), then the module docstring:

```lean
import Mathlib
import Atlas.Knowledge.JumpSet

/-!
# <title>
...
-/
```

In `Challenge.lean` the block stops at the first line: it takes no project-local import at all.

**There is no file-level `set_option` block.** The suppressions it is tempting to open every file with—`warningAsError false`, `linter.style.longLine false`, `linter.style.emptyLine false`—are not used, and the set is empty: nothing stands between a file and the Mathlib linter set that `lakefile.toml` enables. The long-line linter in particular is a check the file is expected to pass, since comments are hard-wrapped at 100 columns (`./rules-comments.md`).

A `set_option` that changes *elaboration* rather than silencing a linter is a different matter and stays available—but only in the scoped form, attached to the one declaration that needs it and carrying a comment saying why:

```lean
set_option maxHeartbeats 1000000 in
-- The instance search for `IsDedekindDomain (integers L)` is the expensive step.
theorem foo : ... := ...
```

This is what Mathlib's own `linter.style.setOption` demands; an unscoped `set_option maxHeartbeats` at the top of a file is reported by it.

## Building

All of these are run from the project directory (from elsewhere, wrap the change of directory in a subshell so it does not leak into later commands):

```bash
lake build                                          # the knowledge layer and every Development
lake build Atlas.Knowledge.JumpSet                  # one knowledge item
lake build 'Atlas.Questions.«20260813».Development'  # one day's answers
lake build 'Atlas.Questions.«20260813».Challenge'    # its questions, which the root module omits
./__graph__.sh                                      # the knowledge web, and what is promised but unwritten
```

The French quotes in a day's module name have to survive the shell, so quote the argument. Every Challenge at once is the loop in `./rules-comparator.md`.

A fresh checkout of a project needs `lake exe cache get` **before** the first build—otherwise Lean compiles Mathlib from source, which takes hours. Alongside the build, run the project's own structural check (`./rules-comparator.md`):

```bash
python3 __check__.py
```

The toolchain and the remaining `lake` commands are documented in the project's own `README.md`, one directory up from this one.
