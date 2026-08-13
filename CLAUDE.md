# CLAUDE.md

This file provides guidance to coding agents—Claude Code (claude.ai/code) and Codex alike—when working with code in this directory. It is surfaced to Codex as `AGENTS.md` through a symlink, so keep the guidance tool-neutral.

## Project

Atlas is a place to **pose formal mathematical questions and have agents answer them**, together with the standing body of formalized mathematics the answers are built from.

Two layers, and the whole design is in the relation between them:

- **`Atlas/Knowledge/`** — a curated, atomic, densely linked library of mathematics **autoformalized from the literature**, each item citing its source. One file states one thing and is named for it, so `ls Atlas/Knowledge/` is the index of everything Atlas knows. It is written to be *read* by whoever is answering, and it is **built ahead of the questions**: the point of a static layer is that it is already there when a question arrives. It also takes in whatever answering turns out to need, but that is the second way it grows, not the first.
- **`Atlas/Questions/YYYYMMDD/`** — one unit per day questions were posed, holding the comparator pair. `Challenge.lean` is the frozen question, `Development.lean` is the answer.

**Atlas is bound to no source.** The questions are the writer's own, posed rather than transcribed, so nothing here follows a paper's exposition and there is no region of a text being worked through. Knowledge items *do* come from the literature and cite it; the questions do not.

**Why the comparator is here at all:** an agent writing a proof can edit the statement in the same edit, and no `git diff` flags that, because a diff on the file the proof goes into is exactly what an answer looks like. The fourth check of `__check__.py` is the only thing that says the statement in the file the agent edited still matches the statement in the file it did not. That is the threat model, and the second file is the mechanism—not overhead.

**Citations resolve against** `bib/__main__.bib` in the `knowledge-base` repository this project is developed alongside—or `bib/__main__.ja.bib`, whose keys carry a `ja_` prefix, for a Japanese-language work. Adding an entry there is that repository's `/pdf-to-bib` skill's job. `@./__docs__/rules-documentation.md` defers to this line for which bibliography a cite key lives in and names none itself, because the rest of it has to hold when this repository is read on its own.

## Architecture

A standalone Lake package following `@./__docs__/rules-formalization-project.md` for the layout and `@./__docs__/rules-comparator.md` for the Challenge / Development pair. The project-specific parameters those documents leave open:

- **A unit is one day's questions**, `Atlas/Questions/YYYYMMDD/`, and the date is the only thing that groups its contents. Modules are `Atlas.Questions.«YYYYMMDD».Challenge` and `.Development`. **The French quotes are mandatory**—`20260813` is not an identifier, so the module name, the namespace, and the root module's import line do not parse without them. Targets are `question_YYYYMMDD_a`, `_b`, … lettered in the order posed.
- **The root namespace is `Atlas`, and knowledge items live in `Atlas.Knowledge`, flat**: `Knowledge/JumpSet.lean` declares `Atlas.Knowledge.JumpSet` and puts what supports it in a nested `namespace JumpSet`. File name = declaration name = index entry, and every way of reading the layer depends on that holding.
- **The comparator namespace is per unit**: `AtlasChallenge.«YYYYMMDD»`, both files of that day. This departs from the template, which uses one project-wide `AtlasChallenge`; with one unit per day that breaks the first time two days clone the same definition. The reasoning is in `@./__docs__/rules-comparator.md`.
- **Questions are stated in Mathlib's vocabulary**, unfolding inline any `Knowledge/` notion they are about, so a Challenge clones nothing and a Development body has no bridge to write. This is the project's statement policy and the reason the knowledge layer stays single-copy; cloning is available as a justified exception. See `@./__docs__/rules-comparator.md`.
- **The production layer is project-wide `Atlas/Knowledge/`, never a per-unit `Defs.lean`.** `Challenge.lean` never imports it. `Development.lean` imports exactly the items its answers draw on, so a Development's import block *is* that day's dependency edge set.
- **There is no `CompareMathlib.lean`.** It exists to set a source's own argument beside the Mathlib API, and Atlas follows no source's argument. A question that turns out to be a Mathlib theorem is recorded as an identification inside the relevant knowledge item—a `theorem foo_eq_mathlibFoo … := rfl`, which the build keeps honest where a comment would not.
- **Mathlib is used without restriction.** Any lemma may enter any proof, and the shortest route is the right one. Finding that Mathlib already answers a question is a result, not a failure.
- **Standing exemption: a `sorry` on a `Knowledge/` theorem is the backlog, not a defect.** It is a claim recorded before its proof, and the build warning is the whole of what tracks it. Under a *definition* a `sorry` is never allowed. The reasoning is in `@./__docs__/rules-comparator.md`.

Every source file must be reachable from the root all-import module `Atlas.lean`; adding a `.lean` file means adding its `import` line there in the same edit. `Challenge.lean` is the exception—it shares `Development.lean`'s namespace and is built by name.

## The two project scripts

```bash
python3 __init_question__.py                    # scaffold today's unit
python3 __init_question__.py 20260813 --append  # add one question to both files identically
./__graph__.sh                                  # the knowledge web; red = promised but unwritten
```

**Use `--append` rather than adding a question by hand.** Writing the same declaration into two files is precisely the operation check 4 exists to police, so letting the script do it turns a check-after-the-fact into a can't-happen.

## Which rules this project carries

The four template documents in `__docs__/`, fine-tuned here and not in the template (https://github.com/0stellensatz/AutoFormalization) they came from, and one document native to this project. What was narrowed:

- **`rules-comparator.md`** — the per-unit comparator namespace; the Mathlib-vocabulary statement policy, with the exception procedure and the three rules a clone block carries; `Knowledge/` exempted from "production modules build without `sorry`", on theorems only.
- **`rules-formalization-project.md`** — a unit is a day rather than a slice of a source; the knowledge layer replaces per-unit production code entirely; the import discipline that keeps days independent and pushes shared work up into `Knowledge/`.
- **`rules-documentation.md`** — an `## In this project` section: a knowledge item's docstring title is the bare term because that line is the index entry, and a backticked `Atlas.Knowledge.*` name may point at an item not yet written, which is the backlog and is not to be "fixed".
- **`rules-comments.md`** — the closing *When the target is Mathlib* section is cut; nothing here is headed upstream.
- **`rules-workflow.md`** — the native one, not from the template: the cycle a phase travels—plan as tracking issue, formalization per PR, adversarial review by a second agent on a different model, revision, verification before the issue's checkboxes are ticked, linear merge. The author never ticks its own boxes; the document says why, and it is the comparator's threat model one layer up.

Run the checker before declaring work done, and a build after it—including the Challenge files, which `lake build` leaves out and whose failure to elaborate is otherwise invisible:

```bash
python3 __check__.py
lake build
find Atlas -name Challenge.lean | sed -E 's|/([0-9]+)/|/«\1»/|g; s|^|lake build |; s|/|.|g; s|\.lean$||' | sh
```

## Editing conventions for the comments

Follow the rules in @./__docs__/rules-comments.md for Markdown-styled comments across the files, and @./__docs__/rules-documentation.md for the module docstrings, the per-declaration docstrings, and the citations.
