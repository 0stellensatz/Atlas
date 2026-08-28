# The Challenge / Development comparator pair

This project freezes each question it poses in a *comparator* file and answers it in a parallel file carrying the same declaration list. The convention follows the agent workflow of the `rigid` project (https://github.com/dagurtomas/rigid/blob/main/AGENTS.md), including its rule that the frozen file stands alone against Mathlib.

The point of the pair is that the *specification* and the *proof* cannot drift apart silently: a statement may only change by changing both files in the same commit, so no proof is ever quietly weakened to fit a proof that was easier to find.

**Here that is the whole reason the project exists.** Questions are answered by agents, and an agent writing a proof can edit the statement in the same edit. No `git diff` flags that, because a diff on the file the proof goes into is exactly what an answer is supposed to look like. The fourth check of `__check__.py` is the only thing that says the statement in the file the agent edited still matches the statement in the file it did not, so the second file is not overhead here—it is the mechanism.

## The three files

A unit—one directory, called whatever the project calls it and covering whatever slice of the source the project gives it (`./rules-formalization-project.md`)—carries:

- **`Challenge.lean` — the frozen specification.** The definitions its targets are stated over, cloned into the comparator namespace, then one declaration per target, each proved by `sorry`. It imports `Mathlib` and nothing else.
- **`Development.lean` — the same declarations, solved.** Exactly the same list, importing the project's production modules and replacing each target's body with a proof drawn from them. The cloned definitions keep their bodies unchanged—a definition has nothing to solve. Bodies still unproved stay `sorry`.
- **`CompareMathlib.lean` — the optional third file.** Same list again, proved *directly off the Mathlib API* rather than by the source's own argument—the shortest idiomatic route, ideally a one-liner naming the exact Mathlib lemma. Like `Challenge.lean` it imports only Mathlib. It exists for projects whose material Mathlib already covers, where reading the two proofs side by side is the point. It shares the comparator namespace, so it too stays out of the root module and is built by name. **Atlas keeps none**, and a unit here is the two files above: the file exists to set a source's own argument beside the Mathlib API, and Atlas follows no source's argument. Where the idea does apply—a question that turns out to be a Mathlib theorem—the identification is recorded in the `Knowledge/` item as a theorem the build keeps honest, not as a third frozen file per unit.

Production code—the real proofs, and the definitions they are stated over—lives outside the three, under the project's own namespace, and is governed by `./rules-formalization-project.md`.

## A comparator file imports only Mathlib

**`Challenge.lean` imports `Mathlib` (or `Mathlib.*`) and nothing else**—not whatever file holds the unit's production definitions, not one of its proof files, not another unit's `Challenge.lean`. `CompareMathlib.lean` is bound by the same rule: it carries the same declaration list, so it would have to hold the same definitions in any case, and reaching Mathlib by the shortest route is its whole purpose. `Development.lean` is the one file of the three that imports the project, since delegating to the production modules is what it is for.

### Questions are stated in Mathlib's vocabulary

**A target here is stated in Mathlib's vocabulary alone, so it clones nothing.** A `Knowledge/` notion a question is *about* is unfolded inline in the statement—`(S : Set ℕ) (hS : 0 ∈ S ∧ …)` rather than a hypothesis typed by `Atlas.Knowledge.JumpSet`. The knowledge layer is what an answer is *built from*, never what a question is *phrased in*.

This promotes to the default what the rest of this document treats as a last resort, and `./rules-formalization-project.md` already anticipates it: a unit whose targets are stated in Mathlib's vocabulary alone clones nothing into its comparator files. It is the default here because Atlas has one unit per topic and a knowledge layer meant to outlive all of them. A cloned definition is copied into two files by hand, and check 4 compares only *within* one unit directory—so a notion cloned by ten units lives in twenty hand-synced copies that nothing relates to each other, or to the original in `Knowledge/`. That is one static knowledge layer turned into eleven drifting ones, which is the opposite of what it is for.

What it costs is statement length, and nothing else. The bridge collapses to naming the production lemma, and the benchmark gets stronger: a Challenge with no project-local definition in scope is one an outside agent can read on its own terms, and one that cannot be weakened by an edit to a definition somewhere else.

**Cloning stays available as the exception**, where unfolding inline would genuinely be unreadable. It costs one sentence of justification in that Challenge's `## Implementation notes`, and the clone block then carries three rules the per-unit comparator namespace below does not cover, because none of the three is namespaced at all:

- **Any `notation` is `scoped`.** A `notation` inside a namespace is global unless marked, so two units cloning one notation declare it twice against different constants, and every use site in the root environment becomes ambiguous.
- **No instance whose head is entirely Mathlib.** It is registered globally under a fresh name per unit—no clash and no error, just N-way ambiguity in synthesis.
- **No top-level `attribute [...]` assignment.** It leaks across imports and is not namespaced at all.

The rest of this section describes what cloning entails when the exception is taken.

A comparator file therefore **clones, into the comparator namespace, every definition its targets are stated over**, ahead of the targets themselves. The clones are declarations like any other: they stand in all three files, in the same order, with the same signatures—and, a definition having nothing to solve, with the same bodies. They are independent copies of the production API and never references to it. The production files hold the originals under `<Project>`; each comparator file holds its own copies under `<Project>Challenge`; the two towers never meet.

A definition that cannot elaborate without a proof brings that proof with it: the well-formedness lemmas the production side carries for the sake of its definitions—the nonemptiness a `max'` needs, the range membership a `choose` needs—are part of the definitional layer and are cloned alongside what they serve. A `Challenge.lean` therefore does hold some real proofs. What it must never hold is a proof of a *target*, and the distinction is exactly the one the production definitions were already held to.

**The benchmark is then `Challenge.lean` alone**: one file, self-contained against Mathlib, stating what is wanted and proving none of it. Nothing beyond Mathlib has to be trusted to read it, and no companion file can quietly weaken it. The older architecture—`Challenge.lean` importing the unit's production definitions instead of cloning them—bought the same guarantee only by imposing two standing obligations (import only Mathlib, prove no target) on a file that was not itself a specification, so a single slip there silently voided the benchmark.

The price is paid twice over, and it is real. The definitional layer is now maintained in two places, three where a `CompareMathlib.lean` exists, with nothing but the production copy and the clones agreeing by hand; `__check__.py` compares the clones' *signatures* across the comparator files like any other declaration, but neither it nor Lean relates a clone to its production original at all. And every Development body must cross from the clone to that original, which is the next section.

### Bridging a clone to the production API

A cloned `def` or `abbrev` is definitionally equal to its original—same body, different namespace—so the two unfold to each other and a Development body delegating to a production lemma typechecks as it stands.

A cloned `structure`, `inductive`, or `class` is a **different type**, and no unfolding relates it to its original. This is the case that used to force a shared definitional layer, and the way through it is to convert at the boundary, inside the body of each target that needs it: take the comparator-namespace term apart with `obtain` (or `have`), rebuild the production term with the anonymous constructor `⟨...⟩`, apply the production result, and reassemble the comparator-namespace conclusion the same way.

```lean
theorem foo (x : Widget) (hx : IsGood x) : IsBetter x := by
  obtain ⟨mono, bound⟩ := hx
  obtain ⟨h₁, h₂⟩ := <Project>.foo ⟨x.toFun, x.mono'⟩ ⟨mono, bound⟩
  exact ⟨h₁, h₂⟩
```

The rebuilt term is accepted because a field of the clone reduces to the corresponding field of the original: `(⟨x.toFun, x.mono'⟩ : <Project>.Widget)` and `x` reach their arguments through their respective `FunLike` instances, and both unfold to `x.toFun`, so a hypothesis about one *is* a hypothesis about the other. This recurses through nested clones—a clone whose field mentions a second clone reduces along with it—and bottoms out because everything is ultimately built from Mathlib types, which the two towers share. A field that could not be traced back to Mathlib this way would be a definition the clone had no honest copy of, and the target mentioning it is the thing to restate.

**No helper declaration may be added to `Development.lean` to shorten this.** The lists must match, so the bridge lives in the body of the target that needs it, however often that repeats. A bridge worth naming is named on the production side, in a proof file—the body still has to cross the boundary itself.

The conversion is expected to carry most targets, not all. Where it genuinely cannot be written, the target stays `sorry` in `Development.lean` with a comment naming the obstruction, and it is the *statement* that gets revisited: restate the target in Mathlib's vocabulary so nothing has to be transported, and propagate the edit to every comparator file of the unit. Importing the production definitions back into `Challenge.lean` is not among the options.

In a project whose units are a source's chapters, later units build on earlier ones in the Development tower, by importing the earlier `Development.lean`. **Atlas's units do not build on each other at all**: a unit is one topic's questions, units are independent, and no `Questions/` directory imports another (`./rules-formalization-project.md`). What a second unit also wants moves up into `Knowledge/`, which is the one direction anything travels here.

## Namespaces

- Production declarations—the definitions and the proofs alike—live in `Atlas.Knowledge`, flat, one principal declaration per file and named for that file.
- **Both comparator files of a unit use that unit's own comparator namespace `AtlasChallenge.«YYYYMMDD<Topic>»`**—`Challenge.lean` and `Development.lean` alike, clones and targets together. The French quotes are not decoration: `20260813LegendreFormula` opens with a digit and so is not an identifier, and the namespace does not parse without them. Its being distinct from `Atlas` is what lets Development delegate to a production declaration of the same short name without a clash; its being *shared* across the unit's files is what makes them literal alternatives, one declaration list under one set of names, and is why no two of them may meet in one environment (see below).

	**The namespace is per unit rather than one project-wide `AtlasChallenge`, and that is where this copy departs from the template it was generated from.** The root module holds every `Development.lean` at once, so under a single shared namespace any two units that clone the same definition declare one name twice—and Lean rejects a duplicate `def` outright. A project with one unit never meets this; a project with one unit per topic meets it on the second unit that clones. `__check__.py` is indifferent to the change: it never parses a `namespace` line as a declaration, it stops a multi-line signature at one, and it keys units by the directory their `Challenge.lean` sits in.

	Name resolution is unaffected. `namespace A.B` is sugar for `namespace A` followed by `namespace B`, so both are enclosing and the clone-wins precedence below holds unchanged; another unit's namespace is a *sibling*, and is never in the resolution chain.
- Dot notation works inside the comparator namespace, because the clone a target's hypothesis is typed by lives there too: `IsJumpSetWithin.isJumpPairWithin` applies to a term of type `<Project>Challenge.IsJumpSetWithin`. The production restatement in the proof file provides it independently, over `<Project>.IsJumpSetWithin`.
- `Development.lean` needs `open Atlas.Knowledge` to name the production declarations it delegates to, and it is the only file where a short name has both a clone and an original in scope. **The clone wins**—a declaration of the enclosing namespace takes precedence over one reached by `open`, with no ambiguity error (checked on Lean v4.28.0). That is the right default, since it is the clone the statements must be about; but it means a delegation that *wants* the original gets the clone silently. Write the production one `Atlas.Knowledge.foo` in full at the call site, every time. Under the statement policy above a Development body usually has no clone in scope at all, which removes the trap rather than managing it.

## The declaration lists must match exactly

Across the files of one unit, preserve **names, kinds, binders, types, attributes, and order**, together with the docstrings. The only differences permitted are the `import` block and the bodies of the *targets*.

- **A cloned definition's body must match too.** A definition has nothing to solve, so a clone whose body differs across two comparator files means the two files specify different objects—precisely the silent drift the pair exists to prevent. `__check__.py` compares signatures and not bodies, so this one is on the editor: copy the clone block between the files verbatim rather than retyping it.
- The clones come first, in dependency order, and the targets after them, in the order of the source. A definition no target mentions—directly, or through another clone—does not belong in the comparator files at all. A definition that *is* cloned brings its own support with it, though: the instances that make it usable, its `ext` and `@[simp]` lemmas, and the well-formedness proofs it cannot elaborate without. In practice a unit whose targets are built on types of its own ends up cloning its whole definitional layer, and copying it outright is then both simpler and safer than pruning it.
- **A clone block may hold two declarations of one short name**, since a name is unique only within its namespace and the block carries the nested ones (`Shift.eStar` and `FiniteShift.eStar`). `__check__.py` pairs the lists positionally, so this is fine—but any tooling that keys declarations by bare name will silently let the second shadow the first.
- **A data-valued *target* is not a clone.** A construction the source itself asks for—a correspondence it builds, a definition whose well-formedness is one of its numbered claims—is declared among the targets, has no production original to be a copy of, and may legitimately differ between `Development.lean` and `CompareMathlib.lean`. Which of the two a `def` is decides whether its body may vary, so keep the clone block and the target block visibly separate.
- Never delete an implemented declaration from `Development.lean` to make something typecheck.
- When the specification changes, make the same declaration-level edit in every file of the unit **in the same commit**. The safe order is: edit `Challenge.lean` first, copy the changed declaration verbatim into the others, then restore each one's body.
- When closing a target, edit **only its body** in `Development.lean`. The Challenge declaration and its `sorry` body stay untouched—`Challenge.lean` is a specification, not a progress tracker.
- A declaration that is genuinely private scaffolding (a helper the API does not expose) does not belong in the comparator files at all; it belongs in a proof file. This includes any bridge a Development body wants: the lists must match, so a comparator file gains no helper of its own.

## Never in one environment

The three comparator files declare the same names in the same namespace, so **no module may reach more than one of them**—not by importing two directly, and not by importing one file that in turn imports another. The root all-import module imports `Development.lean` only; `Challenge.lean` and `CompareMathlib.lean` are built by name. `__check__.py` checks the root module's own import list for the two by name, and separately walks the whole import graph for any module that ends up holding two files of one unit.

**Lean catches only part of the mistake, and not the part that matters.** A duplicate `def` is rejected outright on import, even when its two copies agree in every respect down to the body; so is a duplicate `theorem` whose two types differ, including types that are definitionally equal but not syntactically so. What passes is two `theorem`s whose types match *syntactically*: those are accepted and merged, their bodies being irrelevant by proof irrelevance. The comparator's whole discipline is that the declaration lists match verbatim, so an accidental co-import lands in precisely the tolerated case—no error, no warning, one of the two bodies silently dropped. Which one survives is unspecified and has changed between releases—last-import-wins on Lean v4.28.0, first-import-wins on v4.32.1—so a `sorry`ed Challenge target can quietly supersede a proved Development one, and everything downstream of it becomes vacuous without a diagnostic.

A unit is therefore exposed exactly to the extent that its declaration list is theorems: one data-valued declaration in the list is enough for the build to fault a co-import, and a unit of theorems alone has nothing but `__check__.py` standing between it and a silent merge. Cloning the definitions into the list has narrowed the gap—a unit needing any definition of its own now carries a `def` or a `structure`, and its co-imports fault outright—but a unit whose targets are stated in Mathlib's vocabulary alone still clones nothing and remains fully exposed. Do not read a clean build as evidence either way. `#print axioms <target>` is what exposes the merge after the fact; keeping the files out of each other's reach is what prevents it.

## Section variables

Keep an assumption that does not occur syntactically in a result explicit with `include ... in`. Lean includes a section `variable` in a declaration only when the declaration's statement or *body* mentions it, so a hypothesis used by a `sorry`-free Development body—but absent from the statement—would silently enter Development's elaborated type while missing from Challenge's, breaking the match in exactly the case that is hardest to notice.

```lean
variable (K : Type*) [Field K] [ValuativeRel K] [IsUniformAddGroup K]

include ‹IsUniformAddGroup K› in
theorem foo : ... := ...
```

(The `include`/`omit` commands were absent from early Lean 4 and reintroduced for section variables; they are current Lean 4 and are used throughout Mathlib.)

**`include ... in` is the only tool for this**, one occurrence per declaration that needs it. The alternative it is tempting to reach for—`set_option linter.unusedSectionVars false` at the top of the file—is not available: the file-level `set_option` block is empty (`./rules-formalization-project.md`). It was in any case the weaker instrument, since it silences the warning without changing what Lean includes; the mismatch it was meant to guard against is fixed by `include`, not by the linter setting.

## Checking

Each project carries its own copy of the checker, so a hook or a CI step can run it per project. From the project directory:

```bash
python3 __check__.py
```

It performs four structural checks:

1. The root all-import module directly imports every module of the project except the two built by name, and imports neither of those—so no file can be silently dropped from the build.
2. No module of the project reaches two comparator files of one unit, by direct import or along any chain of imports—so no collision can be silently merged into the build. A violation is reported against the module whose own import list first brings the second file into reach, not against everything downstream of it.
3. `Challenge.lean` and `CompareMathlib.lean` import nothing but `Mathlib`—so a Challenge stands alone as the benchmark it is meant to be.
4. The comparator files of each unit expose the same declarations, of the same kind, with the same attributes and signature, in the same order.

It is a textual check on the sources, so it is fast and needs no build; it does not verify *elaborated* types, which only a build does—a `variable` silently dropped from one side is caught by the build, not by the script. Nor does it compare declaration *bodies*, so a cloned definition that drifts between two comparator files passes check 4; copying the clone block verbatim is what prevents that. Since the two excluded files are outside the default target, each needs its own build:

```bash
lake build
find Atlas -name Challenge.lean | sed -E 's|/([0-9][^/]*)/|/«\1»/|g; s|^|lake build |; s|/|.|g; s|\.lean$||' | sh
```

The second command is a loop rather than a single target because there is one Challenge per question unit, and it is the same loop `.github/workflows/build.yml` runs. Its first substitution wraps the unit directories in the French quotes the module names require—`20260813LegendreFormula` opens with a digit and so is not an identifier, and without them lake cannot resolve the target. Keep the quotes when building one by hand: `lake build 'Atlas.Questions.«20260813LegendreFormula».Challenge'`.

`sorry` warnings from the comparator files are expected, and a Challenge target's `sorry` is permanent—it is the question, not a gap. **`Knowledge/` is exempt from the usual "production modules build without them" rule, in one direction only:**

- A `Knowledge/` **theorem** may be `sorry`. That is a claim recorded before its proof, and the build warning naming its module and line is the whole of the backlog—nothing else tracks it, and nothing else needs to. It is not to be "fixed" by deleting the claim.
- A `Knowledge/` **definition** may never sit above a `sorry`. A `sorry`ed proof obligation inside a `def` is a junk value rather than a hole: it elaborates, it propagates through everything downstream, and it warns in only one place. Prove the obligation, or do not make the definition.
