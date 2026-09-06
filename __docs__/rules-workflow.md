# The workflow cycle of a formalization phase

How formalization work travels from a plan to merged, verified code. The sibling documents govern the *artifact*—what a file carries (`./rules-documentation.md`), how its prose is set (`./rules-comments.md`), how the project is laid out (`./rules-formalization-project.md`), what the comparator protects (`./rules-comparator.md`)—and this one governs the *process* around them. It exists for the same reason the comparator does: the failures worth designing against are the ones the artifact cannot flag itself.

The unit the cycle turns on is a **phase**: one dependency-ordered tranche of an ingestion plan, small enough for one branch and one review, large enough to leave the knowledge layer usable when it lands. Issue #1 and PR #3 are the worked example; everything below was first practiced there.

## One revolution

1. **The plan is a tracking issue, and the issue is the todo list.** An ingestion campaign is drafted as a GitHub issue whose checkboxes are the items, grouped into phases in dependency order, with the ground rules restated inline—one file = one item, definitions sorry-free always, theorems may land as claims recorded ahead of their proofs—so the issue reads standalone. The checkbox is the unit of accounting for the whole cycle: everything downstream either fills one or waits on one.

2. **One phase is formalized per pull request**, by the authoring agent on its own branch. The three checks run before the PR opens—`python3 __check__.py`, `lake build`, and the Challenge builds by name—and the PR body maps the phase's checkboxes to the files that land them, says what is proved against what is merely recorded, and counts its sorries so the reviewer can hold it to that count.

3. **A second agent reviews the PR, on a different model than the author.** The review is adversarial, not editorial: it reads the diff against the rules documents *and against the source transcription*, pinpoint by pinpoint, and it attacks the recorded claims—instantiates degenerate parameters, hunts junk values, tries to derive `False` in Lean against the built project. Findings come back ranked blocking / should-fix / nit, each with a location and a reason.

4. **The author applies the revision on the same branch.** Blocking and should-fix findings land in one commit; nits are deferred *explicitly*, enumerated in a PR comment, so that deferral is a record rather than an evaporation. The comment says what was done, finding by finding, and what was deliberately not.

5. **Verification, then the tick.** The phase's checkboxes are ticked only after a verifier—best the same reviewer resumed, since its own findings are its context—confirms every finding fixed and re-runs the checks. Confirming the fix of a refuted claim means re-running the refutation and watching it fail, and then showing positively that the degeneracy is gone, not re-reading the statement. Only then are the boxes ticked; only the phase's own boxes; and never by the author.

6. **Merge, linearly.** Rebase onto the default branch—this project's history is a line, and the phases read in order—and delete the branch.

## Why the author never ticks its own boxes

This is the comparator's threat model, one layer up. `./rules-comparator.md` exists because an agent writing a proof can edit the statement in the same edit and no diff flags it. The backlog has the same soft spot: an agent recording a claim can record a *false* claim, and a `sorry` warning does not distinguish unproven from unprovable—the build output reads identically, and the defect surfaces only when a later phase tries to discharge the claim and cannot. The adversarial review is what keeps the backlog honest, and the tick is the record that it ran: a ticked box means *verified by the other*, never *the author considers itself done*. This is not hypothetical. The first revolution of this cycle caught four recorded claims that were false at a degenerate multiplicity, refuted in Lean by the reviewer before they could calcify into backlog.

## Mechanics

- **Different models for author and reviewer.** A reviewer sharing the author's model shares its blind spots; the review's value is exactly the failure modes the author does not have. What the rule fixes is that difference and nothing else: any two capable models satisfy it, drawn from one vendor's line or from several, and which two a given run used is a property of that run rather than of this document. It needs no separate record, because the commits already carry it—the authoring commit's trailer names the author, and the revision commit that closes a review is titled for the reviewer.
- **Resume the reviewer as the verifier.** A fresh verifier re-derives the findings from the report; the resumed reviewer holds them as context and can re-run its own refutations verbatim. Resuming is the cheaper *and* stricter option, which is rare enough to insist on.
- **The verifier owns the tick, and the tick is byte-exact.** Ticking edits the issue body so that only the `- [ ]` markers of the phase's own lines change—asserted programmatically (line count, byte length, the exact diff set), not eyeballed. Where a sandbox denies the verifier the write, it prepares the exact edit and the supervising session applies it verbatim: preparing and applying are separable; verifying and authoring are not.
- **Every generated artifact names its session.** An agent-written issue, PR body, or comment ends with the ID of the session that wrote it—``Session: `<id>` ``—so the conversation that produced the artifact can be reopened, with its context intact, through whatever resume command the agent's own CLI provides. It is the resume-the-reviewer principle extended to the human: the record of *what* was done should carry the handle to *the context it was done in*.
- **Deferred is recorded.** A nit deferred without a record is a nit lost. The PR comment that closes a revision names what it did not fix, so the next phase inherits a list rather than a suspicion.
- **A false claim outranks everything.** A review finding that a recorded claim cannot be proved is blocking by definition, whatever its surface size—one missing hypothesis is enough—because the standing exemption for `sorry` on theorems is exactly what it abuses.
