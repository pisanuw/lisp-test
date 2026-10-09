# BPS Homework One — Grading Rubric

Companion to [bps-hwk1-answer-sheet.md](bps-hwk1-answer-sheet.md), which holds the
reference solutions, verified expected outputs, and the catalogue of common errors this
rubric refers to.

**Total: 100 points.** Part 1 = Problem 4 (`multi-fetch`), Part 2 = Problem 6
(lazy introduction rules + the Part B explanation).

| Section | Points |
|---|---:|
| A. Submission and loadability | 5 |
| B. Part 1 — `multi-fetch` | 45 |
| C. Part 2a — lazy AND / BICONDITIONAL INTRODUCTION | 35 |
| D. Part 2b — the assumption, answered in comments | 15 |

---

## A. Submission and loadability — 5 points

The assignment states: *"we should be able to load it into Lisp ourselves to confirm that
it works."* Treat that as a hard requirement.

| Criterion | Pts |
|---|---:|
| Source file loads into a fresh Lisp on top of the BPS `tre` sources with no errors | 3 |
| Header comment: name, which problems are solved, what to load first, how to run the tests | 2 |

**Does not load at all.** Spend up to five minutes on obvious mechanical repairs — a
missing `(in-package :COMMON-LISP-USER)`, a stray paren, a file that assumes `tre.lisp`
was loaded. Fix, note the repair, deduct the 3 points, and grade the rest normally.
Beyond five minutes, grade Parts B–D by reading the code and cap the submission at 70.

Style warnings from SBCL about unused `?` variables come from TRE itself and are **not** a
defect.

---

## B. Part 1 — `multi-fetch` — 45 points

### B1. Joint-match semantics — 20 pts

Does a set returned by `multi-fetch` represent one *consistent simultaneous* match, with
shared variables bound identically across the whole set?

| Level | Description | Pts |
|---|---|---:|
| Full | Genuine join. Grandparent query returns exactly the 2 consistent pairs, not the 9-element unfiltered cross product | 18–20 |
| Strong | Join is correct but recomputes matching redundantly (generate-and-test over the full cross product, then filter) | 14–17 |
| Partial | Attempts consistency but gets it wrong in a reproducible way (e.g. only checks the first shared variable; drops bindings after the second pattern) | 8–13 |
| Weak | `(mapcar #'fetch patterns)` — independent per-pattern fetches, no consistency. See answer sheet §2.1 | 4–7 |
| None | Does not return per-pattern matches at all | 0–3 |

> **Interpretive note.** The "Weak" row is the defensible-but-wrong reading of the problem
> statement. If a student explicitly argues for it in a comment *and* implements it
> cleanly, award up to 10 rather than 7. If `bps-hwk1-unit-test.lsp` turns out to encode
> that reading, the levels invert — regrade against the tests and say so.

### B2. Binding propagation through structure — 10 pts

The discriminating case is a pattern pair like `((implies ?a ?c) ?a)` against a database
holding `(implies (human ?x) (mortal ?x))` and `(human socrates)`.

| Level | Description | Pts |
|---|---|---:|
| Full | Bindings threaded into nested terms; the modus-ponens join returns the fully instantiated pair | 9–10 |
| Partial | Works for atoms, fails or leaves unbound variables inside nested structure; or uses a single non-recursive `sublis` that breaks on variable-to-variable chains | 4–8 |
| None | No binding propagation | 0–3 |

### B3. Return shape and base cases — 7 pts

| Criterion | Pts |
|---|---:|
| One pattern behaves like `fetch` (same matches, wrapped one per set) | 3 |
| No consistent match returns `nil` rather than erroring or returning `(nil)` | 2 |
| Empty pattern list handled without error (`(nil)` or `nil` both accepted) | 2 |

**Grade on set equality, not list order.** A permutation of the expected output is correct.

### B4. Robustness — 5 pts

| Criterion | Pts |
|---|---:|
| Pattern whose head is an unbound variable (`?p`, `(?rel a b)`) does not crash — full scan fallback | 2 |
| Accepts an optional TRE argument defaulting to `*TRE*`, like `fetch` | 1 |
| Pure query: asserts nothing, mutates no TRE state | 2 |

A crash on an unindexable pattern is the expected failure mode for students who call
`get-candidates` directly; see answer sheet §2.3.

### B5. Code quality — 3 pts

Readable decomposition, meaningful names, comments explaining the join; reuses `unify`,
`get-candidates` and `variable?` rather than reimplementing unification by hand.

---

## C. Part 2a — lazy introduction rules — 35 points

### C1. AND INTRODUCTION — 15 pts

| Level | Description | Pts |
|---|---|---:|
| Full | `(show ?b)` is asserted inside the body of the rule that waits for `?a`; the innermost rule on `?b` still guards the conjunction | 14–15 |
| Strong | Correct laziness with harmless extras (a `fetch` guard, redundant re-posting of `(show ?a)`) | 11–13 |
| Partial | Laziness attempted but the saving does not materialise — e.g. both `show`s still posted, or `(show ?b)` posted from the innermost rule where it is dead code | 5–10 |
| Unsound | Conjunction asserted without waiting for `?b` (innermost rule dropped). **Derives false conclusions** | 0–4 |
| None | Rule unchanged from the book | 0 |

### C2. BICONDITIONAL INTRODUCTION — 15 pts

Same levels as C1, with `(show (implies ?b ?a))` moved inside the rule triggered by
`(implies ?a ?b)`.

Additional check: the nested rules must trigger on `(implies ?a ?b)` and `(implies ?b ?a)`,
**not** on `?a` and `?b`. Nesting on the bare propositions is a wrong-trigger error — cap
C2 at 7.

### C3. Correctness preserved — 5 pts

Both rules must still work when the constituents arrive **after** the goal, which is the
normal case. Verify:

```lisp
(assert! '(show (and p q)))   ; goal first
(assert! 'p) (assert! 'q)     ; facts later  =>  (and p q) must appear
```

| Criterion | Pts |
|---|---:|
| Conjunction/biconditional still derived when constituents arrive after the goal | 3 |
| Still derived when they arrive before the goal | 2 |

A student who adds an unnecessary `fetch` guard because they believe a late-installed rule
misses earlier facts is **not** wrong — `add-rule` does scan the existing database — but a
one-line note in the margin is a useful teaching moment.

---

## D. Part 2b — the assumption — 15 points

Must be **in comments attached to the rules**, per the assignment. An answer in a separate
file or the README loses 2 points but is otherwise graded on content.

### D1. Names the assumption — 8 pts

| Level | Description | Pts |
|---|---|---:|
| Full | States that proving the first constituent must not depend on interest in the second having been posted — equivalently, that `show` assertions are pure control and produce no data another proof needs | 7–8 |
| Strong | States the dependency correctly but without the "pure control" generalisation | 5–6 |
| Partial | Gestures at order independence or at "the conjuncts must be independent" without naming the dependency | 3–4 |
| Weak | Talks only about speed, or restates what the new rules do | 1–2 |
| None | Absent | 0 |

### D2. Explains how it can be violated — 7 pts

| Level | Description | Pts |
|---|---|---:|
| Full | Identifies the mechanism — a rule triggering on a `show` that asserts ordinary data — **and** gives a concrete instance (an assumption-making rule such as CONDITIONAL INTRODUCTION or indirect proof, or a worked counterexample) | 6–7 |
| Strong | Mechanism or concrete example, not both | 4–5 |
| Partial | Vague ("some other rule might need it") with no mechanism | 2–3 |
| None | Absent | 0 |

### Bonus — up to 3 pts (may exceed the section total, capped at 100 overall)

- Notices that back-chaining on CE can **re-derive** the suppressed interest, so laziness
  is safe for some rule sets and not others (answer sheet §4.3).
- Notices that `(and A B)` and `(and B A)` now behave differently, breaking the order
  independence claimed in Section 4.5.
- Supplies a runnable counterexample in the submitted file.

---

## Deductions (applied after section scoring)

| Issue | Deduction |
|---|---:|
| Does not load; mechanically repairable in under 5 minutes | −3 (from A) |
| Does not load; not quickly repairable | cap at 70 |
| Part 2b answered outside the rule comments | −2 |
| TRE source files modified instead of extended in the submission | −5 |
| Debugging output left on by default (`*debug-nd*`, stray `format`/`print` in rule bodies) | −2 |
| Submitted as multiple files with no load order given | −2 |
| Unsound rule that asserts conclusions it has not proven | already scored in C1/C2 — do not double-penalise, but flag it prominently in feedback |

---

## Grading workflow

### Setup (once)

```lisp
;; from a fresh Lisp, with the BPS tre/ sources on hand
(dolist (f '("tinter" "data" "rules" "unify"))
  (load (merge-pathnames (concatenate 'string f ".lisp") *bps-tre-path*)))
(load "treex1.lisp") (ex1)     ; smoke test: should derive (MORTAL TURING)
```

### Per submission

1. Load the student's file. Record whether it loads clean.
2. Run `bps-hwk1-unit-test.lsp`. Record pass/fail per test.
3. Run the `multi-fetch` checks from answer sheet §2.4, especially the
   **modus-ponens join** (B2) and the **grandparent join** (B1) — those two separate most
   of the field.
4. Diff the student's two introduction rules against the originals on p. 103. The correct
   change is small and local; anything large deserves a closer read.
5. Run the Part 2a savings scenario from answer sheet §3.4 and confirm `(show q)` is
   absent from the database.
6. Read the rule comments for Part 2b.

### Fast triage (~5 min per submission)

| Check | Tells you |
|---|---|
| `(multi-fetch '((parent ?g ?p) (parent ?p ?c)))` returns 2 sets, not 6 | B1 level in one call |
| `(multi-fetch '((implies ?a ?c) ?a))` returns the instantiated pair | B2 level in one call |
| `(show ?b)` appears lexically inside a `(rule ?a ...)` form | C1 level by inspection |
| The word "show" appears in the Part 2b comment | whether D2 engages with the mechanism at all |

---

## Note on `bps-hwk1-unit-test.lsp`

That file was **not in the repository** when this rubric was written, so the point
allocations above were derived from the problem statements in the text rather than from
the tests. Before grading, reconcile two things (answer sheet §5):

- whether the tests pin `multi-fetch`'s argument order and return shape;
- whether the tests encode the join reading or the independent-fetch reading of Problem 4.

**Where the provided tests and this rubric disagree, the tests govern**, and the B1 levels
should be re-weighted accordingly. Consider allocating a portion of Part 1 and Part 2a
directly to "passes the provided unit tests" once that file is in hand — the assignment
makes passing them an explicit requirement, and the rubric currently scores the underlying
behaviour instead.
