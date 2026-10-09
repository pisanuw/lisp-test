# BPS Homework One — Answer Sheet

Reference solutions for Problems 4 and 6 of Section 4.7 of *Building Problem Solvers*
(Forbus & de Kleer), pages 105–106.

All code in this document was executed against the real BPS `tre` sources
(`tinter.lisp`, `data.lisp`, `rules.lisp`, `unify.lisp`) under SBCL 2.4.0. Measured
numbers quoted below are actual run output, not estimates.

---

## 0. What the problems say

> **4.** `**` Write `multi-fetch`, which takes as input a set of patterns and returns a
> list of sets of assertions which match those patterns.

> **6.** The rules for AND INTRODUCTION and BICONDITIONAL INTRODUCTION actually do
> unnecessary work. If the system cannot prove one conjunct, for example, there is no
> reason to waste time on attempting to prove the other.
>
> **a.** `*` Write new versions of AND INTRODUCTION and BICONDITIONAL INTRODUCTION that
> only look for the second constituent when the first has been proven.
>
> **b.** `*` These more efficient versions make an important assumption about the set of
> rules as a whole. What is that assumption? How might it be violated?

---

## 1. TRE machinery a solution is allowed to lean on

Graders should recognise these as fair game; students do not need to reimplement them.

| From | Used for |
|---|---|
| `fetch` (`data.lisp`) | single-pattern retrieval; returns `(sublis bindings pattern)`, i.e. the *instantiated pattern*, not the raw database fact |
| `get-candidates` / `get-dbclass` (`data.lisp`) | car-indexed candidate lookup |
| `unify` (`unify.lisp`) | takes an optional incoming `bindings` alist and returns `:FAIL` or an extended alist |
| `tre-dbclass-table` (`tinter.lisp`) | the hash table of all dbclasses, for a full scan |
| `rule` / `add-rule` (`rules.lisp`) | installing rules; **note** `add-rule` scans facts already in the database, so a rule installed late still sees earlier facts |
| `*ENV*` | the environment a rule body runs in; `run-rule` already substitutes rule variables before the body evaluates |

---

## 2. Part 1 — `multi-fetch`

### 2.1 The interpretation that matters

The phrase "a list of sets of assertions which match those patterns" is doing real work.
The intended reading is a **conjunctive query / join**: `multi-fetch` returns one set per
*consistent simultaneous* match, where variables shared between patterns receive a single
binding across the whole set.

That is the reading the `**` difficulty rating implies, and it is the data-level analogue
of the multiple-trigger rules introduced in Chapter 5 (`(rule ((implies ?p ?q) ?p) ...)`).
The alternative reading — independently fetching each pattern and collecting the results —
reduces to `(mapcar #'fetch patterns)`, a one-liner that does not deserve two stars and
that throws away exactly the information the function exists to compute.

> **If `bps-hwk1-unit-test.lsp` encodes a different contract, the tests win.** That file
> was not in the repository when this sheet was written, so the function signature and
> return shape below should be reconciled against it before grading. See §5.

### 2.2 Reference solution

```lisp
;;;; Problem 4 of Section 4.7 -- multi-fetch

(defun plug (exp bindings)
  "Substitute BINDINGS into EXP, chasing variable-to-variable chains.
   Unlike SUBLIS this is recursive, so ?x -> ?y -> FOO resolves to FOO."
  (cond ((null exp) nil)
        ((variable? exp)
         (let ((binding (assoc exp bindings)))
           (if binding (plug (cdr binding) bindings) exp)))
        ((not (consp exp)) exp)
        (t (cons (plug (car exp) bindings)
                 (plug (cdr exp) bindings)))))

(defun all-facts (tre &aux facts)
  "Every fact in the database, for patterns car indexing cannot help with."
  (maphash #'(lambda (key dbclass)
               (declare (ignore key))
               (setq facts (append (dbclass-facts dbclass) facts)))
           (tre-dbclass-table tre))
  facts)

(defun indexable? (pattern)
  (let ((head (if (listp pattern) (car pattern) pattern)))
    (and head (not (variable? head)))))

(defun candidates-for (pattern tre)
  (if (indexable? pattern)
      (get-candidates pattern tre)
      (all-facts tre)))

(defun multi-fetch (patterns &optional (tre *TRE*) &aux results)
  "Given a list of PATTERNS, return a list of sets of assertions.  Each set
   contains one assertion per pattern, and the sets are consistent: variables
   shared between patterns receive a single binding across the whole set."
  (labels
      ((walk (remaining bindings)
         (cond ((null remaining)
                (push (mapcar #'(lambda (p) (plug p bindings)) patterns)
                      results))
               (t (dolist (candidate (candidates-for
                                      (plug (car remaining) bindings) tre))
                    (let ((new (unify (car remaining) candidate bindings)))
                      (unless (eq new :FAIL)
                        (walk (cdr remaining) new))))))))
    (walk patterns nil))
  (nreverse results))
```

### 2.3 Why each piece is there

- **Depth-first backtracking.** `walk` commits to a match for the first pattern, carries
  the resulting bindings into the rest, and backtracks. This is what makes the result
  *consistent* rather than a raw cross product.
- **Bindings threaded through `unify`.** `unify` already accepts incoming bindings and
  extends them, so the join is nearly free — this is the key insight the problem is
  testing.
- **`plug` before `candidates-for`, not before `unify`.** The substituted copy is only
  used to pick an index. `unify` is given the *original* pattern plus the bindings,
  because `unify-variable` resolves bound variables correctly on its own. Substituting
  first and then unifying also works, but only if the substitution is recursive.
- **The `all-facts` fallback.** `get-dbclass` signals an error on a pattern whose head is
  an unbound variable. A pattern like `?p`, or `(?rel a b)`, therefore cannot be car
  indexed and needs a full scan. Students who do not handle this get a crash rather than
  a wrong answer, so it is easy to spot.
- **Instantiated patterns, not raw facts.** The result mirrors `fetch`, which returns
  `(sublis bindings pattern)`. For a ground database the two coincide; for a database
  containing variables they do not.

### 2.4 Verified behaviour

Database:

```lisp
(parent abe homer) (parent homer bart) (parent homer lisa)
(male abe) (male homer) (male bart) (female lisa)
(implies (human ?x) (mortal ?x)) (human socrates)
```

| Call | Result |
|---|---|
| `(multi-fetch '((male ?x)))` | `(((male bart)) ((male homer)) ((male abe)))` |
| `(multi-fetch '((parent ?g ?p) (parent ?p ?c)))` | `(((parent abe homer) (parent homer lisa)) ((parent abe homer) (parent homer bart)))` |
| `(multi-fetch '((parent ?g ?p) (parent ?p ?c) (male ?c)))` | `(((parent abe homer) (parent homer bart) (male bart)))` |
| `(multi-fetch '((parent ?x ?y) (female ?x)))` | `nil` |
| `(multi-fetch '((implies ?a ?c) ?a))` | `(((implies (human socrates) (mortal socrates)) (human socrates)))` |
| `(multi-fetch '((female ?x) (male ?y)))` | 3 sets (full cross product — no shared variables) |
| `(multi-fetch '(?p))` | one set per fact in the database |
| `(multi-fetch '())` | `(nil)` |

Two results worth commenting on:

- **`(implies ?a ?c)` with `?a`** is the modus-ponens join. The implication in the
  database is `(implies (human ?x) (mortal ?x))`, and the second pattern forces
  `?x = socrates`. Getting this case right requires threading bindings into *structured*
  terms, not just atoms — it is the single best discriminator in the whole problem.
- **`(multi-fetch '())`** returns `(nil)` — one empty solution — because an empty
  conjunction is vacuously satisfiable. Returning `nil` instead is a defensible
  convention; do not penalise either unless the provided tests pin it down.

### 2.5 Result ordering

Order depends on the order facts were pushed onto their dbclass and on which pattern is
tried first. **Grade on set equality, not list equality.** A student whose output is a
permutation of the table above is correct.

### 2.6 Acceptable variations

- **Returning bindings alongside the assertions**, e.g. `((<assertions> . <bindings>) ...)`.
  Full credit if documented; it is strictly more informative.
- **Generate-and-test**: `fetch` each pattern independently, form the cross product, then
  re-unify each combination and discard `:FAIL`. Correct, but does all the matching work
  twice and explores combinations a join would have pruned immediately. Full credit for
  correctness, minus a small amount for efficiency if the student does not acknowledge it.
- **Iterative worklist** instead of recursion. Fine.
- **Using `sublis` instead of `plug`**, *provided* it is applied to a fixed point or the
  student unifies against the original pattern with bindings threaded. A single
  non-recursive `sublis` pass silently produces wrong answers when one variable is bound
  to another; see §2.7.

### 2.7 Common wrong answers

| Symptom | Cause | Severity |
|---|---|---|
| Returns `((f1 f2 f3) (f4 f5) ...)` — one list per *pattern* | `(mapcar #'fetch patterns)`; no joint consistency | Major — misses the point of the problem |
| Grandparent query returns 9 sets instead of 2 | Unfiltered cross product of per-pattern `fetch` results | Major |
| Crash: `Dbclass unbound: ?P` | No fallback for an unindexable pattern head | Moderate |
| Modus-ponens join returns nothing, or returns an unbound `?x` | Bindings not threaded through nested structure, or single-pass `sublis` | Major |
| Duplicate identical sets | Candidate list scanned more than once; usually harmless | Minor |
| Mutates `*TRE*` or asserts anything | `multi-fetch` must be a pure query | Moderate |
| Ignores the optional `tre` argument | Breaks when a grader runs two TREs | Minor |

---

## 3. Part 2a — lazy AND INTRODUCTION and BICONDITIONAL INTRODUCTION

### 3.1 The rules as published (p. 103)

```lisp
(rule (show (and ?a ?b))                       ;; And Introduction
      (assert! `(show ,?a))
      (assert! `(show ,?b))
      (rule ?a (rule ?b (assert! `(and ,?a ,?b)))))

(rule (show (iff ?a ?b))                       ;; Biconditional Introduction
      (assert! `(show (implies ,?a ,?b)))
      (assert! `(show (implies ,?b ,?a)))
      (rule (implies ?a ?b)
            (rule (implies ?b ?a)
                  (assert! `(iff ,?a ,?b)))))
```

The waste is in line 3 of each: interest in the second constituent is posted
unconditionally, so every rule keyed on that `show` starts working even when the first
constituent is hopeless.

### 3.2 Reference solution

```lisp
;;;; Problem 6a of Section 4.7
;;;; Only express interest in the second constituent once the first has
;;;; actually been proven.  The (rule ?a ...) form installs a rule that waits
;;;; for ?a; its body does not run until ?a is in the database.

(rule (show (and ?a ?b))                       ;; And Introduction, lazy
      (assert! `(show ,?a))
      (rule ?a                                 ; fires only once ?a is proven
            (assert! `(show ,?b))              ; NOW ?b is worth pursuing
            (rule ?b (assert! `(and ,?a ,?b)))))

(rule (show (iff ?a ?b))                       ;; Biconditional Introduction, lazy
      (assert! `(show (implies ,?a ,?b)))
      (rule (implies ?a ?b)                    ; fires only once the first
            (assert! `(show (implies ,?b ,?a)))  ; direction is established
            (rule (implies ?b ?a)
                  (assert! `(iff ,?a ,?b)))))
```

The entire change is **moving the second `assert!` of a `show` from the outer rule body
into the body of the rule that waits for the first constituent.** The innermost rule is
unchanged.

### 3.3 Why this is still correct

Two properties of TRE make the laziness safe with respect to *timing*:

1. **Nested rules are lexically scoped.** `add-rule` stores `*ENV*` in the rule struct, so
   `?a` and `?b` remain bound inside the nested rules even though they are installed much
   later. No re-matching is needed.
2. **`add-rule` scans the existing database.** Its last form is
   `(dolist (candidate (get-candidates trigger *TRE*)) (try-rule-on rule candidate *TRE*))`.
   So `(rule ?b ...)`, installed only after `?a` arrives, still fires if `?b` was proven
   earlier. Students sometimes worry about this and add a redundant `fetch` guard; it is
   unnecessary but not wrong.

### 3.4 Measured effect

Rule set: the chapter-4 KM\* rules of pp. 101–103 (NOT/AND/CONDITIONAL elimination,
back-chaining on CE, OR introduction) plus the variant under test.

**Correctness (unchanged behaviour where it matters)**

| Scenario | Original | Lazy |
|---|---|---|
| `p`, `q` asserted, then `(show (and p q))` | derives `(and p q)` | derives `(and p q)` |
| `(show (and p q))` first, `p` and `q` asserted after | derives `(and p q)` | derives `(and p q)` |
| `(implies a b)`, `(implies b a)`, `(show (iff a b))` | derives `(iff a b)` | derives `(iff a b)` |

**Savings.** Goal `(show (and p q))` where `p` is unprovable and `q` sits behind a chain
`(implies r1 q)`, `(implies r2 r1)`, `(implies r3 r2)`:

| | rules run | `show` assertions posted |
|---|---|---|
| Original | 13 | 6 |
| Lazy | **6** | **2** |

The lazy version never posts `(show q)`, so back-chaining never walks the `r1`/`r2`/`r3`
chain. For the biconditional under goal `(show (iff a b))` with only `(implies b a)`
available, the original posts 3 `show`s and runs 5 rules; the lazy version posts 2 and
runs 4, and never posts `(show (implies b a))`.

A good submission does not have to report numbers, but a student who claims a saving
without one should at least be able to say *which* assertion is no longer posted.

### 3.5 Acceptable variations

- **Adding a `(unless (fetch ...) ...)` guard** around the body, mirroring the optimised
  back-chaining CE rule on p. 102. Harmless and arguably better; full credit.
- **Making both constituents lazy in sequence** for `and` — i.e. not posting `(show ?a)`
  either, and instead waiting for `?a` to turn up on its own. This is *wrong*: nothing
  would ever drive the proof of `?a`, so the rule becomes purely opportunistic. Call it
  out.
- **Handling n-ary conjunctions** (`(and . ?conjuncts)`) with a recursive chain of rules
  that each post the next `show`. Strictly beyond what was asked; award bonus only if it
  is correct and the binary case still works.
- **Choosing which constituent to pursue first** by some heuristic (e.g. whichever is
  already in the database). Fine, as long as exactly one is pursued initially.

### 3.6 Common wrong answers

| Symptom | Cause |
|---|---|
| Both `show`s still posted, just reordered | No actual saving; the student changed nothing semantically |
| `(when (fetch ?a) ...)` used to test whether `?a` is proven | A one-shot test at rule-run time. `?a` is usually proven *later*; this is exactly what rules, not `fetch`, are for. This is the single most common error |
| `(assert! `(show ,?b))` placed inside the *innermost* rule | That rule triggers on `?b`, so the `show` is posted only after `?b` is already proven — dead code |
| Innermost `(rule ?b ...)` dropped; `(and ,?a ,?b)` asserted directly in the `(rule ?a ...)` body | Asserts the conjunction without ever proving `?b`. **Unsound** — treat as a major error |
| Comma/backquote errors producing `(show ?b)` with a literal variable | Pollutes the database with a goal that unifies with everything |
| Biconditional version nests on `?a`/`?b` instead of `(implies ?a ?b)` | Wrong triggers — the iff rule works on implications, not the propositions |

### 3.7 Book erratum worth knowing while grading

Page 101 prints BICONDITIONAL ELIMINATION as:

```lisp
(rule (iff ?arg1 ?arg2)                        ;; as printed -- unsound
      (assert! ?arg1) (assert! ?arg2))
```

This asserts both sides of a biconditional as true, which does not follow. The FTRE
version in `fnd.lisp` has the correct form:

```lisp
(rule ((iff ?p ?q))
      (rassert! (implies ?p ?q))
      (rassert! (implies ?q ?p)))
```

If a student's biconditional tests behave strangely, check whether they copied the
printed version. **Do not deduct for following the book**, and give credit to anyone who
notices and fixes it.

---

## 4. Part 2b — the assumption, and how it can be violated

This is to be answered **in comments attached to the rules**, per the assignment.

### 4.1 Model answer

> **The assumption.** The lazy rules assume that the proof of the first constituent never
> depends — directly or indirectly — on interest having been expressed in the second. Put
> the other way: the rule set as a whole must treat `show` assertions as *pure control*.
> Expressing interest in B may cause the system to search, but it must not produce any
> ordinary fact that the proof of A needs.
>
> The original rules did not need this. By posting both `show`s up front they gave every
> rule keyed on either goal a chance to run, and anything one subgoal happened to derive
> was available to the other. The lazy version trades that away: it is faster, but it is
> **no longer complete** for rule sets where the assumption fails.
>
> **How it is violated.** `show` assertions live in the same database as data, and nothing
> in TRE stops a rule from triggering on a `show` and asserting ordinary facts. Any such
> rule breaks the chain: suppressing `(show B)` suppresses the lemma, A is never proven,
> the rule waiting on A never fires, `(show B)` is never posted, and the conjunction is
> lost even though both conjuncts were derivable.
>
> The clearest realistic instance is the assumption-making introduction rules. CONDITIONAL
> INTRODUCTION triggers on `(show (implies p q))` and *assumes* `p`; NOT INTRODUCTION and
> indirect proof trigger on `(show (not p))` and `(show p)` and assume the negation.
> Everything derived under such an assumption is real data. If proving A relies on a fact
> that only appears because the system went looking for B, the lazy rule never finds it.
> (Chapter 4's TRE cannot retract assumptions, so these rules arrive with FTRE's contexts
> in Chapter 5 — but that is where the published KM\* rule set actually lands, which is
> precisely why the assumption is about "the set of rules as a whole".)
>
> A second consequence: the lazy rules are **order-sensitive** in a way the originals were
> not. `(and A B)` and `(and B A)` are logically identical but now behave differently, and
> Section 4.5's claim that rule order does not affect results no longer holds for this
> rule. The system's answer depends on how the user happened to write the goal.

### 4.2 Verified demonstration

A minimal rule set where the original succeeds and the lazy version fails:

```lisp
(rule (show q) (assert! 'lemma) (assert! 'q))  ; interest in q produces DATA
(assert! '(implies lemma p))
(assert! '(show (and p q)))
```

| | Facts derived |
|---|---|
| **Original** | `(show p)`, `(show q)`, `lemma`, `p`, `q`, **`(and p q)`** |
| **Lazy** | `(show p)`, `(show lemma)` — and nothing else. **No `(and p q)`** |

And the asymmetry, same rule set:

| Goal | Lazy result |
|---|---|
| `(show (and p q))` | fails |
| `(show (and q p))` | succeeds |

### 4.3 A subtlety worth rewarding

Not every such dependency is fatal, because back-chaining on CE can *re-derive* the lost
interest. With goal `(show (and p (or x y)))`, fact `x`, and `(implies (or x y) p)`:

- Original: posts both `show`s, OR INTRODUCTION builds `(or x y)`, CE gives `p`, done.
- Lazy: posts `(show p)` only — but back-chaining on CE sees `(implies (or x y) p)` and
  posts `(show (or x y))` *by itself*. The proof goes through. **Both versions succeed.**

So the assumption is about the rule set *as a whole*, not about AND INTRODUCTION in
isolation: whether laziness is safe depends on whether some other rule independently
regenerates the suppressed interest. A student who notices this has understood the problem
better than one who only produces a counterexample. Treat it as bonus insight, not a
requirement.

### 4.4 Answers that earn partial credit

| Answer | Assessment |
|---|---|
| "Assumes the first conjunct will eventually be proven if it is provable" | Correct but shallow — true of the original too. Partial |
| "Assumes rules can run in any order / assumes order independence" | On the right track, and the asymmetry point is real, but it does not name the dependency. Partial |
| "Assumes proving A does not require showing B" with no mechanism | The right sentence without the reason. Most of the credit |
| "It's slower if the first conjunct is hard" | Addresses performance, not the assumption. Little credit |
| "Assumes the conjuncts are independent" | Ambiguous. Credit only if the surrounding text makes clear this means *proof* independence, not logical independence |
| Any answer that identifies rules triggering on `show` asserting data | Full credit |

---

## 5. Open item for the grader

`bps-hwk1-unit-test.lsp` is referenced by the assignment but was **not present in the
repository** when this sheet was prepared (the repo contained only `BPS-Searchable.pdf`).
Two things should be reconciled against it before grading begins:

1. **`multi-fetch`'s exact contract** — argument order, whether the TRE argument is
   optional, and the expected return shape (see §2.1 and §2.4).
2. **How the tests drive the ND rules** — whether they load a full `nd.lisp`, which
   surrounding KM\* rules they assume, and whether they inspect the database or a return
   value.

Everything else in this document is independent of that file.

---

## 6. How these solutions were verified

- BPS `tre` sources loaded unmodified: `tinter.lisp`, `data.lisp`, `rules.lisp`,
  `unify.lisp`; `treex1.lisp` run first as a smoke test (`ex1` derives `(mortal Turing)`).
- `multi-fetch`: 8 assertions covering single-pattern equivalence to `fetch`, two- and
  three-pattern joins, failure, unindexable patterns, a structured modus-ponens join, the
  empty pattern list, and a no-shared-variable cross product. All pass.
- Part 2a: 4 scenarios comparing original and lazy variants on correctness, order
  independence, and measured work (`tre-rules-run` and the number of `show` assertions).
  All pass.
- Part 2b: 3 scenarios — the failing dependency, the back-chaining rescue, and the
  conjunct-order asymmetry. All behave as described.
- Environment: SBCL 2.4.0, arm64 Darwin.
