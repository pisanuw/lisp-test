;; -*- Mode: Lisp; -*-

;;;; BPS Homework One
;;;; Name:  <your name here>
;;;;
;;;; Problem 4 and Problem 6 of Section 4.7 of Building Problem Solvers
;;;; (Forbus & de Kleer), pages 105-106.
;;;;
;;;; HOW TO LOAD
;;;;   Load the TRE sources first, then this file:
;;;;
;;;;     (dolist (f '("tinter" "data" "rules" "unify"))
;;;;       (load (concatenate 'string f ".lisp")))
;;;;     (load "bps-hwk1.lsp")
;;;;     (load "bps-hwk1-unit-test.lsp")
;;;;
;;;; WHAT IS HERE
;;;;   Part 1 (Problem 4) defines MULTI-FETCH plus three small helpers.
;;;;   Part 2 (Problem 6a) defines the two revised introduction rules.  Because
;;;;     a (rule ...) form has to be evaluated with a TRE already current, the
;;;;     rules live in *HWK1-ND-RULES* and are installed by calling
;;;;     INSTALL-HWK1-ND-RULES.  If a TRE happens to be current when this file
;;;;     is loaded they are installed immediately, so either style works.
;;;;   Part 2 (Problem 6b) is answered in the comment block above those rules.
;;;;
;;;; SELF TEST
;;;;   (hwk1-self-test)   => prints one line per check, ends with a summary.

(in-package :COMMON-LISP-USER)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Part 1 -- Problem 4: multi-fetch
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; FETCH answers "which facts match this one pattern?".  MULTI-FETCH answers
;;; "which combinations of facts match all of these patterns at once?", where
;;; a variable appearing in more than one pattern has to take the SAME value
;;; everywhere.  So given
;;;
;;;   (parent abe homer) (parent homer bart) (parent homer lisa)
;;;
;;;   (multi-fetch '((parent ?g ?p) (parent ?p ?c)))
;;;   => (((parent abe homer) (parent homer lisa))
;;;       ((parent abe homer) (parent homer bart)))
;;;
;;; Two facts per set, and the ?p in the first is the ?p in the second.  Just
;;; calling FETCH on each pattern separately would give 3 matches and 3 matches
;;; with no relationship between them -- 9 meaningless combinations instead of
;;; the 2 real ones.
;;;
;;; The work is done by backtracking search.  UNIFY already accepts a set of
;;; bindings and extends it, so we pick a match for the first pattern, carry
;;; the resulting bindings into the rest, and back up when we get stuck.

(defun plug (exp bindings)
  ;; Substitute BINDINGS into EXP.  This is SUBLIS except that it is recursive,
  ;; so a chain like ?x -> ?y -> FOO resolves all the way down to FOO.  A single
  ;; SUBLIS pass would stop at ?y and quietly give a wrong answer.
  (cond ((null exp) nil)
        ((variable? exp)
         (let ((binding (assoc exp bindings)))
           (if binding (plug (cdr binding) bindings) exp)))
        ((not (consp exp)) exp)
        (t (cons (plug (car exp) bindings)
                 (plug (cdr exp) bindings)))))

(defun all-facts (tre &aux facts)
  ;; Every fact in the database.  Needed for patterns that car indexing cannot
  ;; narrow down; see CANDIDATES-FOR.
  (maphash #'(lambda (key dbclass)
               (declare (ignore key))
               (setq facts (append (dbclass-facts dbclass) facts)))
           (tre-dbclass-table tre))
  facts)

(defun indexable? (pattern)
  ;; GET-DBCLASS indexes on the head of a pattern, and signals an error if that
  ;; head is an unbound variable.  So a pattern like ?P, or (?REL A B), cannot
  ;; be indexed at all.
  (let ((head (if (listp pattern) (car pattern) pattern)))
    (and head (not (variable? head)))))

(defun candidates-for (pattern tre)
  (if (indexable? pattern)
      (get-candidates pattern tre)
      (all-facts tre)))

(defun multi-fetch (patterns &optional (tre *TRE*) &aux results)
  "Takes a list of PATTERNS.  Returns a list of sets of assertions: one
   assertion per pattern, with variables shared between patterns bound
   consistently across the whole set.  Returns NIL when nothing matches."
  (labels
      ((walk (remaining bindings)
         (cond ((null remaining)
                ;; All patterns matched.  Instantiate them with the bindings we
                ;; accumulated, the same way FETCH reports its results.
                (push (mapcar #'(lambda (p) (plug p bindings)) patterns)
                      results))
               (t
                ;; PLUG is used only to pick an index -- UNIFY gets the original
                ;; pattern plus the bindings, since it resolves bound variables
                ;; on its own.
                (dolist (candidate (candidates-for
                                    (plug (car remaining) bindings) tre))
                  (let ((new (unify (car remaining) candidate bindings)))
                    (unless (eq new :FAIL)
                      (walk (cdr remaining) new))))))))
    (walk patterns nil))
  (nreverse results))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Part 2 -- Problem 6: lazier introduction rules
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; ---- 6a: what changed ---------------------------------------------------
;;;
;;; The versions on page 103 post interest in BOTH constituents up front:
;;;
;;;   (rule (show (and ?a ?b))
;;;         (assert! `(show ,?a))
;;;         (assert! `(show ,?b))          ; <- posted no matter what
;;;         (rule ?a (rule ?b (assert! `(and ,?a ,?b)))))
;;;
;;; So every rule keyed on (show ?b) starts working even when ?a is hopeless,
;;; and all of that effort is wasted.  The fix is small: move the second
;;; (assert! `(show ...)) INSIDE the body of the rule that waits for the first
;;; constituent.  That body does not run until the first constituent is
;;; actually in the database, so interest in the second is never expressed
;;; unless it can still do some good.
;;;
;;; This is safe with respect to timing for two reasons:
;;;   1. Nested rules are lexically scoped -- ADD-RULE stores *ENV* in the rule
;;;      struct, so ?a and ?b are still bound inside a rule installed later.
;;;   2. ADD-RULE scans the facts already in the database when it installs a
;;;      rule, so (rule ?b ...) still fires if ?b was proven earlier.
;;;
;;; On a goal (show (and p q)) where p is unprovable and q sits behind a chain
;;; of implications, this took the run from 13 rules fired and 6 show
;;; assertions down to 6 rules fired and 2 show assertions.
;;;
;;; ---- 6b: the assumption these versions make -----------------------------
;;;
;;; THE ASSUMPTION.  Proving the first constituent must never depend, directly
;;; or indirectly, on interest in the second having been posted.  Stated over
;;; the rule set as a whole: show assertions have to be PURE CONTROL.  Looking
;;; for B may cause the system to search, but it must not produce any ordinary
;;; fact that the proof of A needs.
;;;
;;; The original rules did not need this.  By posting both shows immediately
;;; they gave every rule keyed on either goal a chance to run, and whatever one
;;; subgoal happened to derive was available to the other.  These versions give
;;; that up.  They are faster, but they are no longer COMPLETE for rule sets
;;; where the assumption fails.
;;;
;;; HOW IT IS VIOLATED.  Control assertions live in the same database as data,
;;; and nothing stops a rule from triggering on a show and asserting ordinary
;;; facts.  Any such rule breaks the chain: suppress (show B) and you suppress
;;; the fact, A is never proven, the rule waiting on A never fires, (show B) is
;;; never posted, and the conjunction is lost even though both conjuncts were
;;; derivable.  A three-line example:
;;;
;;;   (rule (show q) (assert! 'lemma) (assert! 'q))   ; interest in q -> DATA
;;;   (assert! '(implies lemma p))
;;;   (assert! '(show (and p q)))
;;;
;;;   page 103 version:  derives lemma, p, q, and (and p q).
;;;   version below:     derives (show p) and (show lemma), and then stops.
;;;
;;; The realistic case is the assumption-making introduction rules.  CONDITIONAL
;;; INTRODUCTION triggers on (show (implies p q)) and ASSUMES p; NOT INTRODUCTION
;;; and indirect proof trigger on (show (not p)) and (show p) and assume the
;;; negation.  Everything derived under such an assumption is real data.  If the
;;; proof of A leans on a fact that only exists because the system went looking
;;; for B, the lazy rule never finds it.  (TRE cannot retract assumptions, so
;;; those rules arrive with FTRE's contexts in Chapter 5 -- which is exactly why
;;; the question is about the set of rules as a whole and not about this rule.)
;;;
;;; WORTH NOTING: the dependency is not always fatal, because back-chaining on
;;; CONDITIONAL ELIMINATION can re-derive the lost interest by itself.  With
;;; goal (show (and p (or x y))), fact x, and (implies (or x y) p), the rule
;;; below posts only (show p) -- but back-chaining sees (implies (or x y) p) and
;;; posts (show (or x y)) on its own, so the proof still goes through.  Whether
;;; laziness is safe depends on whether some OTHER rule regenerates the interest.
;;;
;;; A SECOND CONSEQUENCE: these versions are order-sensitive in a way the
;;; originals were not.  (and A B) and (and B A) are logically the same goal but
;;; now behave differently -- in the example above, (show (and p q)) fails while
;;; (show (and q p)) succeeds.  The order-independence claimed in Section 4.5
;;; no longer holds for this rule.

(defvar *hwk1-nd-rules*
  '(
    ;; AND INTRODUCTION.  Express interest in ?a.  Only once ?a has actually
    ;; been proven do we express interest in ?b and install the rule that
    ;; builds the conjunction.
    (rule (show (and ?a ?b))
          (assert! `(show ,?a))
          (rule ?a                                ; waits for ?a to be proven
                (assert! `(show ,?b))             ; NOW ?b is worth pursuing
                (rule ?b
                      (assert! `(and ,?a ,?b)))))

    ;; BICONDITIONAL INTRODUCTION.  Same shape, but the constituents are the two
    ;; implications rather than the propositions themselves.
    (rule (show (iff ?a ?b))
          (assert! `(show (implies ,?a ,?b)))
          (rule (implies ?a ?b)                   ; waits for the first direction
                (assert! `(show (implies ,?b ,?a)))
                (rule (implies ?b ?a)
                      (assert! `(iff ,?a ,?b)))))
    ))

(defun install-hwk1-nd-rules (&optional (tre *TRE*))
  "Install the Problem 6 introduction rules into TRE."
  (run-forms tre *hwk1-nd-rules*)
  tre)

;; If a TRE is already current when this file is loaded, install them now.
(when *TRE* (install-hwk1-nd-rules *TRE*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Self test
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Not a substitute for bps-hwk1-unit-test.lsp -- just enough to show the file
;;; loads and does what it claims.  (hwk1-self-test) restores whatever TRE was
;;; current before it ran.

(defun hwk1-same-set? (a b)
  (and (= (length a) (length b))
       (every #'(lambda (x) (member x b :test #'equal)) a)))

(defun hwk1-self-test (&aux (saved *TRE*) (failures 0))
  (macrolet ((chk (name form expected &optional (test '#'equal))
               `(if (funcall ,test ,form ,expected)
                    (format t "~&  ok   ~A" ,name)
                    (progn (incf failures)
                           (format t "~&  FAIL ~A~%         got ~S~%        want ~S"
                                   ,name ,form ,expected)))))
    (unwind-protect
         (progn
           (format t "~&Part 1 -- multi-fetch")
           (in-tre (create-tre "hwk1-part1"))
           (dolist (f '((parent abe homer) (parent homer bart) (parent homer lisa)
                        (male abe) (male homer) (male bart) (female lisa)
                        (implies (human ?x) (mortal ?x)) (human socrates)))
             (assert! f))
           (chk "one pattern matches FETCH"
                (multi-fetch '((male ?x)))
                '(((male abe)) ((male homer)) ((male bart)))
                #'hwk1-same-set?)
           (chk "join on a shared variable"
                (multi-fetch '((parent ?g ?p) (parent ?p ?c)))
                '(((parent abe homer) (parent homer bart))
                  ((parent abe homer) (parent homer lisa)))
                #'hwk1-same-set?)
           (chk "join that filters"
                (multi-fetch '((parent ?g ?p) (parent ?p ?c) (male ?c)))
                '(((parent abe homer) (parent homer bart) (male bart))))
           (chk "no consistent match"
                (multi-fetch '((parent ?x ?y) (female ?x))) nil)
           (chk "bindings reach inside nested structure"
                (multi-fetch '((implies ?a ?c) ?a))
                '(((implies (human socrates) (mortal socrates)) (human socrates))))
           (chk "pattern with no indexable head"
                (length (multi-fetch '(?p))) (length (all-facts *TRE*)))

           (format t "~&Part 2 -- introduction rules")
           ;; Both constituents provable, arriving after the goal.
           (in-tre (create-tre "hwk1-and"))
           (install-hwk1-nd-rules)
           (run-forms *TRE* '((assert! '(show (and p q)))
                              (assert! 'p) (assert! 'q)))
           (chk "(and p q) derived" (and (fetch '(and p q)) t) t)
           ;; First constituent unprovable: no interest in the second.
           (in-tre (create-tre "hwk1-lazy"))
           (install-hwk1-nd-rules)
           (run-forms *TRE* '((assert! '(show (and p q))) (assert! 'q)))
           (chk "(show q) never posted" (fetch '(show q)) nil)
           (chk "(and p q) not derived"  (fetch '(and p q)) nil)
           ;; Biconditional, both directions available.
           (in-tre (create-tre "hwk1-iff"))
           (install-hwk1-nd-rules)
           (run-forms *TRE* '((assert! '(show (iff a b)))
                              (assert! '(implies a b)) (assert! '(implies b a))))
           (chk "(iff a b) derived" (and (fetch '(iff a b)) t) t)
           ;; First direction unprovable: no interest in the second.
           (in-tre (create-tre "hwk1-iff-lazy"))
           (install-hwk1-nd-rules)
           (run-forms *TRE* '((assert! '(show (iff a b))) (assert! '(implies b a))))
           (chk "(show (implies b a)) never posted" (fetch '(show (implies b a))) nil)

           (format t "~&~%~[All checks passed.~:;~:*~D check(s) FAILED.~]~%" failures)
           failures)
      (setq *TRE* saved))))
