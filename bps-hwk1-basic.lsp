;;;; BPS Homework One
;;;; Name:  <your name here>
;;;; Problems 4 and 6 of Section 4.7, Building Problem Solvers.

(in-package :COMMON-LISP-USER)

;;;; Part 1 -- Problem 4

;;; Like sublis but recursive, so ?x -> ?y -> foo resolves all the way down.
(defun plug (exp bindings)
  (cond ((null exp) nil)
        ((variable? exp)
         (let ((b (assoc exp bindings)))
           (if b (plug (cdr b) bindings) exp)))
        ((not (consp exp)) exp)
        (t (cons (plug (car exp) bindings)
                 (plug (cdr exp) bindings)))))

(defun all-facts (tre)
  (let ((facts nil))
    (maphash #'(lambda (key dbclass)
                 (declare (ignore key))
                 (setq facts (append (dbclass-facts dbclass) facts)))
             (tre-dbclass-table tre))
    facts))

;;; Car indexing needs a head that is not a variable, otherwise check everything.
(defun candidates-for (pattern tre)
  (let ((head (if (listp pattern) (car pattern) pattern)))
    (if (and head (not (variable? head)))
        (get-candidates pattern tre)
        (all-facts tre))))

;;; Matches REMAINING one at a time, carrying the bindings along.
(defun multi-fetch-aux (patterns remaining bindings tre)
  (if (null remaining)
      (list (mapcar #'(lambda (p) (plug p bindings)) patterns))
      (let ((results nil))
        (dolist (candidate (candidates-for (plug (car remaining) bindings) tre))
          (let ((new (unify (car remaining) candidate bindings)))
            (unless (eq new :FAIL)
              (setq results
                    (append results
                            (multi-fetch-aux patterns (cdr remaining) new tre))))))
        results)))

;;; Returns a list of sets of assertions that match all of PATTERNS at once.
(defun multi-fetch (patterns &optional (tre *TRE*))
  (multi-fetch-aux patterns patterns nil tre))

;;;; Part 2 -- Problem 6

;;; 6a.  The versions on page 103 post a show for both constituents right away,
;;; so the system works on the second one even when the first cannot be proven.
;;; Moving that second (assert! `(show ...)) inside the rule that waits for the
;;; first constituent means it is only posted once the first one is proven.
;;;
;;; 6b.  These versions assume that proving the first constituent never depends
;;; on the show for the second constituent having been posted.  The old rules
;;; did not need that, because they posted both shows up front, so whatever one
;;; subgoal happened to derive was there for the other one to use.
;;;
;;; It is violated whenever some rule triggers on a show and asserts ordinary
;;; facts, since show assertions sit in the same database as data.  Suppress
;;; (show ?b) and that fact never appears, so ?a is never proven, so the rule
;;; waiting on ?a never runs and the conjunction is never built even though both
;;; conjuncts were derivable.  The assumption rules do exactly this: conditional
;;; introduction triggers on (show (implies ?p ?q)) and assumes ?p, and anything
;;; derived under that assumption is real data.

(defvar *hwk1-nd-rules*
  '((rule (show (and ?a ?b))
          (assert! `(show ,?a))
          (rule ?a
                (assert! `(show ,?b))
                (rule ?b
                      (assert! `(and ,?a ,?b)))))

    (rule (show (iff ?a ?b))
          (assert! `(show (implies ,?a ,?b)))
          (rule (implies ?a ?b)
                (assert! `(show (implies ,?b ,?a)))
                (rule (implies ?b ?a)
                      (assert! `(iff ,?a ,?b)))))))

(defun install-hwk1-nd-rules (&optional (tre *TRE*))
  (run-forms tre *hwk1-nd-rules*))

(when *TRE* (install-hwk1-nd-rules *TRE*))
