;;; easycrypt-folding.el --- Structural folding for EasyCrypt mode -*- lexical-binding: t; -*-

;; --------------------------------------------------------------------
;; Distributed under the terms of the GPL-v3 license
;; --------------------------------------------------------------------

;;; Commentary:
;;
;; Provides `pg-ec-toggle-hiding' (bound to C-c w in `easycrypt-mode')
;; to fold/unfold the innermost syntactic region containing point.
;;
;; Foldable regions follow EasyCrypt's parser grammar (not heuristics):
;;
;;   * theories   : `theory Name. ... end Name.'
;;   * sections   : `section [Name]. ... end section [Name].'
;;   * proofs     : `{lemma|equiv|hoare|ehoare|phoare} ... {qed|admitted|abort}.'
;;                  (or a single `.'-terminated statement if it contains `by')
;;   * axioms     : `axiom ... .'
;;   * ops/consts : `{op|const} ... .' (including `with' cases)
;;   * clones     : `clone [import|export|include|abstract] ... .'
;;   * comments   : `(* ... *)' (outermost only; nested comments are
;;                  enclosed by their outer fold)
;;
;; Regions are syntactically well-nested; malformed/mismatched theory
;; and section blocks are dropped from the fold set (the scanner is
;; best-effort so unrelated constructs still fold).  Folded regions
;; show an inline ellipsis marker and are protected against edits.

;;; Code:

(require 'cl-lib)

(defgroup pg-ec-folding nil
  "Structural folding for Proof General EasyCrypt mode."
  :group 'easycrypt)

(defcustom pg-ec-folding-persist t
  "If non-nil, save and restore fold state per file across sessions."
  :type 'boolean :group 'pg-ec-folding)

(defcustom pg-ec-folding-omit-proofs t
  "If non-nil, send `admitted.' to EasyCrypt for proofs inside a fold."
  :type 'boolean :group 'pg-ec-folding)

(defface pg-ec-folded-face
  '((t :inherit shadow :box t))
  "Face for the ellipsis marker of folded EasyCrypt regions.")

;; --------------------------------------------------------------------
;; Regexes
;; --------------------------------------------------------------------

(defconst pg-ec--id "[A-Za-z_][A-Za-z0-9_']*")

(defconst pg-ec--re-theory-open
  (concat "^[ \t]*theory[ \t]+\\(" pg-ec--id "\\)[ \t]*\\."))

(defconst pg-ec--re-section-open
  (concat "^[ \t]*section\\(?:[ \t]+\\(" pg-ec--id "\\)\\)?[ \t]*\\."))

(defconst pg-ec--re-section-close
  (concat "^[ \t]*end[ \t]+section\\(?:[ \t]+\\(" pg-ec--id "\\)\\)?[ \t]*\\."))

(defconst pg-ec--re-theory-close
  (concat "^[ \t]*end[ \t]+\\(" pg-ec--id "\\)[ \t]*\\."))

(defconst pg-ec--re-proof-start
  "\\_<\\(lemma\\|equiv\\|hoare\\|ehoare\\|phoare\\)\\_>")

(defconst pg-ec--re-proof-end
  "\\_<\\(qed\\|admitted\\|abort\\)\\_>[ \t]*\\.")

(defconst pg-ec--re-decl-start
  "\\_<\\(axiom\\|op\\|const\\|clone\\|module\\)\\_>")

(defconst pg-ec--re-by "\\_<by\\_>")

(defconst pg-ec--re-comment-open "(\\*")

(defconst pg-ec--re-fold-any
  ;; Ordered: longer/prefix-sensitive alternatives first.
  (mapconcat
   (lambda (r) (concat "\\(?:" r "\\)"))
   (list pg-ec--re-comment-open
         pg-ec--re-section-close   ; `end section ...' before `end NAME.'
         pg-ec--re-theory-close
         pg-ec--re-section-open
         pg-ec--re-theory-open
         pg-ec--re-proof-end
         pg-ec--re-proof-start
         pg-ec--re-decl-start)
   "\\|"))

;; --------------------------------------------------------------------
;; Low-level helpers
;; --------------------------------------------------------------------

(defun pg-ec--in-comment-or-string-p (&optional pos)
  "Non-nil if POS (default: point) is inside a comment or string."
  (save-excursion
    (goto-char (or pos (point)))
    (let ((ppss (syntax-ppss)))
      (or (nth 3 ppss) (nth 4 ppss)))))

(defun pg-ec--skip-comment (pos)
  "If POS is at `(*', return position just after the matching `*)'.
Handles nested comments.  Returns nil if unterminated."
  (save-excursion
    (goto-char pos)
    (when (looking-at "(\\*")
      (let ((depth 1))
        (forward-char 2)
        (while (and (> depth 0)
                    (re-search-forward "(\\*\\|\\*)" nil t))
          (if (string= (match-string 0) "(*")
              (setq depth (1+ depth))
            (setq depth (1- depth))))
        (when (zerop depth) (point))))))

(defun pg-ec--terminator-dot-p (pos)
  "Non-nil if the character at POS is a `.' acting as a statement terminator.
Rejects `..' (range) and other `.' runs."
  (and (eq (char-after pos) ?.)
       (not (eq (char-before pos) ?.))
       (not (eq (char-after (1+ pos)) ?.))
       (let ((after (char-after (1+ pos))))
         (or (null after) (memq after '(?\s ?\t ?\n ?\r))))))

(defun pg-ec--find-statement-end (start)
  "Return the position just after the `.' terminating the statement at START.
Skips comments, strings, and balanced brace/paren/bracket groups.
Returns nil if no terminator is found."
  (save-excursion
    (goto-char start)
    (let ((found nil) (paren 0) (brack 0) (brace 0))
      (while (and (not found) (not (eobp)))
        (let ((c (char-after)))
          (cond
           ((and (eq c ?\() (eq (char-after (1+ (point))) ?*))
            (let ((e (pg-ec--skip-comment (point))))
              (if e (goto-char e) (goto-char (point-max)))))
           ((eq c ?\")
            (forward-char 1)
            (while (and (not (eobp)) (not (eq (char-after) ?\")))
              (when (eq (char-after) ?\\) (forward-char 1))
              (forward-char 1))
            (when (eq (char-after) ?\") (forward-char 1)))
           ((eq c ?\() (setq paren (1+ paren)) (forward-char 1))
           ((eq c ?\)) (setq paren (max 0 (1- paren))) (forward-char 1))
           ((eq c ?\[) (setq brack (1+ brack)) (forward-char 1))
           ((eq c ?\]) (setq brack (max 0 (1- brack))) (forward-char 1))
           ((eq c ?\{) (setq brace (1+ brace)) (forward-char 1))
           ((eq c ?\}) (setq brace (max 0 (1- brace))) (forward-char 1))
           ((and (eq c ?.)
                 (= paren 0) (= brack 0) (= brace 0)
                 (pg-ec--terminator-dot-p (point)))
            (forward-char 1)
            (setq found (point)))
           (t (forward-char 1)))))
      found)))

(defun pg-ec--find-decl-body-start (start limit)
  "Return the position of the first top-level `:' or `=' between START
and LIMIT, skipping comments, strings, and balanced bracket groups.
Returns nil if none is found."
  (save-excursion
    (goto-char start)
    (let ((found nil) (paren 0) (brack 0) (brace 0))
      (while (and (not found) (< (point) limit))
        (let ((c (char-after)))
          (cond
           ((and (eq c ?\() (eq (char-after (1+ (point))) ?*))
            (let ((e (pg-ec--skip-comment (point))))
              (if e (goto-char e) (goto-char limit))))
           ((eq c ?\")
            (forward-char 1)
            (while (and (not (eobp)) (not (eq (char-after) ?\")))
              (when (eq (char-after) ?\\) (forward-char 1))
              (forward-char 1))
            (when (eq (char-after) ?\") (forward-char 1)))
           ((eq c ?\() (setq paren (1+ paren)) (forward-char 1))
           ((eq c ?\)) (setq paren (max 0 (1- paren))) (forward-char 1))
           ((eq c ?\[) (setq brack (1+ brack)) (forward-char 1))
           ((eq c ?\]) (setq brack (max 0 (1- brack))) (forward-char 1))
           ((eq c ?\{) (setq brace (1+ brace)) (forward-char 1))
           ((eq c ?\}) (setq brace (max 0 (1- brace))) (forward-char 1))
           ((and (memq c '(?: ?=))
                 (= paren 0) (= brack 0) (= brace 0))
            (cond
             ;; `<:' digraph (module-of-type): body starts AFTER it.
             ((and (eq c ?:) (eq (char-before) ?<))
              (forward-char 1)
              (setq found (point)))
             (t (setq found (point)))))
           (t (forward-char 1)))))
      found)))

(defun pg-ec--statement-contains-by-p (start end)
  "Non-nil if the statement in [START, END) contains a top-level `by' keyword."
  (save-excursion
    (goto-char start)
    (let ((hit nil))
      (while (and (not hit)
                  (re-search-forward pg-ec--re-by end t))
        (unless (pg-ec--in-comment-or-string-p (match-beginning 0))
          (setq hit t)))
      hit)))

(defun pg-ec--find-proof-closer (from)
  "Return position after the next `qed|admitted|abort.' at/after FROM."
  (save-excursion
    (goto-char from)
    (let ((found nil))
      (while (and (not found)
                  (re-search-forward pg-ec--re-proof-end nil t))
        (unless (pg-ec--in-comment-or-string-p (match-beginning 0))
          (setq found (match-end 0))))
      found)))

;; --------------------------------------------------------------------
;; Region scanning
;; --------------------------------------------------------------------
;;
;; A region is a plist: (:kind KIND :name NAME :beg BEG :header-end HE :end END)
;;   :kind    — one of theory, section, proof, axiom, op, const, clone, comment
;;   :beg     — start of the region (first char of keyword, or `(*')
;;   :header-end — end of the header line (fold overlay starts here)
;;   :end     — position just after the region's terminator
;;
;; The fold overlay covers [HEADER-END, END); the header line stays visible.

(defun pg-ec--region (kind name beg header-end end)
  (list :kind kind :name name :beg beg :header-end header-end :end end))

(defun pg-ec--r-kind  (r) (plist-get r :kind))
(defun pg-ec--r-name  (r) (plist-get r :name))
(defun pg-ec--r-beg   (r) (plist-get r :beg))
(defun pg-ec--r-hend  (r) (plist-get r :header-end))
(defun pg-ec--r-end   (r) (plist-get r :end))

(defun pg-ec--header-end-at (pos)
  "End of the line containing POS."
  (save-excursion (goto-char pos) (line-end-position)))

(defun pg-ec--close-block (stack kind match-pred mend)
  "Close a block on STACK whose entry satisfies MATCH-PRED.
Returns (NEW-STACK . MAYBE-REGION).  Skips mismatched same-kind
entries above the match (error recovery for malformed nesting)."
  (let ((idx (cl-position-if match-pred stack)))
    (if idx
        (let ((open (nth idx stack)))
          (cons (nthcdr (1+ idx) stack)
                (pg-ec--region kind (nth 1 open)
                               (nth 2 open) (nth 3 open) mend)))
      (cons stack nil))))

(defun pg-ec--scan-regions ()
  "Collect all foldable regions in the current buffer.
Returns a list of regions (see `pg-ec--region').  Malformed or
unmatched theory/section blocks are dropped individually; a
malformed block does not prevent surrounding well-formed blocks
from being registered."
  (let ((regions '())
        (sec-stack '())   ; items: (section NAME BEG HEADER-END)
        (thy-stack '()))  ; items: (theory  NAME BEG HEADER-END)
    (save-excursion
      (goto-char (point-min))
      (while (re-search-forward pg-ec--re-fold-any nil t)
        (let ((mb (match-beginning 0)))
          (goto-char mb)
          (cond
           ((looking-at pg-ec--re-comment-open)
            (let ((end (pg-ec--skip-comment mb)))
              (if end
                  (progn
                    (push (pg-ec--region 'comment nil mb
                                         (pg-ec--header-end-at mb) end)
                          regions)
                    (goto-char end))
                (goto-char (point-max)))))
           ((pg-ec--in-comment-or-string-p mb)
            (forward-char 1))
           ;; `end section [NAME].' — close innermost matching section.
           ((looking-at pg-ec--re-section-close)
            (let* ((cname (match-string-no-properties 1))
                   (mend  (match-end 0))
                   (res   (pg-ec--close-block
                           sec-stack 'section
                           (lambda (o)
                             (or (null (nth 1 o)) (null cname)
                                 (string= (nth 1 o) cname)))
                           mend)))
              (setq sec-stack (car res))
              (when (cdr res) (push (cdr res) regions))
              (goto-char mend)))
           ;; `section [NAME].' — open a section.
           ((looking-at pg-ec--re-section-open)
            (let ((name (match-string-no-properties 1))
                  (mend (match-end 0)))
              (push (list 'section name mb (pg-ec--header-end-at mb)) sec-stack)
              (goto-char mend)))
           ;; `end NAME.' — close innermost matching theory.
           ((looking-at pg-ec--re-theory-close)
            (let* ((cname (match-string-no-properties 1))
                   (mend  (match-end 0))
                   (res   (pg-ec--close-block
                           thy-stack 'theory
                           (lambda (o) (string= (nth 1 o) cname))
                           mend)))
              (setq thy-stack (car res))
              (when (cdr res) (push (cdr res) regions))
              (goto-char mend)))
           ;; `theory NAME.' — open a theory.
           ((looking-at pg-ec--re-theory-open)
            (let ((name (match-string-no-properties 1))
                  (mend (match-end 0)))
              (push (list 'theory name mb (pg-ec--header-end-at mb)) thy-stack)
              (goto-char mend)))
           ;; Proof closers outside any proof — ignore (consumed by proof scans).
           ((looking-at pg-ec--re-proof-end)
            (goto-char (match-end 0)))
           ;; Proof starters: lemma / equiv / hoare / ehoare / phoare.
           ((looking-at pg-ec--re-proof-start)
            (let* ((kw       (match-string-no-properties 1))
                   (kw-end   (match-end 0))
                   (pname    (save-excursion
                               (goto-char kw-end)
                               (when (looking-at
                                      (concat "[ \t]+\\(?:nosmt[ \t]+\\)?"
                                              "\\(" pg-ec--id "\\)"))
                                 (match-string-no-properties 1))))
                   (stmt-end (pg-ec--find-statement-end mb))
                   (fold-end (cond
                              ((null stmt-end) nil)
                              ((pg-ec--statement-contains-by-p mb stmt-end)
                               stmt-end)
                              (t (or (pg-ec--find-proof-closer stmt-end)
                                     stmt-end)))))
              (when fold-end
                (push (pg-ec--region (intern kw) pname
                                     mb (pg-ec--header-end-at mb) fold-end)
                      regions)
                (goto-char fold-end))
              (unless fold-end (forward-char 1))))
           ;; Leaf declarations: axiom / op / const / clone / module.
           ((looking-at pg-ec--re-decl-start)
            (let* ((kw (intern (match-string-no-properties 1)))
                   (stmt-end (pg-ec--find-statement-end mb)))
              (when stmt-end
                (let ((hend
                       (cond
                        ;; For op/const/module fold from the first
                        ;; top-level `:' or `=' so the signature stays
                        ;; visible (e.g. `op f (x : t) ' folded).
                        ((memq kw '(op const module))
                         (or (pg-ec--find-decl-body-start mb stmt-end)
                             (pg-ec--header-end-at mb)))
                        (t (pg-ec--header-end-at mb)))))
                  (push (pg-ec--region kw nil mb hend stmt-end) regions))
                (goto-char stmt-end))
              (unless stmt-end (forward-char 1))))
           (t (forward-char 1))))))
    (nreverse regions)))

;; --------------------------------------------------------------------
;; Finding the innermost region at point
;; --------------------------------------------------------------------

(defun pg-ec--region-contains-p (r pos)
  "Non-nil if region R encloses POS (including its header line)."
  (and (<= (pg-ec--r-beg r) pos) (< pos (pg-ec--r-end r))))

(defun pg-ec--region-size (r)
  (- (pg-ec--r-end r) (pg-ec--r-beg r)))

(defun pg-ec--innermost-region-at (pos regions)
  "Return the innermost REGION containing POS, or nil."
  (let ((candidates (cl-remove-if-not
                     (lambda (r) (pg-ec--region-contains-p r pos))
                     regions)))
    (when candidates
      (car (sort candidates
                 (lambda (a b)
                   (< (pg-ec--region-size a) (pg-ec--region-size b))))))))

(defun pg-ec--region-at-point-or-line (regions)
  "Find innermost region containing point, end-of-line, or beginning-of-line."
  (or (pg-ec--innermost-region-at (point) regions)
      (pg-ec--innermost-region-at (line-end-position) regions)
      (pg-ec--innermost-region-at (line-beginning-position) regions)))

;; --------------------------------------------------------------------
;; Overlays
;; --------------------------------------------------------------------

(defun pg-ec--folded-overlay-at (pos)
  (cl-find-if (lambda (ov) (overlay-get ov 'pg-ec-fold))
              (overlays-at pos)))

(defun pg-ec--fold-overlay-starting-at (beg)
  "Return a pg-ec fold overlay whose start is exactly BEG, or nil."
  (cl-find-if (lambda (ov)
                (and (overlay-get ov 'pg-ec-fold)
                     (= (overlay-start ov) beg)))
              (overlays-in beg (1+ beg))))

(defun pg-ec--modification-guard (ov after-p _beg _end &optional _len)
  (unless after-p
    (unless (overlay-get ov 'pg-ec-unfolding)
      (user-error "Cannot edit folded EasyCrypt region (use C-c w to unfold)"))))

(defun pg-ec--label (kind name)
  (let ((k (symbol-name kind)))
    (format "[%s%s folded ...]" k (if name (concat " " name) ""))))

(defun pg-ec--make-fold-overlay (beg end kind name)
  (let ((ov (make-overlay beg end nil t nil))
        (label (pg-ec--label kind name)))
    (overlay-put ov 'pg-ec-fold t)
    (overlay-put ov 'pg-ec-kind kind)
    (overlay-put ov 'pg-ec-name name)
    (overlay-put ov 'invisible 'pg-ec-fold)
    (overlay-put ov 'isearch-open-invisible
                 (lambda (o) (pg-ec--unfold-overlay o)))
    (overlay-put ov 'before-string
                 (propertize (concat " " label " ") 'face 'pg-ec-folded-face))
    (overlay-put ov 'display
                 (propertize (concat " " label) 'face 'pg-ec-folded-face))
    (overlay-put ov 'evaporate t)
    (overlay-put ov 'modification-hooks    '(pg-ec--modification-guard))
    (overlay-put ov 'insert-in-front-hooks '(pg-ec--modification-guard))
    (overlay-put ov 'insert-behind-hooks   '(pg-ec--modification-guard))
    (overlay-put ov 'help-echo
                 (format "Folded EasyCrypt %s. C-c w to unfold." label))
    (when (memq kind '(section theory))
      (add-hook 'after-change-functions #'pg-ec--after-change nil t))
    ov))

(defun pg-ec--unfold-overlay (ov)
  (overlay-put ov 'pg-ec-unfolding t)
  (delete-overlay ov))

(add-to-invisibility-spec '(pg-ec-fold . t))

;; --------------------------------------------------------------------
;; Header→footer name synchronisation for folded sections/theories
;; --------------------------------------------------------------------

(defun pg-ec--parse-open-line (header-end)
  "If the line ending at HEADER-END is a valid section/theory open,
return (KIND . NAME); otherwise nil."
  (save-excursion
    (goto-char header-end)
    (beginning-of-line)
    (cond
     ((looking-at pg-ec--re-section-open)
      (cons 'section (match-string-no-properties 1)))
     ((looking-at pg-ec--re-theory-open)
      (cons 'theory (match-string-no-properties 1))))))

(defun pg-ec--refresh-fold-labels (ov kind name)
  (let ((label (pg-ec--label kind name)))
    (overlay-put ov 'pg-ec-name name)
    (overlay-put ov 'before-string
                 (propertize (concat " " label " ") 'face 'pg-ec-folded-face))
    (overlay-put ov 'display
                 (propertize (concat " " label) 'face 'pg-ec-folded-face))
    (overlay-put ov 'help-echo
                 (format "Folded EasyCrypt %s. C-c w to unfold." label))))

(defun pg-ec--rewrite-closer (ov kind new-name)
  "Find the matching closer inside fold overlay OV and rewrite its name.
Returns non-nil on success."
  (let* ((ov-beg (overlay-start ov))
         (ov-end (overlay-end ov))
         (closer-re (if (eq kind 'section)
                        pg-ec--re-section-close
                      pg-ec--re-theory-close))
         (inhibit-modification-hooks t))
    (overlay-put ov 'pg-ec-unfolding t)
    (unwind-protect
        (save-excursion
          (goto-char ov-beg)
          (let ((found nil) (depth 0))
            ;; Walk to the matching closer at depth 0, accounting for nested
            ;; same-kind opens.
            (let ((open-re (if (eq kind 'section)
                               pg-ec--re-section-open
                             pg-ec--re-theory-open)))
              (while (and (not found)
                          (re-search-forward
                           (concat "\\(?:" closer-re "\\)\\|\\(?:" open-re "\\)")
                           ov-end t))
                (let ((mb (match-beginning 0)))
                  (unless (pg-ec--in-comment-or-string-p mb)
                    (save-excursion
                      (goto-char mb)
                      (cond
                       ((looking-at closer-re)
                        (if (zerop depth)
                            (setq found (cons (match-beginning 0)
                                              (match-end 0)))
                          (setq depth (1- depth))))
                       ((looking-at open-re)
                        (setq depth (1+ depth)))))))))
            (when found
              (let* ((cb (car found)) (ce (cdr found))
                     (replacement
                      (if (eq kind 'section)
                          (if new-name (format "end section %s." new-name)
                            "end section.")
                        (when new-name (format "end %s." new-name)))))
                (when replacement
                  (goto-char cb)
                  (delete-region cb ce)
                  (insert replacement)
                  t)))))
      (overlay-put ov 'pg-ec-unfolding nil))))

(defun pg-ec--sync-fold-name (ov)
  "If OV is a folded section/theory and its header name has changed,
update the overlay labels and rewrite the matching closer."
  (let* ((kind (overlay-get ov 'pg-ec-kind))
         (old  (overlay-get ov 'pg-ec-name))
         (parsed (pg-ec--parse-open-line (overlay-start ov))))
    (when (and parsed (eq (car parsed) kind))
      (let ((new (cdr parsed)))
        (unless (equal old new)
          ;; Theories must have a name; abandon sync if user cleared it.
          (unless (and (eq kind 'theory) (null new))
            (when (pg-ec--rewrite-closer ov kind new)
              (pg-ec--refresh-fold-labels ov kind new))))))))

(defun pg-ec--after-change (beg end _len)
  "Buffer-local hook that propagates header renames into folded closers."
  (dolist (ov (overlays-in (point-min) (point-max)))
    (when (and (overlay-get ov 'pg-ec-fold)
               (memq (overlay-get ov 'pg-ec-kind) '(section theory))
               (not (overlay-get ov 'pg-ec-unfolding)))
      (let* ((hdr-eol (overlay-start ov))
             (hdr-bol (save-excursion
                        (goto-char hdr-eol)
                        (line-beginning-position))))
        (when (and (<= beg hdr-eol) (>= end hdr-bol))
          (pg-ec--sync-fold-name ov))))))

;; --------------------------------------------------------------------
;; Command
;; --------------------------------------------------------------------

;;;###autoload
(defun pg-ec-toggle-hiding ()
  "Toggle folding of the innermost EasyCrypt region at point.
Foldable regions are theories, sections, proofs (lemma/equiv/hoare/
ehoare/phoare), axioms, ops, consts, clones, and comments.  A second
invocation anywhere on a folded region's header line unfolds it."
  (interactive)
  (let ((existing (or (pg-ec--folded-overlay-at (point))
                      (pg-ec--folded-overlay-at (line-end-position))
                      (pg-ec--folded-overlay-at (line-beginning-position)))))
    (if existing
        (progn
          (pg-ec--unfold-overlay existing)
          (message "EasyCrypt region unfolded"))
      (condition-case err
          (progn
            (let* ((regions (pg-ec--scan-regions))
                   (r (pg-ec--region-at-point-or-line regions)))
              (unless r
                (user-error "No foldable EasyCrypt region at point"))
              (let* ((ov-beg (pg-ec--r-hend r))
                     (ov-end (pg-ec--r-end r))
                     (dup (pg-ec--fold-overlay-starting-at ov-beg)))
                (if dup
                    (progn
                      (pg-ec--unfold-overlay dup)
                      (message "EasyCrypt region unfolded"))
                  (pg-ec--make-fold-overlay ov-beg ov-end
                                            (pg-ec--r-kind r)
                                            (pg-ec--r-name r))
                  (goto-char (pg-ec--r-beg r))
                  (message "EasyCrypt %s folded"
                           (pg-ec--label (pg-ec--r-kind r)
                                         (pg-ec--r-name r))))))
            (when pg-ec-folding-persist
              (pg-ec-folding-save-state)))
        (error
         (user-error "pg-ec-toggle-hiding: %s" (error-message-string err)))))))

;; --------------------------------------------------------------------
;; Persistence (sidecar state files)
;; --------------------------------------------------------------------

(defcustom pg-ec-folding-state-dir
  (expand-file-name "pg-ec-folding/" user-emacs-directory)
  "Directory holding per-file fold-state sidecar files."
  :type 'directory :group 'pg-ec-folding)

(defun pg-ec--state-file ()
  "Path to the sidecar state file for the current buffer, or nil."
  (when (and pg-ec-folding-persist buffer-file-name)
    (unless (file-directory-p pg-ec-folding-state-dir)
      (make-directory pg-ec-folding-state-dir t))
    (expand-file-name
     (concat (sha1 (expand-file-name buffer-file-name)) ".el")
     pg-ec-folding-state-dir)))

(defun pg-ec--collect-fold-lines ()
  "Return ((HEADER-LINE . END-LINE) ...) for current fold overlays."
  (let (result)
    (dolist (ov (overlays-in (point-min) (point-max)))
      (when (overlay-get ov 'pg-ec-fold)
        (push (cons (line-number-at-pos (overlay-start ov))
                    (line-number-at-pos (overlay-end ov)))
              result)))
    (nreverse result)))

(defun pg-ec-folding-save-state ()
  "Persist this buffer's fold state to its sidecar file."
  (let ((f (pg-ec--state-file)))
    (when f
      (let ((data (pg-ec--collect-fold-lines)))
        (cond
         (data
          (with-temp-file f
            (let ((print-length nil) (print-level nil))
              (prin1 data (current-buffer)))))
         ((file-exists-p f) (delete-file f)))))))

(defun pg-ec-folding-restore-state ()
  "Re-create fold overlays from this buffer's sidecar file."
  (let ((f (pg-ec--state-file)))
    (when (and f (file-exists-p f))
      (condition-case _err
          (let ((data (with-temp-buffer
                        (insert-file-contents f)
                        (read (current-buffer))))
                (regions (pg-ec--scan-regions)))
            (dolist (entry data)
              (let* ((hdr-line (car entry))
                     (r (cl-find-if
                         (lambda (r)
                           (= hdr-line
                              (line-number-at-pos (pg-ec--r-hend r))))
                         regions)))
                (when r
                  (let ((ov-beg (pg-ec--r-hend r))
                        (ov-end (pg-ec--r-end r)))
                    (unless (pg-ec--fold-overlay-starting-at ov-beg)
                      (pg-ec--make-fold-overlay ov-beg ov-end
                                                (pg-ec--r-kind r)
                                                (pg-ec--r-name r))))))))
        (error nil)))))

(defun pg-ec-folding--setup ()
  "Buffer-local setup: restore folds and register save hooks."
  (when pg-ec-folding-persist
    (pg-ec-folding-restore-state)
    (add-hook 'after-save-hook  #'pg-ec-folding-save-state nil t)
    (add-hook 'kill-buffer-hook #'pg-ec-folding-save-state nil t)
    ;; Also persist on Emacs exit so state survives even when buffers
    ;; aren't killed individually.
    (add-hook 'kill-emacs-hook  #'pg-ec-folding-save-state)))

;; --------------------------------------------------------------------
;; Send `admitted.' for folded proofs (selective omit-proofs)
;; --------------------------------------------------------------------
;;
;; Proof General's omit-proofs framework (proof-script.el:2190) already
;; rewrites a 'proof chunk's last span to `proof-script-proof-admit-
;; command'.  We hook `proof-script-omit-filter' so the chunk
;; classification depends on fold state: a 'proof chunk whose
;; `proof-start-span-end' lies inside a `pg-ec-fold' overlay stays a
;; 'proof chunk (and is therefore omitted); otherwise it is demoted to
;; 'no-proof, which makes the framework leave it untouched.
;;
;; This affects only easycrypt-mode buffers and is a no-op when nothing
;; is folded.

(defun pg-ec--position-in-fold-p (pos)
  "Non-nil if POS is covered by a `pg-ec-fold' overlay."
  (and (integer-or-marker-p pos)
       (cl-some (lambda (ov) (overlay-get ov 'pg-ec-fold))
                (overlays-at pos))))

(defun pg-ec--omit-filter-gate (chunks)
  "Demote `proof' chunks whose lemma is not inside a fold to `no-proof'.
Run as `:filter-return' advice on `proof-script-omit-filter'.
Active only in `easycrypt-mode' buffers when `pg-ec-folding-omit-proofs'
is non-nil."
  (if (and pg-ec-folding-omit-proofs
           (derived-mode-p 'easycrypt-mode))
      (mapcar
       (lambda (chunk)
         (cond
          ((eq (car chunk) 'proof)
           ;; chunk = ('proof cmds-rev start-span-start start-span-end)
           (let ((proof-start-end (nth 3 chunk)))
             (if (pg-ec--position-in-fold-p proof-start-end)
                 chunk
               (list 'no-proof (nth 1 chunk)))))
          (t chunk)))
       chunks)
    chunks))

(with-eval-after-load 'proof-script
  (advice-add 'proof-script-omit-filter
              :filter-return #'pg-ec--omit-filter-gate))

(defun pg-ec-folding--enable-omit ()
  "Buffer-local: keep `proof-omit-proofs-option' on so the gate runs."
  (when pg-ec-folding-omit-proofs
    (setq-local proof-omit-proofs-option t)))

;; --------------------------------------------------------------------
;; Mode integration
;; --------------------------------------------------------------------

;; --------------------------------------------------------------------
;; Diagnostics
;; --------------------------------------------------------------------

;;;###autoload
(defun pg-ec-folding-debug ()
  "Show current state of folding, persistence, and omit-proofs."
  (interactive)
  (let* ((folds (cl-remove-if-not (lambda (ov) (overlay-get ov 'pg-ec-fold))
                                  (overlays-in (point-min) (point-max))))
         (state-file (pg-ec--state-file))
         (have-state (and state-file (file-exists-p state-file)))
         (omit-on  (and (boundp 'proof-omit-proofs-option)
                        proof-omit-proofs-option))
         (omit-cfg (and (boundp 'proof-omit-proofs-configured)
                        proof-omit-proofs-configured))
         (advised  (advice-member-p #'pg-ec--omit-filter-gate
                                    'proof-script-omit-filter))
         (start-re (and (boundp 'proof-script-proof-start-regexp)
                        proof-script-proof-start-regexp))
         (end-re   (and (boundp 'proof-script-proof-end-regexp)
                        proof-script-proof-end-regexp))
         (admit    (and (boundp 'proof-script-proof-admit-command)
                        proof-script-proof-admit-command)))
    (with-output-to-temp-buffer "*pg-ec-folding-debug*"
      (princ (format "Buffer: %s\n" (or buffer-file-name "<no file>")))
      (princ (format "Major mode: %s\n" major-mode))
      (princ (format "Fold overlays: %d\n" (length folds)))
      (dolist (ov folds)
        (princ (format "  %-8s %-18s lines %d..%d\n"
                       (symbol-name (overlay-get ov 'pg-ec-kind))
                       (or (overlay-get ov 'pg-ec-name) "-")
                       (line-number-at-pos (overlay-start ov))
                       (line-number-at-pos (overlay-end ov)))))
      (princ "\n-- persistence --\n")
      (princ (format "pg-ec-folding-persist: %s\n" pg-ec-folding-persist))
      (princ (format "state-dir:  %s\n" pg-ec-folding-state-dir))
      (princ (format "state-file: %s\n" (or state-file "<none>")))
      (princ (format "exists:     %s\n" have-state))
      (when have-state
        (princ "contents:\n")
        (princ (with-temp-buffer
                 (insert-file-contents state-file) (buffer-string)))
        (princ "\n"))
      (princ "\n-- omit-proofs --\n")
      (princ (format "pg-ec-folding-omit-proofs:    %s\n"
                     pg-ec-folding-omit-proofs))
      (princ (format "proof-omit-proofs-option:     %s%s\n" omit-on
                     (if (local-variable-p 'proof-omit-proofs-option)
                         " (buffer-local)" "")))
      (princ (format "proof-omit-proofs-configured: %s\n" omit-cfg))
      (princ (format "filter advice installed:      %s\n" (and advised t)))
      (princ (format "proof-start regexp:           %s\n" start-re))
      (princ (format "proof-end regexp:             %s\n" end-re))
      (princ (format "admit command:                %s\n" admit))
      (when (and (eq major-mode 'easycrypt-mode) (not omit-cfg))
        (princ "\nWARNING: omit-proofs not configured. easycrypt.el may need reloading.\n"))
      (when (and (eq major-mode 'easycrypt-mode) omit-cfg (not omit-on))
        (princ "\nWARNING: omit-proofs configured but not enabled in this buffer.\n"))
      (when (and folds (not advised))
        (princ "\nWARNING: advice not installed; folded proofs won't be omitted.\n")))))

;;;###autoload
(defun pg-ec-folding-debug-omission ()
  "Per-proof report of whether the omit gate would skip the body."
  (interactive)
  (let ((regions (pg-ec--scan-regions))
        rows)
    (dolist (r regions)
      (when (memq (pg-ec--r-kind r)
                  '(lemma equiv hoare ehoare phoare realize))
        (let* ((stmt-end (pg-ec--find-statement-end (pg-ec--r-beg r)))
               (probe (or stmt-end (pg-ec--r-hend r)))
               (in-fold (pg-ec--position-in-fold-p probe))
               (covering
                (cl-remove-if-not
                 (lambda (ov) (overlay-get ov 'pg-ec-fold))
                 (overlays-at probe))))
          (push (list (line-number-at-pos (pg-ec--r-beg r))
                      (symbol-name (pg-ec--r-kind r))
                      (or (pg-ec--r-name r) "<anon>")
                      in-fold
                      (mapcar (lambda (ov)
                                (format "%s:%d-%d"
                                        (or (overlay-get ov 'pg-ec-name)
                                            (symbol-name
                                             (overlay-get ov 'pg-ec-kind)))
                                        (line-number-at-pos (overlay-start ov))
                                        (line-number-at-pos (overlay-end ov))))
                              covering))
                rows))))
    (with-output-to-temp-buffer "*pg-ec-omission*"
      (princ "Per-proof omission decisions (probe = end of lemma statement):\n\n")
      (princ (format "%-6s %-8s %-30s %-6s %s\n"
                     "line" "kind" "name" "omit?" "covering folds"))
      (dolist (row (nreverse rows))
        (princ (format "%-6d %-8s %-30s %-6s %s\n"
                       (nth 0 row) (nth 1 row) (nth 2 row)
                       (if (nth 3 row) "YES" "no")
                       (or (mapconcat #'identity (nth 4 row) ", ") "-")))))))

(with-eval-after-load 'easycrypt
  (when (boundp 'easycrypt-mode-map)
    (define-key easycrypt-mode-map (kbd "C-c w") #'pg-ec-toggle-hiding))
  (add-hook 'easycrypt-mode-hook #'pg-ec-folding--setup)
  (add-hook 'easycrypt-mode-hook #'pg-ec-folding--enable-omit))

(provide 'easycrypt-folding)

;;; easycrypt-folding.el ends here
