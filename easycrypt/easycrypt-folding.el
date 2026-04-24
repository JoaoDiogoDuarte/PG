;;; easycrypt-folding.el --- Section folding for EasyCrypt mode -*- lexical-binding: t; -*-

;; --------------------------------------------------------------------
;; Distributed under the terms of the GPL-v3 license
;; --------------------------------------------------------------------

;;; Commentary:
;;
;; Provides `pg-ec-toggle-hiding' (bound to C-c w in `easycrypt-mode')
;; to fold/unfold the innermost well-formed `section ... end section'
;; block containing point.  Folds are shown with an inline ellipsis
;; marker and protect their contents from modification.

;;; Code:

(require 'cl-lib)

(defgroup pg-ec-folding nil
  "Section folding for Proof General EasyCrypt mode."
  :group 'easycrypt)

(defface pg-ec-folded-face
  '((t :inherit shadow :box t))
  "Face used for the ellipsis marker of folded EasyCrypt sections.")

(defconst pg-ec-section-header-re
  "^[ \t]*section\\(?:[ \t]+\\([A-Za-z_][A-Za-z0-9_']*\\)\\)?[ \t]*\\."
  "Regexp matching an EasyCrypt `section' header.")

(defconst pg-ec-section-footer-re
  "^[ \t]*end[ \t]+section\\(?:[ \t]+\\([A-Za-z_][A-Za-z0-9_']*\\)\\)?[ \t]*\\."
  "Regexp matching an EasyCrypt `end section' footer.")

(defun pg-ec--in-comment-or-string-p (&optional pos)
  "Return non-nil if POS (or point) is inside a comment or string."
  (save-excursion
    (goto-char (or pos (point)))
    (let ((ppss (syntax-ppss)))
      (or (nth 3 ppss) (nth 4 ppss)))))

(defun pg-ec--line-kind ()
  "Return (KIND . NAME) for the current line, or nil.
KIND is `header' or `footer'; NAME is the section name or nil."
  (save-excursion
    (beginning-of-line)
    (cond
     ((and (looking-at pg-ec-section-header-re)
           (not (pg-ec--in-comment-or-string-p (match-beginning 0))))
      (cons 'header (match-string-no-properties 1)))
     ((and (looking-at pg-ec-section-footer-re)
           (not (pg-ec--in-comment-or-string-p (match-beginning 0))))
      (cons 'footer (match-string-no-properties 1))))))

(defun pg-ec--collect-tokens (beg end)
  "Collect section header/footer tokens between BEG and END.
Each token is (KIND NAME LINE-START LINE-END HEADER-END)."
  (let (tokens)
    (save-excursion
      (goto-char beg)
      (while (re-search-forward
              (concat "\\(?:" pg-ec-section-header-re
                      "\\)\\|\\(?:" pg-ec-section-footer-re "\\)")
              end t)
        (let ((mb (match-beginning 0)))
          (unless (pg-ec--in-comment-or-string-p mb)
            (save-excursion
              (goto-char mb)
              (beginning-of-line)
              (cond
               ((looking-at pg-ec-section-header-re)
                (push (list 'header (match-string-no-properties 1)
                            (match-beginning 0)
                            (line-end-position)
                            (match-end 0))
                      tokens))
               ((looking-at pg-ec-section-footer-re)
                (push (list 'footer (match-string-no-properties 1)
                            (match-beginning 0)
                            (line-end-position)
                            (match-end 0))
                      tokens))))))))
    (nreverse tokens)))

(defun pg-ec--find-enclosing-section (pos)
  "Return (HEADER-TOKEN . FOOTER-TOKEN) for the innermost well-formed
section containing POS, or signal a descriptive error if the buffer
structure is malformed.  If POS is on a header/footer line, return that
exact section."
  (let* ((tokens (pg-ec--collect-tokens (point-min) (point-max)))
         (stack '())
         (pairs '())
         (on-line-kind (pg-ec--line-kind))
         (line-start (line-beginning-position))
         (line-end   (line-end-position)))
    (dolist (tok tokens)
      (pcase (car tok)
        ('header (push tok stack))
        ('footer
         (let ((open (car stack)))
           (unless open
             (error "Mismatched `end section' at line %d (no matching `section')"
                    (line-number-at-pos (nth 2 tok))))
           (let ((oname (nth 1 open))
                 (cname (nth 1 tok)))
             (when (and oname cname (not (string= oname cname)))
               (error "Section name mismatch: `%s' opened at line %d, closed with `%s' at line %d"
                      oname (line-number-at-pos (nth 2 open))
                      cname (line-number-at-pos (nth 2 tok))))
             (when (and oname (null cname))
               (error "Unnamed `end section' closes named section `%s' (line %d)"
                      oname (line-number-at-pos (nth 2 open))))
             (when (and (null oname) cname)
               (error "Named `end section %s' closes unnamed section (line %d)"
                      cname (line-number-at-pos (nth 2 tok))))
             (pop stack)
             (push (cons open tok) pairs))))))
    (when stack
      (let ((open (car stack)))
        (error "Unclosed `section%s' opened at line %d"
               (if (nth 1 open) (concat " " (nth 1 open)) "")
               (line-number-at-pos (nth 2 open)))))
    (cond
     ((eq (car on-line-kind) 'header)
      (or (cl-find-if (lambda (p) (= (nth 2 (car p)) line-start)) pairs)
          (error "No matching `end section' for header at point")))
     ((eq (car on-line-kind) 'footer)
      (or (cl-find-if (lambda (p) (and (>= (nth 2 (cdr p)) line-start)
                                       (<= (nth 2 (cdr p)) line-end)))
                      pairs)
          (error "No matching `section' for footer at point")))
     (t
      (let ((containing
             (cl-remove-if-not
              (lambda (p)
                (and (< (nth 4 (car p)) pos)
                     (> (nth 2 (cdr p)) pos)))
              pairs)))
        (unless containing
          (error "Point is not inside any section"))
        (car (last (sort containing
                         (lambda (a b)
                           (< (nth 2 (car a)) (nth 2 (car b))))))))))))

(defun pg-ec--folded-overlay-at (pos)
  "Return a pg-ec fold overlay covering POS, or nil."
  (cl-find-if (lambda (ov) (overlay-get ov 'pg-ec-fold))
              (overlays-at pos)))

(defun pg-ec--overlay-in-region (beg end)
  "Return a pg-ec fold overlay whose start lies in [BEG, END], or nil."
  (cl-find-if (lambda (ov) (overlay-get ov 'pg-ec-fold))
              (overlays-in beg end)))

(defun pg-ec--modification-guard (ov after-p _beg _end &optional _len)
  "Prevent edits inside a folded section overlay OV."
  (unless after-p
    (unless (overlay-get ov 'pg-ec-unfolding)
      (user-error "Cannot edit folded EasyCrypt section (use C-c w to unfold)"))))

(defun pg-ec--make-fold-overlay (beg end name)
  "Create a folding overlay from BEG to END for section NAME."
  (let ((ov (make-overlay beg end nil t nil)))
    (overlay-put ov 'pg-ec-fold t)
    (overlay-put ov 'pg-ec-name name)
    (overlay-put ov 'invisible 'pg-ec-fold)
    (overlay-put ov 'isearch-open-invisible
                 (lambda (o) (pg-ec--unfold-overlay o)))
    (overlay-put ov 'before-string
                 (propertize (format " [section%s folded ...] "
                                     (if name (concat " " name) ""))
                             'face 'pg-ec-folded-face))
    (overlay-put ov 'display
                 (propertize (format " [section%s folded ...]"
                                     (if name (concat " " name) ""))
                             'face 'pg-ec-folded-face))
    (overlay-put ov 'evaporate t)
    (overlay-put ov 'modification-hooks   '(pg-ec--modification-guard))
    (overlay-put ov 'insert-in-front-hooks '(pg-ec--modification-guard))
    (overlay-put ov 'insert-behind-hooks   '(pg-ec--modification-guard))
    (overlay-put ov 'help-echo
                 (format "Folded EasyCrypt section%s. C-c w to unfold."
                         (if name (concat " " name) "")))
    ov))

(defun pg-ec--unfold-overlay (ov)
  "Remove fold overlay OV."
  (overlay-put ov 'pg-ec-unfolding t)
  (delete-overlay ov))

(add-to-invisibility-spec '(pg-ec-fold . t))

;;;###autoload
(defun pg-ec-toggle-hiding ()
  "Toggle folding of the innermost EasyCrypt section at point.
If point is on a `section' header or `end section' footer, fold or
unfold that exact section.  Otherwise operate on the innermost
well-formed section containing point.  Signals a user-visible error if
the buffer's section structure is malformed."
  (interactive)
  (let ((existing (or (pg-ec--folded-overlay-at (point))
                      (pg-ec--folded-overlay-at (line-end-position))
                      (pg-ec--folded-overlay-at (line-beginning-position)))))
    (if existing
        (progn
          (pg-ec--unfold-overlay existing)
          (message "EasyCrypt section unfolded"))
      (condition-case err
          (let* ((pair   (pg-ec--find-enclosing-section (point)))
                 (header (car pair))
                 (footer (cdr pair))
                 (name   (nth 1 header))
                 (beg    (nth 4 header))
                 (end    (nth 3 footer))
                 (dup    (pg-ec--overlay-in-region beg end)))
            (if dup
                (progn
                  (pg-ec--unfold-overlay dup)
                  (message "EasyCrypt section unfolded"))
              (pg-ec--make-fold-overlay beg end name)
              (goto-char (nth 2 header))
              (message "EasyCrypt section%s folded"
                       (if name (concat " " name) ""))))
        (error
         (user-error "pg-ec-toggle-hiding: %s" (error-message-string err)))))))

(with-eval-after-load 'easycrypt
  (when (boundp 'easycrypt-mode-map)
    (define-key easycrypt-mode-map (kbd "C-c w") #'pg-ec-toggle-hiding)))

(provide 'easycrypt-folding)

;;; easycrypt-folding.el ends here
