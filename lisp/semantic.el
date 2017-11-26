;;; semantic.el --- Semantic buffer evaluator. -*- lexical-binding: t; -*-

;; Copyright (C) 1999-2015 Free Software Foundation, Inc.

;; Author: Eric M. Ludlam <zappo@gnu.org>
;; Keywords: syntax tools
;; Version: 2.2

;; This file is part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; API for providing the semantic content of a buffer.
;;
;; The Semantic API provides an interface to a series of different parser
;; implementations.  Each parser outputs a parse tree in a similar format
;; designed to handle typical functional and object oriented languages.
;;
;; To enable Semantic, turn on `semantic-mode', a global minor mode
;; (M-x semantic-mode RET, or "Source Code Parsers" from the Tools
;; menu).  To enable it at startup, put (semantic-mode 1) in your init
;; file.

;;; Code:
(eval-and-compile
  (add-to-list 'load-path default-directory))
(require 'fw)
(require 'tag)
(require 'mode-local)

;; todo: migrate from original files
(defvar semantic-format-face-alist)
(defvar semantic-unmatched-syntax-cache)
(defvar semantic-parser-warnings)
(defvar semantic-unmatched-syntax-cache-check)
(defvar semantic-lex-block-streams)
(defvar semantic--completion-cache)
(defvar semantic-minimum-working-buffer-size)
(defvar semantic-working-type)
(defvar semantic--buffer-cache)
(defvar semantic-bovinate-nonterminal-check-obarray)
(defvar semantic-parse-tree-state)
(defvar semantic-parser-name)
(defvar semantic-edits-verbose-flag)
(defvar last-cond)
(defvar semantic--parse-table)
(defvar semantic-case-fold)
(defvar semantic-debug-mode-map)
(defvar semanticdb-current-table)
(defvar semanticdb-new-database-class)
(defvar semanticdb-out-of-buffer-create-table-fcn)
(defvar semanticdb-file-table-hash)
(defvar semanticdb-database-being-created)

(defclass semanticdb-abstract-table ()
  ((parent-db ;; :initarg :parent-db
    ;; Do not set an initarg, or you get circular writes to disk.
          :documentation "Database Object containing this table.")
   (major-mode :initarg :major-mode
           :initform nil
           :documentation "Major mode this table belongs to.
Sometimes it is important for a program to know if a given table has the
same major mode as the current buffer.")
   (tags :initarg :tags
     :accessor semanticdb-get-tags
     :printer semantic-tag-write-list-slot-value
     :documentation "The tags belonging to this table.")
   (db-refs :initform nil
        :documentation
        "List of `semanticdb-table' objects refering to this one.
These aren't saved, but are instead recalculated after load.
See the file semanticdb-ref.el for how this slot is used.")
   (index :type semanticdb-abstract-search-index
      :documentation "The search index.
Used by semanticdb-find to store additional information about
this table for searching purposes.

Note: This index will not be saved in a persistent file.")
   (cache :type list
      :initform nil
      :documentation "List of cache information for tools.
Any particular tool can cache data to a database at runtime
with `semanticdb-cache-get'.

Using a semanticdb cache does not save any information to a file,
so your cache will need to be recalculated at runtime.  Caches can be
referenced even when the file is not in a buffer.

Note: This index will not be saved in a persistent file.")
   )
  "A simple table for semantic tags.
This table is the root of tables, and contains the minimum needed
for a new table not associated with a buffer."
  :abstract t)

(defclass semantic-debug-frame ()
  (
   )
  "One frame representation.")

(defsubst semantic-edits-os (change)
  "For testing: Start of CHANGE, or smaller of (point) and (mark)."
  (if change (semantic-overlay-start change)
    (if (< (point) (mark)) (point) (mark))))

(defsubst semantic-edits-oe (change)
  "For testing: End of CHANGE, or larger of (point) and (mark)."
  (if change (semantic-overlay-end change)
    (if (> (point) (mark)) (point) (mark))))

(defsubst semantic-edits-flush-change (change)
  "Flush the CHANGE overlay."
  (condition-case nil
      (run-hook-with-args 'semantic-edits-delete-change-functions
              change)
    (error nil))
  (semantic-overlay-delete change))

(defun semantic-find-tag-parent-by-overlay (tag)
  "Find the parent of TAG by overlays.
Overlays are a fast way of finding this information for active buffers."
  (let ((tag (nreverse (semantic-find-tag-by-overlay
            (semantic-tag-start tag)))))
    ;; This is a lot like `semantic-current-tag-parent', but
    ;; it uses a position to do it's work.  Assumes two tags don't share
    ;; the same start unless they are siblings.
    (car (cdr tag))))

(defun semantic-edits-change-between-tags (change)
  "Return a cache list of tags surrounding CHANGE.
The returned list is the CONS cell in the master list pointing to
a tag just before CHANGE.  The CDR will have the tag just after CHANGE.
CHANGE cannot encompass or overlap a leaf tag.
If CHANGE is fully encompassed in a tag that has children, and
this change occurs between those children, this returns non-nil.
See `semantic-edits-change-leaf-tag' for details on parents."
  (let* ((start (semantic-edits-os change))
     (end (semantic-edits-oe change))
     (tags (nreverse
          (semantic-find-tag-by-overlay-in-region
           start end)))
     (list-to-search nil)
         (found nil))
    (if (not tags)
    (setq list-to-search semantic--buffer-cache)
      ;; A leaf is always first in this list
      (if (and (< (semantic-tag-start (car tags)) start)
           (> (semantic-tag-end (car tags)) end))
      ;; We are completely encompassed in a tag.
      (if (setq list-to-search
            (semantic-tag-components (car tags)))
          ;; Ok, we are completely encompassed within the first tag
          ;; entry, AND that tag has children.  This means that change
          ;; occurred outside of all children, but inside some tag
          ;; with children.
          (if (or (not (semantic-tag-with-position-p (car list-to-search)))
              (> start (semantic-tag-end
                (nth (1- (length list-to-search))
                     list-to-search)))
              (< end (semantic-tag-start (car list-to-search))))
          ;; We have modifications to the definition of this parent
          ;; and not between it's children.  Clear the search list.
          (setq list-to-search nil)))
    ;; Search list is nil.
      ))
    ;; If we have a search list, let's go.  Otherwise nothing.
    (while (and list-to-search (not found))
      (if (cdr list-to-search)
          ;; We end when the start of the CDR is after the end of our
          ;; asked change.
          (if (< (semantic-tag-start (cadr list-to-search)) end)
              (setq list-to-search (cdr list-to-search))
            (setq found t))
        (setq list-to-search nil)))
    ;; Return it.  If it is nil, there is a logic bug, and we need
    ;; to avoid this bit of logic anyway.
    list-to-search))

(defun semantic-parse-changes-failed (&rest args)
  "Signal that Semantic failed to parse.
That is, display a message by passing all ARGS to `format', then throw
a 'semantic-parse-changes-failed exception with value t."
  (when semantic-edits-verbose-flag
    (message "Semantic parse changes failed: %S"
         (apply 'format args)))
  (throw 'semantic-parse-changes-failed t))

(define-mode-local-override semantic-format-tag-name
  c-mode (tag &optional parent color)
  "Convert TAG to a string that is the print name for TAG.
Optional PARENT and COLOR are ignored."
  (let ((name (semantic-format-tag-name-default tag parent color))
    (fnptr (semantic-tag-get-attribute tag :function-pointer))
    )
    (if (not fnptr)
    name
      (concat "(*" name ")"))
    ))

(defvar semantic-debug-current-interface)

(defun semantic-create-bovine-debug-error-frame (condition)
  "Create an error frame for bovine debugger.
Argument CONDITION is the thrown error condition."
  (let ((frame (semantic-bovine-debug-error-frame "frame"
                          :condition condition)))
    (semantic-debug-set-frame semantic-debug-current-interface
                  frame)
    frame))

(defvar semantic-debug-user-command)
(defvar semanticdb-hooks)

(defun semantic-debug-break (frame)
  "Stop parsing now at FRAME.
FRAME is an object that represents the parser's view of the
current state of the world.
This function enters a recursive edit.  It returns
on an `exit-recursive-edit', or if someone uses one
of the `semantic-debug-mode' commands.
It returns the command specified.  Parsers need to take action
on different types of return values."
  (save-window-excursion
    ;; Set up displaying information
    (semantic-debug-mode t)
    (unwind-protect
    (progn
      (semantic-debug-frame-highlight frame)
      (semantic-debug-interface-layout semantic-debug-current-interface)
      (condition-case nil
          ;; Enter recursive edit... wait for user command.
          (recursive-edit)
        (error nil)))
      (semantic-debug-unhighlight semantic-debug-current-interface)
      (semantic-debug-mode nil))
    ;; Find the requested user state.  Do something.
    (let ((returnstate semantic-debug-user-command))
      (setq semantic-debug-user-command nil)
      returnstate)
    ))

(defun semantic-bovine-debug-create-frame (nonterm rule match collection
                           lextoken)
  "Create one bovine frame.
NONTERM is the name of a rule we are currently parsing.
RULE is the index into the list of rules in NONTERM.
MATCH is the index into the list of matches in RULE.
For example:
  this: that
      | other thing
      | here
      ;
The NONTERM is THIS.
The RULE is for \"thing\" is 1.
The MATCH for \"thing\" is 1.
COLLECTION is a list of `things' that have been matched so far.
LEXTOKEN, is a token returned by the lexer which is being matched."
  (let ((frame (semantic-bovine-debug-frame "frame"
                        :nonterm nonterm
                        :rule rule
                        :match match
                        :collection collection
                        :lextoken lextoken)))
    (semantic-debug-set-frame semantic-debug-current-interface
                  frame)
    frame))

(defmacro semantic-bovinate-nonterminal-db-nt ()
  "Return the current nonterminal symbol.
Part of the grammar source debugger.  Depends on the existing
environment of `semantic-bovinate-stream'."
  `(if nt-stack
       (car (aref (car nt-stack) 2))
     nonterminal))

(defun semantic-bovinate-nonterminal-check (stream nonterminal)
  "Check if STREAM not already parsed for NONTERMINAL.
If so abort because an infinite recursive parse is suspected."
  (or (vectorp semantic-bovinate-nonterminal-check-obarray)
      (setq semantic-bovinate-nonterminal-check-obarray
            (make-vector 13 nil)))
  (let* ((nt (symbol-name nonterminal))
         (vs (symbol-value
              (intern-soft
               nt semantic-bovinate-nonterminal-check-obarray))))
    (if (memq stream vs)
        ;; Always enter debugger to see the backtrace
        (let ((debug-on-signal t)
              (debug-on-error  t))
          (setq semantic-bovinate-nonterminal-check-obarray nil)
          (error "Infinite recursive parse suspected on %s" nt))
      (set (intern nt semantic-bovinate-nonterminal-check-obarray)
           (cons stream vs)))))

;;;###autoload
(defun semantic-find-tag-by-overlay-in-region (start end &optional buffer)
  "Find all tags which exist in whole or in part between START and END.
Uses overlays to determine position.
Optional BUFFER argument specifies the buffer to use."
  (save-excursion
    (if buffer (set-buffer buffer))
    (let ((ol (semantic-overlays-in start end))
      (ret nil))
      (while ol
    (let ((tmp (semantic-overlay-get (car ol) 'semantic)))
      (when (and tmp
             ;; See above about position
             (semantic-tag-p tmp))
        (setq ret (cons tmp ret))))
    (setq ol (cdr ol)))
      (sort ret (lambda (a b) (< (semantic-tag-start a)
                 (semantic-tag-start b)))))))

(defun semantic-find-tag-by-overlay (&optional positionormarker buffer)
  "Find all tags covering POSITIONORMARKER by using overlays.
If POSITIONORMARKER is nil, use the current point.
Optional BUFFER is used if POSITIONORMARKER is a number, otherwise the current
buffer is used.  This finds all tags covering the specified position
by checking for all overlays covering the current spot.  They are then sorted
from largest to smallest via the start location."
  (save-excursion
    (when positionormarker
      (if (markerp positionormarker)
      (set-buffer (marker-buffer positionormarker))
    (if (bufferp buffer)
        (set-buffer buffer))))
    (let ((ol (semantic-overlays-at (or positionormarker (point))))
      (ret nil))
      (while ol
    (let ((tmp (semantic-overlay-get (car ol) 'semantic)))
      (when (and tmp
             ;; We don't need with-position because no tag w/out
             ;; a position could exist in an overlay.
             (semantic-tag-p tmp))
        (setq ret (cons tmp ret))))
    (setq ol (cdr ol)))
      (sort ret (lambda (a b) (< (semantic-tag-start a)
                 (semantic-tag-start b)))))))

;;;###autoload
(defun semantic-bovinate-stream (stream &optional nonterminal)
  "Bovinate STREAM, starting at the first NONTERMINAL rule.
Use `bovine-toplevel' if NONTERMINAL is not provided.
This is the core routine for converting a stream into a table.
Return the list (STREAM SEMANTIC-STREAM) where STREAM are those
elements of STREAM that have not been used.  SEMANTIC-STREAM is the
list of semantic tokens found."
  (if (not nonterminal)
      (setq nonterminal 'bovine-toplevel))

  ;; Try to detect infinite recursive parse when doing a full reparse.
  (or semantic--buffer-cache
      (semantic-bovinate-nonterminal-check stream nonterminal))

  (let* ((table semantic--parse-table)
     (matchlist (cdr (assq nonterminal table)))
     (starting-stream stream)
     (nt-loop  t)         ;non-terminal loop condition
     nt-popup            ;non-nil if return from nt recursion
     nt-stack         ;non-terminal recursion stack
     s            ;Temp Stream Tracker
     lse              ;Local Semantic Element
     lte              ;Local matchlist element
     tev              ;Matchlist entry values from buffer
     val              ;Value found in buffer.
     cvl              ;collected values list.
     out              ;Output
     end              ;End of match
     result)
    (condition-case debug-condition
        (while nt-loop
          (catch 'push-non-terminal
            (setq nt-popup nil
                  end (semantic-lex-token-end (car stream)))
            (while (or nt-loop nt-popup)
              (setq nt-loop nil
                    out     nil)
              (while (or nt-popup matchlist)
                (if nt-popup
                    ;; End of a non-terminal recursion
                    (setq nt-popup nil)
                  ;; New matching process
                  (setq s   stream      ;init s from stream.
                        cvl nil     ;re-init the collected value list.
                        lte (car matchlist) ;Get the local matchlist entry.
                        )
                  (if (or (byte-code-function-p (car lte))
                          (listp (car lte)))
                      ;; In this case, we have an EMPTY match!  Make
                      ;; stuff up.
                      (setq cvl (list nil))))

                (while (and lte
                            (not (byte-code-function-p (car lte)))
                            (not (listp (car lte))))

                  ;; GRAMMAR SOURCE DEBUGGING!
                  (if (and (boundp 'semantic-debug-enabled)
               semantic-debug-enabled)
                      (let* ((db-nt   (semantic-bovinate-nonterminal-db-nt))
                             (db-ml   (cdr (assq db-nt table)))
                             (db-mlen (length db-ml))
                             (db-midx (- db-mlen (length matchlist)))
                             (db-tlen (length (nth db-midx db-ml)))
                             (db-tidx (- db-tlen (length lte)))
                 (frame (progn
                      (require 'semantic/bovine/debug)
                      (semantic-bovine-debug-create-frame
                       db-nt db-midx db-tidx cvl (car s))))
                 (cmd (semantic-debug-break frame))
                 )
                        (cond ((eq 'fail cmd) (setq lte '(trash 0 . 0)))
                  ((eq 'quit cmd) (signal 'quit "Abort"))
                  ((eq 'abort cmd) (error "Abort"))
                  ;; support more commands here.

                  )))
                  ;; END GRAMMAR SOURCE DEBUGGING!

                  (cond
                   ;; We have a nonterminal symbol.  Recurse inline.
                   ((setq nt-loop (assq (car lte) table))

                    (setq
                     ;; push state into the nt-stack
                     nt-stack (cons (vector matchlist cvl lte stream end
                                            )
                                    nt-stack)
                     ;; new non-terminal matchlist
                     matchlist   (cdr nt-loop)
                     ;; new non-terminal stream
                     stream      s)

                    (throw 'push-non-terminal t)

                    )
                   ;; Default case
                   (t
                    (setq lse (car s)   ;Get the local stream element
                          s   (cdr s))  ;update stream.
                    ;; Do the compare
                    (if (eq (car lte) (semantic-lex-token-class lse)) ;syntactic match
                        (let ((valdot (semantic-lex-token-bounds lse)))
                          (setq val (semantic-lex-token-text lse))
                          (setq lte (cdr lte))
                          (if (stringp (car lte))
                              (progn
                                (setq tev (car lte)
                                      lte (cdr lte))
                                (if (string-match tev val)
                                    (setq cvl (cons
                                               (if (memq (semantic-lex-token-class lse)
                                                         '(comment semantic-list))
                                                   valdot val)
                                               cvl)) ;append this value
                                  (setq lte nil cvl nil))) ;clear the entry (exit)
                            (setq cvl (cons
                                       (if (memq (semantic-lex-token-class lse)
                                                 '(comment semantic-list))
                                           valdot val) cvl))) ;append unchecked value.
                          (setq end (semantic-lex-token-end lse))
                          )
                      (setq lte nil cvl nil)) ;No more matches, exit
                    )))
                (if (not cvl)           ;lte=nil;  there was no match.
                    (setq matchlist (cdr matchlist)) ;Move to next matchlist entry
                  (let ((start (semantic-lex-token-start (car stream))))
                    (setq out (cond
                               ((car lte)
                                (funcall (car lte) ;call matchlist fn on values
                                         (nreverse cvl) start end))
                               ((and (= (length cvl) 1)
                                     (listp (car cvl))
                                     (not (numberp (car (car cvl)))))
                                (append (car cvl) (list start end)))
                               (t
                                ;;(append (nreverse cvl) (list start end))))
                                ;; MAYBE THE FOLLOWING NEEDS LESS CONS
                                ;; CELLS THAN THE ABOVE?
                                (nreverse (cons end (cons start cvl)))))
                          matchlist nil) ;;generate exit condition
                    (if (not end)
                        (setq out nil)))
                  ;; Nothing?
                  ))
              (setq result
                    (if (eq s starting-stream)
                        (list (cdr s) nil)
                      (list s out)))
              (if nt-stack
                  ;; pop previous state from the nt-stack
                  (let ((state (car nt-stack)))

                    (setq nt-popup    t
                          ;; pop actual parser state
                          matchlist   (aref state 0)
                          cvl         (aref state 1)
                          lte         (aref state 2)
                          stream      (aref state 3)
                          end         (aref state 4)
                          ;; update the stack
                          nt-stack    (cdr nt-stack))

                    (if out
                        (let ((len (length out))
                              (strip (nreverse (cdr (cdr (reverse out))))))
                          (setq end (nth (1- len) out) ;reset end to the end of exp
                                cvl (cons strip cvl) ;prepend value of exp
                                lte (cdr lte)) ;update the local table entry
                          )
                      ;; No value means that we need to terminate this
                      ;; match.
                      (setq lte nil cvl nil)) ;No match, exit
                    )))))
      (error
       ;; On error just move forward the stream of lexical tokens
       (setq result (list (cdr starting-stream) nil))
       (when (and (boundp 'semantic-debug-enabled)
          semantic-debug-enabled)
     (require 'semantic/bovine/debug)
     (let ((frame (semantic-create-bovine-debug-error-frame
               debug-condition)))
       (semantic-debug-break frame)))))
    result))

;; Make it the default parser
;;;###autoload
(defalias 'semantic-parse-stream-default 'semantic-bovinate-stream)

(defun semantic-edits-change-over-tags (change)
  "Return a cache list of tags surrounding a CHANGE encompassing tags.
CHANGE must not only include all overlapped tags (excepting possible
parent tags) in their entirety.  In this case, the change may be deleting
or moving whole tags.
The return value is a vector.
Cell 0 is a list of all tags completely encompassed in change.
Cell 1 is the cons cell into a master parser cache starting with
the cell which occurs BEFORE the first position of CHANGE.
Cell 2 is the parent of cell 1, or nil for the buffer cache.
This function returns nil if any tag covered by change is not
completely encompassed.
See `semantic-edits-change-leaf-tag' for details on parents."
  (let* ((start (semantic-edits-os change))
     (end (semantic-edits-oe change))
     (tags (nreverse
          (semantic-find-tag-by-overlay-in-region
           start end)))
     (parent nil)
     (overlapped-tags nil)
     inner-end
     (list-to-search nil))
    ;; By the time this is already called, we know that it is
    ;; not a leaf change, nor a between tag change.  That leaves
    ;; an overlap, and this condition.

    ;; A leaf is always first in this list.
    ;; Is the leaf encompassed in this change?
    (if (and tags
         (>= (semantic-tag-start (car tags)) start)
         (<= (semantic-tag-end (car tags)) end))
    (progn
      ;; We encompass one whole change.
      (setq overlapped-tags (list (car tags))
        inner-end (semantic-tag-end (car tags))
        tags (cdr tags))
      ;; Keep looping while tags are inside the change.
      (while (and tags
              (>= (semantic-tag-start (car tags)) start)
              (<= (semantic-tag-end (car tags)) end))

        ;; Check if this new all-encompassing tag is a parent
        ;; of that which went before.  Only check end because
        ;; we know that start is less than inner-start since
        ;; tags was sorted on that.
        (if (> (semantic-tag-end (car tags)) inner-end)
        ;; This is a parent.  Drop the children found
        ;; so far.
        (setq overlapped-tags (list (car tags))
              inner-end (semantic-tag-end (car tags)))
          ;; It is not a parent encompassing tag
          (setq overlapped-tags (cons (car tags)
                        overlapped-tags)))
        (setq tags (cdr tags)))
      (if (not tags)
          ;; There are no tags left, and all tags originally
          ;; found are encompassed by the change.  Setup our list
          ;; from the cache
          (setq list-to-search semantic--buffer-cache);; We have a tag outside the list.  Check for
        ;; We know we have a parent because it would
        ;; completely cover the change.  A tag can only
        ;; do that if it is a parent after we get here.
        (when (and tags
               (< (semantic-tag-start (car tags)) start)
               (> (semantic-tag-end (car tags)) end))
          ;; We have a parent.  Stuff in the search list.
          (setq parent (car tags)
            list-to-search (semantic-tag-components parent))
          ;; If the first of TAGS is a parent (see above)
          ;; then clear out the list.  All other tags in
          ;; here must therefore be parents of the car.
          (setq tags nil)
          ;; One last check,  If start is before the first
          ;; tag or after the last, we may have overlap into
          ;; the characters that make up the definition of
          ;; the tag we are parsing.
          (when (or (semantic-tag-with-position-p (car list-to-search))
            (< start (semantic-tag-start
                  (car list-to-search)))
            (> end (semantic-tag-end
                (nth (1- (length list-to-search))
                     list-to-search))))
        ;; We have a problem
        (setq list-to-search nil
              parent nil))))

      (when list-to-search

        ;; Ok, return the vector only if all TAGS are
        ;; confirmed as the lineage of `overlapped-tags'
        ;; which must have a value by now.

        ;; Loop over the search list to find the preceding CDR.
        ;; Fortunately, (car overlapped-tags) happens to be
        ;; the first tag positionally.
        (let ((tokstart (semantic-tag-start (car overlapped-tags))))
          (while (and list-to-search
              ;; Assume always (car (cdr list-to-search)).
              ;; A thrown error will be captured nicely, but
              ;; that case shouldn't happen.

              ;; We end when the start of the CDR is after the
              ;; end of our asked change.
              (cdr list-to-search)
              (< (semantic-tag-start (car (cdr list-to-search)))
                 tokstart)
              (setq list-to-search (cdr list-to-search)))))
        ;; Create the return vector
        (vector overlapped-tags
            list-to-search
            parent)
        ))
      nil)))

(defun semantic-edits-splice-insert (newtags parent cachelist)
  "Insert NEWTAGS into PARENT using CACHELIST.
PARENT could be nil, in which case CACHELIST is the buffer cache
which must be updated.
CACHELIST must be searched to find where NEWTAGS are to be inserted.
The positions of NEWTAGS must be synchronized with those in
CACHELIST for this to work.  Some routines pre-position CACHELIST at a
convenient location, so use that."
  (let* ((start (semantic-tag-start (car newtags)))
     (newtagendcell (nthcdr (1- (length newtags)) newtags))
     (end (semantic-tag-end (car newtagendcell)))
     )
    (if (> (semantic-tag-start (car cachelist)) start)
    ;; We are at the beginning.
    (let* ((pc (if parent
               (semantic-tag-components parent)
             semantic--buffer-cache))
           (nc (cons (car pc) (cdr pc)))  ; new cons cell.
           )
      ;; Splice the new cache cons cell onto the end of our list.
      (setcdr newtagendcell nc)
      ;; Set our list into parent.
      (setcar pc (car newtags))
      (setcdr pc (cdr newtags)))
      ;; We are at the end, or in the middle.  Find our match first.
      (while (and (cdr cachelist)
          (> end (semantic-tag-start (car (cdr cachelist)))))
    (setq cachelist (cdr cachelist)))
      ;; Now splice into the list!
      (setcdr newtagendcell (cdr cachelist))
      (setcdr cachelist newtags))))

(defun semantic-edits-splice-replace (oldtag newtag)
  "Replace OLDTAG with NEWTAG in the current cache.
Do this by recycling OLDTAG's first CONS cell.  This effectively
causes the new tag to completely replace the old one.
Make sure that all information in the overlay is transferred.
It is presumed that OLDTAG and NEWTAG are both cooked.
When this routine returns, OLDTAG is raw, and the data will be
lost if not transferred into NEWTAG."
  (let* ((oo (semantic-tag-overlay oldtag))
     (o (semantic-tag-overlay newtag))
     (oo-props (semantic-overlay-properties oo)))
    (while oo-props
      (semantic-overlay-put o (car oo-props) (car (cdr oo-props)))
      (setq oo-props (cdr (cdr oo-props))))
    ;; Free the old overlay(s)
    (semantic--tag-unlink-from-buffer oldtag)
    ;; Recover properties
    (semantic--tag-copy-properties oldtag newtag)
    ;; Splice into the main list.
    (setcdr oldtag (cdr newtag))
    (setcar oldtag (car newtag))
    ;; This important bit is because the CONS cell representing
    ;; OLDTAG is now pointing to NEWTAG, but the NEWTAG
    ;; cell is about to be abandoned.  Here we update our overlay
    ;; to point at the updated state of the world.
    (semantic-overlay-put o 'semantic oldtag)))

(defun semantic-edits-splice-remove (oldtags parent cachelist)
  "Remove OLDTAGS from PARENT's CACHELIST.
OLDTAGS are tags in the current buffer, preferably linked
together also in CACHELIST.
PARENT is the parent tag containing OLDTAGS.
CACHELIST should be the children from PARENT, but may be
pre-positioned to a convenient location."
  (let* ((first (car oldtags))
     (last (nth (1- (length oldtags)) oldtags))
     (chil (if parent
           (semantic-tag-components parent)
         semantic--buffer-cache))
     (cachestart cachelist)
     (cacheend nil)
     )
    ;; First in child list?
    (if (eq first (car chil))
    ;; First tags in the cache are being deleted.
    (progn
      (when semantic-edits-verbose-flag
        (message "To Remove First Tag: (%s)"
             (semantic-format-tag-name first)))
      ;; Find the last tag
      (setq cacheend chil)
      (while (and cacheend (not (eq last (car cacheend))))
        (setq cacheend (cdr cacheend)))
      ;; The spliceable part is after cacheend.. so move cacheend
      ;; one more tag.
      (setq cacheend (cdr cacheend))
      ;; Splice the found end tag into the cons cell
      ;; owned by the current top child.
      (setcar chil (car cacheend))
      (setcdr chil (cdr cacheend))
      (when (not cacheend)
        ;; No cacheend.. then the whole system is empty.
        ;; The best way to deal with that is to do a full
        ;; reparse
        (semantic-parse-changes-failed "Splice-remove failed.  Empty buffer?")
        ))
      (when semantic-edits-verbose-flag
    (message "To Remove Middle Tag: (%s)"
         (semantic-format-tag-name first))))
    ;; Find in the cache the preceding tag
    (while (and cachestart (not (eq first (car (cdr cachestart)))))
      (setq cachestart (cdr cachestart)))
    ;; Find the last tag
    (setq cacheend cachestart)
    (while (and cacheend (not (eq last (car cacheend))))
      (setq cacheend (cdr cacheend)))
    ;; Splice the end position into the start position.
    ;; If there is no start, then this whole section is probably
    ;; gone.
    (if cachestart
    (setcdr cachestart (cdr cacheend))
      (semantic-parse-changes-failed "Splice-remove failed."))

    ;; Remove old overlays of these deleted tags
    (while oldtags
      (semantic--tag-unlink-from-buffer (car oldtags))
      (setq oldtags (cdr oldtags)))))

(defun semantic-repeat-parse-whole-stream
  (stream nonterm &optional returnonerror)
  "Iteratively parse the entire stream STREAM starting with NONTERM.
Optional argument RETURNONERROR indicates that the parser should exit
with the current results on a parse error.
This function returns semantic tags without overlays."
  (let ((result nil)
        (case-fold-search semantic-case-fold)
        nontermsym tag)
    (while stream
      (setq nontermsym (semantic-parse-stream stream nonterm)
            tag (car (cdr nontermsym)))
      (if (not nontermsym)
          (error "Parse error @ %d" (car (cdr (car stream)))))
      (if (eq (car nontermsym) stream)
      (error "Parser error: Infinite loop?"))
      (if tag
          (if (car tag)
              (setq tag (mapcar
                         #'(lambda (tag)
                             ;; Set the 'reparse-symbol property to
                             ;; NONTERM unless it was already setup
                             ;; by a tag expander
                             (or (semantic--tag-get-property
                                  tag 'reparse-symbol)
                                 (semantic--tag-put-property
                                  tag 'reparse-symbol nonterm))
                             tag)
                         (semantic--tag-expand tag))
                    result (append result tag))
            ;; No error in this case, a purposeful nil means don't
            ;; store anything.
            )
        (if returnonerror
            (setq stream nil)
          ;; The current item in the stream didn't match, so add it to
          ;; the list of syntax items which didn't match.
          (setq semantic-unmatched-syntax-cache
                (cons (car stream) semantic-unmatched-syntax-cache))
          ))
      ;; Designated to ignore.
      (setq stream (car nontermsym))
      (if stream
      ;; Use Emacs's built-in progress reporter:
      (and (boundp 'semantic--progress-reporter)
           semantic--progress-reporter
           (eq semantic-working-type 'percent)
           (progress-reporter-update
        semantic--progress-reporter
        (/ (* 100 (semantic-lex-token-start (car stream)))
           (point-max))))))
    result))

(define-overloadable-function semantic-parse-stream (stream nonterminal)
  "Parse STREAM, starting at the first NONTERMINAL rule.
For bovine and wisent based parsers, STREAM is from the output of
`semantic-lex', and NONTERMINAL is a rule in the appropriate language
specific rules file.
The default parser table used for bovine or wisent based parsers is
`semantic--parse-table'.

Must return a list: (STREAM TAGS) where STREAM is the unused elements
from STREAM, and TAGS is the list of semantic tags found; usually only
one tag is returned with the exception of compound statements.")

(defun semantic-changes-in-region (start end &optional buffer)
  "Find change overlays which exist in whole or in part between START and END.
Optional argument BUFFER is the buffer to search for changes in."
  (save-excursion
    (if buffer (set-buffer buffer))
    (let ((ol (semantic-overlays-in (max start (point-min))
                    (min end (point-max))))
      (ret nil))
      (while ol
    (when (semantic-overlay-get (car ol) 'semantic-change)
      (setq ret (cons (car ol) ret)))
    (setq ol (cdr ol)))
      (sort ret #'(lambda (a b) (< (semantic-overlay-start a)
                   (semantic-overlay-start b)))))))

(defun semantic-edits-change-leaf-tag (change)
  "A leaf tag which completely encompasses CHANGE.
If change overlaps a tag, but is not encompassed in it, return nil.
Use `semantic-edits-change-overlap-leaf-tag'.
If CHANGE is completely encompassed in a tag, but overlaps sub-tags,
return nil."
  (let* ((start (semantic-edits-os change))
     (end (semantic-edits-oe change))
     (tags (nreverse
          (semantic-find-tag-by-overlay-in-region
           start end))))
    ;; A leaf is always first in this list
    (if (and tags
         (<= (semantic-tag-start (car tags)) start)
         (> (semantic-tag-end (car tags)) end))
    ;; Ok, we have a match.  If this tag has children,
    ;; we have to do more tests.
    (let ((chil (semantic-tag-components (car tags))))
      (if (not chil)
          ;; Simple leaf.
          (car tags)
        ;; For this type, we say that we encompass it if the
        ;; change occurs outside the range of the children.
        (if (or (not (semantic-tag-with-position-p (car chil)))
            (> start (semantic-tag-end (nth (1- (length chil)) chil)))
            (< end (semantic-tag-start (car chil))))
        ;; We have modifications to the definition of this parent
        ;; so we have to reparse the whole thing.
        (car tags)
          ;; We actually modified an area between some children.
          ;; This means we should return nil, as that case is
          ;; calculated by someone else.
          nil)))
      nil)))

(defun semantic-edits-incremental-parser-1 ()
  "Incrementally reparse the current buffer.
Return the list of tags that changed.
If the incremental parse fails, throw a 'semantic-parse-changes-failed
exception with value t, that can be caught to schedule a full reparse.
This function is for internal use by `semantic-edits-incremental-parser'."
  (let* ((changed-tags nil)
         (debug-on-quit t)            ; try to find this annoying bug!
         (changes (semantic-changes-in-region
                   (point-min) (point-max)))
         (tags nil)                   ;tags found at changes
         (newf-tags nil)              ;newfound tags in change
         (parse-start nil)              ;location to start parsing
         (parse-end nil)                ;location to end parsing
         (parent-tag nil)             ;parent of the cache list.
         (cache-list nil)               ;list of children within which
                    ;we incrementally reparse.
         (reparse-symbol nil)           ;The ruled we start at for reparse.
         (change-group nil)             ;changes grouped in this reparse
     (last-cond nil)        ;track the last case used.
                    ;query this when debugging to find
                    ;source of bugs.
         )
    (or changes
        ;; If we were called, and there are no changes, then we
        ;; don't know what to do.  Force a full reparse.
        (semantic-parse-changes-failed "Don't know what to do"))
    ;; Else, we have some changes.  Loop over them attempting to
    ;; patch things up.
    (while changes
      ;; Calculate the reparse boundary.
      ;; We want to take some set of changes, and group them
      ;; together into a small change group. One change forces
      ;; a reparse of a larger region (the size of some set of
      ;; tags it encompasses.)  It may contain several tags.
      ;; That region may have other changes in it (several small
      ;; changes in one function, for example.)
      ;; Optimize for the simple cases here, but try to handle
      ;; complex ones too.

      (while (and changes               ; we still have changes
                  (or (not parse-start)
                      ;; Below, if the change we are looking at
                      ;; is not the first change for this
                      ;; iteration, and it starts before the end
                      ;; of current parse region, then it is
                      ;; encompassed within the bounds of tags
                      ;; modified by the previous iteration's
                      ;; change.
                      (< (semantic-overlay-start (car changes))
                         parse-end)))

        ;; REMOVE LATER
        (if (eq (car changes) (car change-group))
            (semantic-parse-changes-failed
             "Possible infinite loop detected"))

        ;; Store this change in this change group.
        (setq change-group (cons (car changes) change-group))

        (cond
         ;; Is this is a new parse group?
         ((not parse-start)
      (setq last-cond "new group")
          (let (tmp)
            (cond

;;;; Are we encompassed all in one tag?
             ((setq tmp (semantic-edits-change-leaf-tag (car changes)))
          (setq last-cond "Encompassed in tag")
              (setq tags (list tmp)
                    parse-start (semantic-tag-start tmp)
                    parse-end (semantic-tag-end tmp)))

;;;; Did the change occur between some tags?
             ((setq cache-list (semantic-edits-change-between-tags
                                (car changes)))
          (setq last-cond "Between and not overlapping tags")
              ;; The CAR of cache-list is the tag just before
              ;; our change, but wasn't modified.  Hmmm.
              ;; Bound our reparse between these two tags
              (setq tags nil
                    parent-tag
                    (car (semantic-find-tag-by-overlay
                          parse-start)))
              (cond
               ;; A change at the beginning of the buffer.
           ;; Feb 06 -
           ;; IDed when the first cache-list tag is after
           ;; our change, meaning there is nothing before
           ;; the chnge.
               ((> (semantic-tag-start (car cache-list))
                   (semantic-overlay-end (car changes)))
        (setq last-cond "Beginning of buffer")
                (setq parse-start
                      ;; Don't worry about parents since
                      ;; there there would be an exact
                      ;; match in the tag list otherwise
                      ;; and the routine would fail.
                      (point-min)
                      parse-end
                      (semantic-tag-start (car cache-list))))
               ;; A change stuck on the first surrounding tag.
               ((= (semantic-tag-end (car cache-list))
                   (semantic-overlay-start (car changes)))
        (setq last-cond "Beginning of Tag")
                ;; Reparse that first tag.
                (setq parse-start
                      (semantic-tag-start (car cache-list))
                      parse-end
                      (semantic-overlay-end (car changes))
                      tags
                      (list (car cache-list))))
               ;; A change at the end of the buffer.
               ((not (car (cdr cache-list)))
        (setq last-cond "End of buffer")
                (setq parse-start (semantic-tag-end
                                   (car cache-list))
                      parse-end (point-max)))
               (t
        (setq last-cond "Default")
                (setq parse-start
                      (semantic-tag-end (car cache-list))
                      parse-end
                      (semantic-tag-start (car (cdr cache-list)))))))

;;;; Did the change completely overlap some number of tags?
             ((setq tmp (semantic-edits-change-over-tags
                         (car changes)))
          (setq last-cond "Overlap multiple tags")
              ;; Extract the information
              (setq tags (aref tmp 0)
                    cache-list (aref tmp 1)
                    parent-tag (aref tmp 2))
              ;; We can calculate parse begin/end by checking
              ;; out what is in TAGS.  The one near start is
              ;; always first.  Make sure the reparse includes
              ;; the `whitespace' around the snarfed tags.
              ;; Since cache-list is positioned properly, use it
              ;; to find that boundary.
              (if (eq (car tags) (car cache-list))
                  ;; Beginning of the buffer!
                  (let ((end-marker (nth (length tags)
                                         cache-list)))
                    (setq parse-start (point-min))
                    (if end-marker
                        (setq parse-end
                              (semantic-tag-start end-marker))
                      (setq parse-end (semantic-overlay-end
                                       (car changes)))))
                ;; Middle of the buffer.
                (setq parse-start
                      (semantic-tag-end (car cache-list)))
                ;; For the end, we need to scoot down some
                ;; number of tags.  We 1+ the length of tags
                ;; because we want to skip the first tag
                ;; (remove 1-) then want the tag after the end
                ;; of the list (1+)
                (let ((end-marker (nth (1+ (length tags)) cache-list)))
                  (if end-marker
                      (setq parse-end (semantic-tag-start end-marker))
                    ;; No marker.  It is the last tag in our
                    ;; list of tags.  Only possible if END
                    ;; already matches the end of that tag.
                    (setq parse-end
                          (semantic-overlay-end (car changes)))))))

;;;; Unhandled case.
             ;; Throw error, and force full reparse.
             ((semantic-parse-changes-failed "Unhandled change group")))
            ))
         ;; Is this change inside the previous parse group?
         ;; We already checked start.
         ((< (semantic-overlay-end (car changes)) parse-end)
      (setq last-cond "in bounds")
          nil)
         ;; This change extends the current parse group.
         ;; Find any new tags, and see how to append them.
         ((semantic-parse-changes-failed
       (setq last-cond "overlap boundary")
           "Unhandled secondary change overlapping boundary"))
         )
        ;; Prepare for the next iteration.
        (setq changes (cdr changes)))

      ;; By the time we get here, all TAGS are children of
      ;; some parent.  They should all have the same start symbol
      ;; since that is how the multi-tag parser works.  Grab
      ;; the reparse symbol from the first of the returned tags.
      ;;
      ;; Feb '06 - If reparse-symbol is nil, then they are top level
      ;;     tags.  (I'm guessing.)  Is this right?
      (setq reparse-symbol
            (semantic--tag-get-property (car (or tags cache-list))
                                        'reparse-symbol))
      ;; Find a parent if not provided.
      (and (not parent-tag) tags
           (setq parent-tag
                 (semantic-find-tag-parent-by-overlay
                  (car tags))))
      ;; We can do the same trick for our parent and resulting
      ;; cache list.
      (unless cache-list
    (if parent-tag
        (setq cache-list
          ;; We need to get all children in case we happen
          ;; to have a mix of positioned and non-positioned
          ;; children.
          (semantic-tag-components parent-tag))
      ;; Else, all the tags since there is no parent.
      ;; It sucks to have to use the full buffer cache in
      ;; this case because it can be big.  Failure to provide
      ;; however results in a crash.
      (setq cache-list semantic--buffer-cache)
      ))
      ;; Use the boundary to calculate the new tags found.
      (setq newf-tags (semantic-parse-region
             parse-start parse-end reparse-symbol))
      ;; Make sure all these tags are given overlays.
      ;; They have already been cooked by the parser and just
      ;; need the overlays.
      (let ((tmp newf-tags))
        (while tmp
          (semantic--tag-link-to-buffer (car tmp))
          (setq tmp (cdr tmp))))

      ;; See how this change lays out.
      (cond

;;;; Whitespace change
       ((and (not tags) (not newf-tags))
        ;; A change that occurred outside of any existing tags
        ;; and there are no new tags to replace it.
    (when semantic-edits-verbose-flag
      (message "White space changes"))
        nil
        )

;;;; New tags in old whitespace area.
       ((and (not tags) newf-tags)
        ;; A change occurred outside existing tags which added
        ;; a new tag.  We need to splice these tags back
        ;; into the cache at the right place.
        (semantic-edits-splice-insert newf-tags parent-tag cache-list)

        (setq changed-tags
              (append newf-tags changed-tags))

    (when semantic-edits-verbose-flag
      (message "Inserted tags: (%s)"
           (semantic-format-tag-name (car newf-tags))))
        )

;;;; Old tags removed
       ((and tags (not newf-tags))
        ;; A change occurred where pre-existing tags were
        ;; deleted!  Remove the tag from the cache.
        (semantic-edits-splice-remove tags parent-tag cache-list)

        (setq changed-tags
              (append tags changed-tags))

        (when semantic-edits-verbose-flag
      (message "Deleted tags: (%s)"
           (semantic-format-tag-name (car tags))))
        )

;;;; One tag was updated.
       ((and (= (length tags) 1) (= (length newf-tags) 1))
        ;; One old tag was modified, and it is replaced by
        ;; One newfound tag.  Splice the new tag into the
        ;; position of the old tag.
        ;; Do the splice.
        (semantic-edits-splice-replace (car tags) (car newf-tags))
        ;; Add this tag to our list of changed toksns
        (setq changed-tags (cons (car tags) changed-tags))
        ;; Debug
        (when semantic-edits-verbose-flag
      (message "Update Tag Table: %s"
           (semantic-format-tag-name (car tags) nil t)))
        ;; Flush change regardless of above if statement.
        )

;;;; Some unhandled case.
       ((semantic-parse-changes-failed "Don't know what to do")))

      ;; We got this far, and we didn't flag a full reparse.
      ;; Clear out this change group.
      (while change-group
        (semantic-edits-flush-change (car change-group))
        (setq change-group (cdr change-group)))

      ;; Don't increment change here because an earlier loop
      ;; created change-groups.
      (setq parse-start nil)
      )
    ;; Mark that we are done with this glop
    (semantic-parse-tree-set-up-to-date)
    ;; Return the list of tags that changed.  The caller will
    ;; use this information to call hooks which can fix themselves.
    changed-tags))

(defsubst semantic-edits-incremental-fail ()
  "When the incremental parser fails, we mark that we need a full reparse."
  ;;(debug)
  (semantic-parse-tree-set-needs-rebuild)
  (when semantic-edits-verbose-flag
    (message "Force full reparse (%s)"
         (buffer-name (current-buffer))))
  (run-hooks 'semantic-edits-incremental-reparse-failed-hook))

(defun semantic-clear-parser-warnings ()
  "Clear the current list of parser warnings for this buffer."
  (setq semantic-parser-warnings nil))

(defsubst semantic-parser-working-message (&optional arg)
  "Return the message string displayed while parsing.
If optional argument ARG is non-nil it is appended to the message
string."
  (concat "Parsing"
      (if arg (format " %s" arg))
      (if semantic-parser-name (format " (%s)" semantic-parser-name))
      "..."))

(define-overloadable-function semantic-parse-region
  (start end &optional nonterminal depth returnonerror)
  "Parse the area between START and END, and return any tags found.
If END needs to be extended due to a lexical token being too large, it
will be silently ignored.

Optional arguments:
NONTERMINAL is the rule to start parsing at.
DEPTH specifies the lexical depth to descend for parsers that use
lexical analysis as their first step.
RETURNONERROR specifies that parsing should stop on the first
unmatched syntax encountered.  When nil, parsing skips the syntax,
adding it to the unmatched syntax cache.

Must return a list of semantic tags which have been cooked
\(repositioned properly) but which DO NOT HAVE OVERLAYS associated
with them.  When overloading this function, use `semantic--tag-expand'
to cook raw tags.")

(defmacro semantic-parse-tree-needs-rebuild-p ()
  "Return non-nil if the current parse tree needs to be rebuilt."
  `(eq semantic-parse-tree-state 'needs-rebuild))

(define-overloadable-function semantic-parse-changes ()
  "Reparse changes in the current buffer.
The list of changes are tracked as a series of overlays in the buffer.
When overloading this function, use `semantic-changes-in-region' to
analyze.")

(defmacro semantic-parse-tree-needs-update-p ()
  "Return non-nil if the current parse tree needs to be updated."
  `(eq semantic-parse-tree-state 'needs-update))

(defmacro semantic-parse-tree-up-to-date-p ()
  "Return non-nil if the current parse tree is up to date."
  `(null semantic-parse-tree-state))

(defmacro semantic-parse-tree-unparseable-p ()
  "Return non-nil if the current buffer has been marked unparseable."
  `(eq semantic-parse-tree-state 'unparseable))

(defalias 'semantic-parse-changes-default
  'semantic-edits-incremental-parser)

(defun semantic-edits-incremental-parser ()
  "Incrementally reparse the current buffer.
Incremental parser allows semantic to only reparse those sections of
the buffer that have changed.  This function depends on
`semantic-edits-change-function-handle-changes' setting up change
overlays in the current buffer.  Those overlays are analyzed against
the semantic cache to see what needs to be changed."
  (let ((changed-tags
         ;; Don't use `semantic-safe' here to explicitly catch errors
         ;; and reset the parse tree.
         (catch 'semantic-parse-changes-failed
           (if debug-on-error
               (semantic-edits-incremental-parser-1)
             (condition-case err
                 (semantic-edits-incremental-parser-1)
               (error
                (message "incremental parser error: %S"
                         (error-message-string err))
                t))))))
    (when (eq changed-tags t)
      ;; Force a full reparse.
      (semantic-edits-incremental-fail)
      (setq changed-tags nil))
    changed-tags))

(defmacro semantic-parse-tree-set-up-to-date ()
  "Indicate that the current parse tree is up to date."
  `(setq semantic-parse-tree-state nil))

(defun semantic-clear-unmatched-syntax-cache ()
  "Clear the cache of unmatched syntax tokens."
  (setq semantic-unmatched-syntax-cache nil
        semantic-unmatched-syntax-cache-check t))

(defun semantic--set-buffer-cache (tagtable)
  "Set the toplevel tag cache to TAGTABLE."
  (setq semantic--buffer-cache tagtable
        semantic-unmatched-syntax-cache-check nil)
  ;; This is specific to the bovine parser.
  (set (make-local-variable 'semantic-bovinate-nonterminal-check-obarray)
       nil)
  (semantic-parse-tree-set-up-to-date)
  (semantic-make-local-hook 'after-change-functions)
  (add-hook 'after-change-functions 'semantic-change-function nil t)
  (run-hook-with-args 'semantic-after-toplevel-cache-change-hook
              semantic--buffer-cache)
  (setq semantic--completion-cache nil)
  ;; Refresh the display of unmatched syntax tokens if enabled
  (run-hook-with-args 'semantic-unmatched-syntax-hook
                      semantic-unmatched-syntax-cache)
  ;; Old Semantic 1.3 hook API.  Maybe useful forever?
  (run-hooks 'semantic-after-toplevel-bovinate-hook))

(defun semantic-fetch-tags ()
  "Fetch semantic tags from the current buffer.
If the buffer cache is up to date, return that.
If the buffer cache is out of date, attempt an incremental reparse.
If the buffer has not been parsed before, or if the incremental reparse
fails, then parse the entire buffer.
If a lexical error had been previously discovered and the buffer
was marked unparseable, then do nothing, and return the cache."
  (and
   ;; Is this a semantic enabled buffer?
   (semantic-active-p)
   ;; Application hooks say the buffer is safe for parsing
   (run-hook-with-args-until-failure
    'semantic-before-toplevel-bovination-hook)
   (run-hook-with-args-until-failure
    'semantic--before-fetch-tags-hook)
   ;; If the buffer was previously marked unparseable,
   ;; then don't waste our time.
   (not (semantic-parse-tree-unparseable-p))
   ;; The parse tree actually needs to be refreshed
   (not (semantic-parse-tree-up-to-date-p))
   ;; So do it!
   (let* ((gc-cons-threshold (max gc-cons-threshold 10000000))
          (semantic-lex-block-streams nil)
          (res nil))
     (garbage-collect)
     (cond

;;;; Try the incremental parser to do a fast update.
      ((semantic-parse-tree-needs-update-p)
       (setq res (semantic-parse-changes))
       (if (semantic-parse-tree-needs-rebuild-p)
           ;; If the partial reparse fails, jump to a full reparse.
           (semantic-fetch-tags)
         ;; Clear the cache of unmatched syntax tokens
         ;;
         ;; NOTE TO SELF:
         ;;
         ;; Move this into the incremental parser.  This is a bug.
         ;;
         (semantic-clear-unmatched-syntax-cache)
         (run-hook-with-args ;; Let hooks know the updated tags
          'semantic-after-partial-cache-change-hook res))
       (setq semantic--completion-cache nil))

;;;; Parse the whole system.
      ((semantic-parse-tree-needs-rebuild-p)
       ;; Use Emacs's built-in progress-reporter (only interactive).
       (if noninteractive
           (setq res (semantic-parse-region (point-min) (point-max)))
         (let ((semantic--progress-reporter
                (and (>= (point-max) semantic-minimum-working-buffer-size)
                     (eq semantic-working-type 'percent)
                     (make-progress-reporter
                      (semantic-parser-working-message (buffer-name))
                      0 100))))
           (setq res (semantic-parse-region (point-min) (point-max)))
           (if semantic--progress-reporter
               (progress-reporter-done semantic--progress-reporter))))

       ;; Clear the caches when we see there were no errors.
       ;; But preserve the unmatched syntax cache and warnings!
       (let (semantic-unmatched-syntax-cache
             semantic-unmatched-syntax-cache-check
             semantic-parser-warnings)
         (semantic-clear-toplevel-cache))
       ;; Set up the new overlays
       (semantic--tag-link-list-to-buffer res)
       ;; Set up the cache with the new results
       (semantic--set-buffer-cache res)))))

  ;; Always return the current parse tree.
  semantic--buffer-cache)

(defmacro semantic-parse-tree-set-needs-rebuild ()
  "Indicate that the current parse tree needs to be rebuilt.
The parse tree must be rebuilt by `semantic-parse-region'."
  `(setq semantic-parse-tree-state 'needs-rebuild))

(defun semantic-parse-region-default
  (start end &optional nonterminal depth returnonerror)
  "Parse the area between START and END, and return any tags found.
If END needs to be extended due to a lexical token being too large,
it will be silently ignored.
Optional arguments:
NONTERMINAL is the rule to start parsing at if it is known.
DEPTH specifies the lexical depth to scan.
RETURNONERROR specifies that parsing should end when encountering
unterminated syntax."
  (when (or (null semantic--parse-table) (eq semantic--parse-table t))
    ;; If there is no table, or it was set to t, then we are here by
    ;; some other mistake.  Do not throw an error deep in the parser.
    (error "No support found to parse buffer %S" (buffer-name)))
  (save-restriction
    (widen)
    (when (or (< end start) (> end (point-max)))
      (error "Invalid parse region bounds %S, %S" start end))
    (semantic-repeat-parse-whole-stream
      (or (cdr (assq start semantic-lex-block-streams))
      (semantic-lex start end depth))
      nonterminal returnonerror)))

(defun semantic-clear-toplevel-cache ()
  "Clear the toplevel tag cache for the current buffer.
Clearing the cache will force a complete reparse next time a tag list
is requested."
  (interactive)
  (run-hooks 'semantic-before-toplevel-cache-flush-hook)
  (setq semantic--buffer-cache nil)
  (semantic-clear-unmatched-syntax-cache)
  (semantic-clear-parser-warnings)
  ;; Nuke all semantic overlays.  This is faster than deleting based
  ;; on our data structure.
  (let ((l (semantic-overlay-lists)))
    (mapc 'semantic-delete-overlay-maybe (car l))
    (mapc 'semantic-delete-overlay-maybe (cdr l))
    )
  (semantic-parse-tree-set-needs-rebuild)
  ;; Remove this hook which tracks if a buffer is up to date or not.
  (remove-hook 'after-change-functions 'semantic-change-function t)
  ;; Old model.  Delete someday.
  ;;(run-hooks 'semantic-after-toplevel-bovinate-hook)

  (run-hook-with-args 'semantic-after-toplevel-cache-change-hook
                      semantic--buffer-cache)

  (setq semantic--completion-cache nil))

(define-mode-local-override semantic-format-tag-name
  c-mode (tag &optional parent color)
  "Convert TAG to a string that is the print name for TAG.
Optional PARENT and COLOR are ignored."
  (let ((name (semantic-format-tag-name-default tag parent color))
    (fnptr (semantic-tag-get-attribute tag :function-pointer))
    )
    (if (not fnptr)
    name
      (concat "(*" name ")"))
    ))

(defclass semantic-bovine-debug-frame (semantic-debug-frame)
  ((nonterm :initarg :nonterm
        :type symbol
        :documentation
        "The name of the semantic nonterminal for this frame.")
   (rule :initarg :rule
     :type number
     :documentation
     "The index into NONTERM's rule list.  0 based.")
   (match :initarg :match
      :type number
      :documentation
      "The index into NONTERM's RULE's match.  0 based..")
   (collection :initarg :collection
           :type list
           :documentation
           "List of things matched so far.")
   (lextoken :initarg :lextoken
         :type list
         :documentation
         "A Token created by `semantic-lex-token'.
This is the lexical token being matched by the parser.")
   )
  "Debugger frame representation for the bovinator.")

(defmethod semantic-debug-interface-layout ((iface semantic-debug-interface))
  "Layout windows in the current frame to facilitate debugging."
  (delete-other-windows)
  ;; Deal with the data buffer
  (when (slot-boundp iface 'data-buffer)
    (let ((lines (/ (frame-height (selected-frame)) 3))
      (cnt (with-current-buffer (oref iface data-buffer)
         (count-lines (point-min) (point-max))))
      )
      ;; Set the number of lines to 1/3, or the size of the data buffer.
      (if (< cnt lines) (setq cnt lines))

      (split-window-vertically cnt)
      (switch-to-buffer (oref iface data-buffer))
      )
    (other-window 1))
  ;; Parser
  (switch-to-buffer (oref iface parser-buffer))
  (when (slot-boundp iface 'parser-location)
    (goto-char (oref iface parser-location)))
  (split-window-vertically)
  (other-window 1)
  ;; Source
  (switch-to-buffer (oref iface source-buffer))
  (when (slot-boundp iface 'source-location)
    (goto-char (oref iface source-location)))
  )

(defmethod semantic-debug-frame-highlight ((frame semantic-debug-frame))
  "Highlight one parser frame."
  (let* ((nonterm (oref frame nonterm))
     (pb (oref semantic-debug-current-interface parser-buffer))
     (start (semantic-brute-find-tag-by-class 'start pb))
    )
    ;; Make sure we get a good rule name, and that it is a string
    (if (and (eq nonterm 'bovine-toplevel) start)
    (setq nonterm (semantic-tag-name (car start)))
      (setq nonterm (symbol-name nonterm)))

    (semantic-debug-highlight-rule semantic-debug-current-interface
                   nonterm
                   (oref frame rule)
                   (oref frame match))
    (semantic-debug-highlight-lexical-token semantic-debug-current-interface
                        (oref frame lextoken))
    ))

(defmethod semantic-debug-unhighlight ((iface semantic-debug-interface))
  "Remove all debugging overlays."
  (mapc 'semantic-overlay-delete (oref iface overlays))
  (oset iface overlays nil))

(defun semantic-debug-mode (onoff)
  "Turn `semantic-debug-mode' on and off.
Argument ONOFF is non-nil when we are entering debug mode.
\\{semantic-debug-mode-map}"
  (let ((iface semantic-debug-current-interface))
    (if onoff
    ;; Turn it on
    (with-current-buffer (oref iface parser-buffer)
      ;; Install our map onto this buffer
      (use-local-map semantic-debug-mode-map)
      ;; Make the buffer read only
      (setq buffer-read-only t)

      (set-buffer (oref iface source-buffer))
      ;; Use our map in the source buffer also
      (use-local-map semantic-debug-mode-map)
      ;; Make the buffer read only
      (setq buffer-read-only t)
      ;; Hooks
      (run-hooks 'semantic-debug-mode-hook)
      )
      ;; Restore old mode information
      (with-current-buffer
          (oref semantic-debug-current-interface parser-buffer)
    (use-local-map
     (oref semantic-debug-current-interface parser-local-map))
    (setq buffer-read-only nil)
    )
      (with-current-buffer
          (oref semantic-debug-current-interface source-buffer)
    (use-local-map
     (oref semantic-debug-current-interface source-local-map))
    (setq buffer-read-only nil)
    )
      (run-hooks 'semantic-debug-exit-hook)
      )))

(defmethod semantic-debug-set-frame ((iface semantic-debug-interface) frame)
  "Set the current frame on IFACE to FRAME."
  (if frame
      (oset iface current-frame frame)
    (slot-makeunbound iface 'current-frame)))

(defclass semantic-bovine-debug-error-frame (semantic-debug-frame)
  ((condition :initarg :condition
          :documentation
          "An error condition caught in an action.")
   )
  "Debugger frame representation of a lisp error thrown during parsing.")

(defun semantic-format-tag-name-default (tag &optional parent color)
  "Return an abbreviated string describing TAG.
Optional argument PARENT is the parent type if TAG is a detail.
Optional argument COLOR means highlight the prototype with font-lock colors."
  (let ((name (semantic-tag-name tag))
    (destructor
     (if (eq (semantic-tag-class tag) 'function)
         (semantic-tag-function-destructor-p tag))))
    (when destructor
      (setq name (concat "~" name)))
    (if color
    (setq name (semantic--format-colorize-text name (semantic-tag-class tag))))
    name))

(defun semantic--format-colorize-text (text face-class)
  "Apply onto TEXT a color associated with FACE-CLASS.
FACE-CLASS is a tag type found in `semantic-format-face-alist'.
See that variable for details on adding new types."
  (if (featurep 'font-lock)
      (let ((face (cdr-safe (assoc face-class semantic-format-face-alist)))
        (newtext (concat text)))
    (put-text-property 0 (length text) 'face face newtext)
    newtext)
    text))

(defmethod semantic-debug-highlight-lexical-token ((iface semantic-debug-interface) token)
  "For IFACE, highlight TOKEN in the source buffer .
TOKEN is a lexical token."
  (set-buffer (oref iface :source-buffer))

  (object-add-to-list iface 'overlays
              (semantic-lex-highlight-token token))

  (semantic-debug-set-source-location iface (semantic-lex-token-start token))
  )

(defmethod semantic-debug-highlight-rule ((iface semantic-debug-interface) nonterm &optional rule match)
  "For IFACE, highlight NONTERM in the parser buffer.
NONTERM is the name of the rule currently being processed that shows up
as a nonterminal (or tag) in the source buffer.
If RULE and MATCH indices are specified, highlight those also."
  (set-buffer (oref iface :parser-buffer))

  (let* ((rules (semantic-find-tags-by-class 'nonterminal (current-buffer)))
     (nt (semantic-find-first-tag-by-name nonterm rules))
     (o nil)
     )
    (when nt
      ;; I know it is the first symbol appearing in the body of this token.
      (goto-char (semantic-tag-start nt))

      (setq o (semantic-make-overlay (point) (progn (forward-sexp 1) (point))))
      (semantic-overlay-put o 'face 'highlight)

      (object-add-to-list iface 'overlays o)

      (semantic-debug-set-parser-location iface (semantic-overlay-start o))

      (when (and rule match)

    ;; Rule, an int, is the rule inside the nonterminal we are following.
    (re-search-forward ":\\s-*")
    (while (/= 0 rule)
      (re-search-forward "^\\s-*|\\s-*")
      (setq rule (1- rule)))

    ;; Now find the match inside the rule
    (while (/= 0 match)
      (forward-sexp 1)
      (skip-chars-forward " \t")
      (setq match (1- match)))

    ;; Now highlight the thingy we find there.
    (setq o (semantic-make-overlay (point) (progn (forward-sexp 1) (point))))
    (semantic-overlay-put o 'face 'highlight)

    (object-add-to-list iface 'overlays o)

    ;; If we have a match for a sub-rule, have the parser position
    ;; move so we can see it in the output window for very long rules.
    (semantic-debug-set-parser-location iface (semantic-overlay-start o))

    ))))

(defmacro semantic-brute-find-tag-by-class
  (class streamorbuffer &optional search-parts search-includes)
  "Find all tags with a class CLASS within STREAMORBUFFER.
CLASS is a symbol representing the class of the tags to find.
See `semantic-tag-class'.
Optional argument SEARCH-PARTS and SEARCH-INCLUDES are passed to
`semantic-brute-find-tag-by-function'.

Use `semantic-find-tag-by-class' instead."
  `(semantic-brute-find-tag-by-function
    (lambda (tag) (eq ,class (semantic-tag-class tag)))
    ,streamorbuffer ,search-parts ,search-includes))

(define-mode-local-override semantic-format-tag-name
  c-mode (tag &optional parent color)
  "Convert TAG to a string that is the print name for TAG.
Optional PARENT and COLOR are ignored."
  (let ((name (semantic-format-tag-name-default tag parent color))
    (fnptr (semantic-tag-get-attribute tag :function-pointer))
    )
    (if (not fnptr)
    name
      (concat "(*" name ")"))
    ))

(defmethod semantic-debug-set-parser-location ((iface semantic-debug-interface) point)
  "Set the parser location in IFACE to POINT."
  (with-current-buffer (oref iface parser-buffer)
    (if (not (slot-boundp iface 'parser-location))
    (oset iface parser-location (make-marker)))
    (move-marker (oref iface parser-location) point))
  )

(defun semantic-find-first-tag-by-name (name &optional table)
  "Find the first tag with NAME in TABLE.
NAME is a string.
TABLE is a semantic tags table.  See `semantic-something-to-tag-table'.
Respects `semantic-case-fold'."
  (assoc-string name (semantic-something-to-tag-table table)
        semantic-case-fold))

(defmacro semantic-find-tags-by-class (class &optional table)
  "Find all tags of class CLASS in TABLE.
CLASS is a symbol representing the class of the token, such as
'variable, of 'function..
TABLE is a tag table.  See `semantic-something-to-tag-table'."
  `(semantic--find-tags-by-macro
    (eq ,class (semantic-tag-class (car tags)))
    ,table))

(defmethod semantic-debug-set-source-location ((iface semantic-debug-interface) point)
  "Set the source location in IFACE to POINT."
  (with-current-buffer (oref iface source-buffer)
    (if (not (slot-boundp iface 'source-location))
    (oset iface source-location (make-marker)))
    (move-marker (oref iface source-location) point))
  )

(define-mode-local-override semantic-format-tag-name
  c-mode (tag &optional parent color)
  "Convert TAG to a string that is the print name for TAG.
Optional PARENT and COLOR are ignored."
  (let ((name (semantic-format-tag-name-default tag parent color))
    (fnptr (semantic-tag-get-attribute tag :function-pointer))
    )
    (if (not fnptr)
    name
      (concat "(*" name ")"))
    ))

(defun semantic-something-to-tag-table (something)
  "Convert SOMETHING into a semantic tag table.
Something can be a tag with a valid BUFFER property, a tag table, a
buffer, or a filename.  If SOMETHING is nil return nil."
  (cond
   ;; A list of tags
   ((and (listp something)
     (semantic-tag-p (car something)))
    something)
   ;; A buffer
   ((bufferp something)
    (with-current-buffer something
      (semantic-fetch-tags)))
   ;; A Tag: Get that tag's buffer
   ((and (semantic-tag-with-position-p something)
     (semantic-tag-in-buffer-p something))
    (with-current-buffer (semantic-tag-buffer something)
      (semantic-fetch-tags)))
   ;; Tag with a file name in it
   ((and (semantic-tag-p something)
     (semantic-tag-file-name something)
     (file-exists-p (semantic-tag-file-name something)))
    (semantic-file-tag-table
     (semantic-tag-file-name something)))
   ;; A file name
   ((and (stringp something)
     (file-exists-p something))
    (semantic-file-tag-table something))
   ;; A Semanticdb table
   ((and (featurep 'semantic/db)
     (semanticdb-minor-mode-p)
     (semanticdb-abstract-table-child-p something))
    (semanticdb-refresh-table something)
    (semanticdb-get-tags something))
   ;; Semanticdb find-results
   ((and (featurep 'semantic/db)
     (semanticdb-minor-mode-p)
     (require 'semantic/db-find)
     (semanticdb-find-results-p something))
    (semanticdb-strip-find-results something))
   ;; NOTE: This commented out since if a search result returns
   ;;       empty, that empty would turn into everything on the next search.
   ;; Use the current buffer for nil
;;   ((null something)
;;    (semantic-fetch-tags))
   ;; don't know what it is
   (t nil)))

(define-mode-local-override semantic-format-tag-name
  c-mode (tag &optional parent color)
  "Convert TAG to a string that is the print name for TAG.
Optional PARENT and COLOR are ignored."
  (let ((name (semantic-format-tag-name-default tag parent color))
    (fnptr (semantic-tag-get-attribute tag :function-pointer))
    )
    (if (not fnptr)
    name
      (concat "(*" name ")"))
    ))

(defun semanticdb-strip-find-results (results &optional find-file-match)
  "Strip a semanticdb search RESULTS to exclude objects.
This makes it appear more like the results of a `semantic-find-' call.
Optional FIND-FILE-MATCH loads all files associated with RESULTS
into buffers.  This has the side effect of enabling `semantic-tag-buffer' to
return a value.
If FIND-FILE-MATCH is 'name, then only the filename is stored
in each tag instead of loading each file into a buffer.
If the input RESULTS are not going to be used again, and if
FIND-FILE-MATCH is nil, you can use `semanticdb-fast-strip-find-results'
instead."
  (if find-file-match
      ;; Load all files associated with RESULTS.
      (let ((tmp results)
        (output nil))
    (while tmp
      (let ((tab (car (car tmp)))
        (tags (cdr (car tmp))))
        (dolist (T tags)
          ;; Normalization gives specialty database tables a chance
          ;; to convert into a more stable tag format.
          (let* ((norm (semanticdb-normalize-one-tag tab T))
             (ntab (car norm))
             (ntag (cdr norm))
             (nametable ntab))

        ;; If it didn't normalize, use what we had.
        (if (not norm)
            (setq nametable tab)
          (setq output (append output (list ntag))))

        ;; Find-file-match allows a tool to make sure the tag is
        ;; 'live', somewhere in a buffer.
        (cond ((eq find-file-match 'name)
               (or (semantic--tag-get-property ntag :filename)
               (let ((f (semanticdb-full-filename nametable)))
                 (semantic--tag-put-property ntag :filename f))))
              ((and find-file-match ntab)
               (semanticdb-get-buffer ntab))
              )
        ))
        )
      (setq tmp (cdr tmp)))
    output)
    ;; @todo - I could use nconc, but I don't know what the caller may do with
    ;;         RESULTS after this is called.  Right now semantic-complete will
    ;;         recycling the input after calling this routine.
    (apply #'append (mapcar #'cdr results))))

(defun semanticdb-find-results-p (resultp)
  "Non-nil if RESULTP is in the form of a semanticdb search result.
This query only really tests the first entry in the list that is RESULTP,
but should be good enough for debugging assertions."
  (and (listp resultp)
       (listp (car resultp))
       (semanticdb-abstract-table-child-p (car (car resultp)))
       (or (semantic-tag-p (car (cdr (car resultp))))
       (null (car (cdr (car resultp)))))))

(defmethod semanticdb-get-tags ((table semanticdb-table-SKEL ))
  "Return the list of tags belonging to TABLE."
  ;; NOTE: Omniscient databases probably don't want to keep large tabes
  ;;       lolly-gagging about.  Keep internal Emacs tables empty and
  ;;       refer to alternate databases when you need something.
  nil)

(defmethod semanticdb-refresh-table ((obj semanticdb-table-java-directory) &optional force)
  "Java Directories should be refreshed when files in the directory hange.
No nothing for now."
  nil)

(defun semanticdb-minor-mode-p ()
  "Return non-nil if `semanticdb-minor-mode' is active."
  (member (car (car semanticdb-hooks))
      (symbol-value (car (cdr (car semanticdb-hooks))))))

(defun semantic-file-tag-table (file)
  "Return a tag table for FILE.
If it is loaded, return the stream after making sure it's ok.
If FILE is not loaded, check to see if `semanticdb' feature exists,
   and use it to get tags from files not in memory.
If FILE is not loaded, and semanticdb is not available, find the file
   and parse it."
  (save-match-data
    (if (find-buffer-visiting file)
    (with-current-buffer (find-buffer-visiting file)
      (semantic-fetch-tags))
      ;; File not loaded
      (if (and (require 'semantic/db-mode)
           (semanticdb-minor-mode-p))
      ;; semanticdb is around, use it.
      (semanticdb-file-stream file)
    ;; Get the stream ourselves.
    (with-current-buffer (find-file-noselect file)
      (semantic-fetch-tags))))))

(define-mode-local-override semantic-format-tag-name
  c-mode (tag &optional parent color)
  "Convert TAG to a string that is the print name for TAG.
Optional PARENT and COLOR are ignored."
  (let ((name (semantic-format-tag-name-default tag parent color))
    (fnptr (semantic-tag-get-attribute tag :function-pointer))
    )
    (if (not fnptr)
    name
      (concat "(*" name ")"))
    ))

(defun semanticdb-file-stream (file)
  "Return a list of tags belonging to FILE.
If file has database tags available in the database, return them.
If file does not have tags available, then load the file, and create them."
  (let ((table (semanticdb-file-table-object file)))
    (when table
      (semanticdb-get-tags table))))

(defmethod semanticdb-get-buffer ((obj semanticdb-abstract-table))
  "Return a buffer associated with OBJ.
If the buffer is not in memory, load it with `find-file-noselect'."
  nil)

(defmethod semanticdb-full-filename ((obj semanticdb-project-database-file))
  "Fetch the full filename that OBJ refers to."
  (oref obj file))

(defmethod semanticdb-normalize-one-tag ((obj semanticdb-table-ebrowse) tag)
  "Convert in Ebrowse database OBJ one TAG into a complete tag.
The default tag provided by searches exclude many features of a
semantic parsed tag.  Look up the file for OBJ, and match TAG
against a semantic parsed tag that has all the info needed, and
return that."
  (let ((tagret nil)
    (objret nil))
    ;; SemanticDB will automatically create a regular database
    ;; on top of the file just loaded by ebrowse during the set
    ;; buffer.  Fetch that table, and use it's tag list to look
    ;; up the tag we just got, and thus turn it into a full semantic
    ;; tag.
    (save-excursion
      (semanticdb-set-buffer obj)
      (setq objret semanticdb-current-table)
      (when (not objret)
    ;; What to do??
    (debug))
      (let ((ans nil))
    ;; Gee, it would be nice to do this, but ebrowse LIES.  Oi.
    (when (semantic-tag-with-position-p tag)
      (goto-char (semantic-tag-start tag))
      (let ((foundtag (semantic-current-tag)))
        ;; Make sure the discovered tag is the same as what we started with.
        (when (string= (semantic-tag-name tag)
               (semantic-tag-name foundtag))
          ;; We have a winner!
          (setq ans foundtag))))
    ;; Sometimes ebrowse lies.  Do a generic search
    ;; to find it within this file.
    (when (not ans)
      ;; We might find multiple hits for this tag, and we have no way
      ;; of knowing which one the user wanted.  Return the first one.
      (setq ans (semantic-deep-find-tags-by-name
             (semantic-tag-name tag)
             (semantic-fetch-tags))))
    (if (semantic-tag-p ans)
        (setq tagret ans)
      (setq tagret (car ans)))
    ))
    (cons objret tagret)))

(define-mode-local-override semantic-format-tag-name
  c-mode (tag &optional parent color)
  "Convert TAG to a string that is the print name for TAG.
Optional PARENT and COLOR are ignored."
  (let ((name (semantic-format-tag-name-default tag parent color))
    (fnptr (semantic-tag-get-attribute tag :function-pointer))
    )
    (if (not fnptr)
    name
      (concat "(*" name ")"))
    ))

(defmacro semantic-deep-find-tags-by-name (name &optional table)
  "Find all tags with NAME in TABLE.
Search in top level tags, and their components, in TABLE.
NAME is a string.
TABLE is a tag table.  See `semantic-flatten-tags-table'.
See also `semantic-find-tags-by-name'."
  `(semantic-find-tags-by-name
    ,name (semantic-flatten-tags-table ,table)))

(defun semantic-current-tag ()
  "Return the current tag in the current buffer.
If there are more than one in the same location, return the
smallest tag.  Return nil if there is no tag here."
  (car (nreverse (semantic-find-tag-by-overlay))))

(defmethod semanticdb-set-buffer ((obj semanticdb-table))
  "Set the current buffer to be a buffer owned by OBJ.
If OBJ's file is not loaded, read it in first."
  (set-buffer (semanticdb-get-buffer obj)))

(defun semanticdb-file-table-object (file &optional dontload)
  "Return a semanticdb table belonging to FILE, make it up to date.
If file has database tags available in the database, return it.
If file does not have tags available, and DONTLOAD is nil,
then load the tags for FILE, and create a new table object for it.
DONTLOAD does not affect the creation of new database objects."
  ;; (message "Object Translate: %s" file)
  (when (and file (file-exists-p file) (file-regular-p file))
    (let* ((default-directory (file-name-directory file))
       (tab (semanticdb-file-table-object-from-hash file))
       (fullfile nil))

      ;; If it is not in the cache, then extract the more traditional
      ;; way by getting the database, and finding a table in that database.
      ;; Once we have a table, add it to the hash.
      (when (eq tab 'no-hit)
    (setq fullfile (file-truename file))
    (let ((db (or ;; This line will pick up system databases.
           (semanticdb-directory-loaded-p default-directory)
           ;; this line will make a new one if needed.
           (semanticdb-get-database default-directory))))
      (setq tab (semanticdb-file-table db fullfile))
      (when tab
        (semanticdb-file-table-object-put-hash file tab)
        (when (not (string= fullfile file))
          (semanticdb-file-table-object-put-hash fullfile tab)
        ))
      ))

      (cond
       ((and tab
         ;; Is this in a buffer?
         ;;(find-buffer-visiting (semanticdb-full-filename tab))
         (semanticdb-in-buffer-p tab)
         )
    (save-excursion
      ;;(set-buffer (find-buffer-visiting (semanticdb-full-filename tab)))
      (semanticdb-set-buffer tab)
      (semantic-fetch-tags)
      ;; Return the table.
      tab))
       ((and tab dontload)
    ;; If we have table, and we don't want to load it, just return it.
    tab)
       ((and tab
         ;; Is table fully loaded, or just a proxy?
         (number-or-marker-p (oref tab pointmax))
         ;; Is this table up to date with the file?
         (not (semanticdb-needs-refresh-p tab)))
    ;; A-ok!
    tab)
       ((or (and fullfile (get-file-buffer fullfile))
        (get-file-buffer file))
    ;; are these two calls this faster than `find-buffer-visiting'?

    ;; If FILE is being visited, but none of the above state is
    ;; true (meaning, there is no table object associated with it)
    ;; then it is a file not supported by Semantic, and can be safely
    ;; ignored.
    nil)
       ((not dontload) ;; We must load the file.
    ;; Full file should have been set by now.  Debug why not?
    (when (and (not tab) (not fullfile))
      ;; This case is if a 'nil is erroneously put into the hash table.  This
      ;; would need fixing
      (setq fullfile (file-truename file))
      )

    ;; If we have a table, but no fullfile, that's ok.  Let's get the filename
    ;; from the table which is pre-truenamed.
    (when (and (not fullfile) tab)
      (setq fullfile (semanticdb-full-filename tab)))

    (setq tab (semanticdb-create-table-for-file-not-in-buffer fullfile))

    ;; Save the new table.
    (semanticdb-file-table-object-put-hash file tab)
    (when (not (string= fullfile file))
      (semanticdb-file-table-object-put-hash fullfile tab)
      )
    ;; Done!
    tab)
       (t
    ;; Full file should have been set by now.  Debug why not?
    ;; One person found this.  Is it a file that failed to parse
    ;; in the past?
    (when (not fullfile)
      (setq fullfile (file-truename file)))

    ;; We were asked not to load the file in and parse it.
    ;; Instead just create a database table with no tags
    ;; and a claim of being empty.
    ;;
    ;; This will give us a starting point for storing
    ;; database cross-references so when it is loaded,
    ;; the cross-references will fire and caches will
    ;; be cleaned.
    (let ((ans (semanticdb-create-table-for-file file)))
      (setq tab (cdr ans))

      ;; Save the new table.
      (semanticdb-file-table-object-put-hash file tab)
      (when (not (string= fullfile file))
        (semanticdb-file-table-object-put-hash fullfile tab)
        )
      ;; Done!
      tab))
       )
      )))

(define-mode-local-override semantic-format-tag-name
  c-mode (tag &optional parent color)
  "Convert TAG to a string that is the print name for TAG.
Optional PARENT and COLOR are ignored."
  (let ((name (semantic-format-tag-name-default tag parent color))
    (fnptr (semantic-tag-get-attribute tag :function-pointer))
    )
    (if (not fnptr)
    name
      (concat "(*" name ")"))
    ))

(defun semanticdb-create-table-for-file (filename)
  "Initialize a database table for FILENAME, and return it.
If FILENAME exists in the database already, return that.
If there is no database for the table to live in, create one."
  (let ((cdb nil)
    (tbl nil)
    (dd (file-name-directory (file-truename filename)))
    )
    ;; Allow a database override function
    (setq cdb (semanticdb-create-database semanticdb-new-database-class
                      dd))
    ;; Get a table for this file.
    (setq tbl (semanticdb-create-table cdb filename))

    ;; Return the pair.
    (cons cdb tbl)
    ))

(defun semanticdb-create-table-for-file-not-in-buffer (filename)
  "Create a table for the file FILENAME.
If there are no language specific configurations, this
function will read in the buffer, parse it, and kill the buffer."
  (if (and semanticdb-out-of-buffer-create-table-fcn
       (not (file-remote-p filename)))
      ;; Use external parser only of the file is accessible to the
      ;; local file system.
      (funcall semanticdb-out-of-buffer-create-table-fcn filename)
    (save-excursion
      (let* ( ;; Remember the buffer to kill
         (kill-buffer-flag (find-buffer-visiting filename))
         (buffer-to-kill (or kill-buffer-flag
                 (semantic-find-file-noselect filename t))))

    ;; This shouldn't ever be set.  Debug some issue here?
    ;; (when kill-buffer-flag (debug))

    (set-buffer buffer-to-kill)
    ;; Find file should automatically do this for us.
    ;; Sometimes the DB table doesn't contains tags and needs
    ;; a refresh.  For example, when the file is loaded for
    ;; the first time, and the idle scheduler didn't get a
    ;; chance to trigger a parse before the file buffer is
    ;; killed.
    (when semanticdb-current-table
      (semantic-fetch-tags))
    (prog1
        semanticdb-current-table
      (when (not kill-buffer-flag)
        ;; If we had to find the file, then we should kill it
        ;; to keep the master buffer list clean.
        (kill-buffer buffer-to-kill)
        )))))
  )

(defmethod semanticdb-needs-refresh-p ((table semanticdb-table-ebrowse))
  "EBROWSE database do not need to be refreshed.

JAVE: stub for needs-refresh, because, how do we know if BROWSE files
      are out of date?

EML: Our database should probably remember the timestamp/checksum of
     the most recently read EBROWSE file, and use that."
  nil
)

(defmethod semanticdb-in-buffer-p ((obj semanticdb-abstract-table))
  "Return a nil, meaning abstract table OBJ is not in a buffer."
  nil)

(defun semanticdb-file-table-object-put-hash (file dbtable)
  "For FILE, associate DBTABLE in the hash table."
  (puthash file dbtable semanticdb-file-table-hash))

(defmethod semanticdb-file-table ((obj semanticdb-project-database-SKEL) filename)
  "From OBJ, return FILENAME's associated table object."
  ;; NOTE: See not for `semanticdb-get-database-tables'.
  (car (semanticdb-get-database-tables obj))
  )

(defun semanticdb-get-database (filename)
  "Get a database for FILENAME.
If one isn't found, create one."
  (semanticdb-create-database semanticdb-new-database-class (file-truename filename)))

(defun semanticdb-directory-loaded-p (path)
  "Return the project belonging to PATH if it was already loaded."
  (eieio-instance-tracker-find path 'reference-directory 'semanticdb-database-list))

(defun semanticdb-file-table-object-from-hash (file)
  "Retrieve a DB table from the hash for FILE.
Does not use `file-truename'."
  (gethash file semanticdb-file-table-hash 'no-hit))

(define-mode-local-override semantic-format-tag-name
  c-mode (tag &optional parent color)
  "Convert TAG to a string that is the print name for TAG.
Optional PARENT and COLOR are ignored."
  (let ((name (semantic-format-tag-name-default tag parent color))
    (fnptr (semantic-tag-get-attribute tag :function-pointer))
    )
    (if (not fnptr)
    name
      (concat "(*" name ")"))
    ))

(defun eieio-instance-tracker-find (key slot list-symbol)
  "Find KEY as an element of SLOT in the objects in LIST-SYMBOL.
Returns the first match."
  (object-assoc key slot (symbol-value list-symbol)))

(defmethod semanticdb-get-database-tables ((obj semanticdb-project-database-SKEL))
  "For a SKEL database, there are no explicit tables.
Create one of our special tables that can act as an intermediary."
  ;; NOTE: This method overrides an accessor for the `tables' slot in
  ;;       a database.  You can either construct your own (like tmp here
  ;;       or you can manage any number of tables.

  ;; We need to return something since there is always the "master table"
  ;; The table can then answer file name type questions.
  (when (not (slot-boundp obj 'tables))
    (let ((newtable (semanticdb-table-emacs-lisp "tmp")))
      (oset obj tables (list newtable))
      (oset newtable parent-db obj)
      (oset newtable tags nil)
      ))
  (call-next-method))

(defmethod semanticdb-create-table ((db semanticdb-java-jar-database) dirorfile)
  "Create a new table in DB for DIR and return it.
This overrides the default `semanticdb-create-table' as this database
creates tables of classes based on files, not files in a directory.
The class of DB contains the class name for the type of table to create.
If the table for DIR exists, return it.
If the table for DIR does not exist, create one."
  (when (stringp dirorfile)
    (let ((newtab (semanticdb-file-table db dirorfile)))
      (unless newtab
    (let ((matchingfiles (or (semanticdb-java-jar-package-files db dirorfile)
                 (semanticdb-java-jar-package-one-file db dirorfile)))
          (matchingpkg (semanticdb-java-jar-package-packages db dirorfile)))
      (when matchingfiles
        ;; Only make a table if there are any matching files in it.
        (if (= (length matchingfiles) 1)
        ;; If there is only one table, create a jar-file table.
        (setq newtab (funcall (oref db new-table-class)
                      (car matchingfiles)
                      :filename (car matchingfiles)))
          ;; If there are multiple files, then we want a directory
          ;; The file extractor restricts itself to .class, so no dups?
          (setq newtab (funcall (oref db new-table-dir-class)
                    dirorfile
                    :directory dirorfile))
          (oset newtab filenamecache
            (mapcar 'file-name-nondirectory matchingfiles))
          (oset newtab packagenamecache matchingpkg)
          )
        (oset newtab parent-db db)
        (object-add-to-list db 'tables newtab t)
        )))
      newtab)))

(defmethod semanticdb-create-database :STATIC ((dbc semanticdb-project-database-system)
                           directory)
  "Create a new semantic database for DIRECTORY and return it.
If a database for DIRECTORY has already been loaded, return it.
If a database for DIRECTORY exists, then load that database, and return it.
If DIRECTORY doesn't exist, create a new one."
  ;; System databases span directories.  Be smart about creation.
  (let ((new (or semanticdb-database-being-created
         (call-next-method))))
    ;; Add system paths for this mode
    (let ((m (oref-default dbc major-modes)))
      (while m
    (semantic-add-system-include directory (car m))
    (message "Adding %s to system include for %s" directory (car m))
    (setq m (cdr m))))
    ;; Return it.
    new))

(define-mode-local-override semantic-format-tag-name
  c-mode (tag &optional parent color)
  "Convert TAG to a string that is the print name for TAG.
Optional PARENT and COLOR are ignored."
  (let ((name (semantic-format-tag-name-default tag parent color))
    (fnptr (semantic-tag-get-attribute tag :function-pointer))
    )
    (if (not fnptr)
    name
      (concat "(*" name ")"))
    ))

(defmacro setq-mode-local (mode &rest args)
  "Assign new values to variables local in MODE.
MODE must be a major mode symbol.
ARGS is a list (SYM VAL SYM VAL ...).
The symbols SYM are variables; they are literal (not evaluated).
The values VAL are expressions; they are evaluated.
Set each SYM to the value of its VAL, locally in buffers already in
MODE, or in buffers switched to that mode.
Return the value of the last VAL."
  (when args
    (let (i ll bl sl tmp sym val)
      (setq i 0)
      (while args
        (setq tmp  (make-symbol (format "tmp%d" i))
              i    (1+ i)
              sym  (car args)
              val  (cadr args)
              ll   (cons (list tmp val) ll)
              bl   (cons `(cons ',sym ,tmp) bl)
              sl   (cons `(set (make-local-variable ',sym) ,tmp) sl)
              args (cddr args)))
      `(let* ,(nreverse ll)
         ;; Save mode bindings
         (mode-local-bind (list ,@bl) '(mode-variable-flag t) ',mode)
         ;; Assign to local variables in all existing buffers in MODE
         (mode-local-map-mode-buffers #'(lambda () ,@sl) ',mode)
         ;; Return the last value
         ,tmp)
      )))

(defun semantic-add-system-include (dir &optional mode)
  "Add a system include DIR to path for MODE.
Modifies a mode-local version of `semantic-dependency-system-include-path'.

Changes made by this function are not persistent."
  (interactive "DNew Include Directory: ")
  (if (not mode) (setq mode major-mode))
  (let ((dirtmp (file-name-as-directory dir))
    (value
     (mode-local-value mode 'semantic-dependency-system-include-path))
    )
    (add-to-list 'value dirtmp t)
    (eval `(setq-mode-local ,mode
                semantic-dependency-system-include-path value))
    ))

(defmethod semanticdb-java-jar-package-packages ((dbc semanticdb-java-jar-database) dir)
  "Get the package names from DBC that match DIR.
DIR may already have some .class files in it (see `semanticdb-java-jar-package-files')
while also having sub-packages."
  (when (stringp dir)
    (let ((ans nil))
      (dolist (F (oref dbc jarfilecache))
    (when (string-match (concat "^" (regexp-quote dir) "\\w+/") F)
      (add-to-list 'ans (match-string 0 F))))
      (nreverse ans))))

(defmethod semanticdb-java-jar-package-one-file ((dbc semanticdb-java-jar-database) file)
  "Get the file class names from DBC that match FILE.
File should exclude an extension, as .class will be added."
  (when (stringp file)
    (let ((ans nil))
      (dolist (F (oref dbc jarfilecache))
    (when (string-match (concat "^" (regexp-quote file) "\\.class$") F)
      (push F ans)))
      (nreverse ans))))

(defmethod semanticdb-java-jar-package-files ((dbc semanticdb-java-jar-database) dir)
  "Get the file class names from DBC that match DIR."
  (when (stringp dir)
    (setq dir (file-name-as-directory dir))
    (let ((ans nil))
      (dolist (F (oref dbc jarfilecache))
    (when (string-match (concat "^" (regexp-quote dir) "[a-zA-Z_]*\\.class$")
                F)
      (push F ans)))
      (nreverse ans))))

(defclass semanticdb-table-emacs-lisp (semanticdb-abstract-table)
  ((major-mode :initform emacs-lisp-mode)
   )
  "A table for returning search results from Emacs.")

(define-mode-local-override semantic-format-tag-name
  c-mode (tag &optional parent color)
  "Convert TAG to a string that is the print name for TAG.
Optional PARENT and COLOR are ignored."
  (let ((name (semantic-format-tag-name-default tag parent color))
    (fnptr (semantic-tag-get-attribute tag :function-pointer))
    )
    (if (not fnptr)
    name
    (concat "(*" name ")"))))

(defclass semanticdb-table-emacs-lisp (semanticdb-abstract-table)
  ((major-mode :initform emacs-lisp-mode)
   )
  "A table for returning search results from Emacs.")

(define-overloadable-function semantic-parse-region
  (start end &optional nonterminal depth returnonerror)
  "Parse the area between START and END, and return any tags found.
If END needs to be extended due to a lexical token being too large, it
will be silently ignored.

Optional arguments:
NONTERMINAL is the rule to start parsing at.
DEPTH specifies the lexical depth to descend for parsers that use
lexical analysis as their first step.
RETURNONERROR specifies that parsing should stop on the first
unmatched syntax encountered.  When nil, parsing skips the syntax,
adding it to the unmatched syntax cache.

Must return a list of semantic tags which have been cooked
\(repositioned properly) but which DO NOT HAVE OVERLAYS associated
with them.  When overloading this function, use `semantic--tag-expand'
to cook raw tags.")

(define-overloadable-function semantic-parse-stream (stream nonterminal)
  "Parse STREAM, starting at the first NONTERMINAL rule.
For bovine and wisent based parsers, STREAM is from the output of
`semantic-lex', and NONTERMINAL is a rule in the appropriate language
specific rules file.
The default parser table used for bovine or wisent based parsers is
`semantic--parse-table'.

Must return a list: (STREAM TAGS) where STREAM is the unused elements
from STREAM, and TAGS is the list of semantic tags found; usually only
one tag is returned with the exception of compound statements.")

(defclass semantic-bovine-debug-frame (semantic-debug-frame)
  ((nonterm :initarg :nonterm
        :type symbol
        :documentation
        "The name of the semantic nonterminal for this frame.")
   (rule :initarg :rule
     :type number
     :documentation
     "The index into NONTERM's rule list.  0 based.")
   (match :initarg :match
      :type number
      :documentation
      "The index into NONTERM's RULE's match.  0 based..")
   (collection :initarg :collection
           :type list
           :documentation
           "List of things matched so far.")
   (lextoken :initarg :lextoken
         :type list
         :documentation
         "A Token created by `semantic-lex-token'.
This is the lexical token being matched by the parser.")
   )
  "Debugger frame representation for the bovinator.")

(defclass semantic-bovine-debug-error-frame (semantic-debug-frame)
  ((condition :initarg :condition
          :documentation
          "An error condition caught in an action.")
   )
  "Debugger frame representation of a lisp error thrown during parsing.")

(define-mode-local-override semantic-format-tag-name
  c-mode (tag &optional parent color)
  "Convert TAG to a string that is the print name for TAG.
Optional PARENT and COLOR are ignored."
  (let ((name (semantic-format-tag-name-default tag parent color))
    (fnptr (semantic-tag-get-attribute tag :function-pointer))
    )
    (if (not fnptr)
    name
      (concat "(*" name ")"))
    ))

(provide 'semantic)
;;; semantic.el ends here
