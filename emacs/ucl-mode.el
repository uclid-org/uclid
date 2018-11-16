;;; ucl-mode.el --- A major mode, derived from prog mode, that provides syntax highlighting for editing Uclid files -*- lexical-binding: t -*-

;; Author: Abhishek Singh <abh@cs.unc.edu>
;; Package-Requires: ((emacs "24") (parent-mode "2.0") (highlight-numbers-mode "0.2.3"))

;; This file is NOT part of GNU Emacs.

;; Copyright (c) 2018, Abhishek Singh
;; All rights reserved.
;;
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:
;;
;;   * Redistributions of source code must retain the above copyright
;;     notice, this list of conditions and the following disclaimer.
;;   * Redistributions in binary form must reproduce the above copyright
;;     notice, this list of conditions and the following disclaimer in the
;;     documentation and/or other materials provided with the distribution.
;;
;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
;; IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
;; TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
;; PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
;; OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
;; EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
;; PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
;; PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
;; LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;;; Commentary:

;; To enable: add `(require 'ucl-mode)' to init.el

(require 'highlight-numbers)

(setq ucl-type '("boolean" "integer" "enum" "record")
      ucl-expr '("forall" "exists" "Lambda" "in")
      ucl-stmt '("if" "then" "else" "assert" "assume" "havoc" "for" "skip" "case" "esac" "default")
      ucl-decl '("module" "init" "next" "control" "function" "procedure" "returns" "call" "type" "var" "input" "output" "const" "property" "invariant" "synthesis" "grammar" "requires" "ensures" "modifies" "sharedvar" "instance" "axiom" "define")
      ucl-cmd '("unroll" "check" "print_module" "print_cex" "print_results" "k_induction_base" "k_induction_step" "induction" "clear_context" "synthesize_invariant")
      ucl-const '("false" "true")
      ucl-op '("==>" "<==>" ">" "<" "=" "==" "!=" ">=" "<=" "++" "+" "-" "*" "&&" "||" "&" "|" "^" "!" "~" "bv_sign_extend" "bv_zero_extend" "bv_left_shift" "bv_l_right_shift" "bv_a_right_shift"))

(setq ucl-type-re (regexp-opt ucl-type 'symbols)
      ucl-expr-re (regexp-opt ucl-expr 'symbols)
      ucl-stmt-re (regexp-opt ucl-stmt 'symbols)
      ucl-decl-re (regexp-opt ucl-decl 'symbols)
      ucl-cmd-re (regexp-opt ucl-cmd 'symbols)
      ucl-const-re (regexp-opt ucl-const 'symbols)
      ucl-op-re (regexp-opt ucl-op 'symbols))

(setq ucl-ident-re "\\_<[A-Za-z_][A-Za-z0-9_']*\\_>"
      ucl-usr-type-re "\\_<[A-za-z_][A-Za-z0-9_\.]*_t\\_>"
      ucl-bv-type-re "\\_<bv[0-9]+\\_>")

(eval-when-compile
  (puthash 'ucl-mode
	   (rx (and
		symbol-start
		(or (and (or (+ digit)
			     (and "0"
				  (any "xX")
				  (+ hex-digit)))
			 (? (any "lL")))
		    (and (or (and (+ digit)
				  (? (and "." (* digit))))
			     (and "." (* digit)))
			 (? (and (any "eE")
				 (? (any "-+"))
				 (+ digit)))
			 (? (any "fFdD")))
		    (and (+ digit)
			 "bv"
			 (+ digit)))
		symbol-end))
	   highlight-numbers-modelist)) 

(setq ucl-font-lock-defaults
      `(
	(,ucl-type-re . font-lock-type-face)
	(,ucl-bv-type-re . font-lock-type-face)
	(,ucl-usr-type-re . font-lock-preprocessor-face)
	(,ucl-expr-re . font-lock-function-name-face)
	(,ucl-stmt-re . font-lock-variable-name-face)
	(,ucl-decl-re . font-lock-keyword-face)
	(,ucl-cmd-re . font-lock-builtin-face)
	(,ucl-const-re . font-lock-constant-face)
	(,ucl-op-re . font-lock-string-face)))

(setq ucl-syntax-table
      (let ((table (copy-syntax-table prog-mode-syntax-table)))
	(modify-syntax-entry ?' "_" table)
	(modify-syntax-entry ?_ "_" table)
	(modify-syntax-entry ?! "_" table)
	(modify-syntax-entry ?/ ". 124b" table)
	(modify-syntax-entry ?\n "> b" table)
	(modify-syntax-entry ?* ". 23" table)
	table))

(define-derived-mode ucl-mode prog-mode "uclid mode"
  "A major mode that provides syntax highlighting for Uclid files"
  :syntax-table ucl-syntax-table
  (setq font-lock-defaults '((ucl-font-lock-defaults))))

(add-to-list 'auto-mode-alist '("\\.ucl\\'" . ucl-mode))

(add-hook 'ucl-mode-hook 'highlight-numbers-mode)

(provide 'ucl-mode)
