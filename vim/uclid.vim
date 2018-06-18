" Vim syntax file
" Language: uclid
" Maintainer:   Pramod Subramanyan <pramod.subramanyan@gmail.com>
" Last Change:  Thu Oct 10 17:35:44 EDT 2017
" Filenames:    *.ucl

" Comments:
" Make sure to create a file name .vim/ftdetect/ucl.vim containing this line:
" au BufRead,BufNewFile *.ucl set filetype=uclid

if exists("b:current_syntax")
    finish
endif

" type
syn keyword ucl4Type            boolean integer enum record
" repeat / condition / label
syn keyword ucl4Expr            forall exists Lambda in
syn keyword ucl4Stmt            if then else assert assume havoc for skip case esac default
syn keyword ucl4Decl            module init next control function procedure returns call type var input output const property invariant synthesis grammar requires ensures modifies sharedvar instance axiom define
syn keyword ucl4Cmd             unroll check print_module print_cex print_results k_induction_base k_induction_step induction clear_context synthesize_invariant
" user labels
syn keyword ucl4Constant        false true


syn match   ucl4Identifier      display "[A-Za-z_][A-Za-z0-9_]*"
syn match   ucl4UsrType         display "[A-za-z_][A-Za-z0-9_\.]*_t\w\@!"
syn match   ucl4BVType          "\<bv\d\+\>"


" Comments
"
" TODO: include strings ?
"
" unicode characters
syn match   ucl4Number      "\<\(0[0-7]*\|0[xX]\x\+\|\d\+\)[lL]\=\>"
syn match   ucl4Number      "\(\<\d\+\.\d*\|\.\d\+\)\([eE][-+]\=\d\+\)\=[fFdD]\="
syn match   ucl4Number      "\<\d\+[eE][-+]\=\d\+[fFdD]\=\>"
syn match   ucl4Number      "\<\d\+\([eE][-+]\=\d\+\)\=[fFdD]\>"
syn match   ucl4Number      "\<\d\+bv\d\+\>"
syn match   ucl4Operator    "=\|==\|+\|-\|*\|&&\|||\|^\|!\|==>\|<==>"

syn region ucl4MultilineComment start="/\*" end="\*/"
syn region ucl4TrailingComment start="//" end="$"

" The default highlighting.
hi def link ucl4MultilineComment ucl4TrailingComment
hi def link ucl4TrailingComment  comment
hi def link ucl4Identifier      Normal
hi def link ucl4UsrType         Identifier
hi def link ucl4BVType          ucl4Type
hi def link ucl4Type            Type
hi def link ucl4Decl            Keyword
hi def link ucl4Stmt            Conditional
hi def link ucl4Expr            StorageClass
hi def link ucl4Constant        Constant
hi def link ucl4Cmd             Define
hi def link ucl4Operator        Special
hi def link ucl4Number          Number

let b:current_syntax = "ucl"
