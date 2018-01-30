" Vim syntax file
" Language: Uclid5
" Maintainer:   Pramod Subramanyan <pramod.subramanyan@gmail.com>
" Last Change:  Thu Oct 10 17:35:44 EDT 2017
" Filenames:    *.ucl

" Comments: 
" Make sure to create a file name .vim/ftdetect/ucl.vim containing this line:
" au BufRead,BufNewFile *.ucl set filetype=Uclid5

if exists("b:current_syntax")
    finish
endif

let s:ucl4_cpo_save = &cpo
set cpo&vim


" type
syn keyword ucl4Type            bool int bv\d\+ enum
" repeat / condition / label
syn keyword ucl4Expr            forall exists Lambda 
syn keyword ucl4Stmt            if else assert assume havoc for skip case esac
syn keyword ucl4Decl            module init next control function procedure returns call type var input output const property invariant synthesis grammar requires ensures modifies sharedvar instance axiom in
syn keyword ucl4Cmd             unroll check print_module print_cex print_results k_induction_base k_induction_step induction clear_context
" user labels
syn keyword ucl4Constant        false true

syn match   ucl4Identifier      display "[A-Za-z_][A-Za-z0-9_]\*"


" Comments
"
" TODO: include strings ?
"
syn keyword ucl4Todo contained TODO FIXME XXX NOTE
syn region  ucl4MultilineComment start="\/\*"  end="\*\/" contains=ucl4Todo
hi def link ucl4MultilineComment Comment
syn match   ucl4TrailingComment "\/\/.*$" contains=ucl4Todo
hi def link ucl4TrailingComment  Comment
syn match   ucl4LineComment "\/\/.*$" contains=ucl4Todo
hi def link ucl4LineComment Comment
" unicode characters
syn match   ucl4Number      "\<\(0[0-7]*\|0[xX]\x\+\|\d\+\)[lL]\=\>"
syn match   ucl4Number      "\(\<\d\+\.\d*\|\.\d\+\)\([eE][-+]\=\d\+\)\=[fFdD]\="
syn match   ucl4Number      "\<\d\+[eE][-+]\=\d\+[fFdD]\=\>"
syn match   ucl4Number      "\<\d\+\([eE][-+]\=\d\+\)\=[fFdD]\>"
syn match   ucl4Number      "\<\d\+bv\d\+\>"
syn match   ucl4Operator    ":=\|==\|+\|-\|*\|&&\|||\|^\|!"

" The default highlighting.
hi def link ucl4Type            Type
hi def link ucl4Decl            Conditional
hi def link ucl4Stmt            Conditional
hi def link ucl4Expr            StorageClass
hi def link ucl4Constant        Constant
hi def link ucl4Cmd             Define
hi def link ucl4Operator        Operator

hi def link ucl4Todo             Todo

hi def link ucl4Number          Number

let b:current_syntax = "ucl4"

" let &cpo = s:ucl4_cpo_save
" unlet s:ucl4_cpo_save

" set efm+=%f(%l\\,%c):\ %m

" vim: ts=8
