" Vim syntax file
" Language: Uclid4
" Maintainer:   Pramod Subramanyan <pramod.subramanyan@gmail.com>
" Last Change:  Thu Oct 10 17:35:44 EDT 2017
" Filenames:    *.ucl4

" Comments: 
" Make sure to create a file name .vim/ftdetect/ucl4.vim containing this line:
" au BufRead,BufNewFile *.ucl4      set filetype=Uclid4

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
syn keyword ucl4Decl            module init next control function procedure type var input output constant property instance axiom
syn keyword ucl4Cmd             initialize simulate decide print_module print_cex print_results k_induction_base k_induction_step clear_context
" user labels
syn keyword ucl4Constant        false true

syn match   ucl4Identifier      display "[A-Za-z_][A-Za-z0-9_]\*"


" Comments
"
" PROVIDES: @ucl4CommentHook
"
" TODO: include strings ?
"
syn keyword ucl4Todo        contained TODO FIXME XXX NOTE
syn region  ucl4Comment     start="/\*"  end="\*/" contains=@ucl4CommentHook,ucl4Todo,@Spell
syn match   ucl4Comment     "//.*$" contains=@ucl4CommentHook,ucl4Todo,@Spell

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

hi def link ucl4Todo            Todo
hi def link ucl4Comment         Comment

hi def link ucl4Number          Number

let b:current_syntax = "ucl4"

let &cpo = s:ucl4_cpo_save
unlet s:ucl4_cpo_save

set efm+=%f(%l\\,%c):\ %m

" vim: ts=8
