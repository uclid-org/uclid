# Contributing to UCLID5

UCLID5 is a relatively new tool and we welcome new contributors who want to get involved. Here are some very minimalistic guidelines on code and pull requests:


## CODE:
1. Every new function introduced should be documented, for example like this:
~~~
/**
   * Create new SMT symbolic variables for each state.
   *
   * This is called after each step of symbolic simulation and prevents the expression
   * trees from blowing up.
   *
   * @param st The symbol table.
   * @param step The current frame number.
   * @param scope The current scope.
   */
  def renameStates(st : SymbolTable, eqStates : Set[Identifier], frameNumber : Int, scope : Scope, addAssumption : (smt.Expr, List[ExprDecorator]) => Unit) : SymbolTable = {
~~~

2. Please don’t leave commented out code in the code base if you can avoid it. If it really must stay, add a comment to it saying why it must stay, what it was for and why it was commented out.

## Pull requests:
1. Each new feature or bug fix should be done on a new branch 
2. Create a separate PR for each new feature or bug fix. 
3. Where possible break down large new features into separate PRs. 
4. Every PR for a new feature should include a set of regression tests that fully test the feature
5. Every PR for a bug fix should include a regression test that tests the fix
6. When you get feedback on a PR, push the changes to the same branch so they appear in the same PR.
7. Write good commit messages: https://blogs.gnome.org/danni/2011/10/25/a-guide-to-writing-git-commit-messages/
Every commit should have a meaningful commit message, which is less than 72 characters long. If you need more than that, the commit should have a short heading commit message followed by a longer description on a new line. 
8. Tidy up your commit history before you PR: use interactive rebase to squash together messy commits into a single meaningful commit with a good commit message. e.g., these two commits should be squashed into one:
~~~
commit c76ef1e8bbfa1cb06f42dsdd3g02138002bca938 
Author: polgreen <epolgreen@gmail.com>
Date:   Tue Oct 27 15:12:03 2020 -0700

    fixes mistake in previous commit

commit 6502265e4a85688ff92d963419c1957ef3cb73b5
Author: polgreen <epolgreen@gmail.com>
Date:   Tue Oct 27 11:18:52 2020 -0700

    Add array reads to readset

    The redundant assignment eliminator was removing relevant assigns because
    it was failing to count array select statements as reads of the index variable, if the array select
    happens on the LHS of an assign. Bug exposed by test/test-redundant-assign.ucl
~~~
9. Preserve bisectability: every commit should compile. If your commit does not compile, use interactive rebase to fix it.
10. Don’t change whitespace unnecessarily. If you are going to change whitespace, then change it in a specific commit with a message that says “white space changes”
11. Don’t change the .gitignore unnecessarily. If you are going to change it, do it in a separate commit with a message that explains why the commit is necessary
12. Delete any branches on the main repo (uclid-org/uclid) as soon as the PR has been merged. If you want to keep branches, do it on your own fork. 
