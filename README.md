# Complex Analysis: Has Primitives
## Rutgers Lean Seminar

This project has a blueprint, which, for the moment, is available at <https://jauslin.org/lean-complex-has_primitives-doc/blueprint/>

## Building the project

If you already have Lean installed, you can build the project with
```bash
lake build
```
(see below for lean installation instructions).


## Installing lean

There are many ways of installing lean4, however, with mathlib4 being in the
state that it is in, we recommend using `elan`. It can be downloaded directly
from <https://github.com/leanprover/elan> (it is also available as a package
for most mainstream linux distributions).

Download lean using

```bash
elan toolchain install leanprover/lean4:stable
```

`elan` allows several versions of lean to be installed on the same system. You
can set a default lean installation using

```bash
elan default leanprover/lean4:stable
```

This project includes a `lean-toolchain` file, which overrides the lean
version. To download the appropriate version for this project, run

```
lake update
```

## Setting up the project

Authorization is needed to contribute to this project. If you are having
issues, contact Ian.

To download the project, run

```bash
git clone https://github.com/ianjauslin-rutgers/lean-complex-has_primitives.git
```

or, if you prefer to use SSH,

```bash
git clone git@github.com:ianjauslin-rutgers/lean-complex-has_primitives.git
```

This will download all the files in the project. However, this does not install
mathlib. To do so, `cd` to the project directory and run

```bash
lake update
```

## Cached oleans

By default, lean will compile the files it needs to compile the project. This
can be very time consuming. To make this process quicker, a pre-compiled
version of mathlib is made available by the Mathlib community.  You can
download it by running

```bash
lake exe cache get
```

However, this will only work if you are running the same version of lean as the
one that was used to compile mathlib (otherwise the oleans are unusable, and
your system will recompile all files). You can find out which version of lean
was used by the latest mathlib in the file
<https://github.com/leanprover-community/mathlib4/blob/master/lean-toolchain>


## Git dos and don'ts

Git is a version control system that is very feature rich. As such, it can feel
daunting at first to learn how to use it properly, but there isn't actually
that much that you need to learn to get started.

The basic idea is that every time a change is made to a file, that change gets
recorded on the "git tree", in such a way that everyone can easily share the
latest version of the project, while keeping track of all the past versions of
the project. That way, you cannot really break anything irreversibly.

Git is also very convenient when a group of people work on the same project at
once. The basic concept to understand here is that of a "branch". A branch is a
version of the project, but, unlike a standard numbering scheme (v1.1, v1.2,
etc), git allows multiple concurrent versions to exist. For example, the
default branch is the master branch. Say Alice wants to work on Task 1, and Bob
wants to work on Task 2. Alice can create a branch, called "task1", and Bob
creates "task2". Alice works on the files on her branch, and Bob on his. That
way, both can work independently without interfering with each other, or with
the master branch. At the same time, Alice can see what Bob is doing, and vice
versa. When their work is ready to be combined, they can do so by "merging"
their branches, which will use some clever algorithms to combine Alice and
Bob's changes together. That way, Alice and Bob can work on separate things
without interference, and share their work when it is ready.

In practice, if you want to work on a task, create a branch with a name that
describes the task. For this example let's say I want to prove Proposition 1, I
will create a branch "prop1" with the following command

```bash
git checkout -b prop1
```

This creates the branch and puts you on it. You can then do your work. Every
time you complete a part of your task, you can save it to git by running

```bash
git add .
git commit
```

and writing a description of your work in the commit message. You should then
upload your changes to github with

```bash
git push
```

The first time you push after creating the branch, use

```bash
git push --set-upstream origin prop1
```

(replace "prop1" with the name of your branch).
When you are ready to merge your work with the master branch (that is, when you
are ready for your work to be included in the default branch of the project,
where it can be merged with everyone else's), create a pull request at
<https://github.com/ianjauslin-rutgers/pythagoras4/pulls>

Using git properly can help you streamline your workflow. Using it improperly
might slow you down, but it's actually quite difficult to ruin things for other
people. However, one thing you should NOT do, is rewrite git histories that
have already been pushed to the server. This makes a mess for everyone. So,
unless you know what you are doing, don't use the `git rebase` or
`git filter-branch` commands. And don't use `git commit --amend` if you have
already pushed your commit.

A great resource for learning more is <https://git-scm.com/book/en/v2>.

## Coding style

### Theorem indentation

When stating a theorem or lemma, use the following indentation:

```lean
theorem name_of_theorem {arguments} (more arguments)
    (more arguments) :
    statement := by
  proof...
```
