# Software Foundations

[Online Textbook](https://softwarefoundations.cis.upenn.edu/lf-current/index.html)

[Michael Clarkson's Open Online Course](https://www.youtube.com/watch?v=BGg-gxhsV4E)
[Michael Charkson's Course (on Bilibili)](https://www.bilibili.com/video/BV1kd4y1t7bw/)

[Xiong Yingfei's Course Webpage (2023 Spring)](https://xiongyingfei.github.io/SF/2023/lectures.html)

This note is used as a brief summary and supplementofr the textbook and courses.

## Introduction

### 03 Sources of Knowledge
Type System

Compilers can automatically find errors.

Compliers use deductive resoning to determine whether that are type errors.
And human designer use deductive reasoning to prove that the type system is sound. (Well-typed programs don't go wrong.)


This may not be perfect:
- For example, a type system maybe only strong enough to express function with integer input and output.
- Maybe the system is not complete and cannot type some correct programs.
- Maybe the system will fail at runtime because of typecasts.

Nonetheless, this is still widely accepted.


### 04 The Software Crisis

Large systems become disastrous.

Possible solution: Software Engineering.

Dijkstra present his programming methodology --> formal methods.

### 05 Formal methods

Emphasize logic and proof. 
Formal specifications + proofs about programs + machine checking.

Foundations of mathematics
- Godel's First Incompleteness Theorem
- The Halting Problem
- Rice's Theorem: Every property of a program is undecidable.

But formal methods are still useful and profitable.

### 06 Coq

'Interactive Theorem Proving and Program Development'

Type Theory (improve upon Set Theory)

Coq is implemented in OCaml.

Calculus of inductive constructions, better suited to reasoning about data structures.

Coq features
- **Define** computable functions and logical predicates.
- **State** mathematical theorems and software specifications.
- **Develop** formal proofs of theorems, interactively.
- **Machine-check** those proofs.
- **Extract** verified programs of OCaml, Haskell, Scheme.

<!-- insert PPT P25 -->

### 07 Three Recent Great Works in Formal Verification

CompCert, written in Coq, has not be found any bug.

seL4, written in Isabelle/HOL & Haskell, verifies an operating system microkernel.

Fiat Crypography verified implementations of elliptic curve cryptography algorithms.

### 08 7+1 Myths

Formal methods are controversial.


1. Formal methods guarantee that software is perfect --> better.
2. Formal methods is all about theorem proving. --> Specification comes first, then proof's about programs.
3. Formal methods are only useful for safety-critical systems. --> Also useful in compilers, operating systems, web browser kernels, machine learning systems, distributedd systems etc.
4. Formal methods require highly trained mathematicians. --> Can be mastered by most students.
5. Formal methods increase the cost of software development. --> Hall claims that they decreased the cost.
6. Formal methods are unacceptable to clients. --> They can be explained to clients.
7. Formal methods are not used on real, large-scale software. --> Formal methods are being used on real, large-scale software.

"Formal methods are highly addictive."




