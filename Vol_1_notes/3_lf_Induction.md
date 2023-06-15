# Software Foundations

[Online Textbook](https://softwarefoundations.cis.upenn.edu/lf-current/index.html)

[Michael Clarkson's Open Online Course (on Youtube)](https://www.youtube.com/watch?v=BGg-gxhsV4E)
[Michael Charkson's Course (on Bilibili)](https://www.bilibili.com/video/BV1kd4y1t7bw/)

[Xiong Yingfei's Course Webpage (2023 Spring)](https://xiongyingfei.github.io/SF/2023/lectures.html)

This note is used as a brief summary and supplementofr the textbook and courses.

## Induction

### Compile .v File and Inport It

We need to import all of our definitions from the previous chapter.
```Coq
From LF Require Export Basics.
```
But we have to compile Basics.v file into Basics.vo file before we can import it. 

In Linux terminal, we can generate Makefile with command
```
$ coq_makefile -f _CoqProject *.v -o Makefile
```
And then compile all the files
```
$ make
```
Or just compile Basics.v into Basics.vo
```
$ make Basics.vo
```

It is slightly different in Windows, where you need to input
```
> coqc -Q . LF Basics.v
```

`LF` is the alias of the directory when compiling.


### `induction`

Here is an example of the usage of induction proof.

```Coq
Theorem add_0_r : forall n:nat, n + 0 = n.

Proof. (* A wrong proof *)
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl.       (* ...but here we are stuck again *)
Abort.

Proof. (* Correct proof *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.  Qed.
```

To understand this phenomena, we first look back at the definiton of plus in Basics.v.

```Coq
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
```
The definition of plus operation doesn't tell us how to conclude that `n'+ 0 = n'`, so the destruct way of proof failed. 

But we can use induction to realize the proof:

```Coq
Theorem minus_n_n: forall n, minus n n = 0.
(* Example proof *)
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  
Qed.
(* Another legal proof *)
Proof.
    intro n. induction n as [| n' IHn']. 
    - (* n = 0 *) simpl. reflexivity.
    - (* n = S n' *) simpl. assumption.
Qed.
```

(`as [| n' IHn']` divide n into two circumstances, `O` and `S n'`, and give name `IHn'` to the induction hypothesis)

The first subgoal proves that for n = 0, the theorem is correct. And the second subgoal proves that if for n = n', the theorem holds water, then it also does to n = S n'. 

Structural induction is applicable to any type that is reductively defined. The first methametical induction is a special case of it on natural number.

### `assert`

Proofs within proofs

```Coq
Theorem mult_0_plus'' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
(* Plain proof *)
Proof.
  intros n m.
  rewrite add_comm. simpl. (* ==> (n + 0) * m = n * m  *)
  rewrite add_comm. simpl. (* ==> n * m = n * m *)
  reflexivity.
Qed.
(* Proof using assert tactic *)
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. } 
  rewrite -> H.
  reflexivity.
Qed.
```

And print `Set Printing Parentheses.` to see the parentheses omitted and better understand `rewrite` tactic result.

Rewrite tactic also serve to specify the elements we want to apply hypothesis to. 
```Coq
Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
(* Wrong proof *)
Proof.
  intros n m p q.
  rewrite add_comm.
  (* ==> p + q + (n + m) = m + n + (p + q)
      Obviously that is not what we want.*)
Abort.
(* Corrent proof *)
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.  
Qed.
```

<!-- As human, we generally do informal proof. -->


