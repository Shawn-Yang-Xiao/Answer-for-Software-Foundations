# Software Foundations

[Online Textbook](https://softwarefoundations.cis.upenn.edu/lf-current/index.html)

[Michael Clarkson's Open Online Course (on Youtube)](https://www.youtube.com/watch?v=BGg-gxhsV4E)
[Michael Charkson's Course (on Bilibili)](https://www.bilibili.com/video/BV1kd4y1t7bw/)

[Xiong Yingfei's Course Webpage (2023 Spring)](https://xiongyingfei.github.io/SF/2023/lectures.html)

This note is used as a brief summary and supplementofr the textbook and courses.

## Logic



### `Prop` Type

Every sensible expression in Coq has an associated type. Logical claims are no exception. They all have a type `Prop`, short for **propositions**. 

### Logical Connectives

#### Conjunction

`A /\ B` represents that both `A` and `B` are true.

When a conjuncition servers as the conclusion, we can `split` it into two subgoals.
```Coq
Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.
```

When the hypothesis is a conjunction we can use following tactics to introduce them separately and explicitly:
```Coq
Lemma and_example :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
(* Explicitly derive Hn and Hm from H. *)
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.
(* Another way to introduce Hn and Hm *)
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.
```

#### Disjunction

When a pothesis is in disjunction form, we utilize following strategy:
```Coq
Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     [n = 0 \/ m = 0] *)
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *) rewrite Hn. reflexivity.
  - (* Here, [m = 0] *) rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.
```

To show that disjunction holds, it suffices to show that one of its sides holds. We use `left` and `right` tactic to do this:
```Coq
Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.
```

```Coq
Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.
```


#### Falsehood and Negation

Coq defines `~ P` as `P -> False` (`False` is defined in the standard library).

```Coq
Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.
```

```Coq
Notation "x <> y" := (~(x = y)).
```

We can unfold the definition of `not` to do the proof, like in the examples below:
```Coq
Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.  Qed.
```

#### Truth

Coq's standard library also defines True, here is a proof of trivially true, where we use the constant `I : True`.
```Coq
Lemma True_is_true : True.
Proof. apply I. Qed.
```


#### Logical Equivalence

```Coq
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
```


#### Existential Quantification

To prove a statement of the form `exist x, P`, we must show that `P` holds for some specific choice of value for `x`, known as the witness of the existential.


If we have an existential hypothesis `exist x, P` in the context, we can destruct it to obtain a witness `x` and a hypothesis stating that `P` holds of `x`.

```Coq
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note implicit [destruct] here *)
  exists (2 + m).
  apply Hm.  Qed.
```


### Programming with Propositions



