# Software Foundations

[Online Textbook](https://softwarefoundations.cis.upenn.edu/lf-current/index.html)

[Michael Clarkson's Open Online Course (on Youtube)](https://www.youtube.com/watch?v=BGg-gxhsV4E)
[Michael Charkson's Course (on Bilibili)](https://www.bilibili.com/video/BV1kd4y1t7bw/)

[Xiong Yingfei's Course Webpage (2023 Spring)](https://xiongyingfei.github.io/SF/2023/lectures.html)

This note is used as a brief summary and supplementofr the textbook and courses.


## Tactics

### The `apply` tactic with `symmetry ` and `transitivity`

#### `apply`
When encountering situations where the goal to be proved is exactly the same as some hypothesis in the context or some previously proved lemma, we can use `apply` tactic instead of the `rewrite` & `reflexivity` we previously used.

```Coq
Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.
(** n, m : nat
    eq : n = m
    ______________________________________(1/1)
    n = m
*)
  apply eq.  Qed.
```


The `apply` tactic also works with conditional hypothesis. Like `eq2: n = m -> [n;o] = [m;p]` in the following theorem.
```Coq
Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.
```

#### `symmetry`
The `symmetry` tactic exchange left hand side with right hand side. It is useful in the following example.
```Coq
Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.
  symmetry. apply H.  Qed.
```

#### `transitivity`
Sometimes we need the help of `transitivity` tactic to utilize `apply`:
```Coq
Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]). (* or try transitivity [c;d]. *)
  apply eq1. apply eq2.   Qed.
```

### The `injection` and `discriminate` Tactics

#### Injective property and tactic

Take the example of type `nat`:
```Coq
Inductive nat : Type :=
  | O
  | S (n : nat).
```

Injective means that $S n = S m => n = m$.

Here is an example of the `injective` tactic.
```Coq
Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  (* WORKED IN CLASS *)
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.
```


#### Disjoint Property and The `discriminate` Tactic
Disjoint means that, two terms beginning with different constructors can never be equal. For example, $S n \neq 0$ for all $n \in nat$.

So any time we are given such contradictary assumptions, any conclusion are thus satisfied, like the following example:
```Coq
Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra. discriminate contra. Qed.
```


### Using Tactics on Hypotheses

The tactic `simpl in H` performs simplification on the hypothesis `H` in the context.

Similarly we have `apply H1 in H2` and `symmetry in H`.

```Coq
Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H. symmetry in H.
  apply H.  Qed.
```



### The `generalize dependent` Tactic

To illustrate the need of the tactic, I first show the rule of `intros`, that all variables and hypotheses will be introduced according to its sequance of appearance.

Here is an example of a failed proof:

```Coq
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros x y z l j contra.
  Fail discriminate contra.
```
That is because `x` corresponds to `X` which is a type, `y` `z` and `l` corresponts the three `X` type variable,  and that `j` and `contra` corresponds to the two lists. So we cannot just skip some variable unintroduced.

But sometimes we do need free variables that haven't been introduced. Like in the following theorem:
```Coq
Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
```

Then we can use `generalize dependent` tactic to temporarily free variable n.

```Coq
Proof.
  intros n m.
  (* [n] and [m] are both in the context *)
  generalize dependent n.
  (* Now [n] is back in the goal and we can do induction on
     [m] and get a sufficiently general IH. *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal.
Qed.
```

### Unfolding Definitions

The `simpl` tactic will only unfold `match` or `fixpoint` definition, not `Definition` clause. so we need `unfold` tactic to do this job.


And it comes along with some new example of `destruct` tactic. 
```Coq
Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity.  Qed.
```

Here is another example of the `destrct` tactic being applied to compound expressions:
```Coq
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b. 
  destruct b eqn:H1.
  - destruct (f b) eqn:H2.
    + rewrite H1 in H2. rewrite H2. rewrite H2. rewrite H2. reflexivity.
    + rewrite H1 in H2. rewrite H2. destruct (f false) eqn:E3.
        rewrite H2. reflexivity. 
        rewrite E3. reflexivity.
  - destruct (f b) eqn:H2.
    + rewrite H1 in H2. rewrite H2. destruct (f true) eqn:E3.
        rewrite E3. reflexivity. 
        rewrite H2. reflexivity.
    + rewrite H1 in H2. rewrite H2. rewrite H2. rewrite H2. reflexivity.
Qed.
```




