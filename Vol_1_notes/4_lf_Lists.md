# Software Foundations

[Online Textbook](https://softwarefoundations.cis.upenn.edu/lf-current/index.html)

[Michael Clarkson's Open Online Course (on Youtube)](https://www.youtube.com/watch?v=BGg-gxhsV4E)
[Michael Charkson's Course (on Bilibili)](https://www.bilibili.com/video/BV1kd4y1t7bw/)

[Xiong Yingfei's Course Webpage (2023 Spring)](https://xiongyingfei.github.io/SF/2023/lectures.html)

This note is used as a brief summary and supplement of the textbook and courses.

## Lists

### Pairs

We define the pair of natural numbers. (Cartesian product)
```Coq
Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).
```


Then comes a new usage of `destruct`:

```Coq
Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
(* Wrong proof *)
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.
(* Correct proof *)
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. 
Qed.
```


### Lists of Natural Numbers

```Coq
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
```

The concatenation operation of `natlist` is then defined as follows.
```Coq
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
```


Then comes the usage of `destruct`:
```Coq
Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.  
Qed.
```

And of `instruction`
```Coq
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.  
Qed.
```


### `Search` Command

```Coq

(** Display a list of all theorems involving [rev]:  *)
Search rev.

(** Use a pattern to search for all theorems involving the equality of two additions: *)
Search (_ + _ = _ + _).

(** Search inside a particular module as a restriction: *)
Search (_ + _ = _ + _) inside Induction.

(** Make the search more precise by using variables in the search pattern instead of wildcards: *)
Search (?x + ?y = ?y + ?x).
```



### Options

```Coq
Inductive natoption : Type :=
  | Some (n : nat)
  | None.
```

Recall Haskell's `Maybe`, `Nothing` and `Just`.


### Partial Maps

```Coq
Inductive id : Type :=
  | Id (n : nat).

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map) (x : id) (value : nat) : partial_map :=
  record x value d.
```



