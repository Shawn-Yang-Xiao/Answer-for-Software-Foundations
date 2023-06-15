# Software Foundations

[Online Textbook](https://softwarefoundations.cis.upenn.edu/lf-current/index.html)

[Michael Clarkson's Open Online Course (on Youtube)](https://www.youtube.com/watch?v=BGg-gxhsV4E)
[Michael Charkson's Course (on Bilibili)](https://www.bilibili.com/video/BV1kd4y1t7bw/)

[Xiong Yingfei's Course Webpage (2023 Spring)](https://xiongyingfei.github.io/SF/2023/lectures.html)

This note is used as a brief summary and supplementofr the textbook and courses.


## Poly

### Polymorphism

Types that can take on many forms. 

Ad-hoc Polymorphism

Parametric Polymorphism

Subtyping Polymorphism

#### Omit Type Argument

```Coq
Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).
```
The type list is thus parameterized on another type X.


When we want to avoid typing the type, and let Coq to infer it. We can set:
```Coq
Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.
```

#### Catesian Product

```Coq
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
(** (The annotation [: type_scope] tells Coq that this abbreviation
    should only be used when parsing types, not when parsing
    expressions.  This avoids a clash with the multiplication
    symbol.) *)
```


### Higher-Order Functions

Functions that manipulate other functions are often called **higher-order** functions.

For example, we have `filter` function
```Coq
Fixpoint filter {X:Type} (test: X->bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.
```

#### Functions That Construct Functions

Functions that return the given functor whatever the argument is.
```Coq
Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.
```

This function seems useless, but there is a usage of higher-order functions, let's now mock function currying:
```Coq
Definition plus3 := plus 3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity. Qed.
```



### Anonymous Functions

Just like $\lambda$ function in Haskell, the difference is that Coq use `fun` instead of `\` to denote this.

```Coq
Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.
```

### Map & Fold

`map` is also a function that is useful and interesting:
```Coq
Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.
```

Take `None` value into consideration, we define:
```Coq
Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.
```

And you can't miss `fold`, another fantastic function:
```Coq
Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.
```




