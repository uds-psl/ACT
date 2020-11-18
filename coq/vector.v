Inductive fin : nat -> Type :=
| fin1 : forall n, fin (S n)
| fin2 : forall n, fin n -> fin (S n).

Section Vector.
  Variable X : Type.

  Inductive vector : nat -> Type :=
  | Nil : vector O
  | Cons : forall n, X -> vector n -> vector (S n).
  Arguments Cons {n}.

  Definition hd {n} (v: vector (S n)) : X :=
    match v with Cons x _ => x end.

  Definition tl {n} (v: vector (S n)) : vector n :=
    match v with Cons _ v' => v' end.

  Goal forall n (v:vector (S n)), v = Cons (hd v) (tl v).
  Proof.
    refine (fun n v => match v with Cons x v' => eq_refl end).
  Qed.

  Fixpoint sub {n} (a: fin n) : vector n -> X :=
    match a with
    | fin1 _ => hd
    | fin2 n' a' => fun v => sub a' (tl v)
    end.

  Fixpoint app {m} {n} (v: vector m) (w: vector n) : vector (m + n) :=
    match v with
    | Nil => w
    | Cons x v' => Cons x (app v' w)
    end.

  Fixpoint snoc {n} (v: vector n) (x: X) : vector (S n) :=
    match v with
    | Nil => Cons x Nil
    | Cons x' v' => Cons x' (snoc v' x)
    end.
  
  Fixpoint rev {n} (v: vector n) : vector n :=
    match v with
    | Nil => Nil
    | Cons x v' => snoc (rev v') x
    end.

  Fact rev_snoc n (v: vector n) x :
    rev (snoc v x) = Cons x (rev v).
  Proof.
    induction v as [|n' x' v' IH]; cbn.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  Goal forall n (v: vector n), rev (rev v) = v.
  Proof.
    induction v as [|n' x v' IH]; cbn.
    - reflexivity.
    - rewrite rev_snoc, IH. reflexivity.
  Qed.

  Goal forall v: vector 0, v = Nil.
  Proof.
    refine (fun v => match v with Nil => eq_refl end).
  Qed.
  
  Goal forall n (v: vector (S n)), { x & { v' | v = Cons x v' }}.
  Proof.
    refine (fun n v => match v with Cons x v' => _ end).
    exists x, v'. reflexivity.
  Qed.

  Fixpoint vec2list (v: list X) : vector (length v) :=
    match v with
    | nil => Nil
    | cons x v' => Cons x (vec2list v')
    end.

  Fixpoint list2vec {n} (v : vector n) : list X :=
    match v with
    | Nil => nil
    | Cons x v' => cons x (list2vec v')
    end.

  Fact inv_eq v :
    list2vec (vec2list v) = v.
  Proof.
    induction v as [|x v]; cbn.
    - reflexivity.
    - congruence.
  Qed.

  From Equations Require Import Equations.
  Derive Signature for vector.
  Derive NoConfusionHom for vector.
         
  Fact vector_inj n x x' (v v': vector n) :
    Cons x v = Cons x' v' -> x = x' /\ v = v'.
  Proof.
    depelim v.
    - depelim v'. intros [= <-]. auto.
    - depelim v'. intros H.
      depelim H. easy.
  Qed.

  Definition eq_dec X := forall x x': X, (x = x') + (x <> x').

  Definition vector_eq n :
    eq_dec X -> eq_dec (vector n).
  Proof.
    intros H v1 v2. revert v2.
    induction v1.
    - refine (fun v2 => match v2 with Nil => _ end).
      left. reflexivity.
    - intros v2. depelim v2.
      specialize (H x x0) as [<-|H].
      + destruct (IHv1 v2) as [<-|H1].
        * now left.
        * right. intros [_ <-]%vector_inj. easy.
      + right. intros [<- _]%vector_inj. easy.
  Defined.

  Print Assumptions vector_eq.
   
  Definition cast {m n} (v: vector (m + S n)) : vector (S (m + n)).
    rewrite plus_n_Sm. exact v. (* lemma doesn't compute *)
  Defined.

  Fact snoc_app m n (v: vector m) (w: vector n) x :
      snoc (app v w) x = cast (app v (snoc w x)).
  Proof.
    induction v as [|n' x' v' IH] in n,w |-*.
    - cbn.
  Admitted.
  
End Vector.

Arguments Nil {X}.
Arguments Cons {X n}.
Arguments hd {X n}.
Arguments tl {X n}.
Arguments rev {X n}.

Compute rev (Cons 5 (Cons 2 Nil)).
