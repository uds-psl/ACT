From Coq Require Import Arith Lia.

Inductive lt (x : nat) : nat -> Type :=
| L1 : lt x (S x)
| L2 : forall y, lt x y -> lt x (S y).

Goal forall x y (a b: lt x y), a = b.
Proof.
  induction a.
  - Fail destruct b.
Abort.

From Equations Require Import Equations. (* depelim *)
Set Equations With UIP.
Derive Signature for lt.

Lemma lem1 x y :
  lt x y -> x < y.
Proof.
  induction 1; lia.
Qed.

Goal forall x y (a b: lt x y), a = b.
Proof.
  induction a.
  - depelim b.
    + reflexivity.
    + exfalso. apply lem1 in b. lia.
  - depelim b.
    + exfalso.
      Fail apply lem1 in a. clear IHa.
      apply lem1 in a. lia.
    + f_equal. apply IHa.
Qed.

(* Understand why destruct doesn't work, explain depelim *)

Definition cast {X} {x y: X} {p: X -> Type}
  :  x = y -> p x -> p y
  := fun e a => match e with eq_refl => a end.

From Coq Require Import Eqdep_dec. (* UIP_refl_nat. *)
Check UIP_refl_nat : forall (x: nat) (e: x = x), e = eq_refl.
(* UIP will be explained later *)

Lemma lem2' {x y} :
  forall (e: y = S x) (a: lt x y), cast e a = L1 x.
Proof.
  destruct a.
  - rewrite (UIP_refl_nat _ e). reflexivity.
  - exfalso. apply lem1 in a. lia.
Qed.

Lemma lem2 x :
  forall a: lt x (S x), a = L1 x.
Proof.
  exact (lem2' eq_refl).
Qed.

Lemma lem3' {x y z} :
  forall (e: z = S y) (a : lt x z),
    x <> y -> { b | cast e a = L2 x y b }.
Proof.
  destruct a; intros H.
  - exfalso. congruence.
  - assert (y = y0) as <- by congruence.
    exists a. rewrite (UIP_refl_nat _ e). reflexivity.
Qed.

Lemma lem3 {x y} :
  forall a : lt x (S y),  x <>  y -> { b | a = L2 x y b }.
Proof.
  intros a e. apply (lem3' eq_refl), e.
Qed.

Goal forall x y (a b: lt x y), a = b.
Proof.
  induction a.
  - symmetry. apply lem2.
  - intros b. destruct (lem3 b) as [a' ->].
    + clear IHa b. apply lem1 in a. lia.
    + f_equal. apply IHa.
Qed.

(* Hedberg's Theorem *)

Definition UIP X := forall (x y: X) (e e': x = y), e = e'.
Definition UIP' X := forall (x : X) (e: x = x), e = eq_refl.

Goal forall X, UIP X <-> UIP' X.
Proof.
  intros X. split.
  - intros U x e. apply U.
  - intros H x y e. destruct e'. apply H.
Qed.

Notation "'if' x 'is' p 'then' A 'else' B" :=
  (match x with p => A | _ => B end)
    (at level 200, p pattern,right associativity).

Section Hedberg.
  Variable X: Type.
  Implicit Types x y z: X.
  
  Definition sigma {x y}
    : x = y -> y = x
    := fun e => cast (p:= fun z => z = x) e eq_refl.

  Definition tau {x y z}
    : x = y -> y = z -> x = z
    := fun e => cast e (fun e => e).

  Lemma tau_sigma x y (e: x = y) :
    tau e (sigma e) = eq_refl.
  Proof.
    destruct e. reflexivity.
  Qed.

  Goal forall x y (e: x = y), sigma (sigma e) = e.
  Proof.
    intros x y []. reflexivity.
  Qed.

  Goal forall x y z a (e1: x = y) (e2: y = z) (e3: z = a),
      tau e1 (tau e2 e3) = tau (tau e1 e2) e3.
  Proof.
    intros x y z a [] [] []. reflexivity.
  Qed.

  Variable f: forall {x y }, x = y -> x = y.
  Variable f_eq: forall x y (e e': x = y), f e = f e'.

  Lemma Hedberg' : UIP X.
  Proof.
    intros x y.
    assert (f_eq1: forall e: x = y,  tau (f e) (sigma (f eq_refl)) = e).
    { destruct e. apply tau_sigma. }
    intros e e'.
    rewrite <-(f_eq1 e), <-(f_eq1 e').
    f_equal. apply f_eq.
  Qed.
End Hedberg.

Theorem Hedberg X :
  (forall x y: X, x = y \/ x <> y) -> UIP X.
Proof.
  intros d.
  pose (f x y e := if d x y is or_introl e' then e' else e).
  apply Hedberg' with (f:= f).
  intros x y e e'. unfold f.
  destruct d as [e''|h]. reflexivity. destruct (h e).
Qed.


    
