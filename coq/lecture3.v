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
  : x = y -> p x -> p y
  := fun a H => match a with eq_refl => H end.

From Coq Require Import Eqdep_dec. (* UIP_refl_nat. *)

Lemma K_nat {x: nat} :
  forall (a: x = x), eq_refl = a.
Proof.
  intros H. symmetry. apply UIP_refl_nat.
Qed.

(* UIP will be explained later *)

Lemma lem2' {x y} :
  forall (e: y = S x) (a: lt x y), cast e a = L1 x.
Proof.
  destruct a.
  - destruct (K_nat e). reflexivity.
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
    destruct (K_nat e). cbn. exists a. reflexivity.
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
Definition K X := forall (x : X) (e: x = x), eq_refl = e.

Goal forall X, UIP X <-> K X.
Proof.
  intros X. split.
  - intros U x e. apply U.
  - intros H x y e. destruct e. apply H.
Qed.

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

  Variable f: forall {x y : X}, x = y -> x = y.
 
  Lemma f_tau_sigma {x y} (e: x = y) :
    tau (f e) (sigma (f eq_refl)) = e.
  Proof.
    destruct e. apply tau_sigma.
  Qed.

  Lemma Hedberg' :
    (forall x y (e e': x = y), f e = f e') -> UIP X.
  Proof.
    intros H x y e e'.
    rewrite <-(f_tau_sigma e), <-(f_tau_sigma e').
    f_equal. apply H.
  Qed.
End Hedberg.

Notation "'if' x 'is' p 'then' A 'else' B" :=
  (match x with p => A | _ => B end)
    (at level 200, p pattern,right associativity).

Theorem Hedberg X :
  (forall x y: X, x = y \/ x <> y) -> UIP X.
Proof.
  intros d.
  pose (f x y e := if d x y is or_introl e' then e' else e).
  apply Hedberg' with (f:= f).
  intros x y e e'. unfold f.
  destruct d as [e''|h]. reflexivity. destruct (h e).
Qed.


    
