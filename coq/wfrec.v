From Coq Require Import Arith Lia.

Section Acc.
  Variables (X: Type) (R: X -> X -> Prop).
  Inductive Acc (x: X) : Prop := AccC (h: forall y, R y x -> Acc y).
  Definition wf := forall x, Acc x.
  Variable alpha: wf.
  Variable (p: X -> Type).
  Variable F: (forall x, (forall y, R y x -> p y) -> p x).
  Definition W'
    : forall x, Acc x -> p x
    := fix f x a :=
         match a with AccC _ h => F x (fun y r => f y (h y r)) end.
  Definition W x := W' x (alpha x).
End Acc.
Arguments Acc {X}.
Arguments W' {X R p}.
Arguments wf {X}.
Arguments W {X R} alpha {p}.

(** Successor relation is well-founded *)

Module Successor.
  Definition SR (y x: nat) := S y = x.
  Goal forall x, Acc SR x.
  Proof.
    induction x as [|x IH].
    - constructor. unfold SR at 1. intros y [=].
    - constructor. unfold SR at 1. intros y [= ->]. exact IH.
  Qed.
End Successor.

(** Transitive closure preserves well-foundedness *)

Section TC.
  Variables (X: Type) (R: X -> X -> Prop).
  Inductive TC (x y: X) : Prop :=
  | TC1 : R x y -> TC x y
  | TC2 y' :TC x y' -> R y' y -> TC x y.
  Goal wf R -> wf TC.
  Proof.
    intros H. hnf.
    refine (W H _). intros y IH.
    constructor. intros x H1.
    destruct H1 as [H1|y' H1 H2].
    - apply IH, H1.
    - apply IH in H2. destruct H2 as [H2].
      apply H2, H1.
  Qed.                               
End TC.

(** Exercise: Prove that (TC SR) is < on numbers *)
