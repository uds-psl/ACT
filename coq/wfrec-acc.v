From Coq Require Import Arith Lia.
From Coq Require Import Classical_Prop FunctionalExtensionality.

Section Acc.
  Variables (X: Type) (R: X -> X -> Prop).
  
  Definition elim_Acc
    : forall p, (forall x, (forall y, R y x -> p y) -> p x) -> forall x, Acc R x -> p x
    := fun p f => fix F x a := let (h) := a in f x (fun y r => F y (h y r)).

  Goal forall x, Acc R x <-> forall y, R y x -> Acc R y.
  Proof.
    split.
    - destruct 1 as [h]. exact h.
    - intros H. constructor. exact H.
  Qed.

  Definition alpha (x: nat) : Acc lt x.
  Proof.
    constructor.
    (* The topmost constructor matters for reducibility *)
    induction x as [|x IH]; intros y H.
    - exfalso. lia. 
    - constructor; intros z H1. apply IH. lia.
  Defined.
  
  Definition beta : forall x y, y < x -> Acc lt y.
  Proof.
    refine (
        fix F x := match x with
                   | 0 => fun y H => match _ : False with end
                   | S x' => fun y H => Acc_intro y (fun z H1 => F x' z _)
                   end
      ).
    - exfalso. lia.
    - lia.
  Defined.

  Definition alpha' x : Acc lt x :=
    Acc_intro x (beta x).

  Definition Project
    : forall x, Acc R x -> forall y, R y x -> Acc R y
    := fun x a => let (h) := a in h.

  Definition Destructure
    : forall x (p: Acc R x -> Prop), (forall h, p (Acc_intro x h)) -> forall a, p a
    := fun x p f a => match a with Acc_intro _ h => f h end.

  Goal forall x, Acc R x -> forall y, R y x -> Acc R y.
  Proof.
    intros x. refine (Destructure x _ (fun h => h)).
    Show Proof.
  Qed.

  Goal forall x, Acc R x -> forall y, R y x -> Acc R y.
  Proof.
    induction 1 as [x H _]. exact H.
  Qed.

  Definition progressive_pred (p: X -> Prop) :=
    forall x, p x -> exists y, p y /\ R y x.

  Definition progressive (x:X) :=
    exists p, p x /\ progressive_pred p.

  Fact Acc_progressive_disjoint x :
    Acc R x -> progressive x -> False.
  Proof.
    induction 1 as [x _ IH].
    intros (p&H1&H2).
    destruct (H2 x H1) as (y&H3&H4).
    specialize (IH y H4).
    apply IH. exists p.
    split. exact H3. exact H2.
  Qed.
  
  Fact Acc_progressive_exhaustive_XM x :
    Acc R x \/ progressive x.
  Proof.
    classical_right.
    exists (fun x => ~Acc R x). split. exact H.
    clear. intros x H.
    apply NNPP. contradict H. constructor. intros y H1.
    apply NNPP. contradict H. eauto.
  Qed.

  Fact char_wf_progressive_XM :
    well_founded R <-> ~ ex progressive.
  Proof.
    split.
    - intros H (x&H1). specialize (H x).
      eauto using Acc_progressive_disjoint.
    - intros H x.
      destruct (Acc_progressive_exhaustive_XM x) as [H1|H1].
      + exact H1.
      + contradict H. eauto.
  Qed.

  Fact wf_ind :
    well_founded R ->
    forall p, (forall x, (forall y, R y x -> p y) -> p x) -> forall x, p x.
  Proof.
    exact (fun alpha p f x => elim_Acc p f x (alpha x)).
  Qed.

  Fact char_wf_ind :
    well_founded R <->
    forall p: X -> Prop, (forall x, (forall y, R y x -> p y) -> p x) -> forall x, p x.
  Proof.
    split.
    - intros alpha p. apply wf_ind, alpha.
    - intros H. refine (H (Acc R) _). apply Acc_intro.
  Qed.
  
  Definition has_min (p: X -> Prop) :=
    exists x, p x /\ forall y, p y -> ~R y x.
  
  Fact progressive_no_min_XM p :
    progressive_pred p <-> ~ has_min p.
  Proof.
    split.
    - intros H1 (y&H2&H3). specialize (H1 y H2). firstorder.
    - intros H1 y H2. apply NNPP. firstorder.
  Qed.

  Fact char_wf_min_XM  :
    well_founded R <-> forall p, ex p -> has_min p.
  Proof.
    rewrite char_wf_progressive_XM. split.
    - intros H p (x&H1).
      apply NNPP. rewrite <- progressive_no_min_XM.  firstorder.
    - intros H (y&p&H1&H2%progressive_no_min_XM). eauto.
  Qed.
End Acc.

Arguments elim_Acc {X R p}.

Section Morphism.
  Variables (X: Type) (R: X -> X -> Prop)
            (A: Type) (S: A -> A -> Prop)
            (f: X -> A)
            (Hom: forall x y, R x y -> S (f x) (f y)).

  Fact morphism_Acc x:
    Acc S (f x) -> Acc R x.
  Proof.
    intros H.
    remember (f x) as a eqn:H1.
    induction H as [a _ IH] in x, H1 |-*.
    subst a. constructor. intros y H.
    apply (IH (f y)). apply Hom, H. reflexivity.
  Defined.
  
  Fact morphism_wf :
    well_founded S -> well_founded R.
  Proof.
    intros H x. apply morphism_Acc, H.
  Defined.
End Morphism.  

Fact inv_image {X A} (f: X -> A) {R} :
  well_founded R -> well_founded (fun x y => R (f x) (f y)).
Proof.
  apply morphism_wf with (f:=f). auto.
Defined.

Fact wf_size_induction {X A} (f: X -> A) {R} :
  @well_founded A R ->
  forall p, (forall x, (forall y, R (f y) (f x) -> p y) -> p x) -> forall x, p x.
Proof.
  intros H.
  apply wf_ind, inv_image, H.
Qed.
 
Definition pure (X: Prop) := forall a b: X, a = b.

Lemma Acc_pure_FE X R (x: X) :
  forall a b: Acc R x, a = b.
Proof.
  intros a. assert (c:= a). revert a.
  induction c as [x _ IH].
  destruct a as [h], b as [h'].
  f_equal. extensionality y. extensionality H.
  apply IH, H.
Qed.

Print Assumptions Acc_pure_FE.
Print Assumptions Acc_progressive_exhaustive_XM.

(*** Exercises *)

(* Lexical product *)
Section AccLexicalProduct.
  Variables
    (X: Type) (R1: X -> X -> Prop) (R1wf: forall x, Acc R1 x)
    (Y: Type) (R2: Y -> Y -> Prop) (R2wf: forall x, Acc R2 x).

  Definition lex (xy xy': X * Y) : Prop :=
    let (x,y) := xy in
    let (x',y') := xy' in
    R1 x x' \/ x = x' /\ R2 y y'.

  Goal forall x y, Acc lex (x,y).
  Proof.
    intros x' y'.
    induction (R1wf x') as [x' _ IHx'] in y' |-*.
    induction (R2wf y') as [y' _ IHy'].
    constructor. intros [x y] [H|[<- H]].
    - apply IHx', H.
    - apply IHy', H.
  Qed.
End AccLexicalProduct.

(* Impredicative characterization of Acc *)
Goal forall X (R: X -> X -> Prop) x,
    Acc R x <-> forall p: X -> Prop, (forall x, (forall y, R y x -> p y) -> p x) -> p x.
Proof.
  intros X R x. split.
  - intros H p H1. revert x H. apply Acc_ind.
    intros x _. apply H1.
  - intros H. specialize (H (Acc R)). apply H, Acc_intro.
Qed.

(* Acc push *)

Definition Acc_push X R (x: X) :
  Acc R x -> Acc R x
  := fun a => Acc_intro x (let (h) := a in h).

Definition wf_push3 X (R: X -> X -> Prop) :
  well_founded R ->  well_founded R.
  refine (fun f x => Acc_intro x (fun y r => Acc_intro y
                              (fun y r => Acc_intro y _))).
  refine (let (h) := f y in h).
Defined.

Definition wf_push X (R: X -> X -> Prop) :
  well_founded R ->  nat -> well_founded R.
  refine (fun f => fix F n :=
            match n with
              0 => f
            | S n' => fun x => Acc_intro x (fun y r => F n' y)
            end).
Defined.

(* Idea from Robert Krebbers, 
   https://sympa.inria.fr/sympa/arc/coq-club/2013-09/msg00034.html *)
