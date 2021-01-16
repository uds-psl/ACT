From Coq Require Import Arith Lia.

Section Acc.
  Variables (X: Type) (R: X -> X -> Prop).
  Inductive Acc (x: X) : Prop := AccC (h: forall y, R y x -> Acc y).
  Fact Acc_iff x :
    Acc x <-> forall y, R y x -> Acc y.
  Proof.
    split.
    - intros [h]. exact h.
    - apply AccC.
  Qed.
  Variable p: X -> Type.
  Variable F: (forall x, (forall y, R y x -> p y) -> p x).
  Definition W'
    : forall x, Acc x -> p x
    := fix f x a :=
         match a with AccC _ h => F x (fun y r => f y (h y r)) end.
  Definition wf := forall x, Acc x.
End Acc.
Arguments Acc {X}.
Arguments W' {X R p}.
Arguments wf {X}.
Definition W {X R p} H F x := @W' X R p F x (H x).

Fact lt_wf :
  wf lt.
Proof.
  hnf.
  enough (forall n x, x < n -> Acc lt x) by eauto.
  induction n as [|n IH].
  - easy.
  - intros x H. constructor. intros y H1. apply IH. lia.
Defined.

Section Lexical_product.
  Variables (X: Type) (R: X -> X -> Prop).
  Variables (Y: Type) (S: Y -> Y -> Prop).
  Definition lex (a b: X * Y) : Prop :=
    R (fst a) (fst b) \/ fst a = fst b /\ S (snd a) (snd b).
  Fact lex_wf :
    wf R -> wf S -> wf lex.
  Proof.
    intros H1 H2 [x y]. revert x y.
    refine (W H1 _). intros x IH1.
    refine (W H2 _). intros y IH2.
    constructor. intros [x' y']. unfold lex at 1. cbn. intros [H|[-> H]].
    - apply IH1, H.
    - apply IH2, H.
  Defined.
End Lexical_product.
Arguments lex {X} R {Y}.
Arguments lex_wf {X R Y S}.

Section Retract.
  Variables (X Y: Type) (R: Y -> Y -> Prop) (sigma: X -> Y).
  Definition retract (x x': X) := R (sigma x) (sigma x').
  Lemma retract_Acc :
    forall x, Acc R (sigma x) -> Acc retract x.
  Proof.
    enough (forall y, Acc R y -> forall x, y = sigma x -> Acc retract x) by eauto.
    refine (W' _). intros y IH x ->.
    constructor. unfold retract at 1. intros y H.
    eapply IH. exact H. reflexivity.
  Defined.
        
  Fact retract_wf :
    wf R -> wf retract.
  Proof.
    intros H x. apply retract_Acc, H.
  Defined.
End Retract.
Arguments retract_wf {X Y R}.

Section Transitive_closure.
  Variables (X: Type) (R: X -> X -> Prop).
  Inductive TC (x y: X) : Prop :=
  | TC1 : R x y -> TC x y
  | TC2 y' :TC x y' -> R y' y -> TC x y.
  Fact TC_wf :
    wf R -> wf TC.
  Proof.
    intros H. hnf.
    refine (W H _). intros y IH.
    constructor. intros x H1.
    destruct H1 as [H1|y' H1 H2].
    - apply IH, H1.
    - apply IH in H2. destruct H2 as [H2].
      apply H2, H1.
  Qed.                               
End Transitive_closure.

Section Successor_relation.
  Definition R_S (x y: nat) := S x = y.
  Fact R_S_wf :
    wf R_S.
  Proof.
    hnf. induction x as [|x IH].
    - constructor. unfold R_S at 1. easy.
    - constructor. unfold R_S at 1. intros y [= ->]. exact IH.
  Qed.
End Successor_relation.

(** Exercise: Prove that (TC R_S) is < on numbers *)

From Coq Require Import Classical_Prop FunctionalExtensionality.

Fact Acc_pure X (R: X -> X -> Prop) :
  forall x (a a': Acc R x), a = a'.
Proof.
  enough (forall x (a: Acc R x) (a a': Acc R x), a = a') by eauto.
  refine (W' _). intros x IH [h] [h']. f_equal.
  extensionality y. extensionality r. apply IH, r.
Qed.

Print Assumptions Acc_pure.

Section Unfolding_equation.
  Variables (X: Type) (R: X -> X -> Prop) (R_wf: wf R).
  Variable p: X -> Type.
  Variables F: forall x, (forall y, R y x -> p y) -> p x.
  Fact W_eq x :
    W R_wf F x = F x (fun y _ => W R_wf F y).
  Proof.
    unfold W. destruct (R_wf x) as [h]. cbn.
    f_equal. extensionality y. extensionality r.
    f_equal. apply Acc_pure.
  Qed.
End Unfolding_equation.
Arguments W_eq {X R R_wf p F}.

(** Euclidean division with W *)

(* Guarded step function, y pulled out as parameter *)
Definition Div (y x : nat) (h: forall x', x' < x -> nat) : nat.
Proof.
  refine (if le_lt_dec x y then 0 else S (h (x - S y) _)).
  lia. 
Defined.

Definition div x y : nat := W lt_wf (Div y) x.
Compute div 16 3.
Fact div_eq x y :
  div x y = if le_lt_dec x y then 0 else S (div (x - S y) y).
Proof.
  exact (W_eq x).
Qed.

Print Assumptions div_eq.

(** GCDs with W *)
(* Note: Pairing introduces considerable bureaucratic pain *)

Implicit Types (x y: nat) (a b: nat * nat).
Definition sigma a := fst a + snd a.

Definition GCD a : (forall b, sigma b < sigma a -> nat) -> nat.
Proof.
  (* must take h late because of dependency on a *)
  refine (match a with
          | (0, y) => fun _ => y
          | (S x, 0) => fun _ => S x
          | (S x, S y) => fun h => match (le_lt_dec x y) with
                               | left H => h (S x, y - x) _
                               | right H => h (x - y, S y) _
                               end
          end).
  all: cbn; lia.
Defined.

Definition gcd x y : nat := W (retract_wf sigma lt_wf) GCD (x,y).

Compute gcd 49 63.
      
Fact gcd_eq x y :
  gcd x y = match x, y with
            | 0, y => y
            | S x, 0 => S x
            | S x, S y => if le_lt_dec x y
                         then gcd (S x) (y - x)
                         else gcd (x - y) (S y)
            end.
Proof.
  unfold gcd. rewrite W_eq.
  destruct x. reflexivity.
  destruct y; reflexivity.
Qed.

Fact gcd_eq3 x y :
  gcd (S x) (S y) = if le_lt_dec x y
                    then gcd (S x) (y - x)
                    else gcd (x - y) (S y).
Proof.
  refine (W_eq _).
Qed.

(** Ackermann with W *)

Definition ACK a : (forall b, lex lt lt b a -> nat) -> nat.
Proof.
  (* must take h late because of dependency on a *)
  refine (match a with
          | (0, y) => fun _ => S y
          | (S x, 0) => fun h => h (x, 1) _
          | (S x, S y) => fun h => h (x, h (S x, y) _) _
          end).
  Unshelve.
  all:unfold lex; cbn; auto.
  (* Using lia here will block computation *)
Defined.

Definition ack x y : nat := W (lex_wf lt_wf lt_wf) ACK (x,y).

Compute ack 3 3. 
 
Fact ack_eq x y :
  ack x y = match x, y with
            | 0, y => S y
            | S x, 0 => ack x 1
            | S x, S y => ack x (ack (S x) y)
            end.
Proof.
  unfold ack. rewrite W_eq.
  destruct x. reflexivity.
  destruct y; reflexivity.
Qed.






