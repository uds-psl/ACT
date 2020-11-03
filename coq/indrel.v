From Coq Require Import Arith Lia List.
From Equations Require Import Equations.  (* tactic depelim *)
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).


(** We do most proofs with an hand-written eliminator and in addition
    with the tactics destruct, induction, and depelim.  In practice,
    using the tactics is clearer and more convenient.  *)

(*** Even *)

Inductive even: nat -> Type :=
| evenB: even 0
| evenS: forall n, even n -> even (S (S n)).

Goal even 4.
Proof.
  constructor. constructor. constructor.
  Show Proof.
Qed.

Goal even 6.
Proof.
  repeat constructor.
  Show Proof.
Qed.

Fact even_complete k :
  even (2*k).
Proof.
  induction k as [|k IH].
  - apply evenB.
  - replace (2 * S k) with (S (S (2*k))) by lia.
    apply evenS, IH.
Qed.


Fixpoint D n (a: even n) : nat :=
  match a with
  | evenB => 0
  | evenS n' a' => S (D n' a')
  end.

Definition even_elim (p: forall n, even n -> Type)
  : p 0 evenB ->
    (forall n a, p n a -> p (S (S n)) (evenS n a)) ->
    forall n a, p n a
  := fun f1 f2 => fix F _ a :=
       match a with
       | evenB => f1
       | evenS n' a' => f2 n' a' (F n' a')
       end.

Goal forall n a, n = 2 * D n a.
Proof.
  apply even_elim.
  - reflexivity.
  - intros n a IH. cbn [D]. lia.
Qed.

Goal D = even_elim (fun _ _ => nat) 0 (fun _ _ => S).
Proof.
  cbv. reflexivity.
Qed.

Fact even_elim_index (p: nat -> Type) :
  p 0 ->
  (forall n, even n -> p n -> p (S (S n))) ->
  forall n, even n -> p n.
Proof.
  exact (fun f1 f2 => fix F _ a :=
           match a with
           | evenB => f1
           | evenS n' a' => f2 n' a' (F n' a')
           end).
Qed.

Goal forall n, even n -> { k | 2 * k = n }.
Proof.
  apply even_elim_index.
  - exists 0. reflexivity.
  - intros n _ [k IH]. exists (S k). lia.
Qed.

Goal forall n, even n -> { k | 2 * k = n }.
Proof.
  induction 1 as [|n _ [k IH]].
  - exists 0. reflexivity.
  - exists (S k). lia.
Qed.

(** Inversion laws *)

Goal even 1 -> False.
Proof.
  enough (forall x, even x -> x = 1 -> False) by eauto.
  refine (even_elim_index _ _ _).
  - intros [=].
  - intros ? ? ? [=].
Qed.
  
Goal even 1 -> False.
Proof.
  enough (forall n, even n -> n = 1 -> False) by eauto.
  destruct 1 as [|n _].
  - intros [=].
  - intros [=].
Qed.

  
Goal even 1 -> False.
Proof.
  enough (forall n, even n -> match n with 1 => False | _ => True end) as H.
  - intros H1%H. exact H1.
  - destruct 1; exact I.
Qed.

(* Exploiting conversion *)

Goal even 1 -> False.
Proof.
  refine (even_elim_index
            (fun n => match n with 1 => False | _ => True end)
            I
            (fun _ _ _ => I)
            1).
Qed.

(* Using matches with return clauses *)

Goal even 1 -> False.
Proof.
  refine (fun a => match a in even n return match n with 1 => False | _ => True end
          with evenB => I | evenS _ _ => I end).
Qed.

(* Using the match compiler *)

Goal even 1 -> False.
Proof.
  refine (fun a => match a with end).
Qed.

(* Using tactic depelim from Equations *)

Derive Signature for even.

Goal even 1 -> False.
Proof.
  intros H. depelim H.
Qed.

(* The other inversion law *)

Goal forall n, even (S (S n)) -> even n.
Proof.
  enough (forall n, even n -> forall n', n = S(S n') -> even n') by eauto.
  refine (even_elim_index _ _ _).
  - intros n [=].
  - intros ? H _ ? [= <-]. exact H.
Qed.
  
Goal forall n, even (S (S n)) -> even n.
Proof.
  enough (forall n, even n -> forall n', n = S(S n') -> even n') by eauto.
  destruct 1 as [|n H].
  - intros n [=].
  - intros ? [= <-]. exact H.
Qed.

Goal forall n, even (S (S n)) -> even n.
Proof.
  refine (fun n => even_elim_index
                  (fun n => match n with S (S n) => even n | _ => True end)
                  I
                  (fun n a _ => a)
                  (S (S n))).
Qed.

Goal forall n, even (S (S n)) -> even n.
Proof.
  refine (fun n' a => match a in even n return
                         match n with S (S n) => even n | _ => True end
                   with
                   | evenB => I
                   | evenS n a => a
                   end).
Qed.

Goal forall n, even (S (S n)) -> even n.
Proof.
  refine (fun n a => match a with evenS n' a' => a' end).
Qed.

Goal forall n, even (S (S n)) -> even n.
Proof.
  intros n H. depelim H. exact H.
Qed.

(*** Inductive Equality *)

Module Eq.
  Inductive eq (X: Type) (x: X) : X -> Prop :=
  | Q : eq X x x.
  
  Fact eq_elim (X: Type) (x: X) (p: X -> Type) :
    p x -> forall y, eq X x y -> p y.
  Proof.
    exact (fun f y a => match a with Q _ _ => f end).
  Qed.

  Goal forall X (x y: X), eq X x y <-> x = y.
  Proof.
    intros X x y. split.
    - revert y. apply eq_elim. reflexivity.
    - intros H. rewrite H. apply Q.
  Qed.

  Goal forall X (x y: X), eq X x y <-> x = y.
  Proof.
    intros X x y. split.
    - destruct 1 as []. reflexivity.
    - intros H. rewrite H. apply Q.
  Qed.

  Goal forall X (x y: X) (p: X -> Type), x = y -> p x -> p y.
  Proof.
    intros X x y p H.
    cut (eq X x y).
    - clear H. revert y.
      refine (eq_elim X x _ _).
      auto.
    - rewrite H. apply Q.
  Qed.

  Goal forall X (x y: X) (p: X -> Type), x = y -> p x -> p y.
  Proof.
    intros X x y p H.
    cut (eq X x y).
    - clear H.
      destruct 1 as []. auto.
    - rewrite H. apply Q.
  Qed.
  
  Definition K : Prop := forall X x (p: eq X x x -> Prop), p (Q X x) -> forall a, p a.
  Definition PI : Prop := forall (P: Prop) (a b: P), eq P a b.

  Goal PI -> K.
  Proof.
    intros H X x p H1 a.
    generalize (H _ (Q X x) a).
    apply eq_elim. exact H1.
  Qed.

  Goal PI -> K.
  Proof.
    intros H X x p H1 a.
    generalize (H _ (Q X x) a).
    destruct 1 as []. exact H1.
  Qed.
  
End Eq.

(*** Order *)

Inductive L (x: nat) : nat -> Type :=
| L1: L x (S x)
| L2: forall y z, L x y -> L y z -> L x z.

Goal L 3 7.
Proof.
  apply L2 with 5.
  - apply L2 with 4; apply L1.
  - apply L2 with 6; apply L1.
    Show Proof.
Qed.
  
Goal L 3 7.
Proof.
  eauto using L.
  Show Proof.  
Qed.

Goal forall x y, x < y -> L x y.
Proof.
  intros x y H.
  induction y as [|y IH].
  - exfalso; lia.
  - assert (x <= y) as [H1|<-]%le_lt_eq_dec by lia.
    + eapply L2. apply IH, H1. apply L1.
    + apply L1.
Qed.

Fact L_elim_index (p: nat -> nat -> Type) :
  (forall x, p x (S x)) ->
  (forall x y z, p x y -> p y z -> p x z) ->
  forall x y, L x y -> p x y.
Proof.
  exact (fun f1 f2 => fix F x _ a :=
           match a with
             L1 _ => f1 x
           | L2 _ y z a1 a2 => f2 x y z (F x y a1) (F y z a2)
           end).
Qed.

Goal forall x y, L x y -> x < y.
Proof.
  apply L_elim_index.
  - lia.
  - lia.
Qed.

Goal forall x y, L x y -> x < y.
Proof.
  induction 1 as [x |x y z _ IH1 _ IH2].
  - lia.
  - lia.
Qed.

(*** GCD *)

Definition size_rec {X: Type} (sigma: X -> nat) {p: X -> Type} :
  (forall x, (forall y, sigma y < sigma x -> p y) -> p x) ->
  (forall x, p x).
Proof.
  intros F.
  enough (forall n x, sigma x < n -> p x) as H.
  { intros x. apply (H (S (sigma x))). lia. }
  induction n as [|n IH]; intros x H.
  - exfalso. lia.
  - apply F. intros y H1. apply IH. lia.
Defined.

Definition size_rec2 {X Y: Type} (sigma: X -> Y -> nat) {p: X -> Y -> Type} :
  (forall x y, (forall x' y', sigma x' y' < sigma x y -> p x' y') -> p x y) ->
  (forall x y, p x y).
Proof.
  intros F.
  enough (forall '(x,y), p x y) as H.
  { intros x y. apply (H (x,y)). } 
  refine (size_rec (fun '(x,y) => sigma x y) (fun '(x,y) IH => _)). cbn in IH.
  apply F. intros x' y' H. apply (IH (x',y')), H.
Defined.

Definition functional (p: nat -> nat -> nat -> Prop) :=
  forall x y z z', p x y z -> p x y z' -> z = z'.

Definition respects f (p: nat -> nat -> nat -> Prop) :=
  forall x y, p x y (f x y).

Definition agree f (p: nat -> nat -> nat -> Prop) :=
  forall x y z, p x y z <-> f x y = z.

Fact fun_respects_agree f p :
  functional p -> respects f p -> agree f p.
Proof.
  intros H1 H2 x y z. split.
  - specialize (H2 x y). specialize (H1 x y (f x y) z). auto.
  - intros <-. apply H2.    
Qed.

Definition Gamma f x y :=
  match x, y with
  | 0, y => y
  | S x, 0 => S x
  | (S x), (S y) => if le_lt_dec x y then f (S x) (y - x) else f (x - y) (S y)
  end.

Definition Gamma_sat f := forall x y, f x y = Gamma f x y.

Inductive G: nat -> nat -> nat -> Prop :=
| G1: forall y, G 0 y y
| G2: forall x, G (S x) 0 (S x)
| G3: forall x y z, x <= y -> G (S x) (y - x) z -> G (S x) (S y) z
| G4: forall x y z, y < x -> G (x - y) (S y) z -> G (S x) (S y) z.

Fact G_Gamma f :
  agree f G -> Gamma_sat f.
Proof.
  intros H x y.
  destruct x.
  { cbn. apply H. apply G1. }
  destruct y.
  { cbn. apply H. apply G2. }
  cbn. apply H.
  destruct (le_lt_dec x y) as [H1|H1].
  + apply G3. lia. apply H. reflexivity.
  + apply G4. lia. apply H. reflexivity.
Qed.
 
Fact GF :
  forall x y, { z | G x y z }.
Proof.
  refine (size_rec2 (fun x y => x + y) _).
  intros x y IH.
  destruct x.
  { exists y. apply G1. }
  destruct y.
  { exists (S x). apply G2. }
  destruct (le_lt_dec x y) as [H2|H2].
  - specialize (IH (S x) (y - x)) as [z IH]. lia.
    exists z. apply G3. lia. exact IH.
  - specialize (IH (x - y) (S y)) as [z IH]. lia.
    exists z. apply G4. lia. exact IH.
Defined.

Definition g x y := proj1_sig (GF x y).

Derive Signature for G.

Fact G_fun :
  functional G.
Proof.
  intros x y z z'.
  induction 1 as [y|x|x y z H _ IH|x y z H _ IH].
  all: intros H1; depelim H1.
  all: try (exfalso; lia).
  all: auto 2.
Qed.

Fact g_agrees : agree g G.
Proof.
  hnf.
  apply fun_respects_agree.
  - hnf. apply G_fun.
  - intros x y. unfold g. destruct GF as [z H]. exact H.
Qed.

Fact Gamma_g :
  Gamma_sat g.
Proof.
  apply G_Gamma, g_agrees.
Qed.

Fact Gamma_sat_respect f :
  Gamma_sat f -> respects f G.
Proof.
  intros H. hnf.
  refine (size_rec2 (fun x y => x + y) _).
  intros x y IH.
  destruct x.
  { rewrite H. cbn. apply G1. }
  destruct y.
  { rewrite H. cbn. apply G2. }
  rewrite H. cbn.
  destruct (le_lt_dec x y) as [H1|H1].
  - apply G3. lia. apply IH. lia.
  - apply G4. lia. apply IH. lia.
Qed.

Fact Ginv1 y z :
  G 0 y z -> z = y.
Proof.
  intros H. inversion H; subst. reflexivity.
Qed.
  
Fact Ginv2 x z :
  G (S x) 0 z -> z = S x.
Proof.
  intros H. inversion H; subst. reflexivity.
Qed.

Fact Ginv3 x y z :
  x <= y -> G (S x) (S y) z -> G (S x) (y - x) z.
Proof.
  intros H H1.
  enough (forall a b, G a b z -> a = S x -> b = S y -> G (S x) (y - x) z) by eauto.
  destruct 1.
  - intros [=].
  - intros _ [=].
  - intros [= ->] [= ->]. assumption.
  - intros [= ->] [= ->]. exfalso. lia.
Qed.

Fact Ginv4 x y z :
  x > y -> G (S x) (S y) z -> G (x - y) (S y) z.
Proof.
  intros H1 H2. inversion H2; subst.
  - exfalso. lia.
  - assumption.
Qed.

(*** Post Problem *)

Module Post.
  Inductive char := a | b.
  Definition string : Type := list char.
  Definition card : Type := string * string.
  Definition deck : Type := list card.

  Inductive post (D: deck) : string -> string -> Prop :=
  | post1 : forall A B, (A,B) el D -> post D A B
  | post2 : forall A B A' B', (A,B) el D -> post D A' B' -> post D (A ++ A') (B ++ B').

  Definition D : deck := [([a], []); ([b],[a]); ([], [b;b])].

  Goal post D [b;b;a;a] [b;b;a;a].
  Proof.
    refine (post2 _ [] [b;b] [b;b;a;a] [a;a] _ _).
    { cbn; auto. }
    refine (post2 _ [b] [a] [b;a;a] [a] _ _).
    { cbn; auto. }
    refine (post2 _ [b] [a] [a;a] [] _ _).
    { cbn; auto. }
    refine (post2 _ [a] [] [a] [] _ _).
    { cbn; auto. }
    refine (post1 _ [a] [] _).
    { cbn; auto. }
  Qed.
End Post.


(*** Context-free Grammar *)

Module Grammar.
  Definition terminal := nat.
  Definition string := list terminal.
  Definition nonterminal := nat.
  Inductive rule : Type :=
  | R1 (gamma: nonterminal) (a: terminal)
  | R2 (a: nonterminal) (gamma1: nonterminal) (gamma2: nonterminal).
  Definition grammar := list rule.

  Inductive sentence (G: grammar) (gamma: nonterminal) : string -> Prop :=
  | sentence1 : forall a, R1 gamma a el G  -> sentence G gamma [a]
  | sentence2 : forall gamma1 gamma2 A1 A2,
      R2 gamma gamma1 gamma2 el G ->
      sentence G gamma1 A1 ->
      sentence G gamma2 A2 ->
      sentence G gamma (A1 ++ A2).
  
End Grammar.


(** New commands used used: 
    From Equations Require Import Equations.
    Derive Signature for <ind_pred>.
*)
(** New tactics used: 
    constructor, depelim 
*)
