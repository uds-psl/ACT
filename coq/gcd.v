From Coq Require Import Arith Lia.
From Equations Require Import Equations.  (* tactic depelim *)
Ltac refl := reflexivity.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Notation pi1 := projT1.
Notation pi2 := projT2.
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
                
(*** Preliminaries *)

Implicit Types
         (x y z: nat)
         (f: nat -> nat -> nat)
         (p: nat -> nat -> nat -> Prop).

Definition functional p :=
  forall x y z z', p x y z -> p x y z' -> z = z'.

Definition total p :=
  forall x y, exists z, p x y z.

Definition subsumed p p' :=
  forall x y z, p x y z -> p' x y z.

Definition agreep p p' :=
  subsumed p p' /\ subsumed p' p.

Definition agreef f f' :=
  forall x y, f x y = f' x y.

Definition respects f p :=
  forall x y, p x y (f x y).

Definition agree f p :=
  forall x y z, p x y z <-> f x y = z.

Definition rel f :=
  fun x y z => f x y = z.

Fact agreep_sym p p' :
  agreep p p' -> agreep p' p.
Proof.
  firstorder.
Qed.

Fact agreep_trans p1 p2 p3 :
  agreep p1 p2 -> agreep p2 p3 -> agreep p1 p3.
Proof.
  firstorder.
Qed.

Fact total_fun_agree p p' :
  total p -> functional p' -> subsumed p p' -> agreep p p'.
Proof.
  intros H1 H2 H3. split. exact H3.
  intros x y z H4.
  specialize (H1 x y) as [z' H1].
  enough (z = z') as -> by auto.
  apply H3 in H1. eapply H2; eassumption.
Qed.

Fact fun_respects_agree f p :
  functional p -> respects f p -> agree f p.
Proof.
  intros H1 H2 x y z. split.
  - specialize (H2 x y). specialize (H1 x y (f x y) z). auto.
  - intros <-. apply H2.    
Qed.

Fact rel_agree f :
  agree f (rel f).
Proof.
  apply fun_respects_agree; cbv; congruence.
Qed.

Fact rel_fun f :
  functional (rel f).
Proof.
  cbv. congruence.
Qed.

Fact rel_agreef f f' :
  subsumed (rel f) (rel f') <-> agreef f f'.
Proof.
  split.
  - intros H x y. symmetry. apply H. reflexivity.
  - intros H x y. unfold rel. intros z <-. symmetry.  apply H.
Qed.

(*** GCD predicates *)
    
Definition gcd_pred p : Prop :=
  (forall y, p 0 y y) /\
  (forall x y z, p x y z -> p y x z) /\
  (forall x y z, x <= y ->  p x (y - x) z -> p x y z).

Definition gcd_rec_sym (p: nat -> nat -> Type) :
  (forall y, p 0 y) ->
  (forall x y, p y x -> p x y) ->
  (forall x y, x <= y -> p x (y - x) -> p x y) ->
  forall x y, p x y.
Proof.
  intros e1 e2 e3.
  apply (size_rec2 (fun x y => x + y)).
  intros x y IH.
  destruct x.
  - apply e1.
  - destruct y.
    + apply e2,e1.
    + destruct (le_lt_dec x y) as [H|H].
      * apply e3. lia. apply IH. lia.
      * apply e2,e3. lia. apply IH. lia.
Qed.

Fact gcd_pred_total p :
  gcd_pred p -> forall x y, Sigma z, p x y z.
Proof.
  intros (H11&H12&H13).
  apply gcd_rec_sym.
  - intros y. exists y. apply H11.
  - intros x y [z IH]. exists z. apply H12, IH.
  - intros x y H [z IH]. exists z. apply H13. exact H. exact IH.
Qed.

Inductive G : nat -> nat -> nat -> Prop :=
| G1 y : G 0 y y
| G2 x y z: G x y z -> G y x z
| G3 x y z : x <= y -> G x (y - x) z -> G x y z.

Fact G_gcd_pred :
  gcd_pred G.
Proof.
  repeat split. exact G1. exact G2. exact G3.
Qed.

Fact G_subsumed p  :
  gcd_pred p -> subsumed G p.
Proof.
  intros (H1&H2&H3). hnf.
  induction 1 as [y|x y z _ IH|x y z H _ IH].
  - apply H1.
  - apply H2, IH.
  - apply H3; easy.
Qed.

Fact gcd_pred_fun :
  Sigma f, forall p, gcd_pred p -> respects f p.
Proof.
  exists (fun x y => pi1 (gcd_pred_total G G_gcd_pred x y)).
  intros p H x y. destruct gcd_pred_total as [z H1]. cbn.
  apply G_subsumed; easy.
Qed.

Fact fun_gcd_pred_agree_G p :
  gcd_pred p -> functional p -> agreep p G.
Proof.
  intros H1 H2.
  apply agreep_sym,total_fun_agree.
  - intros x y.
    edestruct gcd_pred_total as [z H3].
    + exact G_gcd_pred.
    + exists z. exact H3.
  - exact H2.
  - apply G_subsumed, H1.
Qed.

Fact fun_gcd_pred_agree p p' :
  gcd_pred p -> functional p ->
  gcd_pred p' -> functional p' ->
  agreep p p'.
Proof.
  intros H1 H2 H1' H2'.
  apply agreep_trans with (p2:=G).
  - apply fun_gcd_pred_agree_G; assumption.
  - apply agreep_sym, fun_gcd_pred_agree_G; assumption.
Qed.

(*** Arithmetic GCD Predicate *)

Definition divides n x : Prop
  := exists k, x = k * n.

Definition gamma x y z : Prop :=
  forall n, divides n z <-> divides n x /\ divides n y.

Fact divides_zero n :
  divides n 0.
Proof.
  exists 0. reflexivity.
Qed.

Fact divides_minus x y n :
  x <= y -> divides n x -> divides n y <->  divides n (y - x).
Proof.
  intros H [k ->]. split.
  - intros [l ->]. exists (l-k). nia.
  - intros [l H1]. exists (k + l). nia.
Qed.

Fact gamma_gcd_pred :
  gcd_pred gamma.
Proof.
  hnf. split. 2:split.
  - intros y n. generalize (divides_zero n). tauto.
  - intros x y z. unfold gamma. firstorder.
  - intros x y z H H1 n.
    specialize (H1 n).
    generalize (divides_minus _ _ n H).
    tauto.
Qed.

Fact divides_bnd n x :
  x > 0 -> divides n x -> n <= x.
Proof.
  intros H [k ->]. destruct k.
  - exfalso. lia.
  - nia.
Qed.
 
Fact divides_eq' x y :
  x > 0 -> y > 0 -> divides x y -> divides y x -> x = y.
Proof.
  intros H1 H2 H3%divides_bnd H4%divides_bnd; lia.
Qed.

Fact divides_eq x y :
  (forall n, divides n x <-> divides n y) -> x = y.
Proof.
  destruct x, y; intros H.
  - reflexivity.
  - exfalso.
    enough (S(S y) <= S y) by lia.
    apply divides_bnd. lia.
    apply H, divides_zero.
  - exfalso.
    enough (S(S x) <= S x) by lia.
    apply divides_bnd. lia.
    apply H, divides_zero.
  - apply divides_eq'. lia. lia.
    + apply H. exists 1. lia.
    + apply H. exists 1. lia.
Qed.

Fact gamma_fun :
  functional gamma.
Proof.
  hnf. intros * H H'.
  apply divides_eq. intros n. split.
  - intros H1. apply H',H,H1.
  - intros H1. apply H,H',H1.
Qed.

(*** Deterministic GCD Predicate *)

Inductive G': nat -> nat -> nat -> Prop :=
| G'1: forall y, G' 0 y y
| G'2: forall x, G' (S x) 0 (S x)
| G'3: forall x y z, x <= y -> G' (S x) (y - x) z -> G' (S x) (S y) z
| G'4: forall x y z, y < x -> G' (x - y) (S y) z -> G' (S x) (S y) z.

Fact G'_fun :
  functional G'.
Proof.
  hnf. induction 1 as  [y|x|x y z H _ IH|x y z H _ IH]; intros H1.
  - depelim H1. refl.
  - depelim H1. refl.
  - depelim H1. auto. exfalso; lia.
  - depelim H1. exfalso; lia. auto.
Qed.

Fact G'_comm x y z :
  G' x y z -> G' y x z.
Proof.
  induction 1 as [y|x|x y z H _ IH|x y z H _ IH].
  - destruct y; constructor.
  - constructor.
  - assert (x < y \/ x = y) as [H1|<-] by lia.
    + apply G'4; easy.
    + replace (x-x) with 0 in IH by lia.
      depelim IH.
      apply G'3. lia.
      replace (x-x) with 0 by lia. constructor.
  - apply G'3. 2:exact IH. lia.
Qed.

Fact G'_sub x y z :
  x <= y -> G' x (y - x) z -> G' x y z.
Proof.
  intros H.
  destruct x.
  - replace (y - 0) with y by lia. easy.
  - destruct y.
    + exfalso; lia.
    + intros H1. apply G'3. lia. exact H1.
Qed.

Fact G'_gcd_predicate :
  gcd_pred G'.
Proof.
  repeat split.
  - exact G'1.
  - exact G'_comm.
  - exact G'_sub.
Qed.

(*** GCD Functions *)

Definition gcd_fun f : Prop :=
  (forall y, f 0 y = y) /\
  (forall x y, f x y = f y x) /\
  (forall x y, x <= y -> f x y = f x (y - x)).

Fact gcd_fun_respects f p :
  gcd_fun f -> gcd_pred p -> respects f p.
Proof.
  intros (H11&H12&H13) (H21&H22&H23).
  hnf. apply gcd_rec_sym.
  - intros y. rewrite H11. apply H21.
  - intros x y. rewrite H12. apply H22.
  - intros x y H IH. rewrite H13. 2:exact H. apply H23. exact H. exact IH.
Qed.

Fact agree_gcd_fun_rel f p :
  agree f p -> gcd_pred p <-> gcd_fun f.
Proof.
  intros H1. split.
  - intros (H21&H22&H23). repeat split.
    + intros y. apply H1. apply H21.
    + intros x y. apply H1. apply H22, H1. reflexivity.
    + intros x y H. apply H1. apply H23. lia. apply H1. reflexivity.
  - intros (H21&H22&H23). repeat split.
    + intros y. apply H1. apply H21.
    + intros x y z. intros <-%H1. apply H1. apply H22.
    + intros x y z H. intros <-%H1. rewrite <- H23. 2:lia.
      apply H1. reflexivity.
Qed.

Corollary respect_fun_gcd_pred f p :
  respects f p -> functional p -> gcd_pred p -> gcd_fun f.
Proof.
  intros H1 H2. apply agree_gcd_fun_rel.
  apply fun_respects_agree; easy.
Qed.

Corollary gcd_fun_rel f :
  gcd_fun f <-> gcd_pred (rel f).
Proof.
  symmetry.
  apply agree_gcd_fun_rel.
  apply rel_agree.
Qed.

Corollary gcd_fun_agreef f f' :
  gcd_fun f -> gcd_fun f' -> agreef f f'.
Proof.
  intros H1%gcd_fun_rel H2%gcd_fun_rel.
  apply rel_agreef.
  apply fun_gcd_pred_agree; (assumption || apply rel_fun).
Qed.

Corollary gcd_fun_rel_agree f p :
  gcd_fun f -> gcd_pred p -> functional p -> agree f p.
Proof.
  intros H1 H2 H3.
  apply fun_respects_agree. exact H3.
  apply gcd_fun_respects; assumption.
Qed.

(*** Procedural Specification *)

Definition Gamma f x y :=
  match x, y with
  | 0, y => y
  | S x, 0 => S x
  | (S x), (S y) => if le_lt_dec x y then f (S x) (y - x) else f (x - y) (S y)
  end.

Definition Gamma_sat f := forall x y, f x y = Gamma f x y.

Goal forall f, Gamma_sat f <->
          (forall y, f 0 y = y) /\
          (forall x, f (S x) 0 = S x) /\
          (forall x y, f (S x) (S y) = if le_lt_dec x y then f (S x) (y - x)
                                  else f (x - y) (S y)).
Proof.
  intros f. split.
  - intros F. repeat split; intros; rewrite F; reflexivity.
  - intros E x y.
    destruct x. easy.
    destruct y; cbn; easy.
Qed.

Fact Gamma_unique f g :
  Gamma_sat f -> Gamma_sat g -> agreef f g.
Proof.
  intros F G.
  refine (size_rec2 (fun x y => x + y) _).
  intros x y IH. rewrite F, G.
  destruct x as [|x]. reflexivity.
  destruct y as [|y]. reflexivity.
  cbn. destruct le_lt_dec as [H|H]; apply IH; lia.
Qed.

Fact Gamma_com f :
  Gamma_sat f -> forall x y, f x y = f y x.
Proof.
  intros F.  
  refine (size_rec2 (fun x y => x + y) _).
  intros x y IH. rewrite !F.
  destruct x,y; cbn. 1-3:reflexivity.
  destruct le_lt_dec as [H|H];
    destruct le_lt_dec as [H'|H'].
  - assert (x = y) as <- by lia. reflexivity.
  - apply IH; lia.
  - apply IH; lia.
  - exfalso; lia.
Qed.

(** Step-indexed Construction *)

Fixpoint g n x y :=
  match n, x, y with
  | 0, _, _ => 0
  | S _, 0, y' => y'
  | S _, S x' , 0 => S x'
  | S n', S x' , S y' => if le_lt_dec x' y'
                        then g n' x (y' - x')
                        else g n' (x' - y') y
  end.

Definition gcd x y := g (S (x + y)) x y.

Compute gcd 12 16.

Fact g_index_eq n n' x y :
  n > x + y -> n' >  x + y -> g n x y = g n' x y.
Proof.
  revert x y n n'.
  refine (size_rec2 (fun x y => x + y) _).
  intros x y IH n n' H1 H2.
  destruct n. lia.
  destruct n'. lia.
  destruct x. reflexivity. 
  destruct y. reflexivity.
  cbn [g].
  destruct le_lt_dec; apply IH; lia.
Qed.

Fact gcd3 x y :
  gcd (S x) (S y) = if le_lt_dec x y
                    then gcd (S x) (y - x)
                    else gcd (x - y) (S y).
Proof.
  unfold gcd at 1. cbn [g].
  destruct le_lt_dec as [H|H];
    apply g_index_eq; lia.
Qed.

Fact Gamma_sat_gcd :
  Gamma_sat gcd.
Proof.
  intros [|x] y. reflexivity.
  destruct y as [|y]. reflexivity.
  cbn [Gamma]. apply gcd3.
Qed.

Fact Gamma_gcd_fun f :
  Gamma_sat f <-> gcd_fun f.
Proof.
  split.
  - intros H. repeat split.
    + apply H.
    + apply Gamma_com, H.
    + intros x y H1. rewrite !H.
      destruct x.
      { cbn. lia. }
      destruct y.
      { reflexivity. }
      unfold Gamma at 1.
      destruct le_lt_dec as [H2|H2].
      2:{ exfalso. lia. }
      apply H.
  - intros (E1&E2&E3) x y.
    destruct x.
    { apply E1. }
    destruct y; cbn.
    { rewrite E2. apply E1. }
    destruct le_lt_dec as [H1|H1].
    + rewrite E3 by lia. reflexivity.
    + rewrite E2. rewrite E3 by lia. apply E2.
Qed.

Fact gcd_gcd_fun :
  gcd_fun gcd.
Proof.
  apply Gamma_gcd_fun, Gamma_sat_gcd.
Qed.

Fact G_fun :
  functional G.
Proof.
  assert (H: agreep (rel gcd) G).
  { apply fun_gcd_pred_agree_G.
    - apply gcd_fun_rel, gcd_gcd_fun.
    - apply rel_fun. }
  intros x y z z' H1%H H2%H. revert H1 H2.
  unfold rel. congruence.
Qed.









