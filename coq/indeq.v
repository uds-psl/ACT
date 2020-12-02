Definition cast {X} {x y: X} {p: X -> Type}
  : x = y -> p x -> p y
  := fun e a => match e with eq_refl => a end.

Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.

Section UIP.
  Variable X: Type.
  Definition UIP := forall (x y: X) (e e': x = y), e = e'.
  Definition UIP' := forall (x : X) (e: x = x), e = eq_refl.
  Definition K_Streicher := forall (x: X) (p: x = x -> Prop), p (eq_refl x) -> forall e, p e.
  Definition CD := forall (p: X -> Type) (x: X) (a: p x) (e: x = x), cast e a = a.
  Definition DPI := forall (p: X -> Type) x u v, Sig p x u = Sig p x v -> u = v.
  
  Goal UIP' -> UIP.
  Proof.
    intros H x y e e'. destruct e'.  apply H.
  Qed.
  
  Goal UIP -> K_Streicher.
  Proof.
    intros H x p a e.
    specialize (H x x eq_refl e).
    destruct H. exact a.
  Qed.

  Goal K_Streicher -> UIP'.
  Proof.
    intros H x. apply (H x (fun z => z = eq_refl)). reflexivity.
  Qed.

  Goal K_Streicher -> CD.
  Proof.
    intros H p x a. apply H. reflexivity.
  Qed.

  Goal CD -> UIP'.
  Proof.  (* Idea from William, 28 Nov 2020 *)
    intros H x.
    enough (forall y  (e': y = x) (e: x = y), cast e' e = eq_refl x) as H'.
    { apply (H' x (eq_refl x)). }
    intros y e' e. destruct e. apply H.
  Qed.

  Lemma cast_eq {x y: X} :
    forall e: x = y, cast e (eq_refl x) = e.
  Proof.
    destruct e. reflexivity.
  Qed.

  Goal CD -> UIP'.
  Proof. (* Idea from Gaëtan Gilbert, 20 Nov 2020 *)
    intros H x e. rewrite <-(cast_eq e). apply H.
  Qed.

  Goal CD -> DPI.
  Proof.
    intros H p x.
    enough (forall a b: sigT p, a = b -> forall e: pi1 a = pi1 b, cast e (pi2 a) = pi2 b) as H'.
    { intros u v e'. apply (H' _ _ e' eq_refl). }
    intros a b []. apply H.
  Qed.

  Goal DPI -> UIP'.
  Proof.
    intros H x e.
    apply (H (fun z => z = x)). revert e.
    enough (forall y (e: x = y), Sig (fun z => z = y) x e = Sig (fun z => z = y) y eq_refl) as H'.
    { apply (H' x). }
    intros y []. reflexivity.
  Qed.
 
  Lemma DPI_eq1 {p: X -> Type} {a b: sigT p} :
    CD -> a = b -> forall e: pi1 a = pi1 b, cast e (pi2 a) = pi2 b.
  Proof.
    intros H [] e. apply H.
  Qed.
  
  Goal CD -> DPI.
  Proof.  (* Idea from Gaëtan Gilbert, 20 Nov 2020 *)
    intros H p x u v e. apply (DPI_eq1 H e eq_refl).
  Qed.

  Lemma DPI_eq2 (x y: X) :
    forall e: x = y, Sig (fun z => z = y) x e = Sig (fun z => z = y) y eq_refl.
  Proof.
    intros []. reflexivity.
  Qed.

  Goal DPI -> UIP'.
  Proof.
    intros H x e. apply (H (fun z => z = x)), DPI_eq2.
  Qed.

End UIP.

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

(* UIP propagates to identity at Type *)

Inductive id X (x: X) : X -> Set := Q : id X x x.
(* Must write Set, Type will be downgraded to Prop *)
Arguments id {X}.
Arguments Q {X}.

Check id nat.
Check id Type.

Definition D {X} {x y: X}
  : id x y -> x = y
  := fun a => match a with Q _ => eq_refl x end.
Definition U {X} {x y: X}
  : x = y -> id x y
  := fun e => match e with eq_refl _ => Q x end.
Fact UD_eq {X} {x y: X} (a: id x y) :
  U (D a) = a.
Proof.
  destruct a. reflexivity.
Qed.
Fact DU_eq {X} {x y: X} (e: x = y) :
  D (U e) = e.
Proof.
  destruct e. reflexivity.
Qed.

Fact id_fun X Y (f: X -> Y) (x x': X) :
  id x x' -> id (f x) (f x').
Proof.
  destruct 1. apply Q.
Qed.

Definition UIP_id X := forall (x y: X) (a b: id x y), id a b.
Fact UIP_up X :
  UIP X -> UIP_id X.
Proof.
  intros H x y a b.
  rewrite <-(UD_eq a), <-(UD_eq b).
  apply id_fun.
  apply U. apply H.
Qed.
Fact UIP_down X :
  UIP_id X -> UIP X.
Proof.
  intros H x y e e'.
  rewrite <-(DU_eq e), <-(DU_eq e').
  apply f_equal. apply D. apply H.
Qed.

