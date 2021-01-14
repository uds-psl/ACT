From Coq Require Import Arith Lia.
From Equations Require Import Equations.

Equations? gcd (x y: nat) : nat by wf (x+y) lt :=
  gcd 0 y         := y ;
  gcd (S x) 0     := S x ;
  gcd (S x) (S y) := if le_lt_dec y x then gcd (x-y) (S y) else gcd (S x) (y -x).
Proof.
  all:lia.
Qed.

Compute gcd 33 121.

Fact gcd_eq x y :
  gcd x y = match x, y with
            | 0, y => y
            | S x, 0 => S x
            | S x, S y => if le_lt_dec y x then gcd (x-y) (S y) else gcd (S x) (y -x)
            end.
Proof.
  destruct x.
  - apply gcd_equation_1.
  - destruct y.
    + apply gcd_equation_2.
    + apply gcd_equation_3.  
Qed.
 
Equations? Mod (x y: nat) : nat by wf x lt :=
  Mod x y := if le_lt_dec x y then x else Mod (x - S y) y. 
Proof.
  lia.
Qed.

Fact Mod_eq x y :
  Mod x y = if le_lt_dec x y then x else Mod (x - S y) y.
Proof.
  apply Mod_equation_1.
Qed.

Fact Mod_le x y :
  Mod x y <= y.
Proof.
  funelim (Mod x y).
  destruct Heqcall.
  destruct le_lt_dec as [H1|H1].
  - exact H1.
  - auto.
Qed.

Equations? GCD (x y: nat) : nat by wf y lt :=
  GCD x 0     := x ;
  GCD x (S y) := GCD (S y) (Mod x y).
Proof.
  specialize (Mod_le x y). lia.
Qed.

Compute GCD 60 24.

Fact GCD_eq x y :
  GCD x y = match y with
            | 0 => x
            | S y => GCD (S y) (Mod x y)
            end.
Proof.
  destruct y.
  - apply GCD_equation_1.
  - apply GCD_equation_2.
Qed.
