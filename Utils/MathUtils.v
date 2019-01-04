Require Import ZArith.

Module Export MathUtils.

Fixpoint add (n m : nat) : nat
  := match n with
     | 0 => m
     | (S n) => S (add n m)
     end.

(* Reserved Notation "n + m" (right associativity, at level 65, only parsing). *)
(* Notation "n + m" := (add n m) (only parsing) : type_scope. *)

(* Compute (10 - 11). *)

Fixpoint sub (n m : nat) : nat
  := match n,m with
     | n , 0 => n
     | 0 , (S m) => 0
     | (S n) , (S m) => sub n m
     end.

(* Compute (sub 23 21). *)

Fixpoint mul (n m : nat) : nat
  := match n with
     | 0 => 0
     | (S n) => (add m (mul n m))
     end.

(* Compute (mul 4 2). *)

Fixpoint div' (k l m n : nat) : nat
  := match m,n with
     | 0 , n => k
     | (S m) , 0 => div' (S k) l m l
     | (S m) , (S n) => div' k l m n
     end.

Fixpoint div (n m : nat) : nat
  := match m with
     | 0 => n
     | (S m) => div' 0 m n m
     end.

(* Compute (div 6 4). *)

Fixpoint exp (n m : nat) : nat
  := match m with
     | 0 => 1
     | (S m) => n * (exp n m)
     end.

(* Compute (exp 10 4). *)

Fixpoint mod' (k l m n : nat) : nat
  := match m,n with
     | 0 , n => k
     | (S m) , 0 => mod' 0 l m l
     | (S m) , (S n) => mod' (S k) l m n
     end.

Fixpoint modl (n m : nat) : nat
  := match m with
     | 0 => 0
     | (S m) => mod' 0 m n m
     end.

(* Compute (modl 10 15).
Compute Z.to_nat (Z.gcd 35 49). *)

Fixpoint lcm (n m : nat) : nat
  := div (mul n m) (Z.to_nat (Z.gcd (Z.of_nat n) (Z.of_nat m))).

(* Compute (lcm 7 5). *)

Axiom abort : forall {A : Type}, Empty_set -> A.
Axiom failed : Empty_set.

(* Check Empty_set. *)

Fixpoint mod_inv' (l n m : nat) : nat
  := match n with
     | 0 => modl 0 m
     | (S n) => match (modl (mul l n) m) with
                | (S 0) => n
                | x => (mod_inv' l n m)
                end
     end.

Fixpoint mod_inv (n m : nat) : nat
  := mod_inv' n m m.

Fixpoint coprime' (index1 : nat) (index2 : nat) (euler_totient : nat) : nat
  := match index1 with
     | 0 => (abort failed) (* Invalid case *)
     | (S index1) => match (Z.gtb (Z.of_nat index2) 1) with
                     | true => match (Z.ltb (Z.of_nat index2) (Z.of_nat euler_totient)) with
                               | true => match (Z.eqb 1 (Z.gcd (Z.of_nat euler_totient) (Z.of_nat index2))) with
                                         | true => index2
                                         | false => (coprime' index1 (S index2) euler_totient)
                                         end
                               | false => (abort failed) (* Invalid case *)
                               end
                     | false => (abort failed) (* Invalid case *)
                     end
     end.


(* Compute (Z.leb 10 10). *)

Fixpoint coprime (euler_totient : nat) : nat
  := coprime' euler_totient 2 euler_totient.

Fixpoint getRand (p : nat) : nat
  := match (Z.eqb 2 (Z.of_nat p)) with
     | true => 1
     | false => 2
     end.

Fixpoint loop {A B : Type} (f : A -> B) (input : list A) : list B
  := match input with
     | nil => nil
     | (cons x xs) => (cons (f x) (loop f xs))
     end.

(* Check list_rec. *)

End MathUtils.