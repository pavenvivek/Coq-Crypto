Require Import paillier_cryptosystem.
Require Import MathUtils.

Module Export Inc_Dec.

Fixpoint increment_100 (i : nat) (input : list nat) : list nat
  := match i, input with
     | i , nil => nil 
     | 0 , (cons x xs) => (cons (x + 100) xs)
     | (S i) , (cons x xs) => (cons x (increment_100 i xs))
     end.


Fixpoint decrement_100 (i : nat) (input : list nat) : list nat
  := match i, input with
     | i , nil => nil 
     | 0 , (cons x xs) => (cons (x - 100) xs)
     | (S i) , (cons x xs) => (cons x (decrement_100 i xs))
     end.


Fixpoint crypt_increment_100 (p q : nat) (i : nat) (input : list nat) : list nat
  := match i, input with
     | i , nil => nil
     | 0 , (cons x xs) => (cons (x * (paillier_encrypt'' p q 100)) xs)
     | (S i) , (cons x xs) => (cons x (crypt_increment_100 p q i xs))
     end.


Fixpoint crypt_decrement_100 (p q : nat) (i : nat) (input : list nat) : list nat
  := match i, input with
     | i , nil => nil
     | 0 , (cons x xs) => (cons (div x (paillier_encrypt'' p q 100)) xs)
     | (S i) , (cons x xs) => (cons x (crypt_decrement_100 p q i xs))
     end.

End Inc_Dec.