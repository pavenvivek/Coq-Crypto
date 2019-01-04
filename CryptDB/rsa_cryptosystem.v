Require Import MathUtils.

Module Export RSA.

Definition rsa_keygen_public (p q : nat) : nat * nat
  := 
  let euler_totient := (p - 1) * (q - 1) in
  let n := (p * q) in 
    ((coprime euler_totient) , n).

Definition rsa_keygen_private (p q : nat) : nat * nat
  := 
  let e := (fst (rsa_keygen_public p q)) in
  let n := p * q in
  let euler_totient := (p - 1) * (q - 1) in
    ((mod_inv e euler_totient) , (p * q)).

Definition rsa_encrypt' (plain_text : nat) (public_key : nat * nat) : nat
  := match public_key with
     | (e , n) => modl (exp plain_text e) n
     end.

Definition rsa_encrypt'' (p q : nat) (plain_text : nat) : nat
  :=
  let public_key := (rsa_keygen_public p q) in
    (rsa_encrypt' plain_text public_key).

Definition rsa_encrypt (p q : nat) (plain_text : list nat) : list nat
  := loop (rsa_encrypt'' p q) plain_text.

Definition rsa_decrypt' (cipher_text : nat) (private_key : nat * nat) : nat
  := match private_key with
     | (d , n) => modl (exp cipher_text d) n
     end.

Definition rsa_decrypt'' (p q : nat) (cipher_text : nat) : nat
  :=
  let private_key := (rsa_keygen_private p q) in
    rsa_decrypt' cipher_text private_key.

Definition rsa_decrypt (p q : nat) (cipher_text : list nat) : list nat
  := loop (rsa_decrypt'' p q) cipher_text.

End RSA.