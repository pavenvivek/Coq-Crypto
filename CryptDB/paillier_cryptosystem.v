Require Import MathUtils.

Module Export Paillier.

Definition paillier_keygen_public (p q : nat) : prod nat nat
 := ((p * q) , ((p * q) + 1)).

Definition calculateL (u n : nat) : nat
  := div (u - 1) n.

Definition paillier_keygen_private (p q : nat) : prod nat nat
  := 
  let λ' := lcm (p - 1) (q - 1) in
  let n := p * q in
  let g := snd (paillier_keygen_public p q) in
    (λ' , (mod_inv (calculateL (modl (exp g λ') (exp n 2)) n) n)).

Definition paillier_encrypt' (plain_text : nat) (random : nat) (public_key : nat * nat) : nat
  := match public_key with
     | (n , g) => modl ((exp g plain_text) * (exp random n)) (exp n 2)
     end.

Definition paillier_encrypt'' (p q : nat) (plain_text : nat) : nat
  :=
  let public_key := (paillier_keygen_public p q) in
  let random := (getRand p) in
    (paillier_encrypt' plain_text random public_key).

Definition paillier_encrypt (p q : nat) (plain_text : list nat) : list nat
  := loop (paillier_encrypt'' p q) plain_text.

Definition paillier_decrypt' (cipher_text : nat) (n : nat) (private_key : nat * nat) : nat
  := match private_key with
     | (λ' , μ) => let L := calculateL (modl (exp cipher_text λ') (exp n 2)) n in
                     (modl (L * μ) n)
     end.

Definition paillier_decrypt'' (p q : nat) (cipher_text : nat) : nat
  := let private_key := (paillier_keygen_private p q) in
       (paillier_decrypt' cipher_text (p * q) private_key).

Definition paillier_decrypt (p q : nat) (cipher_text : list nat) : list nat
  := loop (paillier_decrypt'' p q) cipher_text.

End Paillier.