Require Import PathUtils.
Require Import rsa_cryptosystem.
Require Import paillier_cryptosystem.
Require Import insert_delete.
Require Import inc_dec.

Module Export Repo.

Private Inductive history : nat -> nat -> Type :=
  | hnil : forall {m:nat}, history m m
  | hid : forall {m n:nat}, history m n -> history m n
  | hinsert : forall {m n:nat}, nat -> nat -> history m n -> history m (S n)
  | hdelete : forall {m n:nat}, nat -> history m (S n) -> history m n
  | hrsa_encrypt : forall {m n:nat}, nat -> nat -> history m n -> history m n
  | hrsa_decrypt : forall {m n:nat}, nat -> nat -> history m n -> history m n
  | hpaillier_encrypt : forall {m n:nat}, nat -> nat -> history m n -> history m n
  | hpaillier_decrypt : forall {m n:nat}, nat -> nat -> history m n -> history m n
  | hincrement100 : forall {m n:nat}, nat -> history m n -> history m n
  | hcrypt_increment100 : forall {m n:nat}, nat -> nat -> nat -> history m n -> history m n.
  Arguments hnil [m].
  Arguments hid [m] [n].
  Arguments hinsert [m] [n].
  Arguments hdelete [m] [n].
  Arguments hrsa_encrypt [m] [n].
  Arguments hrsa_decrypt [m] [n].
  Arguments hpaillier_encrypt [m] [n].
  Arguments hpaillier_decrypt [m] [n].
  Arguments hincrement100 [m] [n].
  Arguments hcrypt_increment100 [m] [n].

Axiom hpaillier_homomorphism : forall {m n : nat} (p q i : nat) (r : history m n),
  (@hpaillier_decrypt m n p q (@hcrypt_increment100 m n p q i (@hpaillier_encrypt m n p q r)))
  ≡ (@hincrement100 m n i r).

(* Check history_ind.
Print history_ind. *)
(* Print history_rect. *)

Definition history_recbase (P : Type)
  (cnil : P)
  (cid : (forall (m n : nat) (h : history m n), P -> P))
  (cinsert : (forall (m n : nat) (n0 n1 : nat) (h : history m n), P -> P))
  (cdelete : (forall (m n : nat) (n0 : nat) (h : history m (S n)), P -> P))
  (crsa_encrypt : (forall (m n : nat) (n0 n1 : nat) (h : history m n), P -> P))
  (crsa_decrypt : (forall (m n : nat) (n0 n1 : nat) (h : history m n), P -> P))
  (cpaillier_encrypt : (forall (m n : nat) (n0 n1 : nat) (h : history m n), P -> P))
  (cpaillier_decrypt : (forall (m n : nat) (n0 n1 : nat) (h : history m n), P -> P))
  (cincrement100 : (forall (m n : nat) (n0 : nat) (h : history m n), P -> P))
  (ccrypt_increment100 : (forall (m n : nat) (n0 n1 n2 : nat) (h : history m n), P -> P))
  : forall (m n : nat) (h : history m n), P
  :=
fix F (n n0 : nat) (h : history n n0) {struct h} : P :=
  match h as h0 in (history n1 n2) return P with
  | @hnil m => cnil
  | @hid m n h0 => cid m n h0 (F m n h0)
  | @hinsert m n n2 n3 h0 => cinsert m n n2 n3 h0 (F m n h0)
  | @hdelete m n n2 h0 => cdelete m n n2 h0 (F m (S n) h0)
  | @hrsa_encrypt m n n2 n3 h0 => crsa_encrypt m n n2 n3 h0 (F m n h0)
  | @hrsa_decrypt m n n2 n3 h0 => crsa_decrypt m n n2 n3 h0 (F m n h0)
  | @hpaillier_encrypt m n n2 n3 h0 => cpaillier_encrypt m n n2 n3 h0 (F m n h0)
  | @hpaillier_decrypt m n n2 n3 h0 => cpaillier_decrypt m n n2 n3 h0 (F m n h0)
  | @hincrement100 m n n2 h0 => cincrement100 m n n2 h0 (F m n h0)
  | @hcrypt_increment100 m n n2 n3 n4 h0 => ccrypt_increment100 m n n2 n3 n4 h0 (F m n h0)
  end.


Definition history_rec (P : Type)
  (cnil : P)
  (cid : (forall (m n : nat) (h : history m n), P -> P))
  (cinsert : (forall (m n : nat) (n0 n1 : nat) (h : history m n), P -> P))
  (cdelete : (forall (m n : nat) (n0 : nat) (h : history m (S n)), P -> P))
  (crsa_encrypt : (forall (m n : nat) (n0 n1 : nat) (h : history m n), P -> P))
  (crsa_decrypt : (forall (m n : nat) (n0 n1 : nat) (h : history m n), P -> P))
  (cpaillier_encrypt : (forall (m n : nat) (n0 n1 : nat) (h : history m n), P -> P))
  (cpaillier_decrypt : (forall (m n : nat) (n0 n1 : nat) (h : history m n), P -> P))
  (cincrement100 : (forall (m n : nat) (n0 : nat) (h : history m n), P -> P))
  (ccrypt_increment100 : (forall (m n : nat) (n0 n1 n2 : nat) (h : history m n), P -> P))
  (cpaillier_homomorphism : (forall (m n : nat) (n0 n1 i : nat) (h : history m n),
    (history_recbase P cnil cid cinsert cdelete crsa_encrypt crsa_decrypt 
      cpaillier_encrypt cpaillier_decrypt cincrement100 ccrypt_increment100 m n
      (hpaillier_decrypt n0 n1 (hcrypt_increment100 n0 n1 i (hpaillier_encrypt n0 n1 h))))
    ≡ (history_recbase P cnil cid cinsert cdelete crsa_encrypt crsa_decrypt 
        cpaillier_encrypt cpaillier_decrypt cincrement100 ccrypt_increment100 m n (hincrement100 i h))))
  : forall (m n : nat) (h : history m n), P
  :=  
  history_recbase P cnil cid cinsert cdelete crsa_encrypt crsa_decrypt 
    cpaillier_encrypt cpaillier_decrypt cincrement100 ccrypt_increment100.


Axiom beta_history_rec_paillier_homomorphism : forall (P : Type)
  (cnil : P)
  (cid : (forall (m n : nat) (h : history m n), P -> P))
  (cinsert : (forall (m n : nat) (n0 n1 : nat) (h : history m n), P -> P))
  (cdelete : (forall (m n : nat) (n0 : nat) (h : history m (S n)), P -> P))
  (crsa_encrypt : (forall (m n : nat) (n0 n1 : nat) (h : history m n), P -> P))
  (crsa_decrypt : (forall (m n : nat) (n0 n1 : nat) (h : history m n), P -> P))
  (cpaillier_encrypt : (forall (m n : nat) (n0 n1 : nat) (h : history m n), P -> P))
  (cpaillier_decrypt : (forall (m n : nat) (n0 n1 : nat) (h : history m n), P -> P))
  (cincrement100 : (forall (m n : nat) (n0 : nat) (h : history m n), P -> P))
  (ccrypt_increment100 : (forall (m n : nat) (n0 n1 n2 : nat) (h : history m n), P -> P))
  (cpaillier_homomorphism : (forall (m n : nat) (n0 n1 i : nat) (h : history m n),
    (history_recbase  P cnil cid cinsert cdelete crsa_encrypt crsa_decrypt 
      cpaillier_encrypt cpaillier_decrypt cincrement100 ccrypt_increment100 m n
      (hpaillier_decrypt n0 n1 (hcrypt_increment100 n0 n1 i (hpaillier_encrypt n0 n1 h))))
    ≡ (history_recbase P cnil cid cinsert cdelete crsa_encrypt crsa_decrypt cpaillier_encrypt cpaillier_decrypt
        cincrement100 ccrypt_increment100 m n (hincrement100 i h))))
  (m n : nat) (n0 n1 i : nat) (h : history m n),
  ap (history_rec P cnil cid cinsert cdelete crsa_encrypt crsa_decrypt cpaillier_encrypt cpaillier_decrypt 
    cincrement100 ccrypt_increment100 cpaillier_homomorphism m n) 
    (@hpaillier_homomorphism m n n0 n1 i h)
  ≡ (cpaillier_homomorphism m n n0 n1 i h).

Definition history_indbase (P : forall {n n0 : nat}, history n n0 -> Type) 
  (cnil : forall (m : nat), P hnil)
  (cid : forall (m n : nat) (h : history m n), P h -> P (hid h))
  (cinsert : forall (m n : nat) (n0 n1 : nat) (h : history m n), P h -> P (hinsert n0 n1 h))
  (cdelete : forall (m n : nat) (n0 : nat) (h : history m (S n)), P h -> P (hdelete n0 h))
  (crsa_encrypt : forall (m n : nat) (n0 n1 : nat) (h : history m n), P h -> P (hrsa_encrypt n0 n1 h))
  (crsa_decrypt : forall (m n : nat) (n0 n1 : nat) (h : history m n), P h -> P (hrsa_decrypt n0 n1 h))
  (cpaillier_encrypt : forall (m n : nat) (n0 n1 : nat) (h : history m n), P h -> P (hpaillier_encrypt n0 n1 h))
  (cpaillier_decrypt : forall (m n : nat) (n0 n1 : nat) (h : history m n), P h -> P (hpaillier_decrypt n0 n1 h))
  (cincrement100 : forall (m n : nat) (n0 : nat) (h : history m n), P h -> P (hincrement100 n0 h))
  (ccrypt_increment100 : forall (m n : nat) (n0 n1 n2 : nat) (h : history m n), P h -> P (hcrypt_increment100 n0 n1 n2 h))
  : forall (m n : nat) (h : history m n), P h
  :=
fix F (n n0 : nat) (h : history n n0) {struct h} : P h :=
  match h as h0 in (history n1 n2) return (P h0) with
  | @hnil m => cnil m
  | @hid m n h0 => cid m n h0 (F m n h0)
  | @hinsert m n n2 n3 h0 => cinsert m n n2 n3 h0 (F m n h0)
  | @hdelete m n n2 h0 => cdelete m n n2 h0 (F m (S n) h0)
  | @hrsa_encrypt m n n2 n3 h0 => crsa_encrypt m n n2 n3 h0 (F m n h0)
  | @hrsa_decrypt m n n2 n3 h0 => crsa_decrypt m n n2 n3 h0 (F m n h0)
  | @hpaillier_encrypt m n n2 n3 h0 => cpaillier_encrypt m n n2 n3 h0 (F m n h0)
  | @hpaillier_decrypt m n n2 n3 h0 => cpaillier_decrypt m n n2 n3 h0 (F m n h0)
  | @hincrement100 m n n2 h0 => cincrement100 m n n2 h0 (F m n h0)
  | @hcrypt_increment100 m n n2 n3 n4 h0 => ccrypt_increment100 m n n2 n3 n4 h0 (F m n h0)
  end.

Definition history_ind (P : forall (n n0 : nat), history n n0 -> Type) 
  (cnil : forall (m : nat), P m m hnil)
  (cid : forall (m n : nat) (h : history m n), P m n h -> P m n (hid h))
  (cinsert : forall (m n : nat) (n0 n1 : nat) (h : history m n), P m n h -> P m (S n) (hinsert n0 n1 h))
  (cdelete : forall (m n : nat) (n0 : nat) (h : history m (S n)), P m (S n) h -> P m n (hdelete n0 h))
  (crsa_encrypt : forall (m n : nat) (n0 n1 : nat) (h : history m n), P m n h -> P m n (hrsa_encrypt n0 n1 h))
  (crsa_decrypt : forall (m n : nat) (n0 n1 : nat) (h : history m n), P m n h -> P m n (hrsa_decrypt n0 n1 h))
  (cpaillier_encrypt : forall (m n : nat) (n0 n1 : nat) (h : history m n), P m n h -> P m n (hpaillier_encrypt n0 n1 h))
  (cpaillier_decrypt : forall (m n : nat) (n0 n1 : nat) (h : history m n), P m n h -> P m n (hpaillier_decrypt n0 n1 h))
  (cincrement100 : forall (m n : nat) (n0 : nat) (h : history m n), P m n h -> P m n (hincrement100 n0 h))
  (ccrypt_increment100 : forall (m n : nat) (n0 n1 n2 : nat) (h : history m n), P m n h -> P m n (hcrypt_increment100 n0 n1 n2 h))
  (cpaillier_homomorphism : (forall (m n : nat) (n0 n1 i : nat) (h : history m n),
    ((@hpaillier_homomorphism m n n0 n1 i h) #
     (@history_indbase P cnil cid cinsert cdelete crsa_encrypt crsa_decrypt cpaillier_encrypt cpaillier_decrypt 
      cincrement100 ccrypt_increment100 m n
      (hpaillier_decrypt n0 n1 (hcrypt_increment100 n0 n1 i (hpaillier_encrypt n0 n1 h))))
    ≡ (@history_indbase P cnil cid cinsert cdelete crsa_encrypt crsa_decrypt cpaillier_encrypt cpaillier_decrypt
        cincrement100 ccrypt_increment100 m n (hincrement100 i h)))))  
  : forall (m n : nat) (h : history m n), P m n h
  :=
  history_indbase P cnil cid cinsert cdelete crsa_encrypt crsa_decrypt cpaillier_encrypt cpaillier_decrypt 
    cincrement100 ccrypt_increment100.


Axiom beta_history_ind_paillier_homomorphism : forall (P : forall (n n0 : nat), history n n0 -> Type) 
  (cnil : forall (m : nat), P m m hnil)
  (cid : forall (m n : nat) (h : history m n), P m n h -> P m n (hid h))
  (cinsert : forall (m n : nat) (n0 n1 : nat) (h : history m n), P m n h -> P m (S n) (hinsert n0 n1 h))
  (cdelete : forall (m n : nat) (n0 : nat) (h : history m (S n)), P m (S n) h -> P m n (hdelete n0 h))
  (crsa_encrypt : forall (m n : nat) (n0 n1 : nat) (h : history m n), P m n h -> P m n (hrsa_encrypt n0 n1 h))
  (crsa_decrypt : forall (m n : nat) (n0 n1 : nat) (h : history m n), P m n h -> P m n (hrsa_decrypt n0 n1 h))
  (cpaillier_encrypt : forall (m n : nat) (n0 n1 : nat) (h : history m n), P m n h -> P m n (hpaillier_encrypt n0 n1 h))
  (cpaillier_decrypt : forall (m n : nat) (n0 n1 : nat) (h : history m n), P m n h -> P m n (hpaillier_decrypt n0 n1 h))
  (cincrement100 : forall (m n : nat) (n0 : nat) (h : history m n), P m n h -> P m n (hincrement100 n0 h))
  (ccrypt_increment100 : forall (m n : nat) (n0 n1 n2 : nat) (h : history m n), P m n h -> P m n (hcrypt_increment100 n0 n1 n2 h))
  (cpaillier_homomorphism : (forall (m n : nat) (n0 n1 i : nat) (h : history m n),
    ((@hpaillier_homomorphism m n n0 n1 i h) #
     (@history_indbase P cnil cid cinsert cdelete crsa_encrypt crsa_decrypt cpaillier_encrypt cpaillier_decrypt 
      cincrement100 ccrypt_increment100 m n
      (hpaillier_decrypt n0 n1 (hcrypt_increment100 n0 n1 i (hpaillier_encrypt n0 n1 h))))
    ≡ (@history_indbase P cnil cid cinsert cdelete crsa_encrypt crsa_decrypt cpaillier_encrypt cpaillier_decrypt
        cincrement100 ccrypt_increment100 m n (hincrement100 i h)))))
  (m n : nat) (n0 n1 i : nat) (h : history m n),
  apD (history_ind P cnil cid cinsert cdelete crsa_encrypt crsa_decrypt cpaillier_encrypt cpaillier_decrypt 
    cincrement100 ccrypt_increment100 cpaillier_homomorphism m n) 
    (@hpaillier_homomorphism m n n0 n1 i h)
  ≡ (cpaillier_homomorphism m n n0 n1 i h).

(* Definition id {A : Type} (a : A) := a. *)

Fixpoint replay {m n} (input : history m n) : list nat
  := match input with
     | hnil => nil
     | hid h => id (replay h)
     | hinsert value index h => insert value index (replay h)
     | hdelete index h => delete index (replay h)
     | hrsa_encrypt p q h => rsa_encrypt p q (replay h)
     | hrsa_decrypt p q h => rsa_decrypt p q (replay h)
     | hpaillier_encrypt p q h => paillier_encrypt p q (replay h)
     | hpaillier_decrypt p q h => paillier_decrypt p q (replay h)
     | hincrement100 index h => increment_100 index (replay h)
     | hcrypt_increment100 p q i h => crypt_increment_100 p q i (replay h)
     end.

Private Inductive cryptR : Type :=
  | ctab : forall {n : nat}, history 0 n -> cryptR
  | ctabRSA : forall {n : nat}, history 0 n -> cryptR
  | ctabPL : forall {n : nat}, history 0 n -> cryptR.
  Arguments ctab [n].
  Arguments ctabRSA [n].
  Arguments ctabPL [n].

Axiom insert_query : forall {n : nat} (value : nat) (index : nat) (r : history 0 n), (ctab r) ≡ (ctab (hinsert value index r)).
Axiom delete_query : forall {n : nat} (index : nat) (r : history 0 (S n)), (ctab r) ≡ (ctab (hdelete index r)).
Axiom rsa_enc : forall {n : nat} (p q : nat) (r : history 0 n), (ctab r) ≡ (ctabRSA (hrsa_encrypt p q r)).
Axiom rsa_dec : forall {n : nat} (p q : nat) (r : history 0 n), (ctabRSA r) ≡ (ctab (hrsa_decrypt p q r)).
Axiom paillier_enc : forall {n : nat} (p q : nat) (r : history 0 n), (ctab r) ≡ (ctabPL (hpaillier_encrypt p q r)).
Axiom paillier_dec : forall {n : nat} (p q : nat) (r : history 0 n), (ctabPL r) ≡ (ctab (hpaillier_decrypt p q r)).
Axiom increment_by100 : forall {n : nat} (index : nat) (r : history 0 n), (ctab r) ≡ (ctab (hincrement100 index r)).
Axiom crypt_increment_by100 : forall {n : nat} (p q : nat) (index : nat) (r : history 0 n), (ctabPL r) ≡ (ctabPL (hcrypt_increment100 p q index r)).
Axiom id_cryptR : forall {n : nat} (r : history 0 n), (ctab r) ≡ (ctab (hid r)).

(* Check cryptR_rect.
Print cryptR_rect. *)

Definition cryptR_recbase (P : Type) 
  (ptab : forall (n : nat) (h : history 0 n), P)
  (ptabRSA : forall (n : nat) (h : history 0 n), P)
  (ptabPL : forall (n : nat) (h : history 0 n), P)
  : forall (c : cryptR), P 
  :=
  fun c => match c as c0 return P with
           | @ctab x x0 => ptab x x0
           | @ctabRSA x x0 => ptabRSA x x0
           | @ctabPL x x0 => ptabPL x x0
           end.

Definition cryptR_rec (P : Type) 
  (ptab : forall (n : nat) (h : history 0 n), P)
  (ptabRSA : forall (n : nat) (h : history 0 n), P)
  (ptabPL : forall (n : nat) (h : history 0 n), P)
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n), 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hid r))))
  : forall (c : cryptR), P 
  := cryptR_recbase P ptab ptabRSA ptabPL.


Axiom beta_cryptR_rec_insert : forall (P : Type) 
  (ptab : forall (n : nat) (h : history 0 n), P)
  (ptabRSA : forall (n : nat) (h : history 0 n), P)
  (ptabPL : forall (n : nat) (h : history 0 n), P)
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n), 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (value : nat) (index : nat) (r : history 0 n),
  ap (cryptR_rec P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@insert_query n value index r)
  ≡ (pinsert n value index r).

Axiom beta_cryptR_rec_delete : forall (P : Type) 
  (ptab : forall (n : nat) (h : history 0 n), P)
  (ptabRSA : forall (n : nat) (h : history 0 n), P)
  (ptabPL : forall (n : nat) (h : history 0 n), P)
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n), 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (index : nat) (r : history 0 (S n)),
  ap (cryptR_rec P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@delete_query n index r)
  ≡ (pdelete n index r).

Axiom beta_cryptR_rec_rsa_encrypt : forall (P : Type) 
  (ptab : forall (n : nat) (h : history 0 n), P)
  (ptabRSA : forall (n : nat) (h : history 0 n), P)
  (ptabPL : forall (n : nat) (h : history 0 n), P)
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n), 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (p q : nat) (r : history 0 n),
  ap (cryptR_rec P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@rsa_enc n p q r)
  ≡ (prsa_encrypt n p q r).

Axiom beta_cryptR_rec_rsa_decrypt : forall (P : Type) 
  (ptab : forall (n : nat) (h : history 0 n), P)
  (ptabRSA : forall (n : nat) (h : history 0 n), P)
  (ptabPL : forall (n : nat) (h : history 0 n), P)
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n), 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (p q : nat) (r : history 0 n),
  ap (cryptR_rec P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@rsa_dec n p q r)
  ≡ (prsa_decrypt n p q r).

Axiom beta_cryptR_rec_paillier_encrypt : forall (P : Type) 
  (ptab : forall (n : nat) (h : history 0 n), P)
  (ptabRSA : forall (n : nat) (h : history 0 n), P)
  (ptabPL : forall (n : nat) (h : history 0 n), P)
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n), 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (p q : nat) (r : history 0 n),
  ap (cryptR_rec P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@paillier_enc n p q r)
  ≡ (ppaillier_encrypt n p q r).

Axiom beta_cryptR_rec_paillier_decrypt : forall (P : Type) 
  (ptab : forall (n : nat) (h : history 0 n), P)
  (ptabRSA : forall (n : nat) (h : history 0 n), P)
  (ptabPL : forall (n : nat) (h : history 0 n), P)
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n), 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (p q : nat) (r : history 0 n),
  ap (cryptR_rec P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@paillier_dec n p q r)
  ≡ (ppaillier_decrypt n p q r).

Axiom beta_cryptR_rec_increment100 : forall (P : Type) 
  (ptab : forall (n : nat) (h : history 0 n), P)
  (ptabRSA : forall (n : nat) (h : history 0 n), P)
  (ptabPL : forall (n : nat) (h : history 0 n), P)
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n), 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (index : nat) (r : history 0 n),
  ap (cryptR_rec P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@increment_by100 n index r)
  ≡ (pincrement100 n index r).

Axiom beta_cryptR_rec_crypt_increment100 : forall (P : Type) 
  (ptab : forall (n : nat) (h : history 0 n), P)
  (ptabRSA : forall (n : nat) (h : history 0 n), P)
  (ptabPL : forall (n : nat) (h : history 0 n), P)
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n), 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (p q : nat) (index : nat) (r : history 0 n),
  ap (cryptR_rec P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@crypt_increment_by100 n p q index r)
  ≡ (pcrypt_increment100 n p q index r).

Axiom beta_cryptR_rec_id : forall (P : Type) 
  (ptab : forall (n : nat) (h : history 0 n), P)
  (ptabRSA : forall (n : nat) (h : history 0 n), P)
  (ptabPL : forall (n : nat) (h : history 0 n), P)
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_recbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n), 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_recbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (r : history 0 n),
  ap (cryptR_rec P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@id_cryptR n r)
  ≡ (pid n r).

Definition cryptR_indbase (P : cryptR -> Type) 
  (ptab : forall (n : nat) (h : history 0 n), P (ctab h))
  (ptabRSA : forall (n : nat) (h : history 0 n), P (ctabRSA h))
  (ptabPL : forall (n : nat) (h : history 0 n), P (ctabPL h)) 
  : forall (c : cryptR), P c
  :=
  fun c => match c as c0 return (P c0) with
           | @ctab x x0 => ptab x x0
           | @ctabRSA x x0 => ptabRSA x x0
           | @ctabPL x x0 => ptabPL x x0
           end.

Definition cryptR_ind (P : cryptR -> Type) 
  (ptab : forall (n : nat) (h : history 0 n), P (ctab h))
  (ptabRSA : forall (n : nat) (h : history 0 n), P (ctabRSA h))
  (ptabPL : forall (n : nat) (h : history 0 n), P (ctabPL h))
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n),
             (insert_query value index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (delete_query index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (rsa_enc p q r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n),
             (rsa_dec p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (paillier_enc p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (@paillier_dec n p q r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (@increment_by100 n index r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (crypt_increment_by100 p q index r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n),
          (@id_cryptR n r) #
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hid r))))
  : forall (c : cryptR), P c
  := cryptR_indbase P ptab ptabRSA ptabPL.

Axiom beta_cryptR_ind_insert : forall (P : cryptR -> Type) 
  (ptab : forall (n : nat) (h : history 0 n), P (ctab h))
  (ptabRSA : forall (n : nat) (h : history 0 n), P (ctabRSA h))
  (ptabPL : forall (n : nat) (h : history 0 n), P (ctabPL h))
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n),
             (insert_query value index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (delete_query index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (rsa_enc p q r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n),
             (rsa_dec p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (paillier_enc p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (@paillier_dec n p q r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (@increment_by100 n index r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (crypt_increment_by100 p q index r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n),
          (@id_cryptR n r) #
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (value : nat) (index : nat) (r : history 0 n),
  apD (cryptR_ind P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@insert_query n value index r)
  ≡ (pinsert n value index r).

Axiom beta_cryptR_ind_delete : forall (P : cryptR -> Type) 
  (ptab : forall (n : nat) (h : history 0 n), P (ctab h))
  (ptabRSA : forall (n : nat) (h : history 0 n), P (ctabRSA h))
  (ptabPL : forall (n : nat) (h : history 0 n), P (ctabPL h))
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n),
             (insert_query value index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (delete_query index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (rsa_enc p q r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n),
             (rsa_dec p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (paillier_enc p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (@paillier_dec n p q r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (@increment_by100 n index r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (crypt_increment_by100 p q index r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n),
          (@id_cryptR n r) #
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (index : nat) (r : history 0 (S n)),
  apD (cryptR_ind P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@delete_query n index r)
  ≡ (pdelete n index r).

Axiom beta_cryptR_ind_rsa_enc : forall (P : cryptR -> Type) 
  (ptab : forall (n : nat) (h : history 0 n), P (ctab h))
  (ptabRSA : forall (n : nat) (h : history 0 n), P (ctabRSA h))
  (ptabPL : forall (n : nat) (h : history 0 n), P (ctabPL h))
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n),
             (insert_query value index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (delete_query index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (rsa_enc p q r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n),
             (rsa_dec p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (paillier_enc p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (@paillier_dec n p q r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (@increment_by100 n index r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (crypt_increment_by100 p q index r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n),
          (@id_cryptR n r) #
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (p q : nat) (r : history 0 n),
  apD (cryptR_ind P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@rsa_enc n p q r)
  ≡ (prsa_encrypt n p q r).

Axiom beta_cryptR_ind_rsa_dec : forall (P : cryptR -> Type) 
  (ptab : forall (n : nat) (h : history 0 n), P (ctab h))
  (ptabRSA : forall (n : nat) (h : history 0 n), P (ctabRSA h))
  (ptabPL : forall (n : nat) (h : history 0 n), P (ctabPL h))
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n),
             (insert_query value index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (delete_query index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (rsa_enc p q r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n),
             (rsa_dec p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (paillier_enc p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (@paillier_dec n p q r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (@increment_by100 n index r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (crypt_increment_by100 p q index r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n),
          (@id_cryptR n r) #
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (p q : nat) (r : history 0 n),
  apD (cryptR_ind P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@rsa_dec n p q r)
  ≡ (prsa_decrypt n p q r).

Axiom beta_cryptR_ind_paillier_enc : forall (P : cryptR -> Type) 
  (ptab : forall (n : nat) (h : history 0 n), P (ctab h))
  (ptabRSA : forall (n : nat) (h : history 0 n), P (ctabRSA h))
  (ptabPL : forall (n : nat) (h : history 0 n), P (ctabPL h))
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n),
             (insert_query value index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (delete_query index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (rsa_enc p q r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n),
             (rsa_dec p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (paillier_enc p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (@paillier_dec n p q r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (@increment_by100 n index r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (crypt_increment_by100 p q index r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n),
          (@id_cryptR n r) #
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (p q : nat) (r : history 0 n),
  apD (cryptR_ind P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@paillier_enc n p q r)
  ≡ (ppaillier_encrypt n p q r).

Axiom beta_cryptR_ind_paillier_dec : forall (P : cryptR -> Type) 
  (ptab : forall (n : nat) (h : history 0 n), P (ctab h))
  (ptabRSA : forall (n : nat) (h : history 0 n), P (ctabRSA h))
  (ptabPL : forall (n : nat) (h : history 0 n), P (ctabPL h))
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n),
             (insert_query value index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (delete_query index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (rsa_enc p q r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n),
             (rsa_dec p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (paillier_enc p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (@paillier_dec n p q r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (@increment_by100 n index r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (crypt_increment_by100 p q index r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n),
          (@id_cryptR n r) #
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (p q : nat) (r : history 0 n),
  apD (cryptR_ind P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@paillier_dec n p q r)
  ≡ (ppaillier_decrypt n p q r).

Axiom beta_cryptR_ind_increment100 : forall (P : cryptR -> Type) 
  (ptab : forall (n : nat) (h : history 0 n), P (ctab h))
  (ptabRSA : forall (n : nat) (h : history 0 n), P (ctabRSA h))
  (ptabPL : forall (n : nat) (h : history 0 n), P (ctabPL h))
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n),
             (insert_query value index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (delete_query index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (rsa_enc p q r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n),
             (rsa_dec p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (paillier_enc p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (@paillier_dec n p q r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (@increment_by100 n index r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (crypt_increment_by100 p q index r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n),
          (@id_cryptR n r) #
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (index : nat) (r : history 0 n),
  apD (cryptR_ind P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@increment_by100 n index r)
  ≡ (pincrement100 n index r).

Axiom beta_cryptR_ind_crypt_increment100 : forall (P : cryptR -> Type) 
  (ptab : forall (n : nat) (h : history 0 n), P (ctab h))
  (ptabRSA : forall (n : nat) (h : history 0 n), P (ctabRSA h))
  (ptabPL : forall (n : nat) (h : history 0 n), P (ctabPL h))
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n),
             (insert_query value index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (delete_query index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (rsa_enc p q r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n),
             (rsa_dec p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (paillier_enc p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (@paillier_dec n p q r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (@increment_by100 n index r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (crypt_increment_by100 p q index r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n),
          (@id_cryptR n r) #
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (p q : nat) (index : nat) (r : history 0 n),
  apD (cryptR_ind P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@crypt_increment_by100 n p q index r)
  ≡ (pcrypt_increment100 n p q index r).

Axiom beta_cryptR_ind_id : forall (P : cryptR -> Type) 
  (ptab : forall (n : nat) (h : history 0 n), P (ctab h))
  (ptabRSA : forall (n : nat) (h : history 0 n), P (ctabRSA h))
  (ptabPL : forall (n : nat) (h : history 0 n), P (ctabPL h))
  (pinsert : forall (n : nat) (value : nat) (index : nat) (r : history 0 n),
             (insert_query value index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hinsert value index r)))
  (pdelete : forall (n : nat) (index : nat) (r : history 0 (S n)), 
             (delete_query index r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hdelete index r)))
  (prsa_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (rsa_enc p q r) # 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabRSA (hrsa_encrypt p q r)))
  (prsa_decrypt : forall (n : nat) (p q : nat) (r : history 0 n),
             (rsa_dec p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabRSA r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctab (hrsa_decrypt p q r)))
  (ppaillier_encrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (paillier_enc p q r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL) (ctabPL (hpaillier_encrypt p q r)))
  (ppaillier_decrypt : forall (n : nat) (p q : nat) (r : history 0 n), 
             (@paillier_dec n p q r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hpaillier_decrypt p q r))))
  (pincrement100 : forall (n : nat) (index : nat) (r : history 0 n), 
             (@increment_by100 n index r) #
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hincrement100 index r))))
  (pcrypt_increment100 : forall (n : nat) (p q : nat) (index : nat) (r : history 0 n), 
             (crypt_increment_by100 p q index r) #  
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL r)) ≡ 
             (cryptR_indbase P ptab ptabRSA ptabPL (ctabPL (hcrypt_increment100 p q index r))))
  (pid : forall (n : nat) (r : history 0 n),
          (@id_cryptR n r) #
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab r)) ≡ 
          (cryptR_indbase P ptab ptabRSA ptabPL (ctab (hid r))))
  {n : nat} (r : history 0 n),
  apD (cryptR_ind P ptab ptabRSA ptabPL pinsert pdelete prsa_encrypt prsa_decrypt 
                 ppaillier_encrypt ppaillier_decrypt pincrement100 pcrypt_increment100 pid)
     (@id_cryptR n r)
  ≡ (pid n r).

End Repo.


Definition I_cryptR (inputRec : cryptR) : Type 
  := cryptR_rec Type 
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n val i r => ua (@singleton_equiv (list nat) (list nat) (insert val i) _ (to_Singleton (insert val i))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (delete i) _ (to_Singleton (delete i))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_encrypt p q) _ (to_Singleton (rsa_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_decrypt p q) _ (to_Singleton (rsa_decrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_encrypt p q) _ (to_Singleton (paillier_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_decrypt p q) _ (to_Singleton (paillier_decrypt p q))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (increment_100 i) _ (to_Singleton (increment_100 i))))
       (fun n p q i r => ua (@singleton_equiv (list nat) (list nat) (crypt_increment_100 p q i) _ (to_Singleton (crypt_increment_100 p q i))))
       (fun n r => ua (@singleton_equiv (list nat) (list nat) id _ (to_Singleton id)))
       inputRec.

Definition I_cryptR_insert_path {n} (value : nat) (i : nat) (r : history 0 n) :
  ap I_cryptR (insert_query value i r) ≡ ua (@singleton_equiv (list nat) (list nat) (insert value i) _ (to_Singleton (insert value i)))
  := beta_cryptR_rec_insert Type
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n val i r => ua (@singleton_equiv (list nat) (list nat) (insert val i) _ (to_Singleton (insert val i))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (delete i) _ (to_Singleton (delete i))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_encrypt p q) _ (to_Singleton (rsa_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_decrypt p q) _ (to_Singleton (rsa_decrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_encrypt p q) _ (to_Singleton (paillier_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_decrypt p q) _ (to_Singleton (paillier_decrypt p q))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (increment_100 i) _ (to_Singleton (increment_100 i))))
       (fun n p q i r => ua (@singleton_equiv (list nat) (list nat) (crypt_increment_100 p q i) _ (to_Singleton (crypt_increment_100 p q i))))
       (fun n r => ua (@singleton_equiv (list nat) (list nat) id _ (to_Singleton id)))
       value i r.

Definition I_cryptR_delete_path {n} (i : nat) (r : history 0 (S n)) :
  ap I_cryptR (delete_query i r) ≡ ua (@singleton_equiv (list nat) (list nat) (delete i) _ (to_Singleton (delete i)))
  := beta_cryptR_rec_delete Type
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n val i r => ua (@singleton_equiv (list nat) (list nat) (insert val i) _ (to_Singleton (insert val i))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (delete i) _ (to_Singleton (delete i))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_encrypt p q) _ (to_Singleton (rsa_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_decrypt p q) _ (to_Singleton (rsa_decrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_encrypt p q) _ (to_Singleton (paillier_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_decrypt p q) _ (to_Singleton (paillier_decrypt p q))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (increment_100 i) _ (to_Singleton (increment_100 i))))
       (fun n p q i r => ua (@singleton_equiv (list nat) (list nat) (crypt_increment_100 p q i) _ (to_Singleton (crypt_increment_100 p q i))))
       (fun n r => ua (@singleton_equiv (list nat) (list nat) id _ (to_Singleton id)))
       i r.

Definition I_cryptR_rsa_encrypt {n} (p q : nat) (r : history 0 n) :
  ap I_cryptR (rsa_enc p q r) ≡ ua (@singleton_equiv (list nat) (list nat) (rsa_encrypt p q) _ (to_Singleton (rsa_encrypt p q)))
  := beta_cryptR_rec_rsa_encrypt Type
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n val i r => ua (@singleton_equiv (list nat) (list nat) (insert val i) _ (to_Singleton (insert val i))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (delete i) _ (to_Singleton (delete i))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_encrypt p q) _ (to_Singleton (rsa_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_decrypt p q) _ (to_Singleton (rsa_decrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_encrypt p q) _ (to_Singleton (paillier_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_decrypt p q) _ (to_Singleton (paillier_decrypt p q))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (increment_100 i) _ (to_Singleton (increment_100 i))))
       (fun n p q i r => ua (@singleton_equiv (list nat) (list nat) (crypt_increment_100 p q i) _ (to_Singleton (crypt_increment_100 p q i))))
       (fun n r => ua (@singleton_equiv (list nat) (list nat) id _ (to_Singleton id)))
       p q r.

Definition I_cryptR_rsa_decrypt {n} (p q : nat) (r : history 0 n) :
  ap I_cryptR (rsa_dec p q r) ≡ ua (@singleton_equiv (list nat) (list nat) (rsa_decrypt p q) _ (to_Singleton (rsa_decrypt p q)))
  := beta_cryptR_rec_rsa_decrypt Type
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n val i r => ua (@singleton_equiv (list nat) (list nat) (insert val i) _ (to_Singleton (insert val i))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (delete i) _ (to_Singleton (delete i))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_encrypt p q) _ (to_Singleton (rsa_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_decrypt p q) _ (to_Singleton (rsa_decrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_encrypt p q) _ (to_Singleton (paillier_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_decrypt p q) _ (to_Singleton (paillier_decrypt p q))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (increment_100 i) _ (to_Singleton (increment_100 i))))
       (fun n p q i r => ua (@singleton_equiv (list nat) (list nat) (crypt_increment_100 p q i) _ (to_Singleton (crypt_increment_100 p q i))))
       (fun n r => ua (@singleton_equiv (list nat) (list nat) id _ (to_Singleton id)))
       p q r.

Definition I_cryptR_paillier_encrypt {n} (p q : nat) (r : history 0 n) :
  ap I_cryptR (paillier_enc p q r) ≡ ua (@singleton_equiv (list nat) (list nat) (paillier_encrypt p q) _ (to_Singleton (paillier_encrypt p q)))
  := beta_cryptR_rec_paillier_encrypt Type
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n val i r => ua (@singleton_equiv (list nat) (list nat) (insert val i) _ (to_Singleton (insert val i))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (delete i) _ (to_Singleton (delete i))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_encrypt p q) _ (to_Singleton (rsa_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_decrypt p q) _ (to_Singleton (rsa_decrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_encrypt p q) _ (to_Singleton (paillier_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_decrypt p q) _ (to_Singleton (paillier_decrypt p q))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (increment_100 i) _ (to_Singleton (increment_100 i))))
       (fun n p q i r => ua (@singleton_equiv (list nat) (list nat) (crypt_increment_100 p q i) _ (to_Singleton (crypt_increment_100 p q i))))
       (fun n r => ua (@singleton_equiv (list nat) (list nat) id _ (to_Singleton id)))
       p q r.

Definition I_cryptR_paillier_decrypt {n} (p q : nat) (r : history 0 n) :
  ap I_cryptR (paillier_dec p q r) ≡ ua (@singleton_equiv (list nat) (list nat) (paillier_decrypt p q) _ (to_Singleton (paillier_decrypt p q)))
  := beta_cryptR_rec_paillier_decrypt Type
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n val i r => ua (@singleton_equiv (list nat) (list nat) (insert val i) _ (to_Singleton (insert val i))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (delete i) _ (to_Singleton (delete i))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_encrypt p q) _ (to_Singleton (rsa_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_decrypt p q) _ (to_Singleton (rsa_decrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_encrypt p q) _ (to_Singleton (paillier_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_decrypt p q) _ (to_Singleton (paillier_decrypt p q))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (increment_100 i) _ (to_Singleton (increment_100 i))))
       (fun n p q i r => ua (@singleton_equiv (list nat) (list nat) (crypt_increment_100 p q i) _ (to_Singleton (crypt_increment_100 p q i))))
       (fun n r => ua (@singleton_equiv (list nat) (list nat) id _ (to_Singleton id)))
       p q r.

Definition I_cryptR_increment100 {n} (i : nat) (r : history 0 n) :
  ap I_cryptR (increment_by100 i r) ≡ ua (@singleton_equiv (list nat) (list nat) (increment_100 i) _ (to_Singleton (increment_100 i)))
  := beta_cryptR_rec_increment100 Type
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n val i r => ua (@singleton_equiv (list nat) (list nat) (insert val i) _ (to_Singleton (insert val i))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (delete i) _ (to_Singleton (delete i))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_encrypt p q) _ (to_Singleton (rsa_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_decrypt p q) _ (to_Singleton (rsa_decrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_encrypt p q) _ (to_Singleton (paillier_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_decrypt p q) _ (to_Singleton (paillier_decrypt p q))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (increment_100 i) _ (to_Singleton (increment_100 i))))
       (fun n p q i r => ua (@singleton_equiv (list nat) (list nat) (crypt_increment_100 p q i) _ (to_Singleton (crypt_increment_100 p q i))))
       (fun n r => ua (@singleton_equiv (list nat) (list nat) id _ (to_Singleton id)))
       i r.

Definition I_cryptR_crypt_increment100 {n} (p q : nat) (i : nat) (r : history 0 n) :
  ap I_cryptR (crypt_increment_by100 p q i r) ≡ ua (@singleton_equiv (list nat) (list nat) (crypt_increment_100 p q i) _ (to_Singleton (crypt_increment_100 p q i)))
  := beta_cryptR_rec_crypt_increment100 Type
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n val i r => ua (@singleton_equiv (list nat) (list nat) (insert val i) _ (to_Singleton (insert val i))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (delete i) _ (to_Singleton (delete i))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_encrypt p q) _ (to_Singleton (rsa_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_decrypt p q) _ (to_Singleton (rsa_decrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_encrypt p q) _ (to_Singleton (paillier_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_decrypt p q) _ (to_Singleton (paillier_decrypt p q))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (increment_100 i) _ (to_Singleton (increment_100 i))))
       (fun n p q i r => ua (@singleton_equiv (list nat) (list nat) (crypt_increment_100 p q i) _ (to_Singleton (crypt_increment_100 p q i))))
       (fun n r => ua (@singleton_equiv (list nat) (list nat) id _ (to_Singleton id)))
       p q i r.

Definition I_cryptR_id {n} (r : history 0 n) :
  ap I_cryptR (id_cryptR r) ≡ ua (@singleton_equiv (list nat) (list nat) id _ (to_Singleton id))
  := beta_cryptR_rec_id Type
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n x => (Singleton (replay x)))
       (fun n val i r => ua (@singleton_equiv (list nat) (list nat) (insert val i) _ (to_Singleton (insert val i))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (delete i) _ (to_Singleton (delete i))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_encrypt p q) _ (to_Singleton (rsa_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (rsa_decrypt p q) _ (to_Singleton (rsa_decrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_encrypt p q) _ (to_Singleton (paillier_encrypt p q))))
       (fun n p q r => ua (@singleton_equiv (list nat) (list nat) (paillier_decrypt p q) _ (to_Singleton (paillier_decrypt p q))))
       (fun n i r => ua (@singleton_equiv (list nat) (list nat) (increment_100 i) _ (to_Singleton (increment_100 i))))
       (fun n p q i r => ua (@singleton_equiv (list nat) (list nat) (crypt_increment_100 p q i) _ (to_Singleton (crypt_increment_100 p q i))))
       (fun n r => ua (@singleton_equiv (list nat) (list nat) id _ (to_Singleton id)))
       r.

Definition interp1 {a b : cryptR} (p : a ≡ b) : (equiv (I_cryptR a) (I_cryptR b))
  := coe_biject (ap I_cryptR p).

Definition interp2 {a b : cryptR} (p : a ≡ b) : (I_cryptR a) -> (I_cryptR b)
  := coe (ap I_cryptR p).

(* Definition interp3 {a b : cryptR} (p q : a ≡ b) (x : p ≡ q) : (equiv (I_cryptR a ≡ I_cryptR b) (I_cryptR a ≡ I_cryptR b))
  := coe_biject (apI_path I_cryptR x). *)

