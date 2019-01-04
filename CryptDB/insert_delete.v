Module Export Insert_Delete.

(* Notation "(x :: y)%list" := (x :: y) : type_scope. *)

Fixpoint insert 
  (value : nat)
  (index : nat)
  (input : list nat)
  : list nat
  := match index, input with
     | 0   ,  nil => value :: nil
     | (S i) , nil => nil
     | 0 , (x :: xs)%list => (value :: (x :: xs)%list)%list
     | (S i) , (x :: xs)%list => (x :: (insert value i xs))%list
     end. 

Fixpoint delete
  (index : nat)
  (input : list nat)
  : list nat
  := match index, input with
     | 0 , nil => nil
     | 0, (x :: xs)%list => xs
     | (S i) , nil => nil
     | (S i) , (x :: xs)%list => (x :: (delete i xs))%list
     end.


End Insert_Delete.