Require Import List.

Import ListNotations.

Require Import Ornamental.Ornaments.
Set DEVOID search prove equivalence.
Set DEVOID lift type.

(* Preprocess for lifting: *)
Preprocess Module List as List_pre { opaque (* ignore these nested modules: *)
  RelationClasses
  Nat Coq.Init.Nat 
  Coq.Init.Logic Coq.Init.Peano
  Coq.Init.Datatypes.list_ind Coq.Init.Datatypes.list_rect Coq.Init.Datatypes.list_rec
  Coq.Init.Datatypes.nat_ind Coq.Init.Datatypes.nat_rect Coq.Init.Datatypes.nat_rec
  eq_ind eq_ind_r eq_rec eq_rec_r eq_rect eq_rect_r
}.

Inductive revList (T : Type) : Type :=
| nil : revList T
| cons : T -> revList T -> revList T.

Print List_pre.rev.
Print List_pre.Coq_Init_Datatypes_app.

Definition f_helper (T : Type) (l : revList T) :=
  revList_rect
    T
    (fun _ : revList T => revList T -> revList T)
    (fun m : revList T => m)
    (fun (t : T) _ (app : revList T -> revList T) (m : revList T) => 
      cons T t (app m))
    l.

Definition f (T : Type) (l : list T) : revList T :=
  @list_rect
    T
    (fun _ : list T => revList T)
    (nil T)
    (fun (t : T) _ (rev : revList T) =>
      f_helper T rev (cons T t (nil T)))
    l.

Eval compute in (f _ (5 :: [7])).

(*
 * What is the corresponding eliminator?
 *)


