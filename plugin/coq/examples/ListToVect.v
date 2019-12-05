(*
 * Section 5 Preprocess Example
 *)

Require Import Vector.
Require Import List.

Require Import Ornamental.Ornaments.

Notation vector := Vector.t.

(* --- Preprocess --- *)

Preprocess Module List as List' { opaque (* ignore these: *)
  (* dependent elimination only: *)
  RelationClasses.StrictOrder_Transitive
  RelationClasses.StrictOrder_Irreflexive
  RelationClasses.Equivalence_Symmetric
  RelationClasses.Equivalence_Transitive
  RelationClasses.PER_Symmetric
  RelationClasses.PER_Transitive
  RelationClasses.Equivalence_Reflexive
  (* proofs about these match over the above opaque terms, and would fail: *)
  Nat.add
  Nat.sub
}.  

(* --- Search & Lift --- *)

(*
 * Whole-module lifting doesn't exist yet, so for now we have to do this
 * one function and proof at a time.
 *
 * We use automatic search here rather than calling Find Ornament ourselves.
 *
 * There are still two proofs that fail to lift below, due to implementation bugs.
 * See: https://github.com/uwplse/ornamental-search/issues/32
 *)

Module MyVector.

  Lift list vector in List'.Coq_Init_Datatypes_length as .. _p.
  
  Lift list vector in List'.Coq_Init_Datatypes_app as .. _p.

  Lift list vector in List'.hd as .. _p.

  Lift list vector in List'.hd_error as .. _p.

  Lift list vector in List'.tl as .. _p.

  Lift list vector in List'.In as .. _p.

  Lift list vector in List'.nil_cons as .. _p.

  Lift list vector in List'.destruct_list as .. _p.

  Lift list vector in List'.hd_error_tl_repr as .. _p.

  Lift list vector in List'.hd_error_some_nil as .. _p.

  Lift list vector in List'.length_zero_iff_nil as .. _p.

  Lift list vector in List'.hd_error_nil as .. _p. 

  Lift list vector in List'.hd_error_cons as .. _p. 

  Lift list vector in List'.in_eq as .. _p. 

  Lift list vector in List'.in_cons as .. _p. 

  Lift list vector in List'.not_in_cons as .. _p. 

  Lift list vector in List'.in_nil as .. _p. 

  Lift list vector in List'.in_split as .. _p. 

  Lift list vector in List'.in_inv as .. _p. 

  Lift list vector in List'.in_dec as .. _p. 

  Lift list vector in List'.app_cons_not_nil as .. _p. 

  Lift list vector in List'.app_nil_l as .. _p. 

  Lift list vector in List'.app_nil_r as .. _p.
 
  Lift list vector in List'.app_nil_end as .. _p.

  Lift list vector in List'.app_assoc as .. _p. 

  Lift list vector in List'.app_assoc_reverse as .. _p.

  Lift list vector in List'.app_comm_cons as .. _p. 

  Lift list vector in List'.app_eq_nil as .. _p. 

  Lift list vector in List'.app_eq_unit as .. _p.

  Lift list vector in List'.app_inj_tail as .. _p. 
 
  Lift list vector in List'.app_length as .. _p. 

  Lift list vector in List'.in_app_or as .. _p. 

  Lift list vector in List'.in_or_app as .. _p. 

  Lift list vector in List'.in_app_iff as .. _p. 

  Lift list vector in List'.app_inv_head as .. _p. 

  Lift list vector in List'.app_inv_tail as .. _p.  

  Lift list vector in List'.nth as .. _p. 

  Lift list vector in List'.nth_ok as .. _p. 

  Lift list vector in List'.nth_in_or_default as .. _p. 

  Lift list vector in List'.nth_S_cons as .. _p. 

  Lift list vector in List'.nth_error as .. _p. 

  Lift list vector in List'.nth_default as .. _p. 

  Lift list vector in List'.nth_default_eq as .. _p. 

  Lift list vector in List'.nth_In as .. _p. 

  Lift list vector in List'.In_nth as .. _p. 

  Lift list vector in List'.nth_overflow as .. _p. 

  Lift list vector in List'.nth_indep as .. _p. 

  Lift list vector in List'.app_nth1 as .. _p. 

  Lift list vector in List'.app_nth2 as .. _p. 

  Lift list vector in List'.nth_split as .. _p. 

  Lift list vector in List'.nth_error_In as .. _p. 

  Lift list vector in List'.In_nth_error as .. _p. 

  Lift list vector in List'.nth_error_None as .. _p. 

  Lift list vector in List'.nth_error_Some as .. _p. 

  Lift list vector in List'.nth_error_split as .. _p. 

  Lift list vector in List'.nth_error_app1 as .. _p. 

  Lift list vector in List'.nth_error_app2  as .. _p. 

  Lift list vector in List'.remove as .. _p. 

  Lift list vector in List'.remove_In as .. _p. 

  Lift list vector in List'.last as .. _p.

  Lift list vector in List'.removelast as .. _p. 

  Lift list vector in List'.app_removelast_last as .. _p. 

  Lift list vector in List'.exists_last as .. _p. 

  Lift list vector in List'.removelast_app as .. _p. 

  Lift list vector in List'.count_occ as .. _p. 

  Lift list vector in List'.count_occ_In as .. _p. 

  Lift list vector in List'.count_occ_not_In as .. _p. 

  Lift list vector in List'.count_occ_nil as .. _p. 

  Lift list vector in List'.count_occ_inv_nil as .. _p. 

  Lift list vector in List'.count_occ_cons_eq as .. _p. 

  Lift list vector in List'.count_occ_cons_neq  as .. _p. 

  Lift list vector in List'.rev as .. _p. 

  Lift list vector in List'.rev_app_distr as .. _p. 

  Lift list vector in List'.rev_unit as .. _p. 

  Lift list vector in List'.rev_involutive as .. _p. 

  Lift list vector in List'.in_rev as .. _p. 

  Lift list vector in List'.rev_length as .. _p.

  Lift list vector in List'.rev_nth as .. _p.

  Lift list vector in List'.rev_append as .. _p.

  Lift list vector in List'.rev' as .. _p.

  Lift list vector in List'.rev_append_rev as .. _p. 

  Lift list vector in List'.rev_alt as .. _p. 

  Lift list vector in List'.rev_list_ind as .. _p.

  Lift list vector in List'.rev_ind as .. _p.

  Lift list vector in List'.concat as .. _p.

  Lift list vector in List'.concat_nil as .. _p.

  Lift list vector in List'.concat_cons as .. _p.

  Lift list vector in List'.concat_app as .. _p. 

  Lift list vector in List'.list_eq_dec as .. _p.

  Lift list vector in List'.map as .. _p.

  Lift list vector in List'.map_cons as .. _p.

  Lift list vector in List'.in_map as .. _p.

  Lift list vector in List'.in_map_iff as .. _p.

  Lift list vector in List'.map_length as .. _p.

  Lift list vector in List'.map_nth as .. _p.

  Lift list vector in List'.map_nth_error as .. _p.

  Lift list vector in List'.map_app as .. _p.

  Lift list vector in List'.map_rev as .. _p.

  Lift list vector in List'.map_eq_nil as .. _p.

  Lift list vector in List'.count_occ_map as .. _p.

  Lift list vector in List'.flat_map as .. _p.

  Lift list vector in List'.in_flat_map as .. _p.

  Lift list vector in List'.flat_map_concat_map as .. _p.

  Lift list vector in List'.concat_map as .. _p.

  Lift list vector in List'.map_id as .. _p.

  Lift list vector in List'.map_map as .. _p.

  Lift list vector in List'.map_ext_in as .. _p.

  Lift list vector in List'.map_ext as .. _p.

  Lift list vector in List'.fold_left as .. _p.

  Lift list vector in List'.fold_left_app as .. _p.

  Lift list vector in List'.fold_left_length as .. _p.

  Lift list vector in List'.fold_right as .. _p.

  Lift list vector in List'.fold_right_app as .. _p.

  Lift list vector in List'.fold_left_rev_right as .. _p.

  Lift list vector in List'.fold_symmetric as .. _p.

  Lift list vector in List'.list_power as .. _p.

  Lift list vector in List'.existsb as .. _p.

  Lift list vector in List'.existsb_exists as .. _p.

  Lift list vector in List'.existsb_nth as .. _p.

  Lift list vector in List'.existsb_app as .. _p.

  Lift list vector in List'.forallb as .. _p.

  Lift list vector in List'.forallb_forall as .. _p.

  Lift list vector in List'.forallb_app as .. _p.

  Lift list vector in List'.filter as .. _p.

  Lift list vector in List'.filter_In as .. _p.

  Lift list vector in List'.find as .. _p.

  Lift list vector in List'.find_some as .. _p.

  Lift list vector in List'.find_none as .. _p.

  Lift list vector in List'.partition as .. _p.

  Lift list vector in List'.partition_cons1 as .. _p.

  Lift list vector in List'.partition_cons2 as .. _p.
 
  Fail Lift list vector in List'.partition_length as .. _p.

  Lift list vector in List'.partition_inv_nil  as .. _p.

  Fail Lift list vector in List'.elements_in_partition as .. _p.

  Lift list vector in List'.split as .. _p.

  Lift list vector in List'.in_split_l as .. _p.

  Lift list vector in List'.in_split_r as .. _p.

  Lift list vector in List'.split_nth as .. _p.

  Lift list vector in List'.split_length_l as .. _p.

  Lift list vector in List'.split_length_r as .. _p.

  Lift list vector in List'.combine as .. _p.

  Lift list vector in List'.split_combine as .. _p.

  Lift list vector in List'.combine_split as .. _p.

  Lift list vector in List'.in_combine_l as .. _p.

  Lift list vector in List'.in_combine_r as .. _p.

  Lift list vector in List'.combine_length as .. _p.

  Lift list vector in List'.combine_nth as .. _p.

  Lift list vector in List'.list_prod as .. _p.

  Lift list vector in List'.in_prod_aux as .. _p.

  Lift list vector in List'.in_prod as .. _p.

  Lift list vector in List'.in_prod_iff as .. _p.

  Lift list vector in List'.prod_length as .. _p.

  Lift list vector in List'.lel as .. _p.

  Lift list vector in List'.lel_refl as .. _p.

  Lift list vector in List'.lel_trans as .. _p.

  Lift list vector in List'.lel_cons_cons as .. _p.

  Lift list vector in List'.lel_cons as .. _p.

  Lift list vector in List'.lel_tail as .. _p.

  Lift list vector in List'.lel_nil as .. _p.

  Lift list vector in List'.incl as .. _p.

  Lift list vector in List'.incl_refl as .. _p.

  Lift list vector in List'.incl_tl as .. _p.

  Lift list vector in List'.incl_tran as .. _p.

  Lift list vector in List'.incl_appl as .. _p.

  Lift list vector in List'.incl_appr as .. _p.

  Lift list vector in List'.incl_cons as .. _p.

  Lift list vector in List'.incl_app as .. _p.

  Lift list vector in List'.firstn as .. _p.

  Lift list vector in List'.firstn_nil as .. _p.

  Lift list vector in List'.firstn_cons as .. _p.

  Lift list vector in List'.firstn_all as .. _p.

  Lift list vector in List'.firstn_all2 as .. _p.

  Lift list vector in List'.firstn_O as .. _p.

  Lift list vector in List'.firstn_le_length as .. _p.

  Lift list vector in List'.firstn_length_le as .. _p.

  Lift list vector in List'.firstn_app as .. _p.

  Lift list vector in List'.firstn_app_2 as .. _p.

  Lift list vector in List'.firstn_firstn as .. _p.

  Lift list vector in List'.skipn as .. _p.

  Lift list vector in List'.firstn_skipn as .. _p.

  Lift list vector in List'.firstn_length as .. _p.

  Lift list vector in List'.removelast_firstn as .. _p.

  Lift list vector in List'.firstn_removelast as .. _p.

  (* ... you get the point. Some implementation bugs to work out
    (the next inductive type, Add, would fail because of a bug in lifting
    inductive propositions which tries to use the wrong eliminator)
    but you could lift this way, and then unpack if you want to get 
    a vector library. *)

End MyVector.
