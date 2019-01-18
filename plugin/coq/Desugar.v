Add LoadPath "coq".
Require Import Ornamental.Ornaments.
Require Import Test.
Require Import List.

(** Test a few hand-written functions on vector **)
Section VectorTests.

  Arguments nilV {A}.
  Arguments consV {A}.

  Definition emptyV (A : Type) (xs : {n:nat & vector A n}) : bool :=
    match projT2 xs with
    | consV _ _ _ => false
    | nilV => true
    end.
  Desugar emptyV as emptyV'.

  Definition headV (A : Type) (n : nat) (xs : vector A (S n)) : A :=
    match xs in vector _ n return (match n with S _ => True | O => False end) -> A with
    | consV _ x _ => True_rect x
    | nilV => False_rect A
    end
      I.
  Desugar headV as headV'.

  Definition tailV (A : Type) (n : nat) (xs : vector A (S n)) : vector A n :=
    match xs in vector _ (S n) return vector A n with
    | consV _ _ xs => xs
    end.
  Desugar tailV as tailV'.

End VectorTests.

(** Test a sample of List functions and proofs **)
Section ListTests.

  Desugar hd as hd'.
  Desugar hd_error as hd_error'.
  Desugar tl as tl'.
  Desugar In as In'.
  Desugar nil_cons as nil_cons'.
  Desugar destruct_list as destruct_list'.
  Desugar hd_error_tl_repr as hd_error_tl_repr'.
  Desugar length_zero_iff_nil as length_zero_iff_nil'.
  Desugar hd_error_nil as hd_error_nil'.
  Desugar hd_error_cons as hd_error_cons'.
  Desugar in_eq as in_eq'.
  Desugar in_cons as in_cons'.
  Desugar not_in_cons as not_in_cons'.
  Desugar in_nil as in_nil'.
  Desugar in_split as in_split'.
  Desugar in_dec as in_dec'.
  Desugar app_cons_not_nil as app_cons_not_nil'.
  Desugar app_nil_l as app_nil_l'.
  Desugar app_nil_r as app_nil_r'.
  Desugar app_nil_end as app_nil_end'.
  Desugar app_assoc as app_assoc'.
  Desugar app_assoc_reverse as app_assoc_reverse'.
  Desugar app_comm_cons as app_comm_cons'.
  Desugar app_eq_nil as app_eq_nil'.
  Desugar app_eq_unit as app_eq_unit'.
  Desugar app_length as app_length'.
  Desugar in_app_or as in_app_or'.
  Desugar in_or_app as in_or_app'.
  Desugar in_app_iff as in_app_iff'.
  Desugar app_inv_head as app_inv_head'.
  Desugar app_inv_tail as app_inv_tail'.
  Desugar nth as nth'.
  Desugar nth_ok as nth_ok'.
  Desugar nth_in_or_default as nth_in_or_default'.
  Desugar nth_S_cons as nth_S_cons'.
  Desugar nth_error as nth_error'.
  Desugar nth_default as nth_default'.
  Desugar nth_default_eq as nth_default_eq'.
  Desugar nth_overflow as nth_overflow'.
  Desugar nth_indep as nth_indep'.
  Desugar app_nth1 as app_nth1'.
  Desugar app_nth2 as app_nth2'.
  Desugar nth_split as nth_split'.
  Desugar nth_error_In as nth_error_In'.
  Desugar nth_error_None as nth_error_None'.
  Desugar nth_error_Some as nth_error_Some'.
  Desugar nth_error_split as nth_error_split'.
  Desugar nth_error_app1 as nth_error_app1'.
  Desugar nth_error_app2 as nth_error_app2'.
  Desugar remove as remove'.
  Desugar last as last'.
  Desugar removelast as removelast'.
  Desugar app_removelast_last as app_removelast_last'.
  Desugar exists_last as exists_last'.

End ListTests.
