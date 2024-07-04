From Ornamental Require Import Ornaments.
Require Import Foo.Infrastructure.

Set DEVOID search prove equivalence.
Set DEVOID lift type.
Set Nonrecursive Elimination Schemes.

(*
 * This code is a minimized example from @ptival, which I use as a regression test
 * to make sure projections aren't expanded and left as applications of prod_rect,
 * and that projections/accessors lift to accessors/projections.
 *
 * The proofs here are purposely brittle, since they should break if the terms are not _exactly_ syntactically equal.
 *)

Module Pairs.

  Definition profile : Type := (bool * nat).

  Definition page : Type := (nat * (nat * (bool * ((bool * nat) * nat)))).

  Definition visible (pr : profile) (pa : page) : bool :=
    andb (fst pr) (fst (snd (snd pa))).

End Pairs.

Preprocess Module Pairs as Pairs_PP { opaque andb }.

Module Records.

  Record Profile :=
    {
      public : bool;
      age : nat;
    }.

  Definition is_public (pr : Pairs.profile) : bool := fst pr.

  Definition get_age (pr : Pairs.profile) : nat := snd pr.

End Records.

Preprocess Module Records as Records_PP.

Lift Records_PP.Profile Pairs_PP.profile in Records_PP.public as is_public.
Lift Pairs_PP.profile Records_PP.Profile in Records_PP.is_public as public.

Definition is_public_expected (h : Pairs_PP.profile) :=
  Prod.fst _ _ h.

Lemma test_is_public:
  is_public = is_public_expected.
Proof.
  unfold is_public, is_public_expected.
  test_exact_equality.
Qed.

Lemma test_public:
  public = fun h => Records_PP.public h.
Proof.
  unfold public.
  test_exact_equality.
Qed.

Lift Records_PP.Profile Pairs_PP.profile in Records_PP.age as get_age.
Lift Pairs_PP.profile Records_PP.Profile in Records_PP.get_age as age.

Definition get_age_expected (h : Pairs_PP.profile) :=
  Prod.snd _ _ h.

Lemma test_get_h_n:
  get_age = get_age_expected.
Proof.
  unfold get_age, get_age_expected.
  test_exact_equality.
Qed.

Lemma testGetHN:
  age = fun (h : Records_PP.Profile) => Records_PP.age h.
Proof.
  unfold age. 
  test_exact_equality.
Qed.

Lift Pairs_PP.profile Records_PP.Profile in Pairs_PP.visible as visible_PP { opaque andb }.

Definition visible_PP_expected (pr : Records_PP.Profile) (pa : nat * (nat * (bool * (Records_PP.Profile * nat)))) : bool :=
 Records_PP.public pr 
 &&
 Pairs_PP.Coq_Init_Datatypes_fst bool (Records_PP.Profile * nat)
   (Pairs_PP.Coq_Init_Datatypes_snd nat (bool * (Records_PP.Profile * nat))
      (Pairs_PP.Coq_Init_Datatypes_snd nat (nat * (bool * (Records_PP.Profile * nat))) pa)).

Lemma test_visible_PP:
  visible_PP = visible_PP_expected.
Proof.
  unfold visible_PP, visible_PP_expected.
  test_exact_equality.
Qed.

Module MoreRecords.

  Record Page :=
    {
      friends : nat;
      groups : nat;
      active  : bool;
      profile  : Records_PP.Profile;
      photos : nat;
    }.

  (* We'd like to wrap the ugly access into this: *)
  Definition is_active (pa : Pairs.page) : bool := fst (snd (snd pa)).

End MoreRecords.

Preprocess Module MoreRecords as MoreRecords_PP.

Lift Pairs_PP.profile Records_PP.Profile in Pairs_PP.page as page_PP.

Lift Pairs_PP.profile Records_PP.Profile in MoreRecords_PP.is_active as active0.
Lift page_PP MoreRecords_PP.Page in active0 as active.

Lift Pairs_PP.profile Records_PP.Profile in Pairs_PP.visible as visible0 { opaque andb }.
Lift page_PP MoreRecords_PP.Page in visible0 as visible { opaque andb }.

Definition visible_expected (pr : Records_PP.Profile) (pa : MoreRecords_PP.Page) : bool :=
  (Records_PP.public pr && MoreRecords_PP.active pa)%bool.

Lemma test_visible :
  visible = visible_expected.
Proof.
  unfold visible, visible_expected.
  test_exact_equality.
Qed.
