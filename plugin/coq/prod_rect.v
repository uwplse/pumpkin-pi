From Ornamental Require Import Ornaments.

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

Module SN.

  Definition h : Type := (bool * nat).

  Definition c : Type := (nat * (nat * (bool * ((bool * nat) * nat)))).

  Definition f (h : h) (c : c) : bool :=
    andb (fst h) (fst (snd (snd c))).

End SN.

Preprocess Module SN as SN_PP { opaque andb }.

Module H.

  Record H :=
    {
      b : bool;
      n : nat;
    }.

  Definition get_h_b (h : SN.h) : bool := fst h.

  Definition get_h_n (h : SN.h) : nat := snd h.

End H.

Preprocess Module H as H_PP.

Lift H_PP.H SN_PP.h in H_PP.b as get_h_b.
Lift SN_PP.h H_PP.H in H_PP.get_h_b as getHB.

Definition get_h_b_expected (h : SN_PP.h) :=
  Prod.fst _ _ h.

Lemma test_get_h_b:
  get_h_b = get_h_b_expected.
Proof.
  unfold get_h_b, get_h_b_expected.
  match goal with
  | |- ?x = ?x => reflexivity
  | _ => idtac
  end.
Qed.

Lemma testGetHB:
  getHB = fun h => H_PP.b h.
Proof.
  unfold getHB.
  match goal with
  | |- ?x = ?x => reflexivity
  | _ => idtac
  end.
Qed.

Lift H_PP.H SN_PP.h in H_PP.n as get_h_n.
Lift SN_PP.h H_PP.H in H_PP.get_h_n as getHN.

Definition get_h_n_expected (h : SN_PP.h) :=
  Prod.snd _ _ h.

Lemma test_get_h_n:
  get_h_n = get_h_n_expected.
Proof.
  unfold get_h_n, get_h_n_expected.
  match goal with
  | |- ?x = ?x => reflexivity
  | _ => idtac
  end.
Qed.

Lemma testGetHN:
  getHN = fun (h : H_PP.H) => H_PP.n h.
Proof.
  unfold getHN. 
  match goal with
  | |- ?x = ?x => reflexivity
  | _ => idtac
  end.
Qed.

Lift SN_PP.h H_PP.H in SN_PP.f as f_PP { opaque andb }.
Print f_PP.

Definition f_PP_expected (h : H_PP.H) (c : nat * (nat * (bool * (H_PP.H * nat)))) : bool :=
 H_PP.b h 
 &&
 SN_PP.Coq_Init_Datatypes_fst bool (H_PP.H * nat)
   (SN_PP.Coq_Init_Datatypes_snd nat (bool * (H_PP.H * nat))
      (SN_PP.Coq_Init_Datatypes_snd nat (nat * (bool * (H_PP.H * nat))) c)).

Lemma test_f_PP:
  f_PP = f_PP_expected.
Proof.
  unfold f_PP, f_PP_expected.
  match goal with
  | |- ?x = ?x => reflexivity
  | _ => idtac
  end.
Qed.

Module C.

  Record C :=
    {
      n1 : nat;
      n2 : nat;
      b  : bool;
      h  : H_PP.H;
      n3 : nat;
    }.

  (* We'd like to wrap the ugly access into this: *)
  Definition get_c_b (c : SN.c) : bool := fst (snd (snd c)).

End C.

Preprocess Module C as C_PP.

Lift SN_PP.h H_PP.H in SN_PP.c as c_PP.

Lift SN_PP.h H_PP.H in C_PP.get_c_b as getCB0.
Lift c_PP C_PP.C in getCB0 as getCB.

Lift SN_PP.h H_PP.H in SN_PP.f as f0 { opaque andb }.
Lift c_PP C_PP.C in f0 as f { opaque andb }.

Definition f_expected (h : H_PP.H) (c : C_PP.C) : bool :=
  (H_PP.b h && C_PP.b c)%bool.

Lemma test_f :
  f = f_expected.
Proof.
  unfold f, f_expected.
  match goal with
  | |- ?x = ?x => reflexivity
  | _ => idtac
  end.
Qed.
