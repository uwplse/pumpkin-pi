From Ornamental Require Import Ornaments.

Set DEVOID search prove equivalence.
Set DEVOID lift type.
Set Nonrecursive Elimination Schemes.

(*
 * This code is a minimized example from @ptival, which I use as a regression test
 * to make sure projections aren't expanded and left as applications of prod_rect.
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

End H.

Preprocess Module H as H_PP.
Print H_PP.b.

Print H.b.

Lift SN_PP.h H_PP.H in H_PP.get_h_b as getHB.
Print getHB.
Print SN_PP.f.
Lift SN_PP.h H_PP.H in SN_PP.f as f_PP { opaque andb }.

Definition f_PP_expected (h : H_PP.H) (c : nat * (nat * (bool * (H_PP.H * nat)))) : bool :=
 H_PP.H_rect
    (fun _ : H_PP.H => bool)
    (fun (b : bool) (_ : nat) => b)
    h 
 &&
 SN_PP.Coq_Init_Datatypes_fst bool (H_PP.H * nat)
   (SN_PP.Coq_Init_Datatypes_snd nat (bool * (H_PP.H * nat))
      (SN_PP.Coq_Init_Datatypes_snd nat (nat * (bool * (H_PP.H * nat))) c)).

Lemma test_f_PP:
  f_PP = f_PP_expected.
Proof.
  reflexivity.
Qed.

(*
Also wanted:

- [H_PP.H_rect (fun _ : H_PP.H => bool) (fun (b : bool) (_ : nat) => b) h] is replaced with
   the lifted accessor [getHB]. (TODO not done yet)

 *)

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
(H_PP.H_rect (fun _ : H_PP.H => bool) (fun (b : bool) (_ : nat) => b) h &&
 SN_PP.Coq_Init_Datatypes_fst bool (H_PP.H * nat)
   (SN_PP.Coq_Init_Datatypes_snd nat (bool * (H_PP.H * nat))
      (C_PP.C_rect (fun _ : C_PP.C => (nat * (bool * (H_PP.H * nat)))%type)
         (fun (_ n2 : nat) (b : bool) (h0 : H_PP.H) (n3 : nat) =>
          (n2, (b, (h0, n3)))) c))).

Lemma test_f :
  f = f_expected.
Proof.
  reflexivity.
Qed.

Require Import Patcher.Patch.

(* TODO not done yet: 
Definition f' (h : H_PP.H) (c : C_PP.C)
  : bool
  := (getHB h && getCB c)%bool. *)