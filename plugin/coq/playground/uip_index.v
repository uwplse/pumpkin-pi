Add LoadPath "coq/playground".

Import EqNotations.
From Coq Require Import Eqdep_dec.
Require Import Ornamental.Ornaments.

Set DEVOID search prove coherence.
Set DEVOID lift type.

Lemma foo:
  forall (T : Type) (l : list T) (s1 s2: sigT (fun (n : nat) => length l = n))
    (p1 p2: s1 = s2), p1 = p2.
Proof.
  intros T l s1 s2 p1 p2. apply UIP_dec.
  intros. destruct x. destruct y. subst.
  left. reflexivity.
Defined.

(*
 * Playing around with provable relational UIP, if it turns out to be possible and
 * useful.
 *
 * This is the most basic type combination I can think of with the desired behavior:
 *)
Inductive A: Type :=
| foo : A.

Inductive B : Type -> Type :=
| bar : B nat.

Inductive C : unit -> Type :=
| baz : C tt.

(*
 * Of course A and packed B are equivalent:
 *)
Module A_to_B.

Find ornament A B as a_to_b.

(*
 * Due to a bug, equivalence proof fails for the above, so we'll prove it by hand:
 *)
Definition f := a_to_b.
Definition g := a_to_b_inv.
Definition indexer := a_to_b_index.
Definition coherence := a_to_b_coh.

Lemma section:
  forall a, g (f a) = a.
Proof.
  intros. induction a. reflexivity.
Defined.

Lemma retraction:
  forall b, f (g b) = b.
Proof.
  intros. induction b. induction p. reflexivity.
Defined.

End A_to_B. 

(*
 * We can unpack B:
 *)
Module A_to_B_unpacked.

Program Definition f (T : Type) (a : { a : A & A_to_B.indexer a = T }) : B T.
Proof. 
  induction a. induction x. rewrite <- p. apply bar.
Defined.

Program Definition g (T : Type) (b : B T) : { a : A & A_to_B.indexer a = T }.
Proof.
  induction b. exists foo. reflexivity.
Defined.

Lemma section:
  forall T a, g T (f T a) = a.
Proof.
  intros. induction a. induction x. simpl. rewrite <- p. reflexivity.
Defined.

Lemma retraction:
  forall T b, f T (g T b) = b.
Proof.
  intros. induction b. reflexivity.
Defined.

End A_to_B_unpacked.

(*
 * Of course A and packed C are equivalent:
 *)
Module A_to_C.

Set DEVOID search prove equivalence.

Find ornament A C as a_to_c.

Definition f := a_to_c.
Definition g := a_to_c_inv.
Definition indexer := a_to_c_index.
Definition coherence := a_to_c_coh.
Definition section := a_to_c_section.
Definition retraction := a_to_c_retraction.

End A_to_C. 

(*
 * We can unpack B:
 *)
Module A_to_C_unpacked.

Program Definition f (u : unit) (a : { a : A & A_to_C.indexer a = u }) : C u.
Proof. 
  induction a. induction x. rewrite <- p. apply baz.
Defined.

Program Definition g (u : unit) (c : C u) : { a : A & A_to_C.indexer a = u }.
Proof.
  induction c. exists foo. reflexivity.
Defined.

Lemma section:
  forall u a, g u (f u a) = a.
Proof.
  intros. induction a. induction x. simpl. rewrite <- p. reflexivity.
Defined.

Lemma retraction:
  forall u c, f u (g u c) = c.
Proof.
  intros. induction c. reflexivity.
Defined.

End A_to_C_unpacked.

(*
 * This construction is from Arthur Azevedo de Amorim:
 *)
Module B_to_C_fibered.

Definition f_index (T : Type) (b : B T) : unit :=
  tt.

Definition f (T : Type) (b : B T) : C (f_index T b) :=
  baz.

Definition g_index (u : unit) (c : C u) : Type :=
  nat.

Definition g (u : unit) (c : C u) : B (g_index u c) :=
  bar.

Lemma f_coh:
  forall (T : Type) (b : B T), T = g_index (f_index T b) (f T b).
Proof.
  intros T b. induction b. reflexivity.
Defined.

Lemma g_coh:
  forall (u : unit) (c : C u), u = f_index (g_index u c) (g u c).
Proof.
  intros T c. induction c. reflexivity.
Defined.

Definition transport_f_index:
  forall T (b : B T),
    B (g_index (f_index T b) (f T b)).
Proof.
  intros T b. rewrite <- f_coh. apply b.
Defined.

Definition transport_g_index:
  forall u (c : C u),
    C (f_index (g_index u c) (g u c)). 
Proof.
  intros T c. rewrite <- g_coh. apply c.
Defined.

Lemma section:
  forall T b, g (f_index T b) (f T b) = transport_f_index T b.
Proof.
  intros T b. induction b. reflexivity.
Defined.

Lemma retraction:
  forall u c, f (g_index u c) (g u c) = transport_g_index u c.
Proof.
  intros T c. induction c. reflexivity.
Defined.

End B_to_C_fibered.

(*
 * Is this practically useful in any way? Let's find out.
 *)
Module A_Proofs.

Definition f1 (a : A) : A :=
  foo.

Program Definition f2 (a : A) : A.
Proof.
  induction a. apply foo.
Defined.

Lemma f1_f2 : forall (a : A), f1 a = f2 a.
Proof.
  intros. induction a. reflexivity.
Defined.

Lemma f1_inv_b :
  forall (a : A) (T : Type),
    A_to_B.indexer a = T ->
    A_to_B.indexer (f1 a) = T.
Proof.
  intros a T H. subst. induction a. reflexivity.
Defined.

Lemma f2_inv_b :
  forall (a : A) (T : Type),
    A_to_B.indexer a = T ->
    A_to_B.indexer (f2 a) = T.
Proof.
  intros a T H. subst. induction a. reflexivity.
Defined.

Lemma f1_inv_c :
  forall (a : A) (u : unit),
    A_to_C.indexer a = u ->
    A_to_C.indexer (f1 a) = u.
Proof.
  intros a u H. subst. induction a. reflexivity.
Defined.

Lemma f2_inv_c :
  forall (a : A) (u : unit),
    A_to_C.indexer a = u ->
    A_to_C.indexer (f2 a) = u.
Proof.
  intros a u H. subst. induction a. reflexivity.
Defined.

End A_Proofs.

Preprocess Module A_Proofs as A_Proofs' 
  { opaque A_ind A_rect A_to_B.a_to_b_index A_to_B.indexer
    A_to_C.a_to_c_index A_to_C.indexer Coq.Init.Logic.eq_ind }.

Lift Module A C in A_Proofs' as C_Proofs.

(*
 * The same bug is preventing us from lifting A_Proofs' to B_Proofs, unfortunately.
 * Need to investigate to see what it is.
 *)

Module C_Proofs_unpacked.

Unpack C_Proofs.f1 as f1_u.
Unpack C_Proofs.f2 as f2_u.

Definition f1 (u : unit) (c : C u) :=
  rew (C_Proofs.f1_inv_c (existT _ u c) u eq_refl) in (f1_u u c).

Definition f2 (u : unit) (c : C u) :=
  rew (C_Proofs.f2_inv_c (existT _ u c) u eq_refl) in (f2_u u c).

Lemma cuip:
  forall (u1 u2 : unit) (p1 p2 : u1 = u2),
    p1 = p2.
Proof.
  intros u p1 p2. apply UIP_dec. intros. 
  induction x. induction y. left. reflexivity.
Defined.

Lemma cuip_proj:
  forall (u1 u2 : unit) (c1 : C u1) (c2 : C u2) (H : u1 = u2),
    existT _ u1 c1 = existT _ u2 c2 ->
    rew H in c1 = c2.
Proof.
  intros u1 u2 c1 c2 H Heq. pose proof (projT2_eq Heq). simpl in H0. 
  assert (H = projT1_eq Heq) by (apply cuip).
  rewrite H1. apply H0.
Defined.

Lemma cuip_proj_refl:
  forall (u1 u2 : unit) (c1 : C u1) (c2 : C u2) (H : u1 = u2),
    existT _ u1 c1 = existT _ u2 c2 ->
    rew H in c1 = c2.
Proof.
  intros u1 u2 c1 c2 H Heq. pose proof (projT2_eq Heq). simpl in H0. 
  assert (H = projT1_eq Heq) by (apply cuip).
  rewrite H1. apply H0.
Defined.

Lemma eq_sigT_sig_eq:
  forall (X : Type) (P : X -> Type) (x1 x2 : X) (H1 : P x1) (H2 : P x2),
  existT P x1 H1 = existT P x2 H2 <-> {H : x1 = x2 | rew [P] H in H1 = H2}.
Proof.
  (* Import problem; pretending I have this, since it is generally derivable. *)
Admitted.

Lemma f1_f2:
  forall (u : unit) (c : C u),
    f1 u c = f2 u c.
Proof.
  intros u c.
  unfold f1, f2. unfold f1_u, f2_u.
  pose proof (C_Proofs.f1_f2 (existT _ u c)).
  pose proof (projT1_eq H).
  replace ( projT1
       (C_Proofs.f2
          (let H := existT (fun H : unit => C H) u c in
           existT (fun H0 : unit => C H0) (projT1 H) (projT2 H)))) with (projT1 (C_Proofs.f2 (existT (fun H0 : unit => C H0) u c)))
     in H0 by reflexivity.
  replace ( projT1
       (C_Proofs.f1
          (let H := existT (fun H : unit => C H) u c in
           existT (fun H0 : unit => C H0) (projT1 H) (projT2 H)))) with (projT1 (C_Proofs.f1 (existT (fun H0 : unit => C H0) u c)))
     in H0 by reflexivity.
  remember (projT1 (C_Proofs.f2 (existT (fun H0 : unit => C H0) u c))).
  remember (projT1 (C_Proofs.f1 (existT (fun H0 : unit => C H0) u c))).
  pose proof (projT2_eq H).
  replace ( projT2
       (C_Proofs.f2
          (let H := existT (fun H : unit => C H) u c in
           existT (fun H0 : unit => C H0) (projT1 H) (projT2 H)))) with (projT2 (C_Proofs.f2 (existT (fun H0 : unit => C H0) u c)))
     in H1 by reflexivity.
  replace ( projT2
       (C_Proofs.f1
          (let H := existT (fun H : unit => C H) u c in
           existT (fun H0 : unit => C H0) (projT1 H) (projT2 H)))) with (projT2 (C_Proofs.f1 (existT (fun H0 : unit => C H0) u c)))
     in H1 by reflexivity.
  remember (projT2 (C_Proofs.f2 (existT (fun H0 : unit => C H0) u c))).
  remember (projT2 (C_Proofs.f1 (existT (fun H0 : unit => C H0) u c))).
  eapply cuip_proj. eapply eq_sigT_sig_eq. econstructor.
  apply cuip.


 Search "eq_sigT_sig_eq". eapply eq_sigT. simpl.
  generalize dependent (rew [C] C_Proofs.f2_inv_c (existT (fun H0 : unit => C H0) u c) u eq_refl in
projT2 (C_Proofs.f2 (existT (fun H0 : unit => C H0) u c))).
  rewrite eq_sigT_sig_eq in H. simpl in H.
  eapply cuip_proj. simpl.  . eapply eq_sigT_hprop.
  - apply cuip. destruct H. subst. 
  pose proof (projT2_eq H). simpl in H0. simpl. rewrite <- H0.
  eapply cuip_proj. 
  pose proof (projT2_eq H). simpl. simpl in H0. rewrite <- H0.
  eauto.
 simpl in *.
  pose proof (cuip_proj (projT1 (C_Proofs.f1 (existT _ u c))) (projT1 (C_Proofs.f2 (existT _ u c))) (f1_u u c) (f2_u u c) (projT1_eq H) H).
  unfold f2.
  unfold f1. unfold f1_u. unfold f2_u.


 rewrite <- eq_sigT with (u := u) (. f_equal. rewrite <- H1. f_equal.
 
  unfold f1. f_equal.
  unfold f1. Search eq_rect. 
  assert (C_Proofs.f2_inv_c (existT (fun H1 : unit => C H1) u c) u eq_refl = C_Proofs.f1_inv_c (existT (fun H1 : unit => C H1) u c) u eq_refl).
  simpl in H0.
  unfold f1, f2. unfold f1_u, f2_u in *.
  assert (C_Proofs.f1_inv_c = projT1_eq H).
  simpl.
  pose proof (C_Proofs.f1_f2 (existT _ u c)). simpl in H.
  apply H.
  Print f1_f2.

 simpl in H.
  unfold f1. unfold f2. unfold f1_u. unfold f2_u. eapply projT2_eq.

  simpl in *.
 simpl.

End C_Proofs_unpacked.

Print C_rec.
Print B_rec.

