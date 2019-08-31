(** Credit to Jasper Hugunin (jashug) for this module. *)

(* Turn a pair of inverses into an adjoint equivalence *)
(* Proof follows the HoTT book *)
(* Mostly, just a lot of manipulation of equality proofs *)

(* Lemma 2.4.3 in HoTT book, specialized to g = id *)
Definition commute_homotopy_id {A} {f : A -> A}
  (f_id : forall a, f a = a) {x y : A} (p : x = y)
  : eq_trans (f_id x) p = eq_trans (f_equal f p) (f_id y)
  := match p in (_ = y)
     return eq_trans (f_id x) p = eq_trans (f_equal f p) (f_id y)
     with eq_refl => eq_sym (eq_trans_refl_l (f_id x)) end.

Section adjointify.
Context {A B} (f : A -> B) (g : B -> A).

Section g_adjoint.
Context
  (gf_id : forall a, g (f a) = a)
  (fg_id : forall b, f (g b) = b).

Definition f_adjoint_gives_g_adjoint_pointwise
  (b : B) (f_adjoint_at_gb : fg_id (f (g b)) = f_equal f (gf_id (g b)))
  : gf_id (g b) = f_equal g (fg_id b)
  := let precomposed_eq
      : eq_trans (f_equal (fun a => g (f a)) (f_equal g (fg_id b)))
         (gf_id (g b)) =
        eq_trans (f_equal g (f_equal (fun b => f (g b)) (fg_id b)))
          (f_equal g (fg_id b))
      := eq_trans
         (eq_sym (commute_homotopy_id gf_id (f_equal g (fg_id b))))
         (eq_rect (f_equal g (fg_id (f (g b)))) (fun p => eq_trans p _ = _)
          (eq_trans (eq_trans
           (eq_sym (eq_trans_map_distr g _ _))
           (f_equal (fun p => f_equal g p)
            (commute_homotopy_id fg_id (fg_id b))))
           (eq_trans_map_distr g _ _)) _
          (eq_trans (eq_trans
           (f_equal (fun p => f_equal g p) f_adjoint_at_gb)
           (f_equal_compose f g _))
           (eq_id_comm_r _ gf_id  (g b)))) in
     match fg_id b as p
     return
       forall p1 p2,
       eq_trans (f_equal _ (f_equal g p)) p1 =
       eq_trans (f_equal g (f_equal _ p)) p2 ->
       p1 = p2
     with eq_refl => fun p1 p2 eq =>
       eq_trans (eq_trans
         (eq_sym (eq_trans_refl_l _))
         eq)
         (eq_trans_refl_l _)
     end (gf_id (g b)) (f_equal g (fg_id b)) precomposed_eq.

Definition f_adjoint_gives_g_adjoint
  (f_adjoint : forall a, fg_id (f a) = f_equal f (gf_id a))
  (b : B) : gf_id (g b) = f_equal g (fg_id b)
  := f_adjoint_gives_g_adjoint_pointwise b (f_adjoint (g b)).
End g_adjoint.

Section correction.
Context
  (gf_id : forall a, g (f a) = a)
  (fg_id : forall b, f (g b) = b).

(* N.B.: The adjoint equivalence will use this instead of the given section. *)
Definition fg_id' b : f (g b) = b
  := eq_trans (eq_sym (fg_id (f (g b))))
     (eq_trans (f_equal f (gf_id (g b))) (fg_id b)).

Definition f_adjoint a : fg_id' (f a) = f_equal f (gf_id a)
  := let symmetric_eq
      : eq_trans (f_equal f (gf_id (g (f a)))) (fg_id (f a)) =
        eq_trans (fg_id (f (g (f a)))) (f_equal f (gf_id a))
      := eq_trans (eq_trans
         (f_equal (fun H => eq_trans (f_equal f H) (fg_id (f a)))
          (eq_sym (eq_id_comm_r _ gf_id a)))
         (f_equal (fun p => eq_trans p _)
          (eq_trans
           (f_equal_compose (fun a => g (f a)) f _)
           (eq_sym (f_equal_compose f (fun b => f (g b)) _)))))
         (eq_sym (commute_homotopy_id fg_id (f_equal f (gf_id a)))) in
     match fg_id (f (g (f a))) as p
     return forall p', _ = eq_trans p p' -> eq_trans (eq_sym p) _ = p'
     with eq_refl => fun p' eq =>
       eq_trans (eq_trans_refl_l _) (eq_trans eq (eq_trans_refl_l _))
     end _ symmetric_eq.

Definition g_adjoint
  : forall b, gf_id (g b) = f_equal g (fg_id' b)
  := f_adjoint_gives_g_adjoint gf_id fg_id' f_adjoint.

End correction.

End adjointify.
