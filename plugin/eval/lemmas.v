Require Import Sorting.Permutation.

Notation permutes := Permutation.
Notation perm_sym := Permutation_sym.
Notation perm_app := Permutation_app.
Notation perm_app_comm := Permutation_app_comm.
Notation perm_cons_app := Permutation_cons_app.

Lemma add_Sn_m (n m : nat) : S n + m = S (n + m).
Proof. reflexivity. Defined.

Lemma add_n_Sm (n m : nat) : n + S m = S (n + m).
Proof.
  revert m. induction n; intro m; try reflexivity.
  rewrite add_Sn_m, add_Sn_m, IHn. reflexivity.
Defined.

Lemma add_n_O (n : nat) : n + O = n.
Proof.
  induction n; try reflexivity. rewrite add_Sn_m, IHn. reflexivity.
Defined.

Lemma add_comm (n m : nat) : n + m = m + n.
Proof.
  revert m. induction n; intro m.
  - rewrite add_n_O. reflexivity.
  - rewrite add_Sn_m, add_n_Sm, IHn. reflexivity.
Defined.

Lemma max_comm (n m : nat) : Nat.max n m = Nat.max m n.
Proof.
  revert m. induction n; destruct m; try reflexivity.
  simpl. f_equal. apply IHn.
Defined.
