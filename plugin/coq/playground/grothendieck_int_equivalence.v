
Module IndInt.

Inductive Z : Set :=
| pos : nat -> Z
| negsuc : nat -> Z.

Definition depConstrPos (n : nat) : Z := pos n.
Definition depConstrNegSuc (n : nat) : Z := negsuc n.

Definition depElim (P : Z -> Type)
  (posP : forall (n : nat), P (depConstrPos n))
  (negSucP : forall (n : nat), P (depConstrNegSuc n))
  (z : Z) :
  P z :=
  match z with
  | pos n => posP n
  | negsuc n => negSucP n
  end.

Theorem iotaPosEq (P : Z -> Type)
  (posP : forall (n : nat), P (depConstrPos n))
  (negSucP : forall (n : nat), P (depConstrNegSuc n))
  (n : nat)
  (Q : P (depConstrPos n) -> Type) :
  Q (depElim P posP negSucP (depConstrPos n)) = Q (posP n).
Proof.
  reflexivity.
Qed.

Theorem iotaPos (P : Z -> Type)
  (posP : forall (n : nat), P (depConstrPos n))
  (negSucP : forall (n : nat), P (depConstrNegSuc n))
  (n : nat) :
  forall (Q : P (depConstrPos n) -> Type),
  (Q (depElim P posP negSucP (depConstrPos n))) -> Q (posP n).
Proof.
  intros.
  apply X.
Qed.

Theorem iotaPosRev (P : Z -> Type)
  (posP : forall (n : nat), P (depConstrPos n))
  (negSucP : forall (n : nat), P (depConstrNegSuc n))
  (n : nat) :
  forall (Q : P (depConstrPos n) -> Type),
  Q (posP n) -> (Q (depElim P posP negSucP (depConstrPos n))).
Proof.
  intros.
  apply X.
Qed.

Theorem iotaNegSucEq (P : Z -> Type)
  (posP : forall (n : nat), P (depConstrPos n))
  (negSucP : forall (n : nat), P (depConstrNegSuc n))
  (n : nat)
  (Q : P (depConstrNegSuc n) -> Type) :
  Q (depElim P posP negSucP (depConstrNegSuc n)) = Q (negSucP n).
Proof.
  reflexivity.
Qed.

Theorem iotaNeg (P : Z -> Type)
  (posP : forall (n : nat), P (depConstrPos n))
  (negSucP : forall (n : nat), P (depConstrNegSuc n))
  (n : nat) :
  forall (Q : P (depConstrNegSuc n) -> Type),
  (Q (depElim P posP negSucP (depConstrNegSuc n))) -> Q (negSucP n).
Proof.
  intros.
  apply X.
Qed.

Theorem iotaPosNegSuc (P : Z -> Type)
  (posP : forall (n : nat), P (depConstrPos n))
  (negSucP : forall (n : nat), P (depConstrNegSuc n))
  (n : nat) :
  forall (Q : P (depConstrNegSuc n) -> Type),
  Q (negSucP n) -> (Q (depElim P posP negSucP (depConstrNegSuc n))).
Proof.
  intros.
  apply X.
Qed.
       
End IndInt.
