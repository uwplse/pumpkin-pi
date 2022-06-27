Module Old.

Inductive one : Type :=
  | I : one.

Definition out_of (x : one) : nat :=
  match x with
  | I => 0
  end.

Definition in_to (n : nat) : one := I.

Definition both (x : one) : one := I.

End Old.

Module New.

Inductive two : Type :=
  | first : two
  | second : two.

Definition out_of (x : two) : nat :=
  match x with
  | first => 0
  | second => 0
  end.

Definition in_to (n : nat) : two := first.

Definition both (x : two) : two :=
  match x with
  | first => first
  | second => first
  end.

End New.