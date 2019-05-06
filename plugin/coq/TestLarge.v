Add LoadPath "coq".
Require Import Ornamental.Ornaments.
Require Import Test.

(*
 * This file tests compositional lifting and unpacking
 * of large constants, making sure that the lifting process
 * is not slow as a result of poor interplay of existing optimizations.
 *
 * See: https://github.com/uwplse/ornamental-search/issues/44
 *)

(* --- Original constants --- *)

(*
 * Our original constants are the same as our case study ones,
 * but for the simplified type using nats from Test.v.
 *)

(* 21 nodes, to be exact *)
Definition nt20 :=
  ntBranch 0 
    (ntBranch 1 
       (ntBranch 2 
         (ntBranch 2 (ntLeaf 1) (ntLeaf 2)) 
         (ntBranch 0 (ntLeaf 1) (ntLeaf 2))) 
       (ntBranch 0 (ntLeaf 1) (ntLeaf 2)))
    (ntBranch 2 
      (ntBranch 0 (ntLeaf 1) (ntLeaf 2)) 
      (ntBranch 0
        (ntLeaf 1) 
        (ntBranch 0 (ntLeaf 1) (ntLeaf 2)))).

(* 43 nodes, to be exact *)
Definition nt40 :=
  ntBranch 2 nt20 nt20.

(* 65 nodes, to be exact *)
Definition nt60 :=
  ntBranch 1 nt20 nt40.

(* 87 nodes, to be exact *)
Definition nt80 :=
  ntBranch 0 nt40 nt40.

(* 109 nodes, to be exact *)
Definition nt100 :=
  ntBranch 1 nt40 nt60.

(* 219 nodes, to be exact *)
Definition nt200 :=
  ntBranch 0 nt100 nt100.

(* 439 nodes, to be exact *)
Definition nt400 :=
  ntBranch 1 nt200 nt200.

(* 659 nodes, to be exact *)
Definition nt600 :=
  ntBranch 0 nt200 nt400.

(* 879 nodes, to be exact *)
Definition nt800 :=
  ntBranch 2 nt200 nt600.

(* 1099 nodes, to be exact *)
Definition nt1000 :=
  ntBranch 0 nt400 nt600.

(* 2101 nodes, to be exact *)
Definition nt2000 :=
  ntBranch 1 (ntBranch 2 nt200 nt800) nt1000.

(* 4203 nodes, to be exact *)
Definition nt4000 :=
  ntBranch 0 nt2000 nt2000.

(* 6305 nodes, to be exact *)
Definition nt6000 :=
  ntBranch 2 nt2000 nt4000.

(* 8407 nodes, to be exact *)
Definition nt8000 :=
  ntBranch 2 nt4000 nt4000.

(* 10509 nodes, to be exact *)
Definition nt10000 :=
  ntBranch 2 nt2000 nt8000.

(* --- Lift, lift, lift, unpack, unpack, unpack --- *)

Module all_at_once.

Lift nt __bst in nt20 as __bst20.
Lift nt __bst in nt40 as __bst40.
Lift nt __bst in nt60 as __bst60.
Lift nt __bst in nt80 as __bst80.
Lift nt __bst in nt100 as __bst100.
Lift nt __bst in nt200 as __bst200.
Lift nt __bst in nt400 as __bst400.
Lift nt __bst in nt600 as __bst600.
Lift nt __bst in nt800 as __bst800.
Lift nt __bst in nt1000 as __bst1000.
Lift nt __bst in nt2000 as __bst2000.
Lift nt __bst in nt4000 as __bst4000.
Lift nt __bst in nt6000 as __bst6000.
Lift nt __bst in nt8000 as __bst8000.
Lift nt __bst in nt10000 as __bst10000.

Lift __bst _bst in __bst20 as _bst20.
Lift __bst _bst in __bst40 as _bst40.
Lift __bst _bst in __bst60 as _bst60.
Lift __bst _bst in __bst80 as _bst80.
Lift __bst _bst in __bst100 as _bst100.
Lift __bst _bst in __bst200 as _bst200.
Lift __bst _bst in __bst400 as _bst400.
Lift __bst _bst in __bst600 as _bst600.
Lift __bst _bst in __bst800 as _bst800.
Lift __bst _bst in __bst1000 as _bst1000.
Lift __bst _bst in __bst2000 as _bst2000.
Lift __bst _bst in __bst4000 as _bst4000.
Lift __bst _bst in __bst6000 as _bst6000.
Lift __bst _bst in __bst8000 as _bst8000.
Lift __bst _bst in __bst10000 as _bst10000.

Lift _bst bst in _bst20 as bst20'''.
Lift _bst bst in _bst40 as bst40'''.
Lift _bst bst in _bst60 as bst60'''.
Lift _bst bst in _bst80 as bst80'''.
Lift _bst bst in _bst100 as bst100'''.
Lift _bst bst in _bst200 as bst200'''.
Lift _bst bst in _bst400 as bst400'''.
Lift _bst bst in _bst600 as bst600'''.
Lift _bst bst in _bst800 as bst800'''.
Lift _bst bst in _bst1000 as bst1000'''.
Lift _bst bst in _bst2000 as bst2000'''.
Lift _bst bst in _bst4000 as bst4000'''.
Lift _bst bst in _bst6000 as bst6000'''.
Lift _bst bst in _bst8000 as bst8000'''.
Lift _bst bst in _bst10000 as bst10000'''.

Unpack bst20''' as bst20''.
Unpack bst40''' as bst40''.
Unpack bst60''' as bst60''.
Unpack bst80''' as bst80''.
Unpack bst100''' as bst100''.
Unpack bst200''' as bst200''.
Unpack bst400''' as bst400''.
Unpack bst600''' as bst600''.
Unpack bst800''' as bst800''.
Unpack bst1000''' as bst1000''.
Unpack bst2000''' as bst2000''.
Unpack bst4000''' as bst4000''.
Unpack bst6000''' as bst6000''.
Unpack bst8000''' as bst8000''.
Unpack bst10000''' as bst10000''.

Unpack bst20'' as bst20'.
Unpack bst40'' as bst40'.
Unpack bst60'' as bst60'.
Unpack bst80'' as bst80'.
Unpack bst100'' as bst100'.
Unpack bst200'' as bst200'.
Unpack bst400'' as bst400'.
Unpack bst600'' as bst600'.
Unpack bst800'' as bst800'.
Unpack bst1000'' as bst1000'.
Unpack bst2000'' as bst2000'.
Unpack bst4000'' as bst4000'.
Unpack bst6000'' as bst6000'.
Unpack bst8000'' as bst8000'.
Unpack bst10000'' as bst10000'.

Unpack bst20' as bst20.
Unpack bst40' as bst40.
Unpack bst60' as bst60.
Unpack bst80' as bst80.
Unpack bst100' as bst100.
Unpack bst200' as bst200.
Unpack bst400' as bst400.
Unpack bst600' as bst600.
Unpack bst800' as bst800.
Unpack bst1000' as bst1000.
Unpack bst2000' as bst2000.
Unpack bst4000' as bst4000.
Unpack bst6000' as bst6000.
Unpack bst8000' as bst8000.
Unpack bst10000' as bst10000.

End all_at_once.

(* --- Lift, unpack, lift, unpack, lift, unpack -- *)

Module one_at_a_time.

Lift nt __bst in nt20 as __bst20'.
Lift nt __bst in nt40 as __bst40'.
Lift nt __bst in nt60 as __bst60'.
Lift nt __bst in nt80 as __bst80'.
Lift nt __bst in nt100 as __bst100'.
Lift nt __bst in nt200 as __bst200'.
Lift nt __bst in nt400 as __bst400'.
Lift nt __bst in nt600 as __bst600'.
Lift nt __bst in nt800 as __bst800'.
Lift nt __bst in nt1000 as __bst1000'.
Lift nt __bst in nt2000 as __bst2000'.
Lift nt __bst in nt4000 as __bst4000'.
Lift nt __bst in nt6000 as __bst6000'.
Lift nt __bst in nt8000 as __bst8000'.
Lift nt __bst in nt10000 as __bst10000'.

Unpack __bst20' as __bst20.
Unpack __bst40' as __bst40.
Unpack __bst60' as __bst60.
Unpack __bst80' as __bst80.
Unpack __bst100' as __bst100.
Unpack __bst200' as __bst200.
Unpack __bst400' as __bst400.
Unpack __bst600' as __bst600.
Unpack __bst800' as __bst800.
Unpack __bst1000' as __bst1000.
Unpack __bst2000' as __bst2000.
Unpack __bst4000' as __bst4000.
Unpack __bst6000' as __bst6000.
Unpack __bst8000' as __bst8000.
Unpack __bst10000' as __bst10000.

Lift __bst _bst in __bst20 as _bst20'.
Lift __bst _bst in __bst40 as _bst40'.
Lift __bst _bst in __bst60 as _bst60'.
Lift __bst _bst in __bst80 as _bst80'.
Lift __bst _bst in __bst100 as _bst100'.
Lift __bst _bst in __bst200 as _bst200'.
Lift __bst _bst in __bst400 as _bst400'.
Lift __bst _bst in __bst600 as _bst600'.
Lift __bst _bst in __bst800 as _bst800'.
Lift __bst _bst in __bst1000 as _bst1000'.
Lift __bst _bst in __bst2000 as _bst2000'.
Lift __bst _bst in __bst4000 as _bst4000'.
Lift __bst _bst in __bst6000 as _bst6000'.
Lift __bst _bst in __bst8000 as _bst8000'.
Lift __bst _bst in __bst10000 as _bst10000'.

Unpack _bst20' as _bst20.
Unpack _bst40' as _bst40.
Unpack _bst60' as _bst60.
Unpack _bst80' as _bst80.
Unpack _bst100' as _bst100.
Unpack _bst200' as _bst200.
Unpack _bst400' as _bst400.
Unpack _bst600' as _bst600.
Unpack _bst800' as _bst800.
Unpack _bst1000' as _bst1000.
Unpack _bst2000' as _bst2000.
Unpack _bst4000' as _bst4000.
Unpack _bst6000' as _bst6000.
Unpack _bst8000' as _bst8000.
Unpack _bst10000' as _bst10000.

Lift _bst bst in _bst20 as bst20'.
Lift _bst bst in _bst40 as bst40'.
Lift _bst bst in _bst60 as bst60'.
Lift _bst bst in _bst80 as bst80'.
Lift _bst bst in _bst100 as bst100'.
Lift _bst bst in _bst200 as bst200'.
Lift _bst bst in _bst400 as bst400'.
Lift _bst bst in _bst600 as bst600'.
Lift _bst bst in _bst800 as bst800'.
Lift _bst bst in _bst1000 as bst1000'.
Lift _bst bst in _bst2000 as bst2000'.
Lift _bst bst in _bst4000 as bst4000'.
Lift _bst bst in _bst6000 as bst6000'.
Lift _bst bst in _bst8000 as bst8000'.
Lift _bst bst in _bst10000 as bst10000'.

End one_at_a_time.
