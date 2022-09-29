{-# OPTIONS --safe --cubical #-}
module equivalence_construction where

open import Cubical.Core.Everything
open import Cubical.HITs.SetQuotients as SetQuotients
open import Cubical.Data.Equality

data Two : Set where
  first : Two
  second : Two

data True : Type where
  tt : True

R : Two -> Two -> Type
R a b = True

quot_id : Two / R -> Two / R
quot_id [ x ] = [ x ]
quot_id (eq/ a b r i) = eq/ a b r i
quot_id (squash/ x y p q i j) = squash/ (quot_id x) (quot_id y) (congPath quot_id p) (congPath quot_id q) i j

f : True -> Two / R
f tt = [ first ]

-- how do we define this?
g : Two / R -> True
g [ x ] = tt
g (eq/ a b r i) = tt
g (squash/ x y p q i j) = {!!}
