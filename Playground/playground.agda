module Playground.playground where

open import Lib.Basics
open import Lib.Nat

assoc : (m n k : Nat) -> (m +N n) +N k == m +N (n +N k)
assoc zero n k = refl
assoc (suc m) n k = suc $= assoc m n k

assoc2 : (m n k : Nat) -> (m +N n) +N k == m +N (n +N k)
assoc2 zero n k =
     (zero +N n) +N k
       =[ refl >=
     n +N k
       =< refl ]=
     n +N (zero +N k)
     [QED]
     
assoc2 (suc m) n k =
     (suc m +N n) +N k
       =[ suc $= assoc m n k >=
     suc m +N ( n +N k)
     [QED]



_+Nzero' : (n : Nat) -> n +N zero == n
zero +Nzero' = refl
suc n +Nzero' =
    suc (n +N zero)
    =[ suc $= (n +Nzero') >=
    suc n
    [QED]

_+Nsuc'_ : (n m : Nat) -> n +N suc m == suc (n +N m)
zero +Nsuc' m =
  suc m =[ refl >= suc m [QED]
suc n +Nsuc' m =
  suc (n +N suc m)
    =[ suc $= (n +Nsuc' m) >=
  suc (suc (n +N m))
  [QED]

c : (n m : Nat) -> n +N m == m +N n
c zero m = sym (m +Nzero')
c (suc n) m =
  suc (n +N m)
    =[ suc $= c n m >=
  suc (m +N n)
    =< m +Nsuc' n ]=
  m +N (suc n)
    [QED]
     
