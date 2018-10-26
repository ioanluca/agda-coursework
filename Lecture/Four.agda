{-# OPTIONS --type-in-type --no-unicode #-}

module Lecture.Four where

open import Lib.Basics
open import Lib.Nat
open import Lib.Vec

-- recap (NaturalTransformation, singletonNT)                -- C
-- what has changed? (making equations irrelevant, ID C)     -- C
-- what next?
--   Functor composition                                     -- F
--   Category of Categories                                  -- F
--   Definition of Monad                                     -- C
--   what is join for LIST?                                  -- F
--   concat as a natural transformation                      -- F
--     define concat; it needs append                        -- F
--     naturality of concat needs naturality of append       -- F
--   how can we state the naturality of append?
--     need to work with pairs of things
-- *Cat and *Fun                                             -- C
-- Delta and SETPair                                         -- C
-- construct append as a natural transformation              -- F
-- complete concat as a natural transformation               -- F
-- see what we have to prove to build the LIST monad         -- F
-- cliffhanger, roll credits


postulate
  ext : {S : Set}{T : S -> Set}{f g : (x : S) -> T x} ->
        ((x : S) -> f x == g x) -> f == g

record Category {Obj : Set}(Arr : Obj -> Obj -> Set) : Set where
  field
    -- structure
    idArr       : {X : Obj} -> Arr X X
    _-arr-_     : {R S T : Obj} -> Arr R S -> Arr S T -> Arr R T
    -- laws
    .idArr-arr-  : {S T : Obj}(f : Arr S T) -> (idArr -arr- f) == f
    ._-arr-idArr : {S T : Obj}(f : Arr S T) -> (f -arr- idArr) == f
    .assoc-arr-  : {R S T U : Obj}
                   (f : Arr R S)(g : Arr S T)(h : Arr T U) ->
                   ((f -arr- g) -arr- h) == (f -arr- (g -arr- h))
  infixr 20 _-arr-_

SomeCategory : Set
SomeCategory = Sg Set                 \ Obj ->
               Sg (Obj -> Obj -> Set) \ Arr ->
               Category Arr

SET : Category \ S T -> S -> T
SET = record
        { idArr = λ z → z
        ; _-arr-_ = λ f g → λ r → g (f r)
        ; idArr-arr- = λ f → refl
        ; _-arr-idArr = λ f → refl
        ; assoc-arr- = λ f g h → refl
        }

refl-LE : (n : Nat) -> n <= n
refl-LE zero = <>
refl-LE (suc n) = refl-LE n

trans-LE : (x y z : Nat) -> x <= y -> y <= z -> x <= z
trans-LE zero y z xy yz = <>
trans-LE (suc x) zero z () yz
trans-LE (suc x) (suc y) zero xy ()
trans-LE (suc x) (suc y) (suc z) xy yz = trans-LE x y z xy yz

irrelevant-LE : (x y : Nat) (p q : x <= y) -> p == q
irrelevant-LE zero y p q = refl
irrelevant-LE (suc x) zero p ()
irrelevant-LE (suc x) (suc y) p q = irrelevant-LE x y p q

NAT-LE : Category _<=_
NAT-LE = record
           { idArr = \ {X} -> refl-LE X
           ; _-arr-_ = \ {x}{y}{z} -> trans-LE x y z
           ; idArr-arr- = \ {x}{y} f -> irrelevant-LE x y _ _
           ; _-arr-idArr = \ {x}{y} f -> irrelevant-LE x y _ _
           ; assoc-arr- = \ {x}{y}{z}{w} f g h -> irrelevant-LE x w _ _
           }

_^op : forall {Obj}{Arr : Obj -> Obj -> Set} ->
       Category Arr -> Category \ S T -> Arr T S
C ^op = record
          { idArr = idArr
          ; _-arr-_ = \ g f -> f -arr- g
          ; idArr-arr- = \ f -> f -arr-idArr
          ; _-arr-idArr = \ f -> idArr-arr- f
          ; assoc-arr- = \ f g h -> sym (assoc-arr- h g f)
          }
  where open Category C

ADDITION : Category {One} \ _ _ -> Nat
ADDITION = record
             { idArr = 0
             ; _-arr-_ = _+N_
             ; idArr-arr- = \n -> refl
             ; _-arr-idArr = _+Nzero
             ; assoc-arr- = assoc+N
             }

record Preorder {X : Set}(_<?=_ : X -> X -> Set) : Set where
  field
    reflexive   : {x : X} -> x <?= x
    transitive  : {x y z : X} ->
                  x <?= y -> y <?= z -> x <?= z
    irrelevant  : {x y : X}{p q : x <?= y} -> p == q

SomePreorder : Set1
SomePreorder =
  Sg Set             \ X ->
  Sg (X -> X -> Set) \ _<?=_ ->
  Preorder _<?=_

record MonotoneMap (XP YP : SomePreorder) : Set where
  field
    mapData     : fst XP -> fst YP
    mapMonotone :
      let X , _<X=_ , _ = XP
          Y , _<Y=_ , _ = YP
      in  {x0 x1 : X} -> x0 <X= x1 ->
                 mapData x0 <Y= mapData x1

--PREORDER : Category MonotoneMap
--PREORDER = {!!}

record Functor
  {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}(CatS : Category ArrS)
  {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}(CatT : Category ArrT)
  (ObjF : ObjS -> ObjT)
  : Set where
  module S = Category CatS
  module T = Category CatT
  field
    map      : forall {A B : ObjS} -> ArrS A B -> ArrT (ObjF A) (ObjF B)
    -- laws
    .mapidArr : forall {A} -> map (S.idArr {A}) == T.idArr {ObjF A}
    .map-arr- : forall {A B C}(f : ArrS A B)(g : ArrS B C) ->
                map (f S.-arr- g) == (map f T.-arr- map g)

SomeFunctor : SomeCategory -> SomeCategory -> Set
SomeFunctor (ObjS , ArrS , CatS) (ObjT , ArrT , CatT) =
   Sg (ObjS -> ObjT) \ ObjF ->
   Functor CatS CatT ObjF



list : {A B : Set} -> (A -> B) -> List A -> List B
list f [] = []
list f (a ,- as) = f a ,- list f as

listId : forall {A} (as : List A) -> list (\ z -> z) as == as
listId [] = refl
listId (a ,- as) = (a ,-_) $= listId as   --  (a ,-_) is Haskell's (a :)

listComp : forall {A B C} {f : A -> B} {g : B -> C} (as : List A) ->
           list (\ r -> g (f r)) as == list g (list f as)
listComp [] = refl
listComp (a ,- as) = (_ ,-_) $= listComp as
           
LIST : Functor SET SET List
LIST = record { map = list ; mapidArr = ext listId ; map-arr- = \ f g -> ext listComp }

ID : {Obj : Set}{Arr : Obj -> Obj -> Set}(C : Category Arr) -> Functor C C \ X -> X
ID C = record { map = \ f -> f ; mapidArr = refl ; map-arr- = \ f g -> refl }

{-
ID : Functor SET SET \ X -> X
ID = record { map = \ f -> f
            ; mapidArr = refl
            ; map-arr- = \ f g -> refl
            }
-}

module _
  {ObjR : Set}{ArrR : ObjR -> ObjR -> Set}{CatR : Category ArrR}
  {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}{CatS : Category ArrS}
  {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}{CatT : Category ArrT}
  {ObjF : ObjR -> ObjS}
  {ObjG : ObjS -> ObjT}
  where
  private
    module R = Category CatR
    module S = Category CatS
    module T = Category CatT

  _-Func-_ :  Functor CatR CatS ObjF
           ->
              Functor CatS CatT ObjG
           ->
              Functor CatR CatT \ X -> ObjG (ObjF X)
  Functor.map (F -Func- G) f = G.map (F.map f)
    where
    module F = Functor F
    module G = Functor G
  Functor.mapidArr (F -Func- G) =
      G.map (F.map R.idArr)
        =[ G.map $= F.mapidArr >=
      G.map S.idArr
        =[ G.mapidArr >=
      T.idArr
        [QED]
    where
    module F = Functor F
    module G = Functor G
  Functor.map-arr- (F -Func- G) f g = 
      G.map (F.map (f R.-arr- g))
        =[ G.map $= F.map-arr- f g >=
      G.map (F.map f S.-arr- F.map g)
        =[ G.map-arr- (F.map f) (F.map g) >=
      (G.map (F.map f) T.-arr- G.map (F.map g))
        [QED]
    where
    module F = Functor F
    module G = Functor G

  infixr 20 _-Func-_

CATEGORY : Category SomeFunctor
CATEGORY = record
             { idArr = _ , ID _
             ; _-arr-_ = \ { (ObjF , F) (ObjG , G) -> _ , (F -Func- G) }
             ; idArr-arr- = \ F -> refl
             ; _-arr-idArr = \ F -> refl
             ; assoc-arr- = \ F G H -> refl
             }

{-
VEC : (n : Nat) -> Functor SET SET (\ X -> Vec X n)
VEC n = record { map = {!!} ; mapidArr = {!!} ; map-arr- = {!!} }
-}

take : {X : Set}{A B : Nat} -> B <= A -> Vec X A -> Vec X B
take {X} {m} {zero} p xs = []
take {X} {.0} {suc n} () []
take {X} {(suc m)} {suc n} p (x ,- xs) = x ,- take p xs

takeAll : forall {X n} (xs : Vec X n) -> take (refl-LE n) xs == xs
takeAll [] = refl
takeAll (x ,- xs) = (x ,-_) $= takeAll xs

takeComp : forall a b c (ba : b <= a) (cb : c <= b) {X} (xs : Vec X a) ->
           take {B = c} (trans-LE c b a cb ba) xs ==
            take  cb (take ba xs)
takeComp a b zero ba cb xs = refl
takeComp .0 zero (suc c) ba () []
takeComp .0 (suc b) (suc c) () cb []
takeComp .(suc _) zero (suc c) ba () (x ,- xs)
takeComp (suc a) (suc b) (suc c) ba cb (x ,- xs) =
-- takeComp .(suc a) (suc b) (suc c) ba cb (_,-_ {n = a} x xs) =
  (x ,-_) $= takeComp a b c ba cb xs

TAKE : (X : Set) -> Functor (NAT-LE ^op) SET (Vec X)
TAKE X = record
  { map = take
  ; mapidArr = ext takeAll
  ; map-arr- = \ {a}{b}{c} ba cb -> ext (takeComp a b c ba cb)
  }

record NaturalTransformation
  {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}{CatS : Category ArrS}
  {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}{CatT : Category ArrT}
  {ObjF : ObjS -> ObjT}(F : Functor CatS CatT ObjF)
  {ObjG : ObjS -> ObjT}(G : Functor CatS CatT ObjG)
  : Set where
  open Category CatT
  open Functor
  field
    transform : (X : ObjS) -> ArrT (ObjF X) (ObjG X)
    .natural : {X Y : ObjS} -> (f : ArrS X Y) ->
               (transform X -arr- map G f) == (map F f -arr- transform Y)

module _ where
  open NaturalTransformation
  singletonNT : NaturalTransformation (ID SET) LIST
  transform singletonNT X x = x ,- []
  natural singletonNT f = refl

record Monad {Obj : Set}{Arr : Obj -> Obj -> Set}{C : Category Arr}
             {ObjM : Obj -> Obj}
             (M : Functor C C ObjM) : Set where
  open Category C
  open Functor M
  field
    returnNT : NaturalTransformation (ID C) M
    joinNT   : NaturalTransformation (M -Func- M) M
  module R = NaturalTransformation returnNT
  module J = NaturalTransformation joinNT
  KlArr : Obj -> Obj -> Set
  KlArr S T = Arr S (ObjM T)
  field
    returnJoin : {X : Obj} ->
      (R.transform (ObjM X) -arr- J.transform X) == idArr
    mapReturnJoin : {X : Obj} ->
      (map (R.transform X) -arr- J.transform X) == idArr
    joinJoin : {X : Obj} ->
      (J.transform (ObjM X) -arr- J.transform X)
      ==
      (map (J.transform X) -arr- J.transform X)
  Kleisli : Category KlArr
  Kleisli = {!!}


_*Cat_ : {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}(CatS : Category ArrS)
         {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}(CatT : Category ArrT) ->
         Category {ObjS * ObjT} \ {(SS , TS) (ST , TT) ->
           ArrS SS ST * ArrT TS TT}
CatS *Cat CatT = {!!}
  where
    module S = Category CatS
    module T = Category CatT

module _
         {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}{CatS : Category ArrS}
         {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}{CatT : Category ArrT}
         {ObjF : ObjS -> ObjT}(F : Functor CatS CatT ObjF)
         {ObjS' : Set}{ArrS' : ObjS' -> ObjS' -> Set}{CatS' : Category ArrS'}
         {ObjT' : Set}{ArrT' : ObjT' -> ObjT' -> Set}{CatT' : Category ArrT'}
         {ObjF' : ObjS' -> ObjT'}(F' : Functor CatS' CatT' ObjF')
  where
    private
      module F = Functor F
      module F' = Functor F'
      open Functor

    _*Fun_ : 
         Functor (CatS *Cat CatS') (CatT *Cat CatT') {!!} -- \ { (S , S') -> (ObjF S , ObjF' S') }
    _*Fun_ = {!!}
    

module _ where
  open NaturalTransformation

  _+L_ : {X : Set} -> List X -> List X -> List X
  [] +L ys = ys
  (x ,- xs) +L ys = x ,- (xs +L ys)

  concat : {X : Set} -> List (List X) -> List X
  concat [] = []
  concat (xs ,- xss) = xs +L concat xss

  concatNT : NaturalTransformation (LIST -Func- LIST) LIST
  transform concatNT X = concat
  natural concatNT = {!!}

LISTMonad : Monad LIST
LISTMonad = record
              { returnNT = singletonNT
              ; joinNT = concatNT
              ; returnJoin = {!!}
              ; mapReturnJoin = {!!}
              ; joinJoin = {!!}
              }







{- here are some we made earlier

  Kleisli : Category KlArr
  Kleisli = record
    { idArr = R.transform _
    ; _-arr-_ = \ h k -> h -arr- map k -arr- J.transform _
    ; idArr-arr- = {!!}
    ; _-arr-idArr = {!!}
    ; assoc-arr- = {!!}
    }


  F -Func- G = record
    { map      = \ ab -> G.map (F.map ab)
    ; mapidArr =
        G.map (F.map R.idArr)
          =[ G.map $= F.mapidArr >=
        G.map S.idArr
          =[ G.mapidArr >=
        T.idArr
          [QED] 
    ; map-arr- = \ h k ->
        G.map (F.map (h R.-arr- k))
          =[ G.map $= F.map-arr- h k >=
        G.map (F.map h S.-arr- F.map k)
          =[ G.map-arr- (F.map h) (F.map k) >= 
        (G.map (F.map h) T.-arr- G.map (F.map k))
          [QED]
    } 


CATEGORY = record
  { idArr = \ { {_ , _ , C} -> _ , ID C }
  ; _-arr-_ = \ { (ObjF , F) (ObjG , G) -> _ , (F -Func- G) }
  ; idArr-arr-  = \ _ -> refl
  ; _-arr-idArr = \ _ -> refl
  ; assoc-arr-  = \ _ _ _ -> refl
  }

CatS *Cat CatT = record
  { idArr = S.idArr , T.idArr
  ; _-arr-_ = \ { (fS , fT) (gS , gT) -> (fS S.-arr- gS) , (fT T.-arr- gT) }
  ; idArr-arr- = \ { (fS , fT) -> reff _,_ =$= S.idArr-arr- fS =$= T.idArr-arr- fT }
  ; _-arr-idArr = \ { (fS , fT) -> reff _,_ =$= (fS S.-arr-idArr) =$= (fT T.-arr-idArr) }
  ; assoc-arr- = \ { (fS , fT) (gS , gT) (hS , hT) ->
     reff _,_ =$= S.assoc-arr- fS gS hS =$= T.assoc-arr- fT gT hT }
  }
  where
    module S = Category CatS
    module T = Category CatT

    _*Fun_ : 
         Functor (CatS *Cat CatS') (CatT *Cat CatT') \ { (S , S') -> (ObjF S , ObjF' S') }
    map _*Fun_ (f , f') = F.map f , F'.map f'
    mapidArr _*Fun_ = reff _,_ =$= F.mapidArr =$= F'.mapidArr
    map-arr- _*Fun_ (f , f') (g , g') = reff _,_ =$= F.map-arr- f g =$= F'.map-arr- f' g'



    
module _ {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}{CatS : Category ArrS} where
  open Category CatS
  open Functor

  Delta : Functor CatS (CatS *Cat CatS) \ X -> X , X
  map Delta f = f , f
  mapidArr Delta = refl
  map-arr- Delta _ _ = refl

module _ where
  open Category SET
  open Functor
  
  SETPair : Functor (SET *Cat SET) SET \ { (S , T) -> S * T }
  map SETPair (f , g) (a , b) = f a , g b
  mapidArr SETPair = refl
  map-arr- SETPair f g = refl
  


_+L_ : {X : Set} -> List X -> List X -> List X
[] +L ys = ys
(x ,- xs) +L ys = x ,- (xs +L ys)

concat : {X : Set} -> List (List X) -> List X
concat [] = []
concat (xs ,- xss) = xs +L concat xss

appendNatural : forall {X Y} (f : X -> Y) (xs ys : List X) ->
                list f (xs +L ys) == (list f xs +L list f ys)
appendNatural f [] ys = refl
appendNatural f (x ,- xs) ys = (f x ,-_) $= appendNatural f xs ys

concatNatural : forall {X Y} (f : X -> Y) (xss : List (List X)) ->
                list f (concat xss) == concat (list (list f) xss)
concatNatural f [] = refl
concatNatural f (xs ,- xss) =
  list f (xs +L concat xss)
    =[ appendNatural f xs (concat xss) >=
  list f xs +L list f (concat xss)
    =[ (list f xs +L_) $= concatNatural f xss >=
  list f xs +L concat (list (list f) xss)
    [QED]



  appendNT : NaturalTransformation (Delta -Func- (LIST *Fun LIST) -Func- SETPair) LIST
  transform appendNT X (xs , ys) = xs +L ys
  natural appendNT f = ext \ { (xs , ys) -> appendNatural f xs ys }



  transform concatNT = \ _ -> concat
  natural concatNT = \ f -> ext (concatNatural f)

-}