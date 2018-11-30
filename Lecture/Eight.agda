module Lecture.Eight where

open import Lib.Basics
open import Lib.Nat
open import Lib.Vec

----------------------------------------------------------------------------
-- coinduction for beginners
----------------------------------------------------------------------------

record Stream (X : Set) : Set where
  coinductive
  constructor _,-_
  field
    head : X
    tail : Stream X
open Stream

repeat : {X : Set} -> X -> Stream X
repeat x = {!!}

strapp : {S T : Set} -> Stream (S -> T) -> Stream S -> Stream T
strapp fs ss = {!!}

beginners : {X : Set}(n : Nat) -> Stream X -> Vec X n
beginners n xs = {!!}

----------------------------------------------------------------------------
-- chars and strings and IO (boring bits)
----------------------------------------------------------------------------

{-
postulate  -- needed for Agda 2.5.4
  Char : Set
  String : Set
-}
{-# BUILTIN CHAR Char #-}
{-# BUILTIN STRING String #-}

-- For compilation purposes we make _*_ into its own data type
record _**_ (S T : Set) : Set where
  constructor _,_
  field
    outl : S
    outr : T
open _**_
{-# COMPILE GHC _**_ = data (,) ((,)) #-}
infixr 4 _**_

postulate       -- Connecting to the Haskell IO monad
  IO      : Set -> Set
  return  : {A : Set} -> A -> IO A
  _>>=_   : {A B : Set} -> IO A -> (A -> IO B) -> IO B
infixl 1 _>>=_
{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}
{-# COMPILE GHC return = (\ _ -> return) #-}
{-# COMPILE GHC _>>=_ = (\ _ _ -> (>>=)) #-}


---------------------------------------------------------------------------
-- COLOURS
---------------------------------------------------------------------------

-- We're going to be making displays from coloured text.

data Colour : Set where
  black red green yellow blue magenta cyan white : Colour

{-# COMPILE GHC Colour = data HaskellSetup.Colour (HaskellSetup.Black | HaskellSetup.Red | HaskellSetup.Green | HaskellSetup.Yellow | HaskellSetup.Blue | HaskellSetup.Magenta | HaskellSetup.Cyan | HaskellSetup.White) #-}

-- Keys

data Direction : Set where up down left right : Direction

data Modifier : Set where normal shift control : Modifier

data Key : Set where
  char       : Char -> Key
  arrow      : Modifier -> Direction -> Key
  enter      : Key
  backspace  : Key
  delete     : Key
  escape     : Key
  tab        : Key

-- Events

data Event : Set where
  key     : (k : Key) -> Event
  resize  : (w h : Nat) -> Event

-- The things you're allowed to do with a text window.

data Action : Set where
  goRowCol : Nat -> Nat -> Action        -- send the cursor somewhere
  sendText : List Char -> Action         -- send some text
  move     : Direction -> Nat -> Action  -- which way and how much
  fgText   : Colour -> Action            -- change foreground colour
  bgText   : Colour -> Action            -- change background colour

{- Wiring all of that stuff up to its Haskell counterpart. -}
{-# FOREIGN GHC import qualified Lib.ANSIEscapes as ANSIEscapes #-}
{-# FOREIGN GHC import qualified Lib.HaskellSetup as HaskellSetup #-}
{-# COMPILE GHC Direction = data ANSIEscapes.Dir (ANSIEscapes.DU | ANSIEscapes.DD | ANSIEscapes.DL | ANSIEscapes.DR) #-}
{-# COMPILE GHC Modifier = data HaskellSetup.Modifier (HaskellSetup.Normal | HaskellSetup.Shift | HaskellSetup.Control) #-}
{-# COMPILE GHC Key = data HaskellSetup.Key (HaskellSetup.Char | HaskellSetup.Arrow | HaskellSetup.Enter | HaskellSetup.Backspace | HaskellSetup.Delete | HaskellSetup.Escape | HaskellSetup.Tab) #-}
{-# COMPILE GHC Event = data HaskellSetup.Event (HaskellSetup.Key | HaskellSetup.Resize) #-}
{-# COMPILE GHC Action = data HaskellSetup.Action (HaskellSetup.GoRowCol | HaskellSetup.SendText | HaskellSetup.Move | HaskellSetup.FgText | HaskellSetup.BgText) #-}


data ColourChar : Set where
  _-_/_ : (fg : Colour)(c : Char)(bg : Colour) -> ColourChar

-- ... e.g.     green - '*' / black    for a green * on black.

Matrix : Set -> Nat * Nat -> Set
Matrix C (w , h) = Vec (Vec C w) h

Painting : Nat * Nat -> Set
Painting = Matrix ColourChar

paintAction : {wh : Nat * Nat} -> Matrix ColourChar wh -> List Action
paintAction mat = {!!}

---------------------------------------------------------------------------
-- APPLICATIONS                                                          --
---------------------------------------------------------------------------

-- Here's a general idea of what it means to be an "application".
-- You need to choose some sort of size-dependent state, then provide these
-- bits and pieces. We need to know how the state is updated according to
-- events, with resizing potentially affecting the state's type. We must
-- be able to paint the state. The state should propose a cursor position.
-- (Keen students may modify this definition to ensure the cursor must be
-- within the bounds of the application.)

record Application (wh : Nat * Nat) : Set where
  coinductive
  field
    handleKey     : Key -> Application wh
    handleResize  : (wh' : Nat * Nat) -> Application wh'
    paintMe       : Painting wh
    cursorMe      : Nat * Nat  -- x,y coords
open Application public


APP : Set
APP = Sg (Nat * Nat) Application

appPaint : APP -> List Action
appPaint (_ , app) = {!!}

appHandler : Event -> APP -> APP ** List Action
appHandler ev (wh , app) = {!!}

-- Code on the Haskell side to make things go
postulate
  mainAppLoop : {S : Set} ->             -- program state
    -- INITIALIZER
    S ->                              -- initial state
    -- EVENT HANDLER
    (Event -> S ->                    -- event and state in
     S ** List Action) ->              -- new state and screen actions out
    -- PUT 'EM TOGETHER AND YOU'VE GOT AN APPLICATION!
    IO One
{-# COMPILE GHC mainAppLoop = (\ _ -> HaskellSetup.mainAppLoop) #-}

appMain : (forall wh -> Application wh) -> IO One
appMain app = mainAppLoop ((0 , 0) , app (0 , 0)) appHandler
  -- will get resized dynamically to size of terminal, first thing

rectApp : Char -> forall wh -> Application wh
rectApp c wh = {!!}

main : IO One
main = appMain (rectApp '*')

--  agda --compile --ghc-flag "-lncurses" Lecture/Eight.agda
