module ZK where

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.String 
open import Data.Maybe
open import Data.List hiding (_++_)
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality


data SubExp : Set where
  Var : String → SubExp
  Num : ℕ → SubExp
  Plus : SubExp → SubExp → SubExp 
  Times : SubExp → SubExp → SubExp
  Pow : SubExp → SubExp → SubExp
 
-- Examples

se₁ se₂ se₃ se₄ se₅ : SubExp
se₁ = Var "x"
se₂ = Num 4
se₃ = Plus (Num 3) (Num 4)
se₄ = Pow (Num 4) (se₃)
se₅ = Times (Num 6) (Num 8)

data Atom : Set where
  send : SubExp → Atom
  _←_ : String → Atom → Atom
  recv  : Atom
  idle : Atom 
  seq : Atom → Atom → Atom
  exp : SubExp → Atom

-- Examples
a₁ a₂ a₃ a₄ : Atom

a₁ = "x" ← exp (Num 5)
a₂ = send (Var "x")
a₃ = idle
a₄ = recv
 
data Exp : Set where
  <_$_> : Atom → Atom → Exp

-- Examples
e₁ e₂ e₃ e₄ e₅ : Exp
e₁ = <(send (Var "x")) $ (idle)>  
e₂ = < "x" ← exp (Num 4) $ (idle)>
e₃ = <(idle) $ "y" ← recv >
e₄ = <(idle) $ (idle)>
e₅ = <(idle) $ send (Var "y")>
