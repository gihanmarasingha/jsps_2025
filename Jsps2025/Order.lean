import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

#eval (3 : ZMod 8)  -- evaluates to 3
#eval (10 : ZMod 8) -- evaluates to 2

def a : ZMod 8 := 6

#check addOrderOf


variable {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]

def addOrderOfUpToCard (g : G) : ℕ :=
  let L := (List.range (Fintype.card G + 1)).filter (fun n => 0 < n ∧ n • g = 0)
  L.headD 1


#eval addOrderOfUpToCard a
