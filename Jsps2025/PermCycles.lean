import Mathlib

/-!
# Permutations and cycle notation

In this file (a Lean *module*), we work with permutation groups.

In Mathlib, `Equiv.Perm (Fin n)` is the group of permutations on `{0, 1, ..., n - 1}`.
We abbreviate this to `S n`. It is essentially the same as the standard `Sₙ`.
-/

open Equiv

/-- `S n` is the group of permutations on `{0, 1, 2, ..., n - 1}` -/
abbrev S (n : Nat) := Perm (Fin n)

/-!
## Concrete examples

Below, we work with examples in `S₅`:

`c₁ = (0 1 3), c₂ = (2 4), s = c₁ c₂, t = (0 1 2 3 4)`

A cycle such as `(0 1 3)` is represented in Lean as `c[0, 1, 3]`.

The `#eval` command is used to compute and print permutations as disjoint products of cycles.

Here, `s ^ m` represents the power `sᵐ`.

The syntax of a Lean definition (with no arguments) takes the form

`def t : σ := x`

where `def` is a keyword, `t` is the name of a term of type `σ` and `x` is an expression for `t`.
-/

/-- `c1 = (0 1 3)` -/
def c1 : S 5 := c[0, 1, 3]

/-- `c2 = (2 4)`-/
def c2 : S 5 := c[2, 4]

/-- `c3 = c1 c2` -/
def s : S 5   := c1 * c2

/-- `t = (0 1 2 3 4)` -/
def t : S 5 := c[0, 1, 2, 3, 4]

#eval s

#eval s^3

#eval t

#eval s * t

#eval t * s

/-!
Type `\-1` to enter `⁻¹`.
-/

#eval t⁻¹


/-!

### Exercise 1

1. Let `u = (0 1)(3 1), v = (2 4 1)(3 2)`. By hand, express each of `u`, `v`, `u * v`, `v * u`,
   `u ^ 3`

Below, replace `sorry` in each line with appropriate products of cycles, using Lean notation,
  so that



  Then use `#eval` to express each of  as products of disjoint
  cycles.

2. DO CALCULATIONS BY HAND AND CHECK WITH LEAN.

3. Evaluate `u ^ m` for different values of the natural number `m`. What do you observe?


-/

/-- `u = (0 1)(3 1)` -/
def u : S 5 := c[0, 1] * c[3, 1]

/-- `v = (2 4 1)(3 2)` -/
def v : S 5 := c[2, 4, 1] * c[3, 2]

/-!

### Simple proofs of equality and inequality

Our first proof is

`example : s * t ≠ t * s := by decide`

Here, `s * t ≠ t * s` is the statement to be proved. The proof itself is `by decide`. This
tells Lean to look for and use any appropriate decision procedure.

This works (sometimes) in finite concrete examples.
 -/

example : s * t ≠ t * s := by decide

example : s * t = c[1, 4] * c[3, 2, 0] := by decide

example : s⁻¹⁻¹ = s := by decide

/-!
## Conjugation



-/

/-!

## Commutators

Mathlib defines the commutator `⁅s, t⁆ = s * t * s⁻¹ * t⁻¹`.

Type `\[--` to produce the commutator brackets.
-/

#eval ⁅s, t⁆

#eval ⁅s, s⁆

#eval ⁅s, u⁆

#eval s

#eval u

/-!

### Exercise 2

1. Experiment, by varying `x`, to determine when `⁅s, x⁆` is `1`.

2. Can you generalise your observation?

3. Prove your result

4. Prove (scaffolded) result in Lean (separate file).
-/


/-- The centralizer of `s` as a finset. -/
def centralizer {n : Nat} (s : Perm (Fin n)) : Finset (Perm (Fin n)) :=
  (Finset.univ : Finset (Perm (Fin n))).filter (fun t => s * t = t * s)

#eval centralizer s

/-!
### Exercise

What do you notice about the elements of `centralizer s`?
Generalise.
Prove your conjecture, by hand.


-/

/-- The set of all powers `c₁ᵃ c₂ᵇ` -/
def expected : Finset (Perm (Fin 5)) :=
  let as := List.range 3   -- a = 0,1,2
  let bs := List.range 2   -- b = 0,1
  let lst : List (Perm (Fin 5)) :=
    as >>= fun a => bs.map (fun b => c1 ^ a * c2 ^ b)
  lst.toFinset

#eval s                        -- prints: c[0, 1, 3] * c[2, 4]
#eval (centralizer s).card         -- expect 6
#eval expected.card            -- = 6
#eval decide (expected = centralizer s)  -- expect `true`


/-
### Exercise

Prove that `S n` is not abelian, for `n ≥ 3`.


-/

#lint
