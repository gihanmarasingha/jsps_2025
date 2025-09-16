import Mathlib

/-!
# Permutations and cycle notation

An exploration of Mathlib's functions for working with permutations and cycle notation.

The type `Equiv.Perm (Fin n)` is the type of permutations on the set `{0, 1, ..., n - 1}`,
effectively the same as `Sₙ`.

We abbrevitate this to `S n`.
-/


open Equiv

/-- `S n` is the group of permutations on `{0, 1, 2, ..., n - 1}` -/
abbrev S (n : Nat) := Perm (Fin n)

/-!

## Concrete examples

Below, we work with examples in `S₅`:

`s = (0 1 3)(2 4), t = (0 1 2 3 4)`

A cycle such as `(0 1 3)` is represnted in Lean as `c[0, 1, 3]`.

The `#eval` command is used to compute and print permutations.

Note `s ^ m` represents `sᵐ`, for any natural number `m`.
-/

def c1 : S 5 := c[0, 1, 3]

def c2 : S 5 := c[2, 4]

def s  : S 5   := c1 * c2

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

Below, replace `sorry` in each line with appropriate products of cycles, using Lean notation,
so that

`u = (0 1)(3 1), v = (2 4 1)(3 5)`

Then use `#eval` to express each of `u`, `v`, `u * v`, `v * u`, `u ^ 3` as products of disjoint
cycles.

Evaluate `u ^ m` for different values of the natural number `m`. What do you observe?
-/

def u : S 5 := c[0, 1] * c[3, 1]

def v : S 5 := c[2, 4, 1] * c[3, 5]

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

## Commutators

Mathlib defines the commutator `⁅s, t⁆ = s * t * s⁻¹ * t⁻¹`.

Type `\[--` to produce the commutator brackets.
-/

#eval ⁅s, t⁆

#eval ⁅s, s⁆

#eval ⁅s, u⁆


/-- The centralizer of `s` as a finset. -/
def centralizer {n : Nat} (s : Perm (Fin n)) : Finset (Perm (Fin n)) :=
  (Finset.univ : Finset (Perm (Fin n))).filter (fun t => s * t = t * s)

#eval centralizer s

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
