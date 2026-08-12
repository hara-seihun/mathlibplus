import Mathlib

open scoped BigOperators

namespace MathlibPlus.Combinatorics.Claim10450

/-!
The source's `C₈` is represented by the binary generator `[I₄ | J₄ - I₄]`.
The direct sum uses three independent generator blocks.  The bivariate
weight enumerator is recorded by the exact weight distribution: a word of
weight `k` contributes `x^(24-k) y^k`.
-/

abbrev Coord8 := Fin 4 ⊕ Fin 4
abbrev Coord24 := Fin 3 × Coord8

def c8Word (x : Fin 4 → ZMod 2) : Coord8 → ZMod 2
  | Sum.inl i => x i
  | Sum.inr i => ∑ j : Fin 4, if j = i then 0 else x j

def c83Word (x : Fin 3 → Fin 4 → ZMod 2) : Coord24 → ZMod 2
  | (k, c) => c8Word (x k) c

def c83Code : Finset (Coord24 → ZMod 2) :=
  Finset.univ.image c83Word

def hammingWeight (v : Coord24 → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => v i ≠ 0)).card

def weightDistribution (k : Fin 25) : ℕ :=
  (c83Code.filter (fun v => hammingWeight v = k)).card

/-- The exact weight distribution of `C₈^{⊕3}`, hence its displayed
bivariate weight enumerator. -/
theorem weightDistribution_eq : ∀ k : Fin 25,
    weightDistribution k =
      if k = 0 then 1 else if k = 4 then 42 else if k = 8 then 591 else
      if k = 12 then 2828 else if k = 16 then 591 else
      if k = 20 then 42 else if k = 24 then 1 else 0 := by
  native_decide

end MathlibPlus.Combinatorics.Claim10450
