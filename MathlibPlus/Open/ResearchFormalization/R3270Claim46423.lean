import MathlibPlus.Open.ResearchFormalization.R3270

namespace MathlibPlus.Open.ResearchFormalization.R3270

open scoped BigOperators

/-- The indicator `Xₜ(n)` from the R-3270 finite experiment, with `t` represented
by its residue in `Fin (P(x))`. -/
def survivorIndicator46423 (x : ℕ) (t : Fin (primeProduct x)) (n : ℕ) : ℚ :=
  if Nat.gcd (t.val + n) (primeProduct x) = 1 then 1 else 0

/-- Claim 46423: on the exact R-3270 progression carrier, the uniform residue
average of the joint survivor indicator is the product of the one-forbidden-
residue small-prime factors and the k-forbidden-residue large-prime factors. -/
def claim46423 : Prop :=
  ∀ (x y k H n₀ : ℕ),
    progressionContext x y k H n₀ →
      ((1 : ℚ) / (primeProduct x : ℚ)) *
          (∑ t : Fin (primeProduct x),
            ∏ j : Fin k,
              survivorIndicator46423 x t
                (progressionTerm n₀ y j.val)) =
        (Finset.prod ((Finset.range (y + 1)).filter Nat.Prime)
          (fun q => (1 : ℚ) - 1 / (q : ℚ))) *
          (Finset.prod
            (((Finset.range (x + 1)).filter Nat.Prime).filter (fun p => y < p))
            (fun p => (1 : ℚ) - (k : ℚ) / (p : ℚ)))

end MathlibPlus.Open.ResearchFormalization.R3270
