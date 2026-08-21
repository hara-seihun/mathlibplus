import MathlibPlus.Open.Combinatorics.R1540.Core

namespace MathlibPlus.Open.Combinatorics.R1540

noncomputable section

private def foldedRepresentative (w L : ℕ) : Option ℕ :=
  if 2 * L = w then none else some (min L (w - L))

private def foldedList (w a b c : ℕ) : List ℕ :=
  [a, b, c].filterMap (foldedRepresentative w)

private def foldedListPolynomial (w : ℕ) (xs : List ℕ) : F2Poly :=
  xs.foldr (fun L P => foldedPair w L + P) 0

/-- Claim 39054: Record 4's folded list for a sorted positive triple,
with the midpoint comparison expressed without a floor and with list
multiplicities interpreted in characteristic two. -/
def foldedListsForSortedTriples_claim39054 : Prop :=
  ∀ (w a b c : ℕ), 0 < a → a ≤ b → b ≤ c → a + b + c = w →
    foldedList w a b c =
        (if 2 * c < w then [a, b, c]
         else if 2 * c = w then [a, b]
         else [a, b, a + b]) ∧
      foldedArmPolynomial w a b c =
        foldedListPolynomial w (foldedList w a b c)

end

end MathlibPlus.Open.Combinatorics.R1540
