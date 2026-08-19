import MathlibPlus.Open.ResearchFormalization.R1137Claim30121

namespace MathlibPlus.Open.ResearchFormalization.R1137Claim35025

open MathlibPlus.Open.ResearchFormalization.R1137Claim30121

abbrev A4Coordinates := MathlibPlus.Open.ResearchFormalization.R1137Claim30121.A4Coordinates
abbrev PrimeProduct (p : ℕ) :=
  MathlibPlus.Open.ResearchFormalization.R1137Claim30121.PrimeProduct p

/-- The two retained product-coordinate transport maps. -/
def betaMinus {p : ℕ} : PrimeProduct p → PrimeProduct p :=
  fun z => (-z.1, alpha12T90 z.2)

def betaPlus {p : ℕ} : PrimeProduct p → PrimeProduct p :=
  fun z => (z.1, alpha12T90 z.2)

/-- Product-group automorphism in the retained coordinate multiplication. -/
def productGroupAutomorphism {p : ℕ}
    (f : PrimeProduct p → PrimeProduct p) : Prop :=
  Function.Bijective f ∧
    ∀ x y : PrimeProduct p,
      f (productMul x y) = productMul (f x) (f y)

/-- Inverse closure for the retained product-coordinate group law. -/
def productInverseClosed {p : ℕ} (S : Set (PrimeProduct p)) : Prop :=
  ∀ z : PrimeProduct p, z ∈ S → productInv z ∈ S

/-- Isomorphism of the ordinary undirected Cayley relations on the retained
product-coordinate carrier. -/
def productCayleyGraphIsomorphism {p : ℕ}
    (S T : Set (PrimeProduct p))
    (f : PrimeProduct p → PrimeProduct p) : Prop :=
  Function.Bijective f ∧
    ∀ x y : PrimeProduct p,
      (x ≠ y ∧ productMul (productInv x) y ∈ S) ↔
        (f x ≠ f y ∧ productMul (productInv (f x)) (f y) ∈ T)

/-- The normalization of a common fibrewise affine row. -/
def normalizedAffineRow {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ)
    (tau : A4Coordinates → ZMod p) : Prop :=
  lambda 0 = 1 ∧ tau 0 = 0

/-- The pure row is the zero scalar/translation profile in the retained
normalization. -/
def pureAffineRow {p : ℕ}
    (lambda : A4Coordinates → (ZMod p)ˣ)
    (tau : A4Coordinates → ZMod p) : Prop :=
  (∀ h : A4Coordinates, lambda h = 1) ∧
    tau = (0 : A4Coordinates → ZMod p)

/-- Claim 35025: the pure normalized row uses `betaMinus`, every nonpure
normalized affine row uses `betaPlus`, and both displayed maps are product
-group automorphisms. -/
def claim35025 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    productGroupAutomorphism (betaMinus (p := p)) ∧
      productGroupAutomorphism (betaPlus (p := p)) ∧
      ∀ (lambda : A4Coordinates → (ZMod p)ˣ)
        (tau : A4Coordinates → ZMod p),
        normalizedAffineRow lambda tau →
          ∀ S : Set (PrimeProduct p),
            productInverseClosed S →
              productInverseClosed
                (Set.image (affineLift lambda tau) S) →
                productCayleyGraphIsomorphism S
                  (Set.image (affineLift lambda tau) S)
                  (affineLift lambda tau) →
                  (pureAffineRow lambda tau →
                    Set.image (betaMinus (p := p)) S =
                      Set.image (affineLift lambda tau) S) ∧
                    (¬ pureAffineRow lambda tau →
                      Set.image (betaPlus (p := p)) S =
                        Set.image (affineLift lambda tau) S)

end MathlibPlus.Open.ResearchFormalization.R1137Claim35025
