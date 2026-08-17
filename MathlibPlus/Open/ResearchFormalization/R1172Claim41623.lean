import MathlibPlus.Open.FiberMaps31844

namespace MathlibPlus.Open.ResearchFormalization.R1172Claim41623

abbrev S3 := FiberMapS3
abbrev Carrier (p : ℕ) := FiberMapCarrier p

def identity (p : ℕ) : Carrier p :=
  (0, 1)

def product (p : ℕ) (x y : Carrier p) : Carrier p :=
  fiberMapProductMul p x y

def inverse (p : ℕ) (x : Carrier p) : Carrier p :=
  fiberMapProductInv p x

def cayleyAdjacency (p : ℕ) (S : Set (Carrier p))
    (x y : Carrier p) : Prop :=
  product p (inverse p x) y ∈ S

def inverseClosed (p : ℕ) (S : Set (Carrier p)) : Prop :=
  ∀ ⦃x : Carrier p⦄, x ∈ S → inverse p x ∈ S

def identityFree (p : ℕ) (S : Set (Carrier p)) : Prop :=
  identity p ∉ S

def cayleyGraphIsomorphism (p : ℕ)
    (S T : Set (Carrier p)) (f : Carrier p → Carrier p) : Prop :=
  Function.Bijective f ∧
    ∀ x y : Carrier p,
      cayleyAdjacency p S x y ↔ cayleyAdjacency p T (f x) (f y)

def groupAutomorphism (p : ℕ) (f : Carrier p → Carrier p) : Prop :=
  Function.Bijective f ∧
    f (identity p) = identity p ∧
    (∀ x y : Carrier p,
      f (product p x y) = product p (f x) (f y)) ∧
    (∀ x : Carrier p,
      f (inverse p x) = inverse p (f x))

def nonautomorphicBase (sigma : Equiv.Perm S3) : Prop :=
  ¬ ∃ beta : S3 ≃* S3, ∀ h : S3, beta h = sigma h

def commonChartOrdinaryCIFailure
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm S3) (hsigma : sigma 1 = 1)
    (q : S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1) : Prop :=
  let f := normalizedCommonCoordinateFiberMap31844
    p hp sigma hsigma q hq
  ∃ S T : Set (Carrier p),
    inverseClosed p S ∧
      identityFree p S ∧
      inverseClosed p T ∧
      identityFree p T ∧
      Set.image f S = T ∧
      cayleyGraphIsomorphism p S T f ∧
      ¬ ∃ alpha : Carrier p → Carrier p,
        groupAutomorphism p alpha ∧ Set.image alpha S = T

def claim41623 : Prop :=
  ∀ (p : ℕ), ∀ hp : Nat.Prime p, 7 ≤ p →
    ∀ (sigma : Equiv.Perm S3), ∀ hsigma : sigma 1 = 1,
      nonautomorphicBase sigma →
      ∀ (q : S3 → Equiv.Perm (ZMod p)), ∀ hq : q 1 = 1,
        ¬ commonChartOrdinaryCIFailure p hp sigma hsigma q hq

end MathlibPlus.Open.ResearchFormalization.R1172Claim41623
