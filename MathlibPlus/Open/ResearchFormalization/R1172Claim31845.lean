import MathlibPlus.Open.FiberMaps31844

namespace MathlibPlus.Open.ResearchFormalization.R1172Claim31845

abbrev R1172S3 := FiberMapS3
abbrev R1172Carrier (p : ℕ) := FiberMapCarrier p

def commonFiberEquiv
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1) :
    R1172Carrier p ≃ R1172Carrier p :=
  (Equiv.prodCongrLeft q).trans
    (Equiv.prodCongr (Equiv.refl (ZMod p)) sigma)

def rightFiberEquiv (p : ℕ) (x : R1172Carrier p) : R1172Carrier p ≃ R1172Carrier p :=
  Equiv.prodCongr (Equiv.addRight x.1) (Equiv.mulRight x.2)

def inverseFiberEquiv (p : ℕ) : R1172Carrier p ≃ R1172Carrier p :=
  Equiv.prodCongr (Equiv.neg (ZMod p)) (Equiv.inv R1172S3)

def relativeDerivativeEquiv
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (u : ZMod p) (k : R1172S3) :
    R1172Carrier p ≃ R1172Carrier p :=
  let f := commonFiberEquiv p hp sigma hsigma q hq
  let x : R1172Carrier p := (u, k)
  let y := f x
  ((rightFiberEquiv p x).trans f).trans
    ((rightFiberEquiv p (inverseFiberEquiv p y)).trans f.symm)

def relativeDerivativeGroup
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1) :
    Subgroup (Equiv.Perm (R1172Carrier p)) :=
  Subgroup.closure
    (Set.range (fun x : R1172Carrier p =>
      relativeDerivativeEquiv p hp sigma hsigma q hq x.1 x.2))


def isTranslation31845 (p : ℕ) (e : Equiv.Perm (ZMod p)) : Prop :=
  ∃ t : ZMod p, e = Equiv.addRight t

def nonautomorphicBase31845 (sigma : Equiv.Perm R1172S3) : Prop :=
  ¬ ∃ beta : R1172S3 ≃* R1172S3, ∀ x : R1172S3, beta x = sigma x

def inverseClosed31845 (p : ℕ) (S : Set (R1172Carrier p)) : Prop :=
  ∀ x, x ∈ S → fiberMapProductInv p x ∈ S

def identityFree31845 {p : ℕ} (S : Set (R1172Carrier p)) : Prop :=
  ∀ x, x ∈ S → x ≠ (0, 1)

def derivativeInvariant31845
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (S : Set (R1172Carrier p)) : Prop :=
  ∀ g : relativeDerivativeGroup p hp sigma hsigma q hq,
    Set.image (g : Equiv.Perm (R1172Carrier p)) S = S

def claim31845 : Prop :=
  ∀ (p : ℕ), (hp : Nat.Prime p) → 7 ≤ p →
    ∀ (sigma : Equiv.Perm R1172S3), (hsigma : sigma 1 = 1) →
      nonautomorphicBase31845 sigma →
      ∀ (N : Set R1172S3),
        ∃ beta : R1172S3 ≃* R1172S3,
          ∀ (q : R1172S3 → Equiv.Perm (ZMod p)), (hq : q 1 = 1) →
            (∀ a : R1172S3,
              a ∈ N ↔ a ≠ 1 ∧ ¬ isTranslation31845 p (q a)) →
            ∀ (S : Set (R1172Carrier p)),
              identityFree31845 S →
              inverseClosed31845 p S →
              derivativeInvariant31845 p hp sigma hsigma q hq S →
              Set.image
                  (normalizedCommonCoordinateFiberMap31844 p hp
                    sigma hsigma q hq) S =
                Set.image (fun x : R1172Carrier p => (x.1, beta x.2)) S

end MathlibPlus.Open.ResearchFormalization.R1172Claim31845
