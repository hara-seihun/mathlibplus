import MathlibPlus.Open.FiberMaps31844

namespace MathlibPlus.Open.ResearchFormalization.R1172Claim41610

abbrev R1172S3 := FiberMapS3
abbrev R1172Carrier (p : ℕ) := FiberMapCarrier p

def commonFiberEquiv41610
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1) :
    R1172Carrier p ≃ R1172Carrier p :=
  (Equiv.prodCongrLeft q).trans
    (Equiv.prodCongr (Equiv.refl (ZMod p)) sigma)

def rightFiberEquiv41610 (p : ℕ) (x : R1172Carrier p) :
    R1172Carrier p ≃ R1172Carrier p :=
  Equiv.prodCongr (Equiv.addRight x.1) (Equiv.mulRight x.2)

def inverseFiberEquiv41610 (p : ℕ) :
    R1172Carrier p ≃ R1172Carrier p :=
  Equiv.prodCongr (Equiv.neg (ZMod p)) (Equiv.inv R1172S3)

def relativeDerivativeEquiv41610
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (u : ZMod p) (k : R1172S3) :
    R1172Carrier p ≃ R1172Carrier p :=
  let f := commonFiberEquiv41610 p hp sigma hsigma q hq
  let x : R1172Carrier p := (u, k)
  let y := f x
  ((rightFiberEquiv41610 p x).trans f).trans
    ((rightFiberEquiv41610 p (inverseFiberEquiv41610 p y)).trans f.symm)

def normalizedRelativeDerivativeGroup41610
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1) :
    Subgroup (Equiv.Perm (R1172Carrier p)) :=
  Subgroup.closure
    (Set.range (fun x : R1172Carrier p =>
      relativeDerivativeEquiv41610 p hp sigma hsigma q hq x.1 x.2))

def isTranslation41610 (p : ℕ) (e : Equiv.Perm (ZMod p)) : Prop :=
  ∃ t : ZMod p, e = Equiv.addRight t

def nontranslationSupport41610
    (p : ℕ) (q : R1172S3 → Equiv.Perm (ZMod p)) : Set R1172S3 :=
  {a | a ≠ 1 ∧ ¬ isTranslation41610 p (q a)}

def nonautomorphicBase41610 (sigma : Equiv.Perm R1172S3) : Prop :=
  ¬ ∃ beta : R1172S3 ≃* R1172S3,
      ∀ x : R1172S3, beta x = sigma x

def identityFree41610 {p : ℕ} (S : Set (R1172Carrier p)) : Prop :=
  ∀ x, x ∈ S → x ≠ (0, 1)

def inverseClosed41610 (p : ℕ) (S : Set (R1172Carrier p)) : Prop :=
  ∀ x, x ∈ S → fiberMapProductInv p x ∈ S

def derivativeInvariant41610
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (S : Set (R1172Carrier p)) : Prop :=
  ∀ g : normalizedRelativeDerivativeGroup41610 p hp sigma hsigma q hq,
    Set.image (g : Equiv.Perm (R1172Carrier p)) S = S

def claim41610 : Prop :=
  ∀ (p : ℕ), (hp : Nat.Prime p) → 7 ≤ p →
    ∀ (sigma : Equiv.Perm R1172S3), (hsigma : sigma 1 = 1) →
      nonautomorphicBase41610 sigma →
      ∀ (N : Set R1172S3), 1 ∉ N →
        ∃ beta : R1172S3 ≃* R1172S3,
          ∀ (q : R1172S3 → Equiv.Perm (ZMod p)), (hq : q 1 = 1) →
            (∀ a : R1172S3,
              a ∈ N ↔ a ≠ 1 ∧ ¬ isTranslation41610 p (q a)) →
              ∀ (S : Set (R1172Carrier p)),
                identityFree41610 S →
                inverseClosed41610 p S →
                derivativeInvariant41610 p hp sigma hsigma q hq S →
                Set.image
                    (normalizedCommonCoordinateFiberMap31844 p hp
                      sigma hsigma q hq) S =
                  Set.image (fun x : R1172Carrier p => (x.1, beta x.2)) S

end MathlibPlus.Open.ResearchFormalization.R1172Claim41610
