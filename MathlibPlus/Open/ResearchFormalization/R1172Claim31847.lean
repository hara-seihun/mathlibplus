import MathlibPlus.Open.FiberMaps31844

namespace MathlibPlus.Open.ResearchFormalization.R1172Claim31847

abbrev S3 := FiberMapS3
abbrev Carrier (p : ℕ) := FiberMapCarrier p

def isTranslation31847 (p : ℕ) (e : Equiv.Perm (ZMod p)) : Prop :=
  ∃ t : ZMod p, e = Equiv.addRight t

def nontranslationSupport31847
    (p : ℕ) (q : S3 → Equiv.Perm (ZMod p)) : Set S3 :=
  {a | a ≠ 1 ∧ ¬ isTranslation31847 p (q a)}

def sectionDerivative31847
    (p : ℕ) (sigma : Equiv.Perm S3)
    (q : S3 → Equiv.Perm (ZMod p))
    (u : ZMod p) (k h : S3) : Equiv.Perm (ZMod p) :=
  ((Equiv.addRight u).trans (q (h * k))).trans
    ((Equiv.addRight (-(q k u))).trans
      (q (thetaK sigma k h)).symm)

def derivativeSectionFormula31847
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm S3) (hsigma : sigma 1 = 1)
    (q : S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (u : ZMod p) (k h : S3) : Prop :=
  ∀ z : ZMod p,
    relativeDerivativeOf31844 p hp sigma hsigma q hq u k (z, h) =
      (sectionDerivative31847 p sigma q u k h z,
        thetaK sigma k h)

def derivativeComparison31847
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm S3) (hsigma : sigma 1 = 1)
    (q : S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (a h : S3) (u v : ZMod p) : Prop :=
  derivativeSectionFormula31847 p hp sigma hsigma q hq u a h ∧
    derivativeSectionFormula31847 p hp sigma hsigma q hq v a h ∧
    (sectionDerivative31847 p sigma q v a h).symm.trans
        (sectionDerivative31847 p sigma q u a h) =
      (q (thetaK sigma a h)).trans
        ((Equiv.addRight ((u - q a u) - (v - q a v))).trans
          (q (thetaK sigma a h)).symm)

def primeCycle31847 (p : ℕ) (e : Equiv.Perm (ZMod p)) : Prop :=
  ∃ x : ZMod p,
    (∀ y : ZMod p, ∃ j : Fin p, (e ^ (j : ℕ)) x = y) ∧
      (∀ j k : Fin p,
        (e ^ (j : ℕ)) x = (e ^ (k : ℕ)) x → j = k)

def nontranslationTriggerProducesPrimeCycle31847 : Prop :=
  ∀ (p : ℕ), (hp : Nat.Prime p) →
    ∀ (sigma : Equiv.Perm S3), (hsigma : sigma 1 = 1) →
      ∀ (q : S3 → Equiv.Perm (ZMod p)), (hq : q 1 = 1) →
        ∀ (a h : S3),
          a ∈ nontranslationSupport31847 p q →
          h * a ∉ nontranslationSupport31847 p q →
          isTranslation31847 p (q (h * a)) ∧
          (¬ ∃ c : ZMod p, ∀ u : ZMod p, u - q a u = c) ∧
          ∃ u v : ZMod p,
            (u - q a u) - (v - q a v) ≠ 0 ∧
            derivativeComparison31847 p hp sigma hsigma q hq a h u v ∧
            primeCycle31847 p
              (Equiv.addRight ((u - q a u) - (v - q a v)))

end MathlibPlus.Open.ResearchFormalization.R1172Claim31847
