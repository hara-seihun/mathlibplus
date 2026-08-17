import MathlibPlus.Open.FiberMaps31844

namespace MathlibPlus.Open.ResearchFormalization.R1172Claim31852

abbrev S3 := FiberMapS3


def isTranslation31852 (p : ℕ) (e : Equiv.Perm (ZMod p)) : Prop :=
  ∃ t : ZMod p, e = Equiv.addRight t

def nontranslationSupport31852
    (p : ℕ) (q : S3 → Equiv.Perm (ZMod p)) : Set S3 :=
  {a | a ≠ 1 ∧ ¬ isTranslation31852 p (q a)}

def supportLeftStabilizer31852 (N : Set S3) : Set S3 :=
  {h | ∀ a : S3, a ∈ N ↔ h * a ∈ N}

def translationProfile31852
    (p : ℕ) (q : S3 → Equiv.Perm (ZMod p))
    (N : Set S3) (t : S3 → ZMod p) : Prop :=
  ∀ j : S3, j ∉ N → q j = Equiv.addRight (t j)

def safeDerivativeEdge31852
    (p : ℕ) (sigma : Equiv.Perm S3)
    (t : S3 → ZMod p)
    (h k : S3) : Equiv.Perm (ZMod p) :=
  Equiv.addRight (t (h * k) - t k - t (thetaK sigma k h))

def safePathTarget31852
    (sigma : Equiv.Perm S3) :
    List (Option S3) → S3 → S3
  | [], h => h
  | none :: path, h => safePathTarget31852 sigma path h⁻¹
  | some k :: path, h =>
      safePathTarget31852 sigma path (thetaK sigma k h)

def safePathValid31852
    (N : Set S3) (sigma : Equiv.Perm S3) :
    List (Option S3) → S3 → Prop
  | [], h => True
  | none :: path, h => safePathValid31852 N sigma path h⁻¹
  | some k :: path, h =>
      k ∉ N ∧ h * k ∉ N ∧ thetaK sigma k h ∉ N ∧
        safePathValid31852 N sigma path (thetaK sigma k h)

def safePathAction31852
    (p : ℕ) (N : Set S3)
    (sigma : Equiv.Perm S3)
    (t : S3 → ZMod p) :
    List (Option S3) → S3 → Equiv.Perm (ZMod p)
  | [], h => Equiv.refl (ZMod p)
  | none :: path, h =>
      (Equiv.neg (ZMod p)).trans
        (safePathAction31852 p N sigma t path h⁻¹)
  | some k :: path, h =>
      (safeDerivativeEdge31852 p sigma t h k).trans
        (safePathAction31852 p N sigma t path (thetaK sigma k h))

def safeProjectedComponent31852
    (N : Set S3) (sigma : Equiv.Perm S3)
    (h : S3) : Set S3 :=
  {h' | ∃ path : List (Option S3),
    safePathValid31852 N sigma path h ∧
      safePathTarget31852 sigma path h = h'}

def safeOrbit31852
    (p : ℕ) (N : Set S3)
    (sigma : Equiv.Perm S3)
    (t : S3 → ZMod p)
    (h : S3) (z₀ : ZMod p) : Set (ZMod p × S3) :=
  {x | ∃ path : List (Option S3),
    safePathValid31852 N sigma path h ∧
      (safePathAction31852 p N sigma t path h z₀,
        safePathTarget31852 sigma path h) = x}

def fiberSaturated31852
    (p : ℕ) (N : Set S3)
    (sigma : Equiv.Perm S3)
    (t : S3 → ZMod p)
    (h : S3) (z₀ : ZMod p) : Prop :=
  ∀ h' : S3,
    h' ∈ safeProjectedComponent31852 N sigma h →
      ∀ z : ZMod p,
        (z, h') ∈ safeOrbit31852 p N sigma t h z₀

def safeLoopGenerators31852
    (p : ℕ) (N : Set S3)
    (sigma : Equiv.Perm S3)
    (t : S3 → ZMod p)
    (h : S3) : Set (Equiv.Perm (ZMod p)) :=
  {e | ∃ path : List (Option S3),
    safePathValid31852 N sigma path h ∧
      safePathTarget31852 sigma path h = h ∧
      e = safePathAction31852 p N sigma t path h}

def safeLoopGroup31852
    (p : ℕ) (N : Set S3)
    (sigma : Equiv.Perm S3)
    (t : S3 → ZMod p)
    (h : S3) : Subgroup (Equiv.Perm (ZMod p)) :=
  Subgroup.closure (safeLoopGenerators31852 p N sigma t h)

def containsNonzeroTranslation31852
    (p : ℕ) (N : Set S3)
    (sigma : Equiv.Perm S3)
    (t : S3 → ZMod p)
    (h : S3) : Prop :=
  ∃ e : safeLoopGroup31852 p N sigma t h,
    ∃ c : ZMod p, c ≠ 0 ∧
      (e : Equiv.Perm (ZMod p)) = Equiv.addRight c

def commonCenter31852
    (p : ℕ) (N : Set S3)
    (sigma : Equiv.Perm S3)
    (t : S3 → ZMod p)
    (h : S3) (c : ZMod p) : Prop :=
  ∀ e : safeLoopGroup31852 p N sigma t h,
    ∃ epsilon b : ZMod p,
      (epsilon = 1 ∨ epsilon = -1) ∧
        b = (1 - epsilon) * c ∧
        ∀ z : ZMod p,
          (e : Equiv.Perm (ZMod p)) z = epsilon * z + b

def everySafePathAffine31852
    (p : ℕ) (C N : Set S3)
    (sigma : Equiv.Perm S3)
    (t : S3 → ZMod p) : Prop :=
  ∀ (path : List (Option S3)) (h : S3),
    h ∈ C →
      safePathValid31852 N sigma path h →
        safePathTarget31852 sigma path h ∈ C ∧
          ∃ epsilon b : ZMod p,
            (epsilon = 1 ∨ epsilon = -1) ∧
              ∀ z : ZMod p,
                safePathAction31852 p N sigma t path h z =
                  epsilon * z + b

def loopTranslationCommonCenterDichotomy31852 : Prop :=
  ∀ (p : ℕ), (hp : Nat.Prime p) →
    ∀ (sigma : Equiv.Perm S3), (hsigma : sigma 1 = 1) →
      ∀ (q : S3 → Equiv.Perm (ZMod p)), (hq : q 1 = 1) →
        let N := nontranslationSupport31852 p q
        ∀ (t : S3 → ZMod p),
          translationProfile31852 p q N t →
            ∀ (h : S3),
              let C := safeProjectedComponent31852 N sigma h
              C ⊆ supportLeftStabilizer31852 N →
                everySafePathAffine31852 p C N sigma t ∧
                  ((containsNonzeroTranslation31852 p N sigma t h →
                      ∀ z₀ : ZMod p,
                        fiberSaturated31852 p N sigma t h z₀) ∧
                    (¬ containsNonzeroTranslation31852 p N sigma t h →
                      ∃ c : ZMod p,
                        commonCenter31852 p N sigma t h c))

end MathlibPlus.Open.ResearchFormalization.R1172Claim31852
