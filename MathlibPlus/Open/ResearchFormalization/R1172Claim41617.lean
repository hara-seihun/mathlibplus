import MathlibPlus.Open.FiberMaps31844

namespace MathlibPlus.Open.ResearchFormalization.R1172Claim41617

abbrev R1172S3 := FiberMapS3
abbrev R1172Carrier (p : ℕ) := FiberMapCarrier p

def commonFiberEquiv41617
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1) :
    R1172Carrier p ≃ R1172Carrier p :=
  (Equiv.prodCongrLeft q).trans
    (Equiv.prodCongr (Equiv.refl (ZMod p)) sigma)

def rightFiberEquiv41617 (p : ℕ) (x : R1172Carrier p) :
    R1172Carrier p ≃ R1172Carrier p :=
  Equiv.prodCongr (Equiv.addRight x.1) (Equiv.mulRight x.2)

def inverseFiberEquiv41617 (p : ℕ) :
    R1172Carrier p ≃ R1172Carrier p :=
  Equiv.prodCongr (Equiv.neg (ZMod p)) (Equiv.inv R1172S3)

def relativeDerivativeEquiv41617
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1)
    (u : ZMod p) (k : R1172S3) :
    R1172Carrier p ≃ R1172Carrier p :=
  let f := commonFiberEquiv41617 p hp sigma hsigma q hq
  let x : R1172Carrier p := (u, k)
  let y := f x
  ((rightFiberEquiv41617 p x).trans f).trans
    ((rightFiberEquiv41617 p (inverseFiberEquiv41617 p y)).trans f.symm)

def normalizedRelativeDerivativeGroup41617
    (p : ℕ) (hp : Nat.Prime p)
    (sigma : Equiv.Perm R1172S3) (hsigma : sigma 1 = 1)
    (q : R1172S3 → Equiv.Perm (ZMod p)) (hq : q 1 = 1) :
    Subgroup (Equiv.Perm (R1172Carrier p)) :=
  Subgroup.closure
    (Set.range (fun x : R1172Carrier p =>
      relativeDerivativeEquiv41617 p hp sigma hsigma q hq x.1 x.2))

def isTranslation41617 (p : ℕ) (e : Equiv.Perm (ZMod p)) : Prop :=
  ∃ t : ZMod p, e = Equiv.addRight t

def nontranslationSupport41617
    (p : ℕ) (q : R1172S3 → Equiv.Perm (ZMod p)) : Set R1172S3 :=
  {a | a ≠ 1 ∧ ¬ isTranslation41617 p (q a)}

def supportLeftStabilizer41617 (N : Set R1172S3) : Set R1172S3 :=
  {h | ∀ a : R1172S3, a ∈ N ↔ h * a ∈ N}

def translationProfile41617
    (p : ℕ) (q : R1172S3 → Equiv.Perm (ZMod p))
    (N : Set R1172S3) (t : R1172S3 → ZMod p) : Prop :=
  ∀ j : R1172S3, j ∉ N → q j = Equiv.addRight (t j)

def safeDerivativeEdge41617
    (p : ℕ) (sigma : Equiv.Perm R1172S3)
    (t : R1172S3 → ZMod p)
    (h k : R1172S3) : Equiv.Perm (ZMod p) :=
  Equiv.addRight (t (h * k) - t k - t (thetaK sigma k h))

def safePathTarget41617
    (sigma : Equiv.Perm R1172S3) :
    List (Option R1172S3) → R1172S3 → R1172S3
  | [], h => h
  | none :: path, h => safePathTarget41617 sigma path h⁻¹
  | some k :: path, h =>
      safePathTarget41617 sigma path (thetaK sigma k h)

def safePathValid41617
    (N : Set R1172S3) (sigma : Equiv.Perm R1172S3) :
    List (Option R1172S3) → R1172S3 → Prop
  | [], h => True
  | none :: path, h => safePathValid41617 N sigma path h⁻¹
  | some k :: path, h =>
      k ∉ N ∧ h * k ∉ N ∧ thetaK sigma k h ∉ N ∧
        safePathValid41617 N sigma path (thetaK sigma k h)

def safePathAction41617
    (p : ℕ) (N : Set R1172S3)
    (sigma : Equiv.Perm R1172S3)
    (t : R1172S3 → ZMod p) :
    List (Option R1172S3) → R1172S3 → Equiv.Perm (ZMod p)
  | [], h => Equiv.refl (ZMod p)
  | none :: path, h =>
      (Equiv.neg (ZMod p)).trans
        (safePathAction41617 p N sigma t path h⁻¹)
  | some k :: path, h =>
      (safeDerivativeEdge41617 p sigma t h k).trans
        (safePathAction41617 p N sigma t path (thetaK sigma k h))

def safeOrbit41617
    (p : ℕ) (N : Set R1172S3)
    (sigma : Equiv.Perm R1172S3)
    (t : R1172S3 → ZMod p)
    (h : R1172S3) : Set (R1172Carrier p) :=
  {x | ∃ path : List (Option R1172S3),
    safePathValid41617 N sigma path h ∧
      (safePathAction41617 p N sigma t path h (0 : ZMod p),
        safePathTarget41617 sigma path h) = x}

def safeProjectedComponent41617
    (p : ℕ) (N : Set R1172S3)
    (sigma : Equiv.Perm R1172S3)
    (t : R1172S3 → ZMod p)
    (h : R1172S3) : Set R1172S3 :=
  {h' | ∃ z : ZMod p,
    (z, h') ∈ safeOrbit41617 p N sigma t h}

def safeFiberSaturated41617
    (p : ℕ) (N : Set R1172S3)
    (sigma : Equiv.Perm R1172S3)
    (t : R1172S3 → ZMod p)
    (h : R1172S3) : Prop :=
  ∀ h' : R1172S3,
    h' ∈ safeProjectedComponent41617 p N sigma t h →
      ∀ z : ZMod p,
        (z, h') ∈ safeOrbit41617 p N sigma t h

def safeLoopGenerators41617
    (p : ℕ) (N : Set R1172S3)
    (sigma : Equiv.Perm R1172S3)
    (t : R1172S3 → ZMod p)
    (h : R1172S3) : Set (Equiv.Perm (ZMod p)) :=
  {e | ∃ path : List (Option R1172S3),
    safePathValid41617 N sigma path h ∧
      safePathTarget41617 sigma path h = h ∧
      e = safePathAction41617 p N sigma t path h}

def safeLoopGroup41617
    (p : ℕ) (N : Set R1172S3)
    (sigma : Equiv.Perm R1172S3)
    (t : R1172S3 → ZMod p)
    (h : R1172S3) : Subgroup (Equiv.Perm (ZMod p)) :=
  Subgroup.closure (safeLoopGenerators41617 p N sigma t h)

def containsNonzeroTranslation41617
    (p : ℕ) (N : Set R1172S3)
    (sigma : Equiv.Perm R1172S3)
    (t : R1172S3 → ZMod p)
    (h : R1172S3) : Prop :=
  ∃ e : safeLoopGroup41617 p N sigma t h,
    ∃ c : ZMod p, c ≠ 0 ∧
      (e : Equiv.Perm (ZMod p)) = Equiv.addRight c

def commonCenter41617
    (p : ℕ) (N : Set R1172S3)
    (sigma : Equiv.Perm R1172S3)
    (t : R1172S3 → ZMod p)
    (h : R1172S3) (c : ZMod p) : Prop :=
  ∀ e : safeLoopGroup41617 p N sigma t h,
    ∃ epsilon b : ZMod p,
      (epsilon = 1 ∨ epsilon = -1) ∧
        b = (1 - epsilon) * c ∧
        ∀ z : ZMod p,
          (e : Equiv.Perm (ZMod p)) z = epsilon * z + b

def everySafePathAffine41617
    (p : ℕ) (C N : Set R1172S3)
    (sigma : Equiv.Perm R1172S3)
    (t : R1172S3 → ZMod p) : Prop :=
  ∀ (path : List (Option R1172S3)) (h : R1172S3),
    h ∈ C → safePathValid41617 N sigma path h →
      ∃ epsilon : ZMod p, (epsilon = 1 ∨ epsilon = -1) ∧
        ∃ b : ZMod p, ∀ z : ZMod p,
          safePathAction41617 p N sigma t path h z = epsilon * z + b

def claim41617 : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ (sigma : Equiv.Perm R1172S3), sigma 1 = 1 →
      ∀ (q : R1172S3 → Equiv.Perm (ZMod p)), q 1 = 1 →
        let N := nontranslationSupport41617 p q
        ∀ (t : R1172S3 → ZMod p),
          translationProfile41617 p q N t →
          ∀ (h : R1172S3),
            let C := safeProjectedComponent41617 p N sigma t h
            C ⊆ supportLeftStabilizer41617 N →
              everySafePathAffine41617 p C N sigma t ∧
                (containsNonzeroTranslation41617 p N sigma t h →
                    safeFiberSaturated41617 p N sigma t h) ∧
                (¬ containsNonzeroTranslation41617 p N sigma t h →
                    ∃ c : ZMod p,
                      commonCenter41617 p N sigma t h c)

end MathlibPlus.Open.ResearchFormalization.R1172Claim41617
