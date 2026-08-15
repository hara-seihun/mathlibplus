import Mathlib

noncomputable section

open scoped BigOperators

namespace MathlibPlus.Open

/-! Exact carrier and weight definitions supplied in the admitted repair context for Claim 7518. -/

structure OneHeightPresentation7518 where
  multiplicity : (ℕ × ℕ) →₀ ℕ
  no_zero_fold : multiplicity (0, 0) = 0
  deriving DecidableEq

instance : Zero OneHeightPresentation7518 where
  zero :=
    { multiplicity := 0
      no_zero_fold := by simp }

instance : Inhabited OneHeightPresentation7518 := ⟨0⟩

abbrev Prime7518 := {p : ℕ // Nat.Prime p}
abbrev EulerScarweave7518 := Prime7518 →₀ OneHeightPresentation7518

def foldLoad7518 (q : ℕ × ℕ) : ℕ := 2 * q.1 + q.2

def foldCount7518 (ell : ℕ) : ℕ := ell / 2 + 1

def presentationLoad7518 (X : OneHeightPresentation7518) : ℕ :=
  Finset.sum X.multiplicity.support (fun q => X.multiplicity q * foldLoad7518 q)

def presentationWeight7518 (X : OneHeightPresentation7518) : ℝ :=
  Finset.prod X.multiplicity.support (fun q =>
    1 / (((Nat.factorial (X.multiplicity q) : ℕ) : ℝ) *
      (((foldLoad7518 q * foldCount7518 (foldLoad7518 q)) ^ X.multiplicity q : ℕ) : ℝ)))

def seam7518 (X : EulerScarweave7518) : ℕ :=
  Finset.prod X.support (fun p => (p : ℕ) ^ presentationLoad7518 (X p))

def weight7518 (X : EulerScarweave7518) : ℝ :=
  Finset.prod X.support (fun p => presentationWeight7518 (X p))

def everyIntegerSeamHasUnitFiberMassClaim7518 : Prop :=
  ∀ n : ℕ, 0 < n →
    (∑' X : EulerScarweave7518,
      if seam7518 X = n then weight7518 X else 0) = 1

/-! Exact finite-group carrier and hypotheses from the admitted statement for Claim 60011. -/

abbrev V60011 := Fin 3 → ZMod 3
abbrev G60011 := ZMod 4 × V60011

def inverseClosed60011 (S : Set G60011) : Prop :=
  ∀ ⦃x : G60011⦄, x ∈ S → -x ∈ S

def dSet60011 (S : Set G60011) (w : V60011) : Set (ZMod 4) :=
  {a | (a, w) ∈ S}

def lambda60011 (S : Set G60011) (w : V60011) : ℕ := by
  classical
  exact (Finset.univ.filter (fun a : ZMod 4 => a ∈ dSet60011 S w)).card

def translateSet60011 (a : ZMod 4) (A : Set (ZMod 4)) : Set (ZMod 4) :=
  {b | ∃ c, c ∈ A ∧ b = a + c}

def intersectionCard60011 (S : Set G60011) (a : ZMod 4) (z u : V60011) : ℕ := by
  classical
  exact (Finset.univ.filter (fun b : ZMod 4 =>
    b ∈ dSet60011 S z ∩ translateSet60011 a (dSet60011 S (z - u)))).card

def kappa60011 (S : Set G60011) (a : ZMod 4) (u : V60011) : ℕ :=
  Finset.sum Finset.univ (fun z => intersectionCard60011 S a z u)

def nonzeroVector60011 : V60011 := fun _ => 1

def cayleyGraph60011 (S : Set G60011) (hS : inverseClosed60011 S) : SimpleGraph G60011 where
  Adj x y := x ≠ y ∧ y - x ∈ S
  symm := ⟨by
    intro x y h
    constructor
    · exact Ne.symm h.1
    · simpa using hS h.2⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩

def ciConnectionSet60011 (S : Set G60011) (hS : inverseClosed60011 S) : Prop :=
  ∀ (T : Set G60011) (hT : inverseClosed60011 T),
    T ⊆ {x | x ≠ 0} →
    cayleyGraph60011 S hS ≃g cayleyGraph60011 T hT →
      ∃ e : G60011 ≃+ G60011, e '' S = T

-- The explicit hypotheses are kept in the final statement; the graph isomorphism
-- arguments use the inverse-closure witnesses supplied by those hypotheses.
def residualFingerprintRigidityClaim60011 : Prop :=
  ∀ (S : Set G60011),
    (hS : inverseClosed60011 S) →
    S ⊆ {x | x ≠ 0} →
    (let three : Finset (ZMod 4) := {1, 2, 3}
     let nonzeroPairs : Finset (V60011 × ZMod 4) :=
       (Finset.univ.filter (fun p => p.1 ≠ 0))
     let minSame :=
       (three.image (fun a => kappa60011 S a 0)).min'
         (by simp [three])
     let maxDifferent :=
       (nonzeroPairs.image (fun p => kappa60011 S p.2 p.1)).max'
         (by
           classical
           refine ⟨kappa60011 S 0 nonzeroVector60011, ?_⟩
           refine Finset.mem_image.mpr ⟨(nonzeroVector60011, (0 : ZMod 4)), ?_, rfl⟩
           have hv : nonzeroVector60011 ≠ 0 := by
             intro h
             have h0 := congrFun h 0
             simpa [nonzeroVector60011] using h0
           simp [nonzeroPairs, hv])
     minSame > maxDifferent) →
    (∀ (u v : V60011),
      LinearIndependent (ZMod 3) ![u, v] →
        ¬ (lambda60011 S u = lambda60011 S v ∧
          lambda60011 S v = lambda60011 S (v - u))) →
    ciConnectionSet60011 S hS

end MathlibPlus.Open
