import MathlibPlus.Open.ResearchFormalization.R1285.Claim39994

namespace MathlibPlus.Open.ResearchFormalization.R1285.Claim39991

noncomputable section

open Classical
attribute [local instance] Classical.decEq Classical.propDecidable
open MathlibPlus.Open.ResearchFormalization.R1182.Claim31941
open MathlibPlus.Open.ResearchFormalization.R1285

private def derivativeTranslationsAt
    (n : ℕ) (f : Equiv.Perm (HallQ12Carrier n))
    (h : Q12) : Set (ZMod n) :=
  {c | ∃ d ∈ hallQ12DerivativeGenerators n f,
    d (0, h) = (c, h)}

private def derivativeSubgroupAt
    (n : ℕ) (f : Equiv.Perm (HallQ12Carrier n))
    (h : Q12) : AddSubgroup (ZMod n) :=
  AddSubgroup.closure (derivativeTranslationsAt n f h)

private def atomTranslationSubgroup
    (n : ℕ) (f : Equiv.Perm (HallQ12Carrier n))
    (X : Set Q12) : AddSubgroup (ZMod n) :=
  AddSubgroup.closure
    {c | ∃ h ∈ X, c ∈ derivativeTranslationsAt n f h}

private def sectionPeriodic
    (n : ℕ) (S : Set (HallQ12Carrier n))
    (X : Set Q12) (D : AddSubgroup (ZMod n)) : Prop :=
  ∀ h ∈ X, ∀ x : ZMod n, ∀ c ∈ D,
    ((x + c, h) ∈ S ↔ (x, h) ∈ S)

/-- The full cyclic subgroup belonging to the `p`-coordinate in the
square-free CRT decomposition of `Cₙ`. -/
private def pCoordinateSubgroup (n p : ℕ) : AddSubgroup (ZMod n) :=
  AddSubgroup.closure
    (Set.range (fun a : ZMod p =>
      ((n / p : ℕ) : ZMod n) * (a.val : ZMod n)))

private def pActive (n p : ℕ) (D : AddSubgroup (ZMod n)) : Prop :=
  pCoordinateSubgroup n p ≤ D

private def pQuiet (n p : ℕ) (D : AddSubgroup (ZMod n)) : Prop :=
  ¬ pActive n p D

private def quietAtomPattern
    (n p : ℕ) (D_A D_B : AddSubgroup (ZMod n)) : Set (Set Q12) :=
  {X |
    (X = axisAtom ∧ pQuiet n p D_A) ∨
      (X = outerAtom ∧ pQuiet n p D_B)}

/-- Claim 39991: the exact atomwise derivative subgroups define the
square-free prime-coordinate active/quiet split, active coordinates are
section periods, and the nonempty quiet atom patterns are the three stated
subsets of the two Q12 atoms. -/
def claim39991_q12PrimeCoordinateActiveQuiet : Prop :=
  ∀ n : ℕ, Squarefree n → Nat.Coprime n 6 →
    ∀ (lam : Q12 → (ZMod n)ˣ) (tau : Q12 → ZMod n)
      (σ : Equiv.Perm Q12)
      (f : Equiv.Perm (HallQ12Carrier n)),
      normalizedHallQ12AffineLift n lam tau σ f →
      ∀ S : Set (HallQ12Carrier n),
        hallQ12IdentityFree n S →
        hallQ12InverseClosed n S →
        hallQ12DerivativeInvariant n f S →
        ∀ p : ℕ, Nat.Prime p → p ∣ n →
          let D_A := atomTranslationSubgroup n f axisAtom
          let D_B := atomTranslationSubgroup n f outerAtom
          let Q := quietAtomPattern n p D_A D_B
          (∀ X : Set Q12, (X = axisAtom ∨ X = outerAtom) →
            let D := atomTranslationSubgroup n f X
            (∀ h ∈ X, derivativeSubgroupAt n f h = D) ∧
              sectionPeriodic n S X D ∧
              (pActive n p D →
                sectionPeriodic n S X (pCoordinateSubgroup n p))) ∧
          (Q.Nonempty →
            Q = {axisAtom} ∨ Q = {outerAtom} ∨
              Q = {axisAtom, outerAtom})

end

end MathlibPlus.Open.ResearchFormalization.R1285.Claim39991
