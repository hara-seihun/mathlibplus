import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0296ConnectivityScalar

noncomputable section

abbrev ConnectivityModule := Fin 2 →₀ ℝ

def basisS : ConnectivityModule := Finsupp.single 0 1

def basisT : ConnectivityModule := Finsupp.single 1 1

/-- The literal contact tensor `L(w)=wS+wT`. -/
def literalContact (w : ℝ) : ConnectivityModule :=
  w • basisS + w • basisT

/-- The proposed zipper tensor `Z(w)=S+(2w-1)T`. -/
def zipperTensor (w : ℝ) : ConnectivityModule :=
  basisS + (2 * w - 1) • basisT

/-- The scalar augmentation with both free basis vectors sent to `1`. -/
def scalarAugmentation (x : ConnectivityModule) : ℝ :=
  x 0 + x 1

/-- Claim 19519: on every intended weight `w=5/4+s` with `s≥0`, scalar
augmentation identifies the literal and zipper tensors although they differ in
the free connectivity module. -/
def scalarEqualityDoesNotLift_claim19519 : Prop :=
  ∀ s : ℝ, 0 ≤ s →
    let w : ℝ := 5 / 4 + s
    scalarAugmentation (literalContact w) = scalarAugmentation (zipperTensor w) ∧
      literalContact w ≠ zipperTensor w

end

end MathlibPlus.Open.ResearchFormalization.R0296ConnectivityScalar
