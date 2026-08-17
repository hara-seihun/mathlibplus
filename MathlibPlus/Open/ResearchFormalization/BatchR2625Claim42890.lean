import MathlibPlus.Algebra.Claim42889

namespace MathlibPlus.Open.ResearchFormalization.BatchR2625Claim42890

abbrev Vec4 := Fin 4 → ℝ

open MathlibPlus.Algebra.Claim42889

noncomputable section

def symmetricMultilinear {j : ℕ}
    (B : MultilinearMap ℝ (fun _ : Fin j => Vec4) ℝ) : Prop :=
  ∀ σ : Equiv.Perm (Fin j), ∀ v : Fin j → Vec4,
    B (v ∘ σ) = B v

def polarizationTwo : Prop :=
  ∃! B : MultilinearMap ℝ (fun _ : Fin 2 => Vec4) ℝ,
    symmetricMultilinear B ∧
      ∀ t : Vec4, B (fun _ : Fin 2 => t) = determinantPiece₂ t

def polarizationThree : Prop :=
  ∃! B : MultilinearMap ℝ (fun _ : Fin 3 => Vec4) ℝ,
    symmetricMultilinear B ∧
      ∀ t : Vec4, B (fun _ : Fin 3 => t) = determinantPiece₃ t

def polarizationFour : Prop :=
  ∃! B : MultilinearMap ℝ (fun _ : Fin 4 => Vec4) ℝ,
    symmetricMultilinear B ∧
      ∀ t : Vec4, B (fun _ : Fin 4 => t) = determinantPiece₄ t

/-- The unique symmetric j-linear polarizations of the three displayed
homogeneous determinant pieces, with their diagonal identities. -/
def symmetricPolarizations_claim42890 : Prop :=
  polarizationTwo ∧ polarizationThree ∧ polarizationFour

end
end MathlibPlus.Open.ResearchFormalization.BatchR2625Claim42890
