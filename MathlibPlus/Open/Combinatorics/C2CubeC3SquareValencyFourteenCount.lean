import MathlibPlus.Basic

namespace MathlibPlus.Open.Combinatorics

/-- The exact number of identity-free inverse-closed valency-fourteen
connection sets in `C₂³ × C₃²`, in its additive `ZMod` model. -/
noncomputable def c2CubeC3SquareValencyFourteenConnectionSetCount : Prop :=
  let G := (Fin 3 → ZMod 2) × (Fin 2 → ZMod 3)
  let X := {S : Finset G //
    0 ∉ S ∧ S.card = 14 ∧ ∀ x : G, x ∈ S → -x ∈ S}
  letI : Fintype X := Fintype.ofFinite X
  Fintype.card X = 29695768

end MathlibPlus.Open.Combinatorics
