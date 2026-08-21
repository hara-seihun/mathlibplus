-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

open BigOperators
open scoped BigOperators

namespace MathlibPlus.Combinatorics.Claim39921

abbrev F₃ := ZMod 3
abbrev V := F₃ × F₃

/-- Normalized lower-shear functions, with the value at the origin fixed to
zero exactly as in claim 39921. -/
def NormalizedFunction := {q : V → F₃ // q (0, 0) = 0}
deriving instance Fintype for NormalizedFunction

theorem normalized_function_card : Fintype.card NormalizedFunction = 3 ^ 8 := by
  native_decide

theorem normalized_function_card_value : Fintype.card NormalizedFunction = 6561 := by
  rw [normalized_function_card]
  norm_num

/-- The complete split-top, one-lower-shear map from the claim. -/
def h (q : NormalizedFunction) (x u v w : F₃) : F₃ × F₃ × F₃ × F₃ :=
  (x + v * w, u + q.1 (v, w), v + w, w)

end MathlibPlus.Combinatorics.Claim39921

namespace MathlibPlus.Combinatorics.Claim39202

abbrev F₃ := ZMod 3

def NormalizedV := {v : F₃ → F₃ // v 0 = 0}
deriving instance Fintype for NormalizedV
def NormalizedW := {w : (F₃ × F₃) → F₃ // w (0, 0) = 0}
deriving instance Fintype for NormalizedW
def TriangularData := NormalizedV × NormalizedW
deriving instance Fintype for TriangularData

theorem triangular_data_card : Fintype.card TriangularData = 3 ^ 10 := by
  native_decide

theorem triangular_data_card_value : Fintype.card TriangularData = 59049 := by
  rw [triangular_data_card]
  norm_num

/-- The normalized triangular transporter normal form. -/
def q (data : TriangularData) (a b c : F₃) : F₃ × F₃ × F₃ :=
  (a + data.2.1 (b, c), b + data.1.1 c, c)

/-- The unitriangular parameter family in the claim. -/
def unitriangular (α β γ a b c : F₃) : F₃ × F₃ × F₃ :=
  (a + α * b + β * c, b + γ * c, c)

theorem unitriangular_parameter_card : Fintype.card (F₃ × F₃ × F₃) = 27 := by
  native_decide

theorem triangular_coset_count : 3 ^ 10 / 27 = 2187 := by
  norm_num

end MathlibPlus.Combinatorics.Claim39202
