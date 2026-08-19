import Mathlib

namespace MathlibPlus.Open.Research.CorrectedGaleRank61324

noncomputable section

open scoped BigOperators TensorProduct Matrix

abbrev R := ZMod 5
abbrev A := Fin 4 → R
abbrev B := Fin 5 → R
abbrev I := Fin 5 ⊕ Fin 4

/-- The bounded exponent indices for the degree-`n` monomial basis. -/
abbrev Exponent (n : ℕ) :=
  {α : Fin 5 → Fin 5 // ∑ j : Fin 5, (α j).val = n}

/-- Coordinates in the reduced homogeneous component of degree `n`. -/
abbrev H (n : ℕ) := Exponent n → R

def profileX : Matrix (Fin 5) (Fin 4) R :=
  !![2, 2, 0, 1;
     0, 4, 4, 2;
     2, 4, 4, 3;
     0, 2, 2, 1;
     4, 1, 0, 2]

/-- The direction and label columns of `[I_5|X]` and `[-X^T|I_4]`. -/
def direction (i : I) : B :=
  Sum.elim
    (fun k => fun j => if j = k then 1 else 0)
    (fun k => fun j => profileX j k)
    i

def label (i : I) : A :=
  Sum.elim
    (fun k => fun j => -profileX k j)
    (fun k => fun j => if j = k then 1 else 0)
    i

/-- Multiplication by the linear form `ell_d` in the reduced monomial basis.
Terms whose exponent would reach five are absent, as in the truncated
characteristic-five component. -/
def ellMultiply (d : B) (h : H 4) : H 5 :=
  fun α =>
    ∑ j : Fin 5, ∑ β : Exponent 4,
      if (∀ k : Fin 5,
          (α.1 k).val =
            (β.1 k).val + if k = j then 1 else 0) then
        d j * h β
      else 0

/-- The divided-power coefficient of `Gamma_5(d)` at a reduced exponent. -/
def gamma (d : B) : H 5 :=
  fun α =>
    ∏ j : Fin 5,
      (d j) ^ (α.1 j).val *
        ((Nat.factorial (α.1 j).val : R)⁻¹)

def labelledTensor (i : I) : TensorProduct R A B :=
  TensorProduct.tmul R (label i) (direction i)

def relationSet : Set (I → R) :=
  {c | ∑ i : I, c i • labelledTensor i = 0}

def tensorRank : ℕ :=
  Module.finrank R (Submodule.span R (Set.range labelledTensor))

def relationDimension : ℕ :=
  Module.finrank R (Submodule.span R relationSet)

def denominatorGenerator (i : I) (h : H 4) :
    TensorProduct R A (H 5) :=
  TensorProduct.tmul R (label i) (ellMultiply (direction i) h)

def denominatorSet : Set (TensorProduct R A (H 5)) :=
  {t | ∃ i : I, ∃ h : H 4, t = denominatorGenerator i h}

def denominator : Submodule R (TensorProduct R A (H 5)) :=
  Submodule.span R denominatorSet

def relationImage : TensorProduct R A (H 5) :=
  ∑ i : I, TensorProduct.tmul R (label i) (gamma (direction i))

def augmentedDenominator : Submodule R (TensorProduct R A (H 5)) :=
  Submodule.span R (denominatorSet ∪ {relationImage})

def denominatorRank : ℕ :=
  Module.finrank R denominator

def augmentedRank : ℕ :=
  Module.finrank R augmentedDenominator

def defectRank : ℕ :=
  augmentedRank - denominatorRank

def rankTriple : ℕ × ℕ × ℕ :=
  (relationDimension, denominatorRank, defectRank)

/-- Claim 61324: the corrected degree-five rank calculation for the displayed
canonical `F_5` Gale profile. -/
def claim61324 : Prop :=
  tensorRank = 8 ∧
    relationDimension = 1 ∧
    (∀ c : I → R,
      c ∈ relationSet ↔ ∃ t : R, ∀ i : I, c i = t) ∧
    denominatorRank = 449 ∧
    relationImage ∈ denominator ∧
    augmentedRank = denominatorRank ∧
    defectRank = 0 ∧
    rankTriple = (1, 449, 0)

end
end MathlibPlus.Open.Research.CorrectedGaleRank61324
