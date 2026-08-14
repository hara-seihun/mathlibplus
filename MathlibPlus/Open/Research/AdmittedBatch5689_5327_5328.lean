import Mathlib


namespace MathlibPlus.Open.Research

noncomputable section

abbrev ShiftMonomial := ℕ × Multiset ℕ
abbrev ShiftTracePoly := AddMonoidAlgebra ℤ ShiftMonomial

def shiftMonomial (s : ℕ) (m : ShiftMonomial) : ShiftMonomial :=
  (0, {m.1 + s} + m.2)

def shiftTrace (s : ℕ) (P : ShiftTracePoly) : ShiftTracePoly :=
  AddMonoidAlgebra.ofCoeff
    ((Finsupp.lmapDomain ℤ ℤ (shiftMonomial s)) P.coeff)

def zMonomial : ShiftTracePoly := AddMonoidAlgebra.single (1, 0) 1

def xMonomial (parts : Multiset ℕ) : ShiftTracePoly :=
  AddMonoidAlgebra.single (0, parts) 1

def shiftJ (P : ShiftTracePoly) : ShiftTracePoly :=
  zMonomial * P + shiftTrace 1 P

def shiftS₁ : ShiftTracePoly := shiftJ 1

def shiftS₂ : ShiftTracePoly := shiftJ shiftS₁

def shiftP₃ : ShiftTracePoly := shiftJ shiftS₂

def shiftY₃ : ShiftTracePoly := shiftJ (shiftS₁ ^ 2)

def shiftU₅ : ShiftTracePoly := shiftJ (shiftS₁ * shiftP₃)

def shiftV₄ : ShiftTracePoly := shiftJ shiftY₃

def shiftTraceRootedFactorSetup : Prop :=
  (∀ (s a : ℕ) (parts : Multiset ℕ),
    shiftTrace s (AddMonoidAlgebra.single (a, parts) 1) =
      xMonomial ({a + s} + parts)) ∧
  shiftS₁ = shiftJ 1 ∧
  shiftS₂ = shiftJ shiftS₁ ∧
  shiftP₃ = shiftJ shiftS₂ ∧
  shiftY₃ = shiftJ (shiftS₁ ^ 2) ∧
  shiftU₅ = shiftJ (shiftS₁ * shiftP₃) ∧
  shiftV₄ = shiftJ shiftY₃

end
end MathlibPlus.Open.Research



namespace MathlibPlus.Open.Research

noncomputable section
open scoped BigOperators

/-- A finite collection of nonempty pairwise-disjoint blocks covering `Fin k`. -/
def IsBlockPartition {k : ℕ} (π : Finset (Finset (Fin k))) : Prop :=
  (∀ B ∈ π, B.Nonempty) ∧
  (∀ B ∈ π, ∀ C ∈ π, B ≠ C → Disjoint B C) ∧
  (∀ i : Fin k, ∃ B ∈ π, i ∈ B)

def blockPartitions (k : ℕ) : Finset (Finset (Finset (Fin k))) := by
  classical
  exact (Finset.powerset (Finset.powerset (Finset.univ))).filter IsBlockPartition

def blockSum (parts : List ℕ) (B : Finset (Fin parts.length)) : ℕ :=
  ∑ i ∈ B, parts.get i

def quotientParts (parts : List ℕ)
    (π : Finset (Finset (Fin parts.length))) : Multiset ℕ :=
  π.attach.val.map (fun B => blockSum parts B.1)

def componentPartitionMobiusRow
    (u : Multiset ℕ → ℚ) (parts : List ℕ) : ℚ :=
  (blockPartitions parts.length).sum (fun π =>
    (-1 : ℚ) ^ (π.card - 1) * (π.card - 1).factorial *
      u (quotientParts parts π))

def componentPartitionMobiusRowClaim
    (u m : Multiset ℕ → ℚ) : Prop :=
  ∀ parts : List ℕ,
    m (Multiset.ofList parts) = componentPartitionMobiusRow u parts

end
end MathlibPlus.Open.Research



namespace MathlibPlus.Open.Research

noncomputable section

abbrev JordanVector (p r : ℕ) := Fin r → ZMod p

def jordanBasis (p r : ℕ) (i : Fin r) : JordanVector p r :=
  fun j => if j = i then 1 else 0

def jordanNilpotent (p r : ℕ) (v : JordanVector p r) : JordanVector p r :=
  fun i => if h : i.val + 1 < r then v ⟨i.val + 1, h⟩ else 0

def jordanStep (p r : ℕ) (v : JordanVector p r) : JordanVector p r :=
  fun i => v i + jordanNilpotent p r v i

def jordanTopBasis (p r : ℕ) (h : 0 < r) : JordanVector p r :=
  jordanBasis p r ⟨r - 1, by omega⟩

def jordanOrbitPoint (p r : ℕ) (h : 0 < r) (k : Fin p) : JordanVector p r :=
  (jordanStep p r)^[k.val] (jordanTopBasis p r h)

def jordanOrbit (p r : ℕ) (h : 0 < r) : Finset (JordanVector p r) :=
  Finset.univ.image (jordanOrbitPoint p r h)

def jordanFixedLine (p r : ℕ) (h : 0 < r) :
    Submodule (ZMod p) (JordanVector p r) :=
  Submodule.span (ZMod p) {jordanBasis p r ⟨0, h⟩}

def jordanReplayCase (p r : ℕ) : Prop :=
  Nat.Prime p ∧ 0 < r ∧ r < p ∧
    ∀ h : 0 < r,
      (jordanOrbit p r h).card = p ∧
      Submodule.span (ZMod p) (↑(jordanOrbit p r h) :
        Set (JordanVector p r)) = ⊤ ∧
      Function.Injective (fun k : Fin p =>
        (jordanFixedLine p r h).mkQ (jordanOrbitPoint p r h k))

def exactJordanReplayChecks : Prop :=
  jordanReplayCase 7 6 ∧
  jordanReplayCase 11 6 ∧
  jordanReplayCase 11 7 ∧
  jordanReplayCase 11 8 ∧
  jordanReplayCase 13 6 ∧
  jordanReplayCase 13 11

end
end MathlibPlus.Open.Research
