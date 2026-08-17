import Mathlib
import MathlibPlus.Open.ResearchBatch.Lease_01a001c2.ActualAffine

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1821Suborbits

open MathlibPlus.Open.ResearchBatch.ActualAffine

noncomputable section

/-- The displayed quadratic vertical displacement for a symmetric matrix. -/
def quadraticScalar (B : Matrix (Fin 5) (Fin 5) F3) (x : H3) : F3 :=
  2 * ∑ i, B i i * (x i) ^ 2 +
    ∑ i, (∑ j ∈ Finset.Ioi i, B i j * x i * x j)

/-- The quadratic transporter `q_B(z,x)=(z+f_B(x),x)`. -/
def quadraticTransporter (B : Matrix (Fin 5) (Fin 5) F3) : Equiv.Perm Omega3 :=
  { toFun := fun z => (z.1 + quadraticScalar B z.2, z.2)
    invFun := fun z => (z.1 - quadraticScalar B z.2, z.2)
    left_inv := by
      intro z
      ext <;> simp
    right_inv := by
      intro z
      ext <;> simp }

/-- The copy `R_B=T^{q_B}`, with the conjugation convention used by the
    affine actual-image model. -/
def quadraticConjugateSet (B : Matrix (Fin 5) (Fin 5) F3) :
    Set (Equiv.Perm Omega3) :=
  {σ | ∃ t : Equiv.Perm Omega3,
    t ∈ translationImageGroup ∧
      σ = (quadraticTransporter B)⁻¹ * t * quadraticTransporter B}

def quadraticCopy (B : Matrix (Fin 5) (Fin 5) F3) :
    Subgroup (Equiv.Perm Omega3) :=
  Subgroup.closure (quadraticConjugateSet B)

/-- `G_B=⟨T,R_B⟩`. -/
def generatedGroup (B : Matrix (Fin 5) (Fin 5) F3) :
    Subgroup (Equiv.Perm Omega3) :=
  Subgroup.closure
    ((translationImageGroup : Set (Equiv.Perm Omega3)) ∪
      (quadraticCopy B : Set (Equiv.Perm Omega3)))

def origin : Omega3 := (0, 0)

def displacementFiber (h : H3) : Set Omega3 :=
  {p | p.2 = h}

def pointStabilizerOrbit
    (G : Subgroup (Equiv.Perm Omega3)) (y : Omega3) : Set Omega3 :=
  {w | ∃ g : Equiv.Perm Omega3,
    g ∈ G ∧ g origin = origin ∧ g y = w}

def directedSuborbits
    (G : Subgroup (Equiv.Perm Omega3)) : Set (Set Omega3) :=
  Set.range (pointStabilizerOrbit G)

def directedSuborbitCount
    (G : Subgroup (Equiv.Perm Omega3)) : ℕ :=
  (directedSuborbits G).ncard

/-- Claim 32622: the exact displacement-fiber orbit split for the point
    stabilizer of the generated group. -/
def claim_32622 : Prop :=
  ∀ B : Matrix (Fin 5) (Fin 5) F3, B.IsSymm →
    ∀ h : H3,
      (Matrix.mulVec B h ≠ 0 →
        ∀ z : F3,
          pointStabilizerOrbit (generatedGroup B) (z, h) =
            displacementFiber h) ∧
      (Matrix.mulVec B h = 0 →
        ∀ z : F3,
          pointStabilizerOrbit (generatedGroup B) (z, h) =
            {(z, h)})

/-- Claim 32623: the exact number of directed point-stabilizer suborbits. -/
def claim_32623 : Prop :=
  ∀ B : Matrix (Fin 5) (Fin 5) F3, B.IsSymm →
    directedSuborbitCount (generatedGroup B) =
      243 + 2 * 3 ^ (5 - Matrix.rank B)

end
end MathlibPlus.Open.ResearchFormalization.R1821Suborbits
