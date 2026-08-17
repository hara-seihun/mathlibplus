import Mathlib

open scoped BigOperators TensorProduct

namespace MathlibPlus.Open.ResearchFormalizationBatch_20260817_R1254

noncomputable section

abbrev RepairF3_30644 := ZMod 3
abbrev RepairCube_30644 := Fin 3 → RepairF3_30644
abbrev RepairScalarSpace_30644 := Fin 23 → RepairF3_30644
abbrev RepairRelationCarrier_30644 := Fin 13 → RepairScalarSpace_30644

/-- The thirteen normalized representatives of the projective directions of
`F₃³`. -/
def repairCubeDirection30644 : Fin 13 → RepairCube_30644 :=
  ![
    ![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![0, 1, 2],
    ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0],
    ![1, 1, 1], ![1, 1, 2], ![1, 2, 0], ![1, 2, 1],
    ![1, 2, 2]
  ]

/-- The twenty-three residual points after fixing the origin and the three
coordinate points for the affine normalization. -/
def repairCubeResidual30644 : Fin 23 → RepairCube_30644 :=
  ![
    ![0, 0, 2], ![0, 1, 1], ![0, 1, 2], ![0, 2, 0], ![0, 2, 1],
    ![0, 2, 2], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![1, 1, 1],
    ![1, 1, 2], ![1, 2, 0], ![1, 2, 1], ![1, 2, 2], ![2, 0, 0],
    ![2, 0, 1], ![2, 0, 2], ![2, 1, 0], ![2, 1, 1], ![2, 1, 2],
    ![2, 2, 0], ![2, 2, 1], ![2, 2, 2]
  ]

/-- Evaluation of a normalized scalar function on the full cube. -/
def repairScalarValue30644
    (u : RepairScalarSpace_30644) (x : RepairCube_30644) : RepairF3_30644 :=
  ∑ i : Fin 23, if repairCubeResidual30644 i = x then u i else 0

/-- The reduced-polynomial degree of an exponent vector. -/
def repairExponentDegree30644 (e : Fin 3 → Fin 3) : ℕ :=
  ∑ i : Fin 3, (e i).val

/-- Reduced monomials with their affine part removed. -/
def repairNormalizedMonomial30644
    (e : Fin 3 → Fin 3) : RepairScalarSpace_30644 :=
  fun i =>
    let x := repairCubeResidual30644 i
    let value :=
      (x 0) ^ (e 0).val * (x 1) ^ (e 1).val * (x 2) ^ (e 2).val
    let affinePart :=
      if e 0 ≠ 0 ∧ e 1 = 0 ∧ e 2 = 0 then x 0
      else if e 0 = 0 ∧ e 1 ≠ 0 ∧ e 2 = 0 then x 1
      else if e 0 = 0 ∧ e 1 = 0 ∧ e 2 ≠ 0 then x 2
      else 0
    value - affinePart

/-- The algebraic-degree filtration modulo affine scalar functions. -/
def repairDegreeFunctions30644 (bound : ℕ) : Set RepairScalarSpace_30644 :=
  {u | ∃ e : Fin 3 → Fin 3,
      2 ≤ repairExponentDegree30644 e ∧
        repairExponentDegree30644 e ≤ bound ∧
          u = repairNormalizedMonomial30644 e}

def repairDegreeSpace30644 (bound : ℕ) :
    Submodule RepairF3_30644 RepairScalarSpace_30644 :=
  Submodule.span RepairF3_30644 (repairDegreeFunctions30644 bound)

/-- The scalar kernel `K_x` from the affine-quotient formulation. -/
def repairKernelCondition30644
    (x : RepairCube_30644) (u : RepairScalarSpace_30644) : Prop :=
  ∀ y : RepairCube_30644,
    repairScalarValue30644 u (y + x) =
      repairScalarValue30644 u y + repairScalarValue30644 u x

/-- The tensor relation `Σ x ⊗ u_x = 0` for the thirteen projective
 directions. -/
def repairTensorRelation30644
    (r : RepairRelationCarrier_30644) : Prop :=
  ∑ j : Fin 13,
      repairCubeDirection30644 j ⊗ₜ[RepairF3_30644] r j = 0

/-- Degree-restricted tensor relations. -/
def repairRelationGenerators30644 (bound : ℕ) :
    Set RepairRelationCarrier_30644 :=
  {r | (∀ j : Fin 13,
          repairKernelCondition30644 (repairCubeDirection30644 j) (r j)) ∧
      (∀ j : Fin 13, r j ∈ repairDegreeSpace30644 bound) ∧
        repairTensorRelation30644 r}

def repairRelationSpace30644 (bound : ℕ) :
    Submodule RepairF3_30644 RepairRelationCarrier_30644 :=
  Submodule.span RepairF3_30644 (repairRelationGenerators30644 bound)

/-- The full tensor-relation space, without a degree restriction. -/
def repairFullRelationGenerators30644 :
    Set RepairRelationCarrier_30644 :=
  {r | (∀ j : Fin 13,
          repairKernelCondition30644 (repairCubeDirection30644 j) (r j)) ∧
        repairTensorRelation30644 r}

def repairFullRelationSpace30644 :
    Submodule RepairF3_30644 RepairRelationCarrier_30644 :=
  Submodule.span RepairF3_30644 repairFullRelationGenerators30644

/-- The obstruction functional `Σ u_x(x)`. -/
def repairObstruction30644 (r : RepairRelationCarrier_30644) : RepairF3_30644 :=
  ∑ j : Fin 13,
    repairScalarValue30644 (r j) (repairCubeDirection30644 j)

/-- Claim 30644: the quadratic, cubic, and full tensor-relation dimensions
and the vanishing of the obstruction on the quadratic space. -/
def claim30644 : Prop :=
  Module.finrank RepairF3_30644 (repairRelationSpace30644 2) = 24 ∧
    Module.finrank RepairF3_30644 (repairRelationSpace30644 3) = 35 ∧
    Module.finrank RepairF3_30644 repairFullRelationSpace30644 = 35 ∧
    ∀ r : RepairRelationCarrier_30644,
      r ∈ repairRelationSpace30644 2 → repairObstruction30644 r = 0

end
end MathlibPlus.Open.ResearchFormalizationBatch_20260817_R1254
