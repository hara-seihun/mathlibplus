import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.A4MorrisProfileShadow

noncomputable section

abbrev A (F : Type*) := Fin 5 → F
abbrev B (F : Type*) := Fin 3 → F
abbrev G (F : Type*) := A F × B F

private def covectorOf {F : Type*} [Field F] (c : Fin 5 → F) :
    A F →ₗ[F] F :=
  (LinearMap.proj (R := F) (φ := fun _ : Fin 1 => F) (0 : Fin 1)).comp
    (Matrix.mulVecLin (fun _ j => c j))

private def directions {F : Type*} [Field F] : Fin 11 → B F :=
  ![
    ![1, 0, 0],
    ![1, 0, 0],
    ![0, 1, 0],
    ![0, 0, 1],
    ![1, 1, 0],
    ![1, 0, 1],
    ![0, 1, 1],
    ![1, 1, 1],
    ![2, 1, 1],
    ![1, 2, 1],
    ![1, 1, 2]
  ]

private def covectors {F : Type*} [Field F] :
    Fin 11 → A F →ₗ[F] F :=
  ![
    covectorOf ![0, 0, 1, 0, 0],
    covectorOf ![0, 0, 0, 1, 0],
    covectorOf ![0, 1, 0, 0, 0],
    covectorOf ![1, 0, 0, 0, 0],
    covectorOf ![0, 1, 0, -1, 0],
    covectorOf ![1, 0, -1, 0, 0],
    covectorOf ![1, 1, 0, 0, 1],
    covectorOf ![1, 1, -1, -1, 1],
    covectorOf ![1, 1, 1, 1, 1],
    covectorOf ![-1, -1, 1, -1, 1],
    covectorOf ![-1, -1, -1, 1, 1]
  ]

private def slopeValue {F : Type*} [Field F]
    (i : Fin 11) (L : B F →ₗ[F] A F) : F :=
  covectors i (L (directions i))

private def affineRow {F : Type*} [Field F]
    (i : Fin 11) (c : F) : Set (G F) :=
  {z | z.2 = directions i ∧ covectors i z.1 = c}

private def duplicatedDirectionRow {F : Type*} [Field F]
    (c₀ c₁ : F) : Set (G F) :=
  {z | z.2 = directions 0 ∧
    covectors 0 z.1 = c₀ ∧ covectors 1 z.1 = c₁}

private def negSet {α : Type*} [Neg α] (S : Set α) : Set α :=
  {z | -z ∈ S}

private def baseZeroPart {F : Type*} [Field F]
    (M : Set (A F)) : Set (G F) :=
  {z | ∃ a : A F, a ∈ M ∧ z = (a, 0)}

private def allowedConnectionSet {F : Type*} [Field F]
    (levels : Fin 11 → F) (markers : Set (A F)) : Set (G F) :=
  baseZeroPart markers ∪
    ⋃ i : Fin 11,
      affineRow i (levels i) ∪ negSet (affineRow i (levels i))

private def qNonlinear {F : Type*} [Field F]
    (s : B F → A F) : G F → G F :=
  fun z => (z.1 + s z.2, z.2)

private def qLinear {F : Type*} [Field F]
    (L : B F →ₗ[F] A F) : G F → G F :=
  fun z => (z.1 + L z.2, z.2)

private def finiteDifferenceCondition {F : Type*} [Field F]
    (s : B F → A F) (lambda : Fin 11 → F) : Prop :=
  ∀ (x : B F) (i : Fin 11),
    covectors i (s (x + directions i) - s x) = lambda i

private def differenceTransport {F : Type*} [Field F]
    (q : G F → G F) (v z : G F) : G F :=
  q (z + v) - q z

private def connectionImage {F : Type*} [Field F]
    (q : G F → G F) (S : Set (G F)) : Set (G F) :=
  {w | ∃ v ∈ S, ∃ z : G F, differenceTransport q v z = w}

private def additiveAutomorphism {F : Type*} [Field F]
    (q : G F → G F) : Prop :=
  Function.Bijective q ∧
    ∀ z w : G F, q (z + w) = q z + q w

private def groupAutomorphismShadow {F : Type*} [Field F]
    (q : G F → G F) (S T : Set (G F)) : Prop :=
  ∃ e : G F ≃+ G F,
    (∀ z : G F, (e : G F → G F) z = q z) ∧
      Set.image (e : G F → G F) S = T

private def inversePaired {F : Type*} [Field F]
    (S : Set (G F)) : Prop :=
  ∀ z : G F, z ∈ S ↔ -z ∈ S

private def identityFree {F : Type*} [Field F]
    (S : Set (G F)) : Prop :=
  (0 : G F) ∉ S

private def ordinaryConnectionSet {F : Type*} [Field F]
    (S : Set (G F)) : Prop :=
  identityFree S ∧ inversePaired S

/-- Claim 61228.  The eleven displayed direction/covector rows have a
surjective slope map in every field in which 2 and 3 are nonzero.  Any
function with constant labelled differences on those rows therefore has the
same row, inverse-row, duplicated-direction intersection, and base-zero
connection images as a linear shear; every ordinary inverse-paired
construction from those parts consequently has an additive-automorphism
shadow. -/
def morrisProfileLinearShadow_claim61228 : Prop :=
  ∀ (F : Type*) [Field F],
    (2 : F) ≠ 0 →
    (3 : F) ≠ 0 →
      (∀ lambda : Fin 11 → F,
        ∃ L : B F →ₗ[F] A F,
          ∀ i : Fin 11, slopeValue i L = lambda i) ∧
      (∀ (lambda : Fin 11 → F) (s : B F → A F),
        finiteDifferenceCondition s lambda →
          ∃ L : B F →ₗ[F] A F,
            (∀ i : Fin 11, slopeValue i L = lambda i) ∧
            additiveAutomorphism (qLinear L) ∧
            (∀ (i : Fin 11) (c : F),
              connectionImage (qNonlinear s) (affineRow i c) =
                connectionImage (qLinear L) (affineRow i c)) ∧
            (∀ (i : Fin 11) (c : F),
              connectionImage (qNonlinear s)
                  (negSet (affineRow i c)) =
                connectionImage (qLinear L)
                  (negSet (affineRow i c))) ∧
            (∀ (c₀ c₁ : F),
              connectionImage (qNonlinear s)
                  (duplicatedDirectionRow c₀ c₁) =
                connectionImage (qLinear L)
                  (duplicatedDirectionRow c₀ c₁)) ∧
            (∀ (M : Set (A F)),
              connectionImage (qNonlinear s) (baseZeroPart M) =
                  baseZeroPart M ∧
                connectionImage (qLinear L) (baseZeroPart M) =
                  baseZeroPart M) ∧
            (∀ (levels : Fin 11 → F) (M : Set (A F)),
              connectionImage (qNonlinear s)
                  (allowedConnectionSet levels M) =
                connectionImage (qLinear L)
                  (allowedConnectionSet levels M)) ∧
            (∀ (levels : Fin 11 → F) (M : Set (A F)),
              ordinaryConnectionSet (allowedConnectionSet levels M) →
                groupAutomorphismShadow (qLinear L)
                  (allowedConnectionSet levels M)
                  (connectionImage (qNonlinear s)
                    (allowedConnectionSet levels M))))

end
end MathlibPlus.Open.ResearchFormalization.A4MorrisProfileShadow
