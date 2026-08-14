import Mathlib

namespace MathlibPlus.Open.Combinatorics.ResearchFormalizationC0207

noncomputable section

/-- A standard polynomial model of the universal ring of symmetric functions. -/
abbrev universalSymmetricFunctions3029 := MvPolynomial ℕ ℤ

/-- The complete homogeneous generators, with `h 0 = 1`. -/
def completeHomogeneous3029 (n : ℕ) : universalSymmetricFunctions3029 :=
  match n with
  | 0 => 1
  | n + 1 => MvPolynomial.X n

def completeHomogeneousInt3029 (n : ℤ) : universalSymmetricFunctions3029 :=
  if n < 0 then 0 else completeHomogeneous3029 n.toNat

/-- A partition is represented by its list of parts after zero parts are removed. -/
def deleteZeroParts3029 (parts : List ℤ) : List ℤ :=
  parts.filter (fun n => n ≠ 0)

/-- Jacobi--Trudi's Schur element in the universal symmetric-function ring. -/
def schur3029 (parts : List ℤ) : universalSymmetricFunctions3029 :=
  Matrix.det (fun i j =>
    completeHomogeneousInt3029
      (parts.get i - (i.val : ℤ) + (j.val : ℤ)))

def theta3029 (C r p : ℤ) : List ℤ :=
  deleteZeroParts3029
    (List.replicate p.toNat (C + 1) ++ List.replicate (r - p).toNat C)

def lambdaParts3029 (C r p : ℤ) : List ℤ :=
  deleteZeroParts3029
    (List.replicate p.toNat (C + 1) ++ List.replicate (r - p).toNat (C - 1))

def rho3029 (C r : ℤ) : List ℤ :=
  deleteZeroParts3029 (List.replicate r.toNat (C + 1))

def mu3029 (C r p : ℤ) : List ℤ :=
  deleteZeroParts3029
    (List.replicate p.toNat (C + 2) ++ List.replicate (r - p - 1).toNat C)

def sigma3029 (C r : ℤ) : List ℤ :=
  deleteZeroParts3029 (List.replicate (r + 1).toNat C)

/-- Four-term near-rectangle Schur--Plücker identity. -/
def claim3029 : Prop :=
  ∀ (C r p : ℤ),
    1 ≤ C → 2 ≤ r → 1 ≤ p → p < r →
      schur3029 (theta3029 C r p) ^ 2 -
          schur3029 (theta3029 C r (p - 1)) *
            schur3029 (theta3029 C r (p + 1)) =
        schur3029 (lambdaParts3029 C r p) * schur3029 (rho3029 C r) +
          schur3029 (mu3029 C r p) * schur3029 (sigma3029 C r)

end
end MathlibPlus.Open.Combinatorics.ResearchFormalizationC0207
