import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim7558

/-- The generalized Hankel minor for two strictly increasing profiles. -/
noncomputable def generalizedHankelMinor {R ι : Type*} [CommRing R]
    {n : ℕ} (a : ℕ → ι → R) (r : ι) (I J : Fin n → ℕ)
    (_hI : StrictMono I) (_hJ : StrictMono J) : R :=
  Matrix.det (fun s t => a (I s + J t) r)

/-- The initial profile `0, ..., n - 1`. -/
def initialProfile (n : ℕ) : Fin n → ℕ := fun i => i.val

/-- The principal initial-profile generalized Hankel determinant. -/
noncomputable def principalInitialProfileDeterminant {R ι : Type*} [CommRing R]
    {n : ℕ} (a : ℕ → ι → R) (r : ι) : R :=
  generalizedHankelMinor a r (initialProfile n) (initialProfile n)
    (by intro i j hij; exact hij) (by intro i j hij; exact hij)

end MathlibPlus.LinearAlgebra.Claim7558
