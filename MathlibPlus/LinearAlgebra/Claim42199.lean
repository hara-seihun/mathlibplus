import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim42199

/-- A nonzero square minor supplies a lower rank certificate, while a span
certificate for all columns supplies the matching upper bound. -/
theorem rank_eq_of_minor_and_column_span_claim42199
    {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (I : Fin r → Fin m) (J : Fin r → Fin n)
    (hminor : (A.submatrix I J).det ≠ 0)
    (hspan : ∀ j : Fin n,
      A.col j ∈ Submodule.span ℚ (Set.range (fun k : Fin r => A.col (J k)))) :
    A.rank = r := by
  have hsub : (A.submatrix I J).rank ≤ A.rank :=
    Matrix.rank_submatrix_le A I J
  rw [Matrix.rank_of_det_ne_zero hminor] at hsub
  have hspan_le :
      Submodule.span ℚ (Set.range A.col) ≤
        Submodule.span ℚ (Set.range (fun k : Fin r => A.col (J k))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hspan j
  have hupper : A.rank ≤ r := by
    rw [Matrix.rank_eq_finrank_span_cols]
    calc
      Module.finrank ℚ (Submodule.span ℚ (Set.range A.col)) ≤
          Module.finrank ℚ
            (Submodule.span ℚ (Set.range (fun k : Fin r => A.col (J k)))) :=
        Submodule.finrank_mono hspan_le
      _ ≤ Fintype.card (Fin r) := by
        simpa [Set.finrank] using
          (finrank_range_le_card (R := ℚ)
            (fun k : Fin r => A.col (J k)))
      _ = r := Fintype.card_fin r
  apply Nat.le_antisymm hupper
  simpa using hsub

/-- A nonzero determinant after reduction modulo a prime is already nonzero
as an integer determinant and remains nonzero over the rationals. -/
theorem rationalMinor_ne_zero_of_primeResidue_claim42199
    {m n r p : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (I : Fin r → Fin m) (J : Fin r → Fin n)
    (hp : Nat.Prime p)
    (hmod : ((A.submatrix I J).map (Int.castRingHom (ZMod p))).det ≠ 0) :
    ((A.submatrix I J).map (Int.castRingHom ℚ)).det ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hdetZ : (A.submatrix I J).det ≠ 0 := by
    intro hzero
    apply hmod
    change ((Int.castRingHom (ZMod p)).mapMatrix (A.submatrix I J)).det = 0
    rw [← RingHom.map_det]
    simp [hzero]
  have hcast : (Int.castRingHom ℚ) ((A.submatrix I J).det) ≠ 0 := by
    exact (Int.cast_ne_zero.mpr hdetZ)
  rw [RingHom.map_det] at hcast
  simpa [Matrix.map] using hcast

end MathlibPlus.LinearAlgebra.Claim42199
