import Mathlib

/-!
# Compressed even translations

The exact three-branch pointwise operator from admitted claim 112 (`C-0007`).
Functions are represented on `ℝ`; in the source application they are the zero-extended
representatives of real functions on `(0, 1)`.
-/

namespace MathlibPlus.Analysis.CompressedEvenTranslation

/-- The compressed even translation at displacement `a`.  Below the fold it is the
sum of the reflected and untranslated surviving branches; between the fold and
support loss it is the partial reflection; at and beyond support loss it is zero. -/
noncomputable def compressedEvenTranslation (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if a < 1 then
    f |x - a| + (Set.Icc 0 (1 - a)).indicator (fun y => f (y + a)) x
  else if a < 2 then
    (Set.Icc (a - 1) 1).indicator (fun y => f (a - y)) x
  else
    0

/-- The full folded branch, valid exactly when `a < 1`. -/
theorem compressedEvenTranslation_of_lt_one (a : ℝ) (f : ℝ → ℝ) (x : ℝ)
    (ha : a < 1) :
    compressedEvenTranslation a f x =
      f |x - a| + (Set.Icc 0 (1 - a)).indicator (fun y => f (y + a)) x := by
  simp [compressedEvenTranslation, ha]

/-- On `1 ≤ a < 2`, compressed even translation is precisely the stated partial
reflection on `[a - 1, 1]`. -/
theorem compressedEvenTranslation_of_one_le_of_lt_two (a : ℝ) (f : ℝ → ℝ) (x : ℝ)
    (ha1 : 1 ≤ a) (ha2 : a < 2) :
    compressedEvenTranslation a f x =
      (Set.Icc (a - 1) 1).indicator (fun y => f (a - y)) x := by
  simp [compressedEvenTranslation, not_lt.mpr ha1, ha2]

/-- At and beyond displacement `2`, the compressed translation vanishes. -/
theorem compressedEvenTranslation_of_two_le (a : ℝ) (f : ℝ → ℝ) (x : ℝ)
    (ha : 2 ≤ a) :
    compressedEvenTranslation a f x = 0 := by
  have h1 : ¬a < 1 := by linarith
  have h2 : ¬a < 2 := by linarith
  simp [compressedEvenTranslation, h1, h2]

end MathlibPlus.Analysis.CompressedEvenTranslation
