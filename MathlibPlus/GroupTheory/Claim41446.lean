-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

namespace MathlibPlus.GroupTheory

abbrev Claim41446Point := Fin 6 → ZMod 3
abbrev Claim41446Profile := Fin 5 → ZMod 3

def claim41446Normalizer (prof : Claim41446Profile)
    (p : Claim41446Point) : Claim41446Point :=
  ![p 0 + prof 0 * p 1 + prof 1 * p 2 + prof 2 * p 3 + prof 3 * p 4 + prof 4 * p 5,
    p 1, p 2, p 3 + 2 * p 1, p 4 + 2 * p 2, p 5]

def claim41446NormalizerInv (prof : Claim41446Profile)
    (p : Claim41446Point) : Claim41446Point :=
  ![p 0 - prof 0 * p 1 - prof 1 * p 2 - prof 2 * (p 3 - 2 * p 1) -
      prof 3 * (p 4 - 2 * p 2) - prof 4 * p 5,
    p 1, p 2, p 3 - 2 * p 1, p 4 - 2 * p 2, p 5]

def claim41446Translation (v : Claim41446Point)
    (p : Claim41446Point) : Claim41446Point := p + v

lemma claim41446Normalizer_left_inverse (prof : Claim41446Profile) :
    Function.LeftInverse (claim41446NormalizerInv prof)
      (claim41446Normalizer prof) := by
  intro p
  funext k
  fin_cases k <;> simp [claim41446Normalizer, claim41446NormalizerInv] <;> ring

lemma claim41446Normalizer_right_inverse (prof : Claim41446Profile) :
    Function.RightInverse (claim41446NormalizerInv prof)
      (claim41446Normalizer prof) := by
  intro p
  funext k
  fin_cases k <;> simp [claim41446Normalizer, claim41446NormalizerInv] <;> ring

/-- Every five-parameter map in the atlas is a permutation. -/
theorem affineNormalizer_bijective_claim41446 (prof : Claim41446Profile) :
    Function.Bijective (claim41446Normalizer prof) := by
  exact ⟨(claim41446Normalizer_left_inverse prof).injective,
    (claim41446Normalizer_right_inverse prof).surjective⟩

/-- Conjugating a regular translation by a displayed atlas map gives another
regular translation, so the whole translation group is normalized. -/
theorem affineNormalizer_normalizes_translation_claim41446
    (prof : Claim41446Profile) (v p : Claim41446Point) :
    claim41446Normalizer prof
        (claim41446Translation v (claim41446NormalizerInv prof p)) =
      claim41446Translation (claim41446Normalizer prof v) p := by
  funext k
  fin_cases k <;>
    simp [claim41446Translation, claim41446Normalizer,
      claim41446NormalizerInv] <;> ring

/-- The five independent ternary parameters give exactly `3^5 = 243` maps. -/
theorem affineNormalizer_count_claim41446 :
    Fintype.card Claim41446Profile = 243 := by
  native_decide

end MathlibPlus.GroupTheory
