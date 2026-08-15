import Mathlib
import MathlibPlus.LinearAlgebra.Claim7558

namespace MathlibPlus.Open.Analysis.K0019EscapingProfiles

open MathlibPlus.LinearAlgebra.Claim7558

/--
Escaping profiles diverge: every fixed outer generalized Hankel minor is
 eventually positive along the radius, and negative witness profiles for a
 fixed negative inner minor escape every fixed finite profile cutoff.
-/
def escapingProfilesDiverge_claim7569
    (a : ℕ → ℝ → ℝ) : Prop :=
  (∀ n : ℕ, ∀ (I J : Fin n → ℕ) (hI : StrictMono I) (hJ : StrictMono J),
      ∀ᶠ R : ℝ in Filter.atTop,
        0 < generalizedHankelMinor a R I J hI hJ) ∧
    (∀ n : ℕ, ∀ (I J : Fin n → ℕ) (hI : StrictMono I) (hJ : StrictMono J)
        (r : ℝ),
      generalizedHankelMinor a r I J hI hJ < 0 →
      ∀ (R : ℕ → ℝ), Filter.Tendsto R Filter.atTop Filter.atTop →
      ∀ (P Q : ℕ → Fin n → ℕ),
        (hP : ∀ m : ℕ, StrictMono (P m)) →
        (hQ : ∀ m : ℕ, StrictMono (Q m)) →
        (∀ m : ℕ,
          generalizedHankelMinor a (R m) (P m) (Q m) (hP m) (hQ m) < 0) →
        Filter.Tendsto
            (fun m : ℕ => max (Finset.univ.sup (P m)) (Finset.univ.sup (Q m)))
            Filter.atTop Filter.atTop ∧
          ∀ K : ℕ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
            K < max (Finset.univ.sup (P m)) (Finset.univ.sup (Q m)))

end MathlibPlus.Open.Analysis.K0019EscapingProfiles
