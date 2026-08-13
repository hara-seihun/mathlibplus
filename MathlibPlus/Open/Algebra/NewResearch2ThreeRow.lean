import Mathlib
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
open scoped BigOperators
open MvPolynomial
namespace MathlibPlus.Open.Algebra.NewResearch2
noncomputable section
/-- Claim 1815: three-row flagged-minor and cup vocabulary. -/
def threeRowFlaggedMinorVocabulary_claim1815 : Prop :=
  ∀ (R : Type*) [CommRing R] (a : R) (d : ℕ) (part : Fin d → ℕ),
    Antitone part →
      let K : Fin d → ℕ := fun i => i.1 + part ⟨d - 1 - i.1, by omega⟩
      let A : R → ℕ → ℕ → R := fun x r j =>
        (r + 1 : R) * if r + 1 ≤ 2 * j then
          eval₂ (RingHom.id R) (fun q : Fin (r + 2) => x + (q.1 : R))
            (hsymm (Fin (r + 2)) R (2 * j - r - 1)) else 0
      let H : R := Matrix.det (fun (i : Fin d) (j : Fin d) => A a (K i) (j.1 + 1))
      H = H
end
end MathlibPlus.Open.Algebra.NewResearch2
