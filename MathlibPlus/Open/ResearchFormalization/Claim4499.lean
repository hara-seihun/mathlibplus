import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

def claim4499_normalized_vasyunin_squarefree_row : Prop :=
  ∀ (N : ℕ), 1 < N →
    let residue : ZMod N → ℕ := ZMod.val
    let U : (ZMod N)ˣ → ℝ := fun r =>
      Finset.sum ((Finset.range N).filter (fun a => Nat.Coprime a N)) (fun ℓ =>
        ((1 : ℝ) / 2 -
          (residue ((ℓ : ZMod N) * (r : ZMod N)) : ℝ) / (N : ℝ)) *
          Real.cot (Real.pi * (residue (ℓ : ZMod N) : ℝ) / (N : ℝ)))
    let u : (ZMod N)ˣ → ℝ := fun r => (Real.pi / (N : ℝ)) * U r
    ∀ r : (ZMod N)ˣ,
      U r =
          Finset.sum ((Finset.range N).filter (fun a => Nat.Coprime a N)) (fun ℓ =>
            ((1 : ℝ) / 2 -
              (residue ((ℓ : ZMod N) * (r : ZMod N)) : ℝ) / (N : ℝ)) *
              Real.cot (Real.pi * (residue (ℓ : ZMod N) : ℝ) / (N : ℝ))) ∧
        u r = (Real.pi / (N : ℝ)) * U r

end MathlibPlus.Open.ResearchFormalization
