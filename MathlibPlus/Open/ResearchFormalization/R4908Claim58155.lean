import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R4908Claim58155

private def jump {n : ℕ} (q : Fin (n + 1) → ℚ) : Fin (n + 1) → ℚ :=
  Fin.cases
    (q 0 - q (Fin.last n))
    (fun i : Fin n => q i.succ - q i.castSucc)

private def pathMap {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module ℚ W]
    (x : Fin (n + 2) → W) :
    (Fin (n + 1) → ℚ) → W :=
  fun q => ∑ i : Fin (n + 1), q i • (x i.castSucc - x i.succ)

/-- Claim 58155: the cyclic coefficient-jump expansion has zero total
coefficient and exactly the constant line as its kernel. -/
def jumpExpansionAndKernel_claim58155 : Prop :=
  ∀ (n : ℕ) {W : Type*} [AddCommGroup W] [Module ℚ W]
    (x : Fin (n + 2) → W)
    (hclose : x (Fin.last (n + 1)) = x 0)
    (q : Fin (n + 1) → ℚ),
    (∑ i : Fin (n + 1), jump q i = 0) ∧
      pathMap x q =
        ∑ i : Fin (n + 1), jump q i • x i.castSucc ∧
      ((∀ i : Fin (n + 1), jump q i = 0) ↔
        ∃ c : ℚ, ∀ i : Fin (n + 1), q i = c)

end MathlibPlus.Open.ResearchFormalization.R4908Claim58155
