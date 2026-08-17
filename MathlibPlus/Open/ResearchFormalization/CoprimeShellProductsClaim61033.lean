import MathlibPlus.Open.CayleyCI.FormalizationBatch

namespace MathlibPlus.Open.CoprimeShellProductsClaim61033

/-- The cyclic factor and the standard dihedral/dicyclic realizations of the
 two inversion semidirect products in the claim. -/
abbrev cyclicFactor (n : ℕ) := Multiplicative (ZMod n)
abbrev inversionByC2 (n : ℕ) := DihedralGroup n
abbrev inversionByC4 (n : ℕ) := QuaternionGroup n
abbrev quaternionEight := QuaternionGroup 2

/-- Claim 61033: the three stated cyclic square-free ordinary-undirected CI
chambers, with no extra totient or `3 ∤ k` restriction. -/
def cyclicSquarefreeCoprimeShellProducts_claim61033 : Prop :=
  ∀ (h k : ℕ) (hh : 0 < h) (hk : 0 < k),
    Odd h → Odd k → Squarefree h → Squarefree k → Nat.Coprime h k →
      letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
      letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
      MathlibPlus.Open.CayleyCI.OrdinaryUndirectedCIGroup
          (cyclicFactor h × inversionByC2 k) ∧
        MathlibPlus.Open.CayleyCI.OrdinaryUndirectedCIGroup
          (cyclicFactor h × inversionByC4 k) ∧
        (¬ 3 ∣ h →
          MathlibPlus.Open.CayleyCI.OrdinaryUndirectedCIGroup
            (cyclicFactor h × quaternionEight))

end MathlibPlus.Open.CoprimeShellProductsClaim61033
