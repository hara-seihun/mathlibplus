import MathlibPlus.Open.GraphTheory.FiniteCIBatch

namespace MathlibPlus.Open.ResearchFormalization.R1182Claim41728

/-- The fixed `p = 11` specialization: `QuaternionGroup 33` is the named
`Q₁₃₂ = Dic(33)` carrier and has the ordinary undirected CI property. -/
def claim41728 : Prop :=
  let G := QuaternionGroup 33
  Nat.card G = 132 ∧
    MathlibPlus.Open.GraphTheory.FiniteCIBatch.undirectedCIGroup G

end MathlibPlus.Open.ResearchFormalization.R1182Claim41728
