import MathlibPlus.Open.ResearchFormalization.R1003Claim28185

namespace MathlibPlus.Open.ResearchFormalization.R1003.Claim28184

abbrev Omega := MathlibPlus.Open.ResearchFormalization.R1003.Claim28185.Omega

/-- The directed point orbit of a point under the actual root stabilizer of the
lifted pair. -/
def directedPointOrbit (t : MathlibPlus.Open.ResearchFormalization.R1003.Claim28185.HCoordinate → ZMod 7)
    (x : Omega) : Set Omega :=
  {y | ∃ p : Equiv.Perm Omega,
    p ∈ MathlibPlus.Open.ResearchFormalization.R1003.Claim28185.pointStabilizer t ∧
      p x = y}

/-- The orbit family is formed on the non-root points, so the fixed root is not
counted in the directed census. -/
def nonrootDirectedOrbits
    (t : MathlibPlus.Open.ResearchFormalization.R1003.Claim28185.HCoordinate → ZMod 7) :
    Set (Set Omega) :=
  {O | ∃ x : Omega, x ≠ MathlibPlus.Open.ResearchFormalization.R1003.Claim28185.root ∧
    O = directedPointOrbit t x}

/-- Claim 28184: the actual point-stabilizer action has the exact directed
orbit-size multiset `1^6, 7^19, 14^10` on the 279 non-root points. -/
def pointStabilizerOrbitSizeCensus : Prop :=
  ∀ t : MathlibPlus.Open.ResearchFormalization.R1003.Claim28185.HCoordinate → ZMod 7,
    MathlibPlus.Open.ResearchFormalization.R1003.Claim28185.nonzeroNormalizedOneSupport t →
      Set.ncard ({x : Omega |
        x ≠ MathlibPlus.Open.ResearchFormalization.R1003.Claim28185.root} : Set Omega) = 279 ∧
        (∀ O : Set Omega, O ∈ nonrootDirectedOrbits t →
          O ⊆ {x : Omega |
            x ≠ MathlibPlus.Open.ResearchFormalization.R1003.Claim28185.root}) ∧
        (∀ O : Set Omega, O ∈ nonrootDirectedOrbits t →
          MathlibPlus.Open.ResearchFormalization.R1003.Claim28185.root ∉ O) ∧
        (∀ O₁ O₂ : Set Omega,
          O₁ ∈ nonrootDirectedOrbits t → O₂ ∈ nonrootDirectedOrbits t →
            O₁ ≠ O₂ → Disjoint O₁ O₂) ∧
        ⋃₀ nonrootDirectedOrbits t =
          {x : Omega | x ≠ MathlibPlus.Open.ResearchFormalization.R1003.Claim28185.root} ∧
        (∀ O : Set Omega, O ∈ nonrootDirectedOrbits t →
          O.ncard = 1 ∨ O.ncard = 7 ∨ O.ncard = 14) ∧
        Set.ncard {O : Set Omega |
          O ∈ nonrootDirectedOrbits t ∧ O.ncard = 1} = 6 ∧
        Set.ncard {O : Set Omega |
          O ∈ nonrootDirectedOrbits t ∧ O.ncard = 7} = 19 ∧
        Set.ncard {O : Set Omega |
          O ∈ nonrootDirectedOrbits t ∧ O.ncard = 14} = 10

end MathlibPlus.Open.ResearchFormalization.R1003.Claim28184
