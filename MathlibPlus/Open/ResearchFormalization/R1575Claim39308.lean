import MathlibPlus.Open.ResearchFormalization.R1575Claim39301

namespace MathlibPlus.Open.ResearchFormalization.R1575Claim39308

open MathlibPlus.Open.ResearchFormalization.R1575Claim39301

noncomputable section

/-- The zero voltage profile in the fixed rank-one nilpotent model. -/
def zeroTau39308 : H → W := fun _ => wZero

/-- A concrete nonzero normalized multiplier profile. -/
def witnessLambda39308 : H → F7 := fun h => h.1

/-- The zero-valued global scalar cocycle used in the pure-translation
criterion. -/
def zeroCocycle39308 : H → W := fun _ => wZero

/-- The exact defect space `D_h = span {d_h(k) : k ∈ H}`. -/
noncomputable def defectSpace39308 (tau : H → W) (h : H) : Submodule F7 W :=
  Submodule.span F7 (Set.range (defect tau h))

/-- A translate of a linear defect space in the additive fibre. -/
def defectCoset39308 (D : Submodule F7 W) (v : W) : Set W :=
  {x | x - v ∈ D}

/-- The `W`-valued scalar cocycle condition for the matching `chi` action. -/
def scalarCocycle39308 (z : H → W) : Prop :=
  z hOne = wZero ∧
    ∀ h k : H, z (hMul h k) = z h + chi h • z k

/-- Claim 39308: on the explicit period fibre of a nonzero multiplier with
zero voltage, the defect space is zero but the exact derivative group still
has shear orbits of sizes one and seven. Thus the pure-translation condition
cannot be reused as a coset description of these orbits. -/
def claim39308 : Prop :=
  let lam := witnessLambda39308
  let tau := zeroTau39308
  let z := zeroCocycle39308
  let h := hOne
  let Gamma := periodFiberSubgroup lam tau h
  let D := defectSpace39308 tau h
  normalizedProfile lam tau ∧
    (∃ k : H, lam k ≠ 0) ∧
    h ∈ leftPeriod lam ∧
    scalarCocycle39308 z ∧
    (∀ h' : H, tau h' - z h' ∈ defectSpace39308 tau h') ∧
    D = ⊥ ∧
    (∃ g : HeisenbergPoint,
      g ∈ Gamma ∧
        g ≠ heisOne ∧
          g.1 ≠ 0 ∧
            g.2.1 = 0 ∧
              g.2.2 = 0) ∧
    Set.ncard (heisOrbit Gamma wZero) = 1 ∧
    Set.ncard (heisOrbit Gamma (0, 1)) = 7 ∧
    ¬ (∀ w : W, ∃ v : W,
      heisOrbit Gamma w = defectCoset39308 D v)

end

end MathlibPlus.Open.ResearchFormalization.R1575Claim39308
