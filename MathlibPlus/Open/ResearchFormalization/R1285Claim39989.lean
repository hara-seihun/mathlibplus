import MathlibPlus.Open.ResearchFormalization.R1285.Claim39994

namespace MathlibPlus.Open.ResearchFormalization.R1285Claim39989

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1285
open MathlibPlus.Open.ResearchFormalization.R1182.Claim31941

abbrev HallCarrier (n : ℕ) := HallQ12Carrier n

/-- The exact three projected atom labels in the Q12 carrier. -/
def q12C4 : Set Q12 := {h | h.1 = 0}
def identityAtom : Set Q12 := {q12One}
def atomA : Set Q12 := q12C4 \ {q12One}
def atomB : Set Q12 := (Set.univ : Set Q12) \ q12C4

/-- The relative-derivative subgroup used for ordinary projected atoms. -/
def derivativeGroup (n : ℕ) (f : Equiv.Perm (HallCarrier n)) :
    Subgroup (Equiv.Perm (HallCarrier n)) :=
  Subgroup.closure (hallQ12DerivativeGenerators n f)

/-- Projection to the Q12 coordinate of the derivative orbit of `(0,h)`. -/
def projectedDerivativeOrbit (n : ℕ)
    (f : Equiv.Perm (HallCarrier n)) (h : Q12) : Set Q12 :=
  {k | ∃ d : derivativeGroup n f, ∃ u : ZMod n,
    (d : Equiv.Perm (HallCarrier n)) (0, h) = (u, k)}

/-- The complete family of ordinary projected relative-derivative atoms. -/
def projectedDerivativeAtoms (n : ℕ)
    (f : Equiv.Perm (HallCarrier n)) : Set (Set Q12) :=
  Set.range (projectedDerivativeOrbit n f)

/-- Claim 39989: on the verified Hall-Q12 carrier, the exceptional cubic
    switch has exactly the identity, C4-minus-identity, and outer projected
    derivative atoms, while normalized lifts and coboundaries fix the identity
    fibre, leaving only the two nonidentity atoms. -/
def claim39989 : Prop :=
  ∀ n : ℕ, Squarefree n → Nat.Coprime n 6 →
    ∀ (lam : Q12 → (ZMod n)ˣ) (tau : Q12 → ZMod n)
      (σ : Equiv.Perm Q12) (f : Equiv.Perm (HallCarrier n)),
      normalizedHallQ12AffineLift n lam tau σ f →
        projectedDerivativeAtoms n f =
            ({identityAtom, atomA, atomB} : Set (Set Q12)) ∧
          (∀ x : ZMod n,
            f (x, q12One) = (x, q12One)) ∧
            (∀ c : ZMod n,
              hallQ12Automorphism n (hallQ12Coboundary n c) →
                ∀ x : ZMod n,
                  hallQ12Coboundary n c (x, q12One) = (x, q12One)) ∧
              projectedDerivativeAtoms n f \ {identityAtom} =
                ({atomA, atomB} : Set (Set Q12))

end

end MathlibPlus.Open.ResearchFormalization.R1285Claim39989
