import MathlibPlus.Open.Research.R1330Claim41037

namespace MathlibPlus.Open.ResearchFormalization.R1330Claim41035

noncomputable section

open MathlibPlus.Open.Research.R1330Formalization_41037

abbrev V (p : ℕ) := MathlibPlus.Open.Research.R1330Formalization_41037.V p
abbrev Ω (p : ℕ) := MathlibPlus.Open.Research.R1330Formalization_41037.Ω p
abbrev AltV (p : ℕ) [NeZero p] := alternatingGroup (V p)
abbrev PairV (p : ℕ) [NeZero p] := AltV p × AltV p

/-- The two-coordinate restriction set obtained from the actual block kernel.
The coordinates are the common restrictions on one rotation and one reflection
block, and are required to lie in the corresponding alternating factors. -/
def restrictedKernelPairs (p : ℕ) [NeZero p]
    (K : Subgroup (Equiv.Perm (Ω p))) : Set (PairV p) :=
  {z | ∃ k : K,
    actsAsPair p (z.1 : Equiv.Perm (V p))
      (z.2 : Equiv.Perm (V p)) k.1}

/-- Every element of the concrete kernel has common rotation and reflection
restrictions in the two alternating factors. -/
def kernelHasAlternatingRestrictions (p : ℕ) [NeZero p]
    (K : Subgroup (Equiv.Perm (Ω p))) : Prop :=
  ∀ k : K, ∃ a b : AltV p,
    actsAsPair p (a : Equiv.Perm (V p))
      (b : Equiv.Perm (V p)) k.1

/-- Subdirectness of a subgroup of the two alternating coordinates. -/
def isSubdirectAltPair (p : ℕ) [NeZero p]
    (L : Subgroup (PairV p)) : Prop :=
  (∀ a : AltV p, ∃ b : AltV p, (a, b) ∈ L) ∧
    (∀ b : AltV p, ∃ a : AltV p, (a, b) ∈ L)

def automorphismGraph (p : ℕ) [NeZero p] (φ : AltV p ≃* AltV p) : Set (PairV p) :=
  {z | φ z.1 = z.2}

/-- Claim 41035: the actual six-block kernel, restricted to one rotation and
one reflection coordinate, is a subdirect subgroup of the two alternating
factors.  Goursat's alternatives are the full direct product or an
automorphism graph. -/
def claim41035 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), Odd p →
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∃ F : Equiv.Perm (Ω p),
      (∀ z : Ω p, F z = blockShear p z) ∧
        let R : Subgroup (Equiv.Perm (Ω p)) := regularCopy p
        let T : Subgroup (Equiv.Perm (Ω p)) := conjugateSubgroup F R
        let M : Subgroup (Equiv.Perm (Ω p)) :=
          Subgroup.closure ((R : Set (Equiv.Perm (Ω p))) ∪
            (T : Set (Equiv.Perm (Ω p))))
        ∃ K : Subgroup (Equiv.Perm (Ω p)),
          (∀ k : Equiv.Perm (Ω p),
            k ∈ K ↔ k ∈ M ∧ fixesBlocks k) ∧
            kernelHasAlternatingRestrictions p K ∧
              ∃ L : Subgroup (PairV p),
                (∀ z : PairV p,
                  z ∈ L ↔ z ∈ restrictedKernelPairs p K) ∧
                  isSubdirectAltPair p L ∧
                    ((L : Set (PairV p)) = Set.univ ∨
                      ∃ φ : AltV p ≃* AltV p,
                        (L : Set (PairV p)) = automorphismGraph p φ)

end

end MathlibPlus.Open.ResearchFormalization.R1330Claim41035
