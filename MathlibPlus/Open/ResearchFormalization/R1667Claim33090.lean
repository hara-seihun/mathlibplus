import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1667Claim33090

noncomputable section

abbrev Nine := ZMod 9
abbrev NinePermutation := Equiv.Perm Nine
abbrev Pair := Nine × Nine

private def regularGenerator : NinePermutation := Equiv.addRight 1

private def regularCyclicNine : Subgroup NinePermutation :=
  Subgroup.closure ({regularGenerator} : Set NinePermutation)

private def conjugateSubgroup (g : NinePermutation)
    (H : Subgroup NinePermutation) : Subgroup NinePermutation :=
  Subgroup.map (MulAut.conj g).toMonoidHom H

private def normalizer : Set NinePermutation :=
  {g | conjugateSubgroup g regularCyclicNine = regularCyclicNine}

private def doubleCoset (g : NinePermutation) : Set NinePermutation :=
  {h | ∃ a b : NinePermutation, a ∈ normalizer ∧ b ∈ normalizer ∧
    h = a * g * b}

private def doubleCosets : Finset (Set NinePermutation) :=
  Finset.univ.image doubleCoset

private def targetCyclicNine (g : NinePermutation) : Subgroup NinePermutation :=
  conjugateSubgroup g regularCyclicNine

private def generatedPairGroup (g : NinePermutation) : Subgroup NinePermutation :=
  Subgroup.closure
    ((regularCyclicNine : Set NinePermutation) ∪
      (targetCyclicNine g : Set NinePermutation))

private def pairOrbit (G : Subgroup NinePermutation) (z : Pair) : Set Pair :=
  {w | ∃ h : NinePermutation, h ∈ G ∧ w = (h z.1, h z.2)}

private def symmetricOrbital (G : Subgroup NinePermutation) (z : Pair) : Set Pair :=
  pairOrbit G z ∪ {w | (w.2, w.1) ∈ pairOrbit G z}

private def finestSymmetricClosure (g : NinePermutation) : Finset (Set Pair) :=
  Finset.univ.image (symmetricOrbital (generatedPairGroup g))

private def preserves (h : NinePermutation) (S : Set Pair) : Prop :=
  ∀ z : Pair, z ∈ S ↔ (h z.1, h z.2) ∈ S

private def symmetricClosureAutomorphisms (g : NinePermutation) : Set NinePermutation :=
  {h | ∀ S ∈ finestSymmetricClosure g, preserves h S}

private def closureOrder (g : NinePermutation) : ℕ :=
  Set.ncard (symmetricClosureAutomorphisms g)

private def conjugacyFailureFree (g : NinePermutation) : Prop :=
  ∃ h : NinePermutation,
    h ∈ symmetricClosureAutomorphisms g ∧
      conjugateSubgroup h regularCyclicNine = targetCyclicNine g

/-- Claim 33090, with the fixed translation copy of `C₉`, its actual
normalizer/double-coset carrier, and the finest symmetric orbital closure
constructed from each generated regular pair. -/
def normalizerDoubleCosetReplayArithmeticClaim33090 : Prop :=
  Set.ncard normalizer = 54 ∧
    doubleCosets.card = 139 ∧
      ∃ reps : Fin 139 → NinePermutation,
        (∀ D ∈ doubleCosets, ∃ i : Fin 139, doubleCoset (reps i) = D) ∧
          (∀ i j : Fin 139,
            doubleCoset (reps i) = doubleCoset (reps j) → i = j) ∧
            (Finset.univ.filter
                (fun i : Fin 139 => closureOrder (reps i) = 18)).card = 1 ∧
              (Finset.univ.filter
                  (fun i : Fin 139 => closureOrder (reps i) = 1296)).card = 4 ∧
                (Finset.univ.filter
                    (fun i : Fin 139 => closureOrder (reps i) = 362880)).card = 134 ∧
                  (∀ i : Fin 139,
                    closureOrder (reps i) = 18 ∨
                      closureOrder (reps i) = 1296 ∨
                        closureOrder (reps i) = 362880) ∧
                    1 * 18 + 4 * 1296 + 134 * 362880 = 48631122 ∧
                      (∀ i : Fin 139, conjugacyFailureFree (reps i))

end

end MathlibPlus.Open.ResearchFormalization.R1667Claim33090
