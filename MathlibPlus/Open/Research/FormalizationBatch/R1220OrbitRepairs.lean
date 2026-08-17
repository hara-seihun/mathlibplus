import MathlibPlus.Open.Research.FormalizationBatch.R1220

open scoped BigOperators

namespace MathlibPlus.Open.Research.R1220.Repairs

open MathlibPlus.Open.Research.R1220

private noncomputable def fixedSubsetCount (k : ℕ)
    (φ : G90 ≃* G90) : ℕ :=
  letI := Classical.decEq (valencySlice k)
  (Finset.univ.filter (fun S : valencySlice k => sliceAction k φ S = S)).card

private noncomputable def burnsideNumerator (k : ℕ) : ℕ :=
  ∑ φ : G90 ≃* G90, fixedSubsetCount k φ

private noncomputable def burnsideOrbitCount (k : ℕ) : ℕ :=
  burnsideNumerator k / Fintype.card (G90 ≃* G90)

/-- Claim 30271: Burnside's weighted fixed-subset sum is taken over all
960 automorphisms and all raw valency-k subsets, then agrees with the orbit
quotient without any prior subset-orbit deduplication. -/
def weightedCycleIndexBurnside_claim30271 : Prop :=
  ∀ k : ℕ, k ≤ 11 →
    burnsideNumerator k =
        Fintype.card (G90 ≃* G90) *
          Fintype.card
            (Quotient (MulAction.orbitRel (G90 ≃* G90) (valencySlice k))) ∧
      burnsideOrbitCount k =
        Fintype.card
          (Quotient (MulAction.orbitRel (G90 ≃* G90) (valencySlice k)))

private noncomputable def containsAtom (S : ConnectionSet) (A : InverseAtom) : Prop :=
  ∀ x ∈ A.1, (x : G90) ∈ S.1

private noncomputable def singletonReflectionStratum (S : ConnectionSet) :
    Finset InverseAtom :=
  letI := Classical.decEq InverseAtom
  letI := Classical.propDecidable
  Finset.univ.filter (fun A => singletonInverseAtom A ∧ containsAtom S A)

private noncomputable def singletonAtomAction
    (φ : G90 ≃* G90) (R : Finset InverseAtom) : Finset InverseAtom :=
  letI := Classical.decEq InverseAtom
  R.image (mapInverseAtom φ)

private noncomputable def singletonSubsetStabilizer
    (R : Finset InverseAtom) : Finset (G90 ≃* G90) :=
  letI := Classical.decEq (G90 ≃* G90)
  letI := Classical.propDecidable
  (Finset.univ.filter (fun φ => singletonAtomAction φ R = R))

private noncomputable def singletonSubsetOrbitSize
    (R : Finset InverseAtom) : ℕ :=
  letI := Classical.decEq (Finset InverseAtom)
  (Finset.univ.image (fun φ : G90 ≃* G90 => singletonAtomAction φ R)).card

private def expectedSingletonOrbitSize (k : Fin 4) : ℕ :=
  match k.1 with
  | 0 => 5
  | 1 => 10
  | 2 => 10
  | _ => 5

private def singletonReflectionSubset (R : Finset InverseAtom) : Prop :=
  ∀ A ∈ R, singletonInverseAtom A

private def fullActionEquivalent (S T : ConnectionSet) : Prop :=
  ∃ φ : G90 ≃* G90, automorphismImage φ S = T

private def stabilizerSliceExact (R : Finset InverseAtom) : Prop :=
  ∀ S T : ConnectionSet,
    singletonReflectionStratum S = R →
      singletonReflectionStratum T = R →
        (fullActionEquivalent S T ↔
          ∃ φ ∈ singletonSubsetStabilizer R,
            automorphismImage φ S = T)

private def realizedSingletonStratum (R : Finset InverseAtom)
    (k : ℕ) : Prop :=
  ∃ S : ConnectionSet,
    valency S = k ∧ singletonReflectionStratum S = R

/-- Claim 30279: singleton-reflection subsets are acted on without replacing
connection sets by the singleton stratum; paired inverse atoms remain free in
S, and stabilizer slices recover the full action orbit relation. -/
def singletonReflectionOrbitSlices_claim30279 : Prop :=
  (∀ k : Fin 4, ∀ R : Finset InverseAtom,
    singletonReflectionSubset R → R.card = k.1 + 1 →
      singletonSubsetOrbitSize R = expectedSingletonOrbitSize k) ∧
    (∃ R2 R3 R4 : Finset InverseAtom,
      singletonReflectionSubset R2 ∧ singletonReflectionSubset R3 ∧
        singletonReflectionSubset R4 ∧
        R2.card = 2 ∧ R3.card = 3 ∧ R4.card = 4 ∧
        singletonSubsetOrbitSize R2 = 10 ∧
        singletonSubsetOrbitSize R3 = 10 ∧
        singletonSubsetOrbitSize R4 = 5 ∧
        (singletonSubsetStabilizer R2).card = 96 ∧
        (singletonSubsetStabilizer R3).card = 96 ∧
        (singletonSubsetStabilizer R4).card = 192 ∧
        stabilizerSliceExact R2 ∧ stabilizerSliceExact R3 ∧
        stabilizerSliceExact R4 ∧
        (realizedSingletonStratum R2 12 ∨
          realizedSingletonStratum R2 13) ∧
        (realizedSingletonStratum R3 12 ∨
          realizedSingletonStratum R3 13) ∧
        (realizedSingletonStratum R4 12 ∨
          realizedSingletonStratum R4 13))

end MathlibPlus.Open.Research.R1220.Repairs
