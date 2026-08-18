import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2052BooleanComplement

noncomputable section
open Classical

/-- The nonempty Boolean downset of an indexed finite family. -/
def booleanDownset {α : Type*} {m : ℕ}
    (A : Fin m → Finset α) : Finset (Finset α) :=
  ((Finset.univ : Finset (Fin m)).biUnion (fun i => (A i).powerset)).erase ∅

/-- The full coordinate set, with `none` representing the special coordinate
`★` and `some T` representing a downset coordinate. -/
def transformedMember {α : Type*} {m : ℕ}
    (A : Fin m → Finset α) (i : Fin m) : Finset (Option (Finset α)) :=
  insert (none : Option (Finset α))
    (((booleanDownset A).filter (fun T => ¬ T ⊆ A i)).image
      (fun T => some T))

/-- The source support `S_T = {i : [m] : T ⊆ A_i}`. -/
def sourceSupport {α : Type*} {m : ℕ}
    (A : Fin m → Finset α) (T : Finset α) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter (fun i => T ⊆ A i)

/-- The support of one transformed coordinate. -/
def transformedSupport {α : Type*} {m : ℕ}
    (A : Fin m → Finset α) (c : Option (Finset α)) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter (fun i => c ∈ transformedMember A i)

/-- The finite family of all transformed-coordinate supports. -/
def transformedSupportFamily {α : Type*} {m : ℕ}
    (A : Fin m → Finset α) : Finset (Finset (Fin m)) :=
  (insert (none : Option (Finset α))
    (((booleanDownset A).image (fun T => some T)))).image
      (transformedSupport A)

/-- Claim 35862: full Boolean complementation of a nonempty distinct
`r`-uniform family gives a distinct uniform family of rank
`N - 2^r + 2`, and its coordinate supports are union-closed, with `★`
supplying the full support when a union is unrealized. -/
def claim35862 : Prop :=
  ∀ {α : Type*} (m r : ℕ) (A : Fin m → Finset α),
    0 < m →
      Function.Injective A →
        (∀ i : Fin m, (A i).card = r) →
          let D := booleanDownset A
          let N := D.card
          let transformedRank := N + 2 - 2 ^ r
          (Function.Injective (transformedMember A) ∧
            (∀ i : Fin m, (transformedMember A i).card = transformedRank) ∧
              (∀ T : Finset α, T ∈ D →
                transformedSupport A (some T) =
                  (Finset.univ : Finset (Fin m)) \
                    sourceSupport A T) ∧
                transformedSupport A none =
                  (Finset.univ : Finset (Fin m)) ∧
                  (∀ T U : Finset α, T ∈ D → U ∈ D →
                    sourceSupport A (T ∪ U) =
                      sourceSupport A T ∩ sourceSupport A U) ∧
                    (∀ T U : Finset α, T ∈ D → U ∈ D →
                      (T ∪ U ∈ D →
                        transformedSupport A (some (T ∪ U)) =
                          transformedSupport A (some T) ∪
                            transformedSupport A (some U)) ∧
                        (T ∪ U ∉ D →
                          transformedSupport A none =
                            transformedSupport A (some T) ∪
                              transformedSupport A (some U))) ∧
                      (∀ S ∈ transformedSupportFamily A,
                        ∀ T ∈ transformedSupportFamily A,
                          S ∪ T ∈ transformedSupportFamily A))

end

end MathlibPlus.Open.ResearchFormalization.R2052BooleanComplement
