import MathlibPlus.Open.ResearchFormalizationBatchR1851

namespace MathlibPlus.Open.ResearchFormalization.R1851Claim32914

open MathlibPlus.Open.ResearchFormalizationBatchR1851

abbrev A := A11Squared

/-- The exact edge-colour relation of the Cayley structure labelled by c. -/
def colorGraphIso11 (c d : A → Fin 5) (f : A ≃ A) : Prop :=
  ∀ x y : A, x ≠ y → c (y - x) = d (f y - f x)

/-- The exact colour-preserving group-isomorphism relation, with the value at
zero omitted because Cayley edges have distinct endpoints. -/
def colorGroupIso11 (c d : A → Fin 5) : Prop :=
  ∃ α : A ≃+ A,
    ∀ v : A, v ≠ 0 → c v = d (α v)

def exactColorCI11 (c d : A → Fin 5) : Prop :=
  (∃ f : A ≃ A, colorGraphIso11 c d f) ↔ colorGroupIso11 c d

/-- Surjectivity on projective lines, with no restriction on the value at the
identity. -/
def lineSurjective11 (c : A → Fin 5) : Prop :=
  ∀ k : Fin 5, ∃ v : A, v ≠ 0 ∧ c v = k

/-- The alternate convention in which the identity supplies colour zero and
only colours one through four are required on nonzero projective lines. -/
def totalMapLineSurjective11 (c : A → Fin 5) : Prop :=
  c 0 = 0 ∧
    ∀ k : Fin 4, ∃ v : A, v ≠ 0 ∧ c v = Fin.succ k

/-- The actual colour-complement involution on the five labels. -/
def colorComplement11 (c : A → Fin 5) : A → Fin 5 :=
  fun v => Fin.rev (c v)

/-- Claim 32914: all line-constant symmetric profiles, without a
surjectivity restriction, satisfy exact colour-preserving CI; the two
surjectivity conventions and the complement cases are included in the same
carrier. -/
def everyLineConstantProfileColorPreservingCI_claim32914 : Prop :=
  (∀ c d : A → Fin 5,
    isLineConstantSymmetricFiveColor11 c →
      isLineConstantSymmetricFiveColor11 d →
        exactColorCI11 c d) ∧
    (∀ c : A → Fin 5,
      isLineConstantSymmetricFiveColor11 c →
        isLineConstantSymmetricFiveColor11 (colorComplement11 c)) ∧
      (∀ c d : A → Fin 5,
        isLineConstantSymmetricFiveColor11 c →
          isLineConstantSymmetricFiveColor11 d →
            lineSurjective11 c → lineSurjective11 d →
              exactColorCI11 c d) ∧
        (∀ c d : A → Fin 5,
          isLineConstantSymmetricFiveColor11 c →
            isLineConstantSymmetricFiveColor11 d →
              totalMapLineSurjective11 c → totalMapLineSurjective11 d →
                exactColorCI11 c d)

end MathlibPlus.Open.ResearchFormalization.R1851Claim32914
