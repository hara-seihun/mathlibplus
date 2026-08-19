import MathlibPlus.Open.Research.R3193.Claim47053

namespace MathlibPlus.Open.Research.R3193

/-- The three branches of the deterministic component tree, including the
    queried branch bits, returned bit, and exact path depth. -/
def componentTreeRealizesStatedProcedure (n : ℕ) (j : Fin n) : Prop :=
  ∀ ω : RademacherSample n,
    (ω.u j = false ∧
      componentTranscript n j ω =
        { u := false, v := none, answer := ω.b j } ∧
      transcriptQueryCount n j ω = 2) ∨
    (ω.u j = true ∧ ω.v j = true ∧
      componentTranscript n j ω =
        { u := true, v := some true, answer := ω.a } ∧
      transcriptQueryCount n j ω = 3) ∨
    (ω.u j = true ∧ ω.v j = false ∧
      componentTranscript n j ω =
        { u := true, v := some false, answer := ω.b j } ∧
      transcriptQueryCount n j ω = 3)

/-- Claim 47047: on the explicit finite product of Boolean coordinates with
    uniform average, the common-branch indicator and component value realize
    the shared-bit Rademacher construction, and the displayed transcript is
    the stated deterministic tree of depth at most three. -/
def claim47047 : Prop :=
  p = 1 / 4 ∧
  ∀ (n : ℕ) (j : Fin n),
    commonBranchProbability n j = p ∧
    (∀ ω : RademacherSample n,
      commonIndicator n j ω = 1 ↔
        (ω.u j = true ∧ ω.v j = true)) ∧
    componentTreeRealizesStatedProcedure n j ∧
    (∀ ω : RademacherSample n,
      componentValue n j ω =
        transcriptValue (componentTranscript n j ω)) ∧
    (∀ ω : RademacherSample n,
      componentValue n j ω = -1 ∨ componentValue n j ω = 1) ∧
    (∀ ω : RademacherSample n,
      transcriptQueryCount n j ω ≤ 3)

end MathlibPlus.Open.Research.R3193
