import MathlibPlus.Open.Research.Q12CIBatch

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R1336.Census

private abbrev NormalizedChartProfile (G : Type*) [One G] :=
  {h : ZMod 7 → G // h 0 = 1}

private abbrev NormalizedOffsetDatum (G : Type*) [One G] :=
  NormalizedChartProfile G × (ZMod 7 × ZMod 7)

private def chartDifference {G : Type*} [Group G]
    (h : ZMod 7 → G) (i : ZMod 7) : G :=
  (h i)⁻¹ * h (i + 1)

private def chartPairSubgroup {G : Type*} [Group G]
    (h : ZMod 7 → G) (r : ZMod 7) : Subgroup (G × G) :=
  Subgroup.closure (Set.range (fun k : ZMod 7 =>
    (chartDifference h k, chartDifference h (k + r))))

private def chartPairSurjective {G : Type*} [Group G]
    (h : ZMod 7 → G) : Prop :=
  ∀ i r : ZMod 7,
    (h i, h (i + r)) ∈
      (chartPairSubgroup h r : Set (G × G))

private noncomputable def chartSupportSize {G : Type*} [One G]
    (h : ZMod 7 → G) : ℕ :=
  Nat.card {i : ZMod 7 // h i ≠ 1}

private def normalizedOffsetFailure {G : Type*} [Group G]
    (w : NormalizedOffsetDatum G) : Prop :=
  let h := w.1.1
  let i := w.2.1
  let r := w.2.2
  (h i, h (i + r)) ∉
    (chartPairSubgroup h r : Set (G × G))

/-- Claim 30970: the exact normalized-profile census and support histogram. -/
def exactNormalizedProfileCensus_claim30970 : Prop :=
  ∀ (G : Type*) [Group G] [Fintype G] (a b : G),
    MathlibPlus.Open.Research.Q12.isQ12Presentation a b →
    let Profile := NormalizedChartProfile G
    let pairSurjective : Profile → Prop := fun h =>
      chartPairSurjective h.1
    let supportSize : Profile → ℕ := fun h =>
      chartSupportSize h.1
    (Nat.card Profile = 12 ^ 6) ∧
      Nat.card Profile = 2985984 ∧
      (∀ h : Profile, pairSurjective h) ∧
      Nat.card {h : Profile // ¬ pairSurjective h} = 0 ∧
      Nat.card {w : NormalizedOffsetDatum G // normalizedOffsetFailure w} = 0 ∧
      Nat.card {h : Profile // supportSize h = 0} = 1 ∧
      Nat.card {h : Profile // supportSize h = 1} = 66 ∧
      Nat.card {h : Profile // supportSize h = 2} = 1815 ∧
      Nat.card {h : Profile // supportSize h = 3} = 26620 ∧
      Nat.card {h : Profile // supportSize h = 4} = 219615 ∧
      Nat.card {h : Profile // supportSize h = 5} = 966306 ∧
      Nat.card {h : Profile // supportSize h = 6} = 1771561 ∧
      1 + 66 + 1815 + 26620 + 219615 + 966306 + 1771561 =
        2985984

end MathlibPlus.Open.ResearchFormalization.R1336.Census
