import MathlibPlus.Open.Research.FormalizationBatch.R1529

namespace MathlibPlus.Open.ResearchFormalization.R1529.Claim38318

open MathlibPlus.Open.Research.FormalizationBatch.R1529

abbrev F7 := ZMod 7
abbrev Z8 := ZMod 8
abbrev OrderedBlockPairRow :=
  NormalizedAffineProfileSeven × (Z8 × Z8)

/-- The second row coordinate records separation first and starting block
second; it therefore determines the ordered pair `(k,k+d)`. -/
def rowSeparation (r : OrderedBlockPairRow) : Z8 :=
  r.2.1

def rowStartingBlock (r : OrderedBlockPairRow) : Z8 :=
  r.2.2

def orderedBlockPair (r : OrderedBlockPairRow) : Z8 × Z8 :=
  (rowStartingBlock r, rowStartingBlock r + rowSeparation r)

/-- The blockwise affine chart carried by an affine profile. -/
def blockwiseChart (p : AffineProfileSeven) :
    F7 × Z8 → F7 × Z8 :=
  fun z => (((p.a z.2 : F7) * z.1 + p.t z.2), z.2)

structure AffineLineMapSeven where
  slope : F7ˣ
  intercept : F7

def affineApply (f : AffineLineMapSeven) (x : F7) : F7 :=
  (f.slope : F7) * x + f.intercept

def affineCompose (g f : AffineLineMapSeven) : AffineLineMapSeven :=
  ⟨g.slope * f.slope,
    (g.slope : F7) * f.intercept + g.intercept⟩

def affineInverse (f : AffineLineMapSeven) : AffineLineMapSeven :=
  ⟨f.slope⁻¹, -(f.slope⁻¹ : F7) * f.intercept⟩

def affineIdentity : AffineLineMapSeven :=
  ⟨1, 0⟩

def profileSlopePeriodic (p : NormalizedAffineProfileSeven)
    (d : Z8) : Prop :=
  ∀ k : Z8, p.1.a (k + d) = p.1.a k

def profileDelta (p : NormalizedAffineProfileSeven)
    (d k : Z8) : F7 :=
  p.1.t (k + d) - p.1.t k

def profileGamma (p : NormalizedAffineProfileSeven)
    (d k : Z8) : F7 :=
  (-1 : F7) ^ k.val * profileDelta p d k

def profilePhi (p : NormalizedAffineProfileSeven)
    (d k : Z8) : AffineLineMapSeven :=
  ⟨p.1.a k, profileGamma p d k⟩

def profileDerivative (p : NormalizedAffineProfileSeven)
    (d k : Z8) : AffineLineMapSeven :=
  affineCompose (profilePhi p d (k + 1))
    (affineInverse (profilePhi p d k))

def affineWord (p : NormalizedAffineProfileSeven) (d : Z8) :
    List (Z8 × Bool) → AffineLineMapSeven
  | [] => affineIdentity
  | (k, forward) :: w =>
      affineCompose (affineWord p d w)
        (if forward then profileDerivative p d k
         else affineInverse (profileDerivative p d k))

def inDerivativeGeneratedSet (p : NormalizedAffineProfileSeven)
    (d : Z8) (f : AffineLineMapSeven) : Prop :=
  ∃ w : List (Z8 × Bool), affineWord p d w = f

def hasNonzeroDerivativeTranslation
    (p : NormalizedAffineProfileSeven) (d : Z8) : Prop :=
  ∃ w : List (Z8 × Bool),
    let f := affineWord p d w
    f.slope = 1 ∧ f.intercept ≠ 0

def hasCommonFixedPointAt
    (p : NormalizedAffineProfileSeven) (d : Z8) (z : F7) : Prop :=
  ∀ k : Z8, affineApply (profileDerivative p d k) z = z

def hasFixedPointTelescopeAt
    (p : NormalizedAffineProfileSeven) (d : Z8)
    (z₀ u : F7) : Prop :=
  ∀ k : Z8,
    profileGamma p d k = z₀ - u * (p.1.a k : F7)

def selectedFixedPointMap
    (p : NormalizedAffineProfileSeven) (d k : Z8) (z₀ : F7) : Prop :=
  affineApply (profilePhi p d k) z₀ = z₀

def nonperiodFullTranslation (r : OrderedBlockPairRow) : Prop :=
  rowSeparation r ≠ 0 ∧
    ¬ profileSlopePeriodic r.1 (rowSeparation r)

def periodTranslationSubgroup (r : OrderedBlockPairRow) : Prop :=
  rowSeparation r ≠ 0 ∧ profileSlopePeriodic r.1 (rowSeparation r) ∧
    hasNonzeroDerivativeTranslation r.1 (rowSeparation r)

def periodFixedPointTelescope (r : OrderedBlockPairRow) : Prop :=
  rowSeparation r = 0 ∨
    (rowSeparation r ≠ 0 ∧
      profileSlopePeriodic r.1 (rowSeparation r) ∧
      ∃ z₀ u : F7,
        hasCommonFixedPointAt r.1 (rowSeparation r) z₀ ∧
          hasFixedPointTelescopeAt r.1 (rowSeparation r) z₀ u ∧
            selectedFixedPointMap r.1 (rowSeparation r)
              (rowStartingBlock r) z₀)

def missingDifferenceMap (r : OrderedBlockPairRow) : Prop :=
  rowSeparation r ≠ 0 ∧
    profileSlopePeriodic r.1 (rowSeparation r) ∧
    ∃ z₀ u : F7,
      hasCommonFixedPointAt r.1 (rowSeparation r) z₀ ∧
        hasFixedPointTelescopeAt r.1 (rowSeparation r) z₀ u ∧
          ¬ selectedFixedPointMap r.1 (rowSeparation r)
              (rowStartingBlock r) z₀

/-- The six normalized equal-copy alternating translations. -/
def equalCopyProfile (p : NormalizedAffineProfileSeven) : Prop :=
  ∃ ε : F7, ε ≠ 0 ∧
    p.1.a = (fun _ : Z8 => (1 : F7ˣ)) ∧
      ∀ j : Z8,
        p.1.t j = if j.val % 2 = 0 then 0 else ε

def missingProfile (p : NormalizedAffineProfileSeven) : Prop :=
  ∃ d k : Z8, missingDifferenceMap (p, (d, k))

def missingSeparation (d : Z8) : Prop :=
  ∃ p : NormalizedAffineProfileSeven, ∃ k : Z8,
    missingDifferenceMap (p, (d, k))

def missingStartingBlock (k : Z8) : Prop :=
  ∃ p : NormalizedAffineProfileSeven, ∃ d : Z8,
    missingDifferenceMap (p, (d, k))

/-- A normalized profile has a transporter on every ordered block-pair row. -/
def orderedTransporterRow (r : OrderedBlockPairRow) : Prop :=
  nonperiodFullTranslation r ∨
    periodTranslationSubgroup r ∨ periodFixedPointTelescope r

def orderedTransporterProfile
    (p : NormalizedAffineProfileSeven) : Prop :=
  ∀ d k : Z8, orderedTransporterRow (p, (d, k))

/-- The global affine normalization of a raw chart. -/
def rawNormalizesTo
    (raw : AffineProfileSeven)
    (p : NormalizedAffineProfileSeven) : Prop :=
  ∀ j : Z8,
    p.1.a j = (raw.a 0)⁻¹ * raw.a j ∧
      p.1.t j = (raw.a 0 : F7)⁻¹ * (raw.t j - raw.t 0)

def rawTransporterProfile (raw : AffineProfileSeven) : Prop :=
  ∃ p : NormalizedAffineProfileSeven,
    rawNormalizesTo raw p ∧ orderedTransporterProfile p

def rawEqualCopyProfile (raw : AffineProfileSeven) : Prop :=
  ∃ p : NormalizedAffineProfileSeven,
    rawNormalizesTo raw p ∧ equalCopyProfile p

/-- Profiles supported on only one affine component. -/
def pureSlopeProfile (p : NormalizedAffineProfileSeven) : Prop :=
  ∀ j : Z8, p.1.t j = 0

def pureTranslationProfile (p : NormalizedAffineProfileSeven) : Prop :=
  ∀ j : Z8, p.1.a j = 1

def genuinelyMixedProfile (p : NormalizedAffineProfileSeven) : Prop :=
  ¬ pureSlopeProfile p ∧ ¬ pureTranslationProfile p

/-- Claim 38318: the missing rows, equal-copy profiles, normalized and raw
transporter counts, and the exact genuinely-mixed closure census. -/
def claim38318 : Prop :=
  Nat.card {r : OrderedBlockPairRow // missingDifferenceMap r} = 192 ∧
    Nat.card {p : NormalizedAffineProfileSeven // missingProfile p} = 6 ∧
    Nat.card {d : Z8 // missingSeparation d} = 4 ∧
    (∀ d : Z8, missingSeparation d → d.val % 2 = 1) ∧
    Nat.card {k : Z8 // missingStartingBlock k} = 8 ∧
    (∀ p : NormalizedAffineProfileSeven,
      missingProfile p ↔ equalCopyProfile p) ∧
    Nat.card {p : NormalizedAffineProfileSeven // orderedTransporterProfile p} =
      230_539_333_242 ∧
    Nat.card {p : NormalizedAffineProfileSeven // equalCopyProfile p} = 6 ∧
    (∀ p : NormalizedAffineProfileSeven,
      Nat.card {raw : AffineProfileSeven // rawNormalizesTo raw p} = 42) ∧
    Nat.card {raw : AffineProfileSeven // rawTransporterProfile raw} =
      9_682_651_996_164 ∧
    Nat.card {raw : AffineProfileSeven // rawEqualCopyProfile raw} = 252 ∧
    Nat.card {p : NormalizedAffineProfileSeven // genuinelyMixedProfile p} =
      230_538_229_770 ∧
    (∀ p : NormalizedAffineProfileSeven,
      genuinelyMixedProfile p → orderedTransporterProfile p)

end MathlibPlus.Open.ResearchFormalization.R1529.Claim38318
