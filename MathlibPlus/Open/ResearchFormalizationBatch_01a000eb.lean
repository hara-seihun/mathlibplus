import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a000eb

/-- An edge of the complete graph on `Fin n`, represented by its two-element vertex set. -/
abbrev CompleteEdge (n : ℕ) := {s : Finset (Fin n) // s.card = 2}

/-- A labeled graph on the fixed vertex set is a finite set of complete-graph edges. -/
abbrev LabeledGraph (n : ℕ) := Finset (CompleteEdge n)

/-- Relabel one complete-graph edge by a vertex permutation. -/
def relabelEdge {n : ℕ} (σ : Equiv.Perm (Fin n)) (e : CompleteEdge n) : CompleteEdge n :=
  ⟨e.1.image σ, by
    rw [Finset.card_image_of_injective e.1 σ.injective, e.2]⟩

/-- Relabel all edges of a labeled graph. -/
def relabelGraph {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : LabeledGraph n) : LabeledGraph n :=
  G.image (relabelEdge σ)

/-- The labeled edge sets having the same unlabeled shape as `A`. -/
def shapeOrbit {n : ℕ} (A : LabeledGraph n) : Finset (LabeledGraph n) :=
  Finset.univ.image (fun σ : Equiv.Perm (Fin n) => relabelGraph σ A)

/-- The Walsh character indexed by an edge set. -/
def walshCharacter {n : ℕ} (A G : LabeledGraph n) : ℤ :=
  (-1 : ℤ) ^ (A ∩ G).card

/-- The rational-valued version used for Fourier coefficients. -/
def walshCharacterQ {n : ℕ} (A G : LabeledGraph n) : ℚ :=
  (-1 : ℚ) ^ (A ∩ G).card

/-- The shape character, as the orbit sum over labeled edge sets of the shape. -/
def shapeCharacter {n : ℕ} (A G : LabeledGraph n) : ℤ :=
  ∑ B ∈ shapeOrbit A, walshCharacter B G

def shapeCharacterQ {n : ℕ} (A G : LabeledGraph n) : ℚ :=
  ∑ B ∈ shapeOrbit A, walshCharacterQ B G

/-- The spanning-subgraph count for a graph type represented by `Y`. -/
def spanningSubgraphCount {n : ℕ} (Y G : LabeledGraph n) : ℕ :=
  ((shapeOrbit Y).filter (fun A => A ⊆ G)).card

/-- The indicator monomial contributed by one labeled copy. -/
def spanningCopyMonomial {n : ℕ} (A G : LabeledGraph n) : ℚ :=
  ∏ e ∈ A, (1 - walshCharacterQ ({e} : LabeledGraph n) G) / 2

/-- The Fourier coefficient on the Boolean edge-set cube. -/
def fourierCoefficient {n : ℕ} (F : LabeledGraph n → ℚ) (A : LabeledGraph n) : ℚ :=
  (Fintype.card (LabeledGraph n) : ℚ)⁻¹ *
    ∑ G : LabeledGraph n, F G * walshCharacterQ A G

/-- The degree-`m` Fourier part of a function on labeled graphs. -/
def fourierTop {n : ℕ} (F : LabeledGraph n → ℚ) (m : ℕ)
    (G : LabeledGraph n) : ℚ :=
  ∑ A ∈ (Finset.univ.filter (fun A : LabeledGraph n => A.card = m)),
    fourierCoefficient F A * walshCharacterQ A G

/-- Claim 31481: the Walsh and shape characters on the complete-graph edge cube. -/
def claim31481 : Prop :=
  ∀ (n : ℕ) (A G : LabeledGraph n),
    walshCharacter A G = (-1 : ℤ) ^ (A ∩ G).card ∧
      shapeCharacter A G = ∑ B ∈ shapeOrbit A, walshCharacter B G

/-- The card obtained by deleting either vertex from a two-vertex graph.  Its
carrier has one vertex and therefore no two-element edge. -/
def twoVertexCard (G : LabeledGraph 2) (v : Fin 2) : LabeledGraph 1 :=
  ∅

/-- The two-card deck at order two. -/
def twoVertexDeck (G : LabeledGraph 2) : Multiset (LabeledGraph 1) :=
  Multiset.ofList [twoVertexCard G 0, twoVertexCard G 1]

/-- Claim 31491: `K₂` and the empty two-vertex graph have the same deck but
are separated by the connected spanning Walsh character. -/
def claim31491 : Prop :=
  let complete : LabeledGraph 2 := Finset.univ
  let empty : LabeledGraph 2 := ∅
  twoVertexDeck complete = twoVertexDeck empty ∧
    twoVertexDeck complete = Multiset.ofList [∅, ∅] ∧
    walshCharacter complete complete ≠ walshCharacter complete empty

/-- Claim 31482: the Fourier expansion of a spanning-subgraph count. -/
def claim31482 : Prop :=
  ∀ (n : ℕ) (Y G : LabeledGraph n),
    (spanningSubgraphCount Y G : ℚ) =
      ∑ A ∈ shapeOrbit Y, ∏ e ∈ A,
        (1 - walshCharacterQ ({e} : LabeledGraph n) G) / 2

/-- Claim 31483: the top Fourier contribution of each labeled copy and of the
spanning count. -/
def claim31483 : Prop :=
  ∀ (n : ℕ) (Y A : LabeledGraph n), A ∈ shapeOrbit Y →
    (fourierCoefficient (spanningCopyMonomial A) A =
        (-1 : ℚ) ^ A.card / (2 : ℚ) ^ A.card ∧
      ∀ B : LabeledGraph n, B.card = A.card → B ≠ A →
        fourierCoefficient (spanningCopyMonomial A) B = 0) ∧
    (∀ G : LabeledGraph n,
      fourierTop (fun H => (spanningSubgraphCount Y H : ℚ)) Y.card G =
        ((-1 : ℚ) ^ Y.card / (2 : ℚ) ^ Y.card) * shapeCharacterQ Y G)

end MathlibPlus.Open.ResearchFormalizationBatch_01a000eb



namespace MathlibPlus.Open.ResearchFormalizationBatch_01a000eb

abbrev F3 := ZMod 3
abbrev F3Square := Fin 2 → F3
abbrev F3Cube := Fin 3 → F3
abbrev RankFiveE := F3 × (F3Square × F3Cube)

/-- The dot product on the three-dimensional `u` coordinate. -/
def dot3 (v w : F3Cube) : F3 := ∑ k : Fin 3, v k * w k

/-- The displayed quadratic increment `Q(i,j)`. -/
def quadraticIncrement (x : F3Square) : F3Cube :=
  fun k => if k = 0 then x 0 * (x 0 - 1)
    else if k = 1 then (2 * x 0 - 1) * x 1
    else x 1 ^ 2

/-- The transporter displayed in the rank-five quadratic claim. -/
def rankFiveQuadraticTransporter
    (f : F3Square → F3) (Fmap : F3Square → F3Cube) : RankFiveE → RankFiveE :=
  fun p =>
    (p.1 + f p.2.1 + dot3 (Fmap p.2.1) p.2.2,
      (p.2.1, p.2.2 + quadraticIncrement p.2.1))

/-- Claim 31676: the stated formula defines `q_{f,F}` on the stated carrier. -/
def claim31676 : Prop :=
  ∀ (f : F3Square → F3) (Fmap : F3Square → F3Cube)
    (z : F3) (x : F3Square) (u : F3Cube),
    rankFiveQuadraticTransporter f Fmap (z, (x, u)) =
      (z + f x + dot3 (Fmap x) u, (x, u + quadraticIncrement x))

/-- An explicit inverse for the displayed transporter. -/
def rankFiveQuadraticTransporterInv
    (f : F3Square → F3) (Fmap : F3Square → F3Cube) : RankFiveE → RankFiveE :=
  fun p =>
    (p.1 - f p.2.1 - dot3 (Fmap p.2.1) (p.2.2 - quadraticIncrement p.2.1),
      (p.2.1, p.2.2 - quadraticIncrement p.2.1))

/-- The transporter as a permutation, with its inverse written explicitly. -/
def rankFiveQuadraticTransporterPerm
    (f : F3Square → F3) (Fmap : F3Square → F3Cube) : RankFiveE ≃ RankFiveE := by
  refine @Equiv.mk _ _ (rankFiveQuadraticTransporter f Fmap)
    (rankFiveQuadraticTransporterInv f Fmap) ?_ ?_
  · rintro ⟨z, x, u⟩
    apply Prod.ext
    · dsimp [rankFiveQuadraticTransporter, rankFiveQuadraticTransporterInv]
      have hu : u + quadraticIncrement x - quadraticIncrement x = u := by
        ext k
        simp
      rw [hu]
      ring
    · apply Prod.ext
      · rfl
      · funext k
        dsimp [rankFiveQuadraticTransporter, rankFiveQuadraticTransporterInv]
        simp
  · rintro ⟨z, x, u⟩
    apply Prod.ext
    · dsimp [rankFiveQuadraticTransporter, rankFiveQuadraticTransporterInv]
      ring
    · apply Prod.ext
      · rfl
      · funext k
        dsimp [rankFiveQuadraticTransporter, rankFiveQuadraticTransporterInv]
        simp

/-- The five-parameter atlas normalizer as a function. -/
def atlasNormalizerFunction (param : Fin 5 → F3) : RankFiveE → RankFiveE :=
  fun p =>
    (p.1 + param 0 * p.2.1 0 + param 1 * p.2.1 1 +
        param 2 * p.2.2 0 + param 3 * p.2.2 1 + param 4 * p.2.2 2,
      (p.2.1,
        fun k => if k = 0 then p.2.2 0 + 2 * p.2.1 0
          else if k = 1 then p.2.2 1 + 2 * p.2.1 1
          else p.2.2 2))

/-- An explicit inverse for the atlas normalizer. -/
def atlasNormalizerInverse (param : Fin 5 → F3) : RankFiveE → RankFiveE :=
  fun p =>
    (p.1 - param 0 * p.2.1 0 - param 1 * p.2.1 1 -
        param 2 * (p.2.2 0 - 2 * p.2.1 0) -
        param 3 * (p.2.2 1 - 2 * p.2.1 1) - param 4 * p.2.2 2,
      (p.2.1,
        fun k => if k = 0 then p.2.2 0 - 2 * p.2.1 0
          else if k = 1 then p.2.2 1 - 2 * p.2.1 1
          else p.2.2 2))

/-- The atlas normalizer as a permutation. -/
def atlasNormalizer (param : Fin 5 → F3) : RankFiveE ≃ RankFiveE := by
  refine @Equiv.mk _ _ (atlasNormalizerFunction param)
    (atlasNormalizerInverse param) ?_ ?_
  · rintro ⟨z, x, u⟩
    apply Prod.ext
    · dsimp [atlasNormalizerFunction, atlasNormalizerInverse]
      ring
    · apply Prod.ext
      · rfl
      · funext k
        fin_cases k <;> simp [atlasNormalizerFunction, atlasNormalizerInverse]
  · rintro ⟨z, x, u⟩
    apply Prod.ext
    · dsimp [atlasNormalizerFunction, atlasNormalizerInverse]
      ring
    · apply Prod.ext
      · rfl
      · funext k
        fin_cases k <;> simp [atlasNormalizerFunction, atlasNormalizerInverse]

/-- The regular translation group on the additive carrier. -/
def rankFiveTranslationGroup : Subgroup (Equiv.Perm RankFiveE) :=
  Subgroup.closure (Set.range (fun v : RankFiveE => Equiv.addRight v))

/-- Conjugation of permutations with the convention `H^q = q⁻¹ H q`. -/
def permutationConjugationHom (q : Equiv.Perm RankFiveE) :
    Equiv.Perm RankFiveE →* Equiv.Perm RankFiveE :=
  { toFun := fun g => q⁻¹ * g * q
    map_one' := by simp
    map_mul' := by
      intro g h
      simp [mul_assoc] }

/-- The conjugate subgroup `H^q`. -/
def conjugatedTranslationGroup (H : Subgroup (Equiv.Perm RankFiveE))
    (q : Equiv.Perm RankFiveE) : Subgroup (Equiv.Perm RankFiveE) :=
  H.map (permutationConjugationHom q)

/-- The orbital definition of the exact two-closure. -/
def exactTwoClosure (G : Subgroup (Equiv.Perm RankFiveE)) :
    Set (Equiv.Perm RankFiveE) :=
  {c | ∀ p : RankFiveE × RankFiveE,
      ∃ g : Equiv.Perm RankFiveE, g ∈ G ∧
        (c p.1, c p.2) = (g p.1, g p.2)}

/-- The group generated by the translation group and its displayed conjugate. -/
def rankFivePairGroup
    (f : F3Square → F3) (Fmap : F3Square → F3Cube) :
    Subgroup (Equiv.Perm RankFiveE) :=
  Subgroup.closure
    ((rankFiveTranslationGroup : Set (Equiv.Perm RankFiveE)) ∪
      (conjugatedTranslationGroup rankFiveTranslationGroup
        (rankFiveQuadraticTransporterPerm f Fmap) : Set (Equiv.Perm RankFiveE)))

/-- The zero point in the displayed coordinate carrier. -/
def rankFiveZero : RankFiveE :=
  (0, ((fun _ : Fin 2 => 0), (fun _ : Fin 3 => 0)))

/-- The atlas composite `c_λ = n_λ q_{f,F}`. -/
def atlasComposite (param : Fin 5 → F3)
    (f : F3Square → F3) (Fmap : F3Square → F3Cube) : Equiv.Perm RankFiveE :=
  atlasNormalizer param * rankFiveQuadraticTransporterPerm f Fmap

/-- Claim 31677: every mixed affine table gives a conjugating element in the
exact two-closure of the generated pair. -/
def claim31677 : Prop :=
  ∀ (f : F3Square → F3) (Fmap : F3Square → F3Cube),
    ∃ c : Equiv.Perm RankFiveE,
      c ∈ exactTwoClosure (rankFivePairGroup f Fmap) ∧
        conjugatedTranslationGroup rankFiveTranslationGroup c =
          conjugatedTranslationGroup rankFiveTranslationGroup
            (rankFiveQuadraticTransporterPerm f Fmap)

/-- Claim 31683: every atlas composite fixes zero and conjugates the regular
translation group to the displayed conjugate. -/
def claim31683 : Prop :=
  ∀ (param : Fin 5 → F3)
    (f : F3Square → F3) (Fmap : F3Square → F3Cube),
    atlasComposite param f Fmap rankFiveZero = rankFiveZero ∧
      conjugatedTranslationGroup rankFiveTranslationGroup
          (atlasComposite param f Fmap) =
        conjugatedTranslationGroup rankFiveTranslationGroup
          (rankFiveQuadraticTransporterPerm f Fmap)

/-- Claim 31682: every displayed atlas map is a normalizing permutation and the atlas
contains exactly `3^5 = 243` distinct maps. -/
def claim31682 : Prop :=
  (∀ param : Fin 5 → F3,
      atlasNormalizer param ∈ Subgroup.normalizer (rankFiveTranslationGroup)) ∧
    (Finset.univ.image (fun param : Fin 5 → F3 => (atlasNormalizer param : Equiv.Perm RankFiveE))).card = 3 ^ 5 ∧
    (Finset.univ.image (fun param : Fin 5 → F3 => (atlasNormalizer param : Equiv.Perm RankFiveE))).card = 243

/-- Claim 41440: the same fixed rank-five quadratic transporter formula. -/
def claim41440 : Prop :=
  ∀ (f : F3Square → F3) (Fmap : F3Square → F3Cube)
    (z : F3) (x : F3Square) (u : F3Cube),
    rankFiveQuadraticTransporter f Fmap (z, (x, u)) =
      (z + f x + dot3 (Fmap x) u, (x, u + quadraticIncrement x))

/-- Claim 41441: the same exact-two-closure conjugacy assertion. -/
def claim41441 : Prop :=
  ∀ (f : F3Square → F3) (Fmap : F3Square → F3Cube),
    ∃ c : Equiv.Perm RankFiveE,
      c ∈ exactTwoClosure (rankFivePairGroup f Fmap) ∧
        conjugatedTranslationGroup rankFiveTranslationGroup c =
          conjugatedTranslationGroup rankFiveTranslationGroup
            (rankFiveQuadraticTransporterPerm f Fmap)

/-- Claim 41447: the same atlas-composite conjugacy assertion. -/
def claim41447 : Prop :=
  ∀ (param : Fin 5 → F3)
    (f : F3Square → F3) (Fmap : F3Square → F3Cube),
    atlasComposite param f Fmap rankFiveZero = rankFiveZero ∧
      conjugatedTranslationGroup rankFiveTranslationGroup
          (atlasComposite param f Fmap) =
        conjugatedTranslationGroup rankFiveTranslationGroup
          (rankFiveQuadraticTransporterPerm f Fmap)

end MathlibPlus.Open.ResearchFormalizationBatch_01a000eb
