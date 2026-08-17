import MathlibPlus.Open.FormalizationBatch.R1242Claim30516

namespace MathlibPlus.Open.FormalizationBatch.R1242Claim30514

noncomputable section

open scoped BigOperators
open MathlibPlus.Open.FormalizationBatch.R1242Claim30516

/-- The pairing of the displayed vector coefficient with a `w` direction. -/
def vectorPairing (a b : Vector) : F3 :=
  ∑ i : Fin 3, a i * b i

/-- The layer condition using the verified `Vector` carrier. -/
def layerCondition (x : Plane) (r : F3) (v : Vector) : Prop :=
  vectorPairing (ell x) v = r

/-- The corrected central coefficient on the layer `ell_x(v)=r`. -/
def layerCoefficient (x : Plane) (H : Plane → F3) (F : Table)
    (r : F3) (s : Plane) : Vector :=
  delta x F s + (2 : F3) • (r • (H s • ell x))

/-- The central translation obtained by pairing the layer coefficient with `w`. -/
def layerTranslation (x : Plane) (H : Plane → F3) (F : Table)
    (r : F3) (s : Plane) (w : Vector) : F3 :=
  vectorPairing (layerCoefficient x H F r s) w

/-- Claim 30514: the displayed coefficient vanishes on a layer exactly for
`exceptionalLayer`; when it does not, one `s,w` gives a nonzero translation
at every point of that layer. -/
def claim30514_layerCoefficient : Prop :=
  ∀ (x : Plane) (H : Plane → F3) (F : Table) (r : F3),
    x ≠ 0 →
      H ≠ 0 →
        (∀ s : Plane, H (s + x) = H s) →
          ((∀ s : Plane, layerCoefficient x H F r s = 0) ↔
              exceptionalLayer x H F r) ∧
            (¬ exceptionalLayer x H F r →
              ∃ s : Plane, ∃ w : Vector,
                ∀ v : Vector, layerCondition x r v →
                  layerTranslation x H F r s w ≠ 0)

end

end MathlibPlus.Open.FormalizationBatch.R1242Claim30514
