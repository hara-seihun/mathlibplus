import Mathlib

open scoped BigOperators TensorProduct

namespace MathlibPlus.Open.Research.CIElementaryAbelianOddResidualRanksFullSlopeCompression

/-- The full-function slope compression, shear-separation, and oddification
statement for a finite family of directions and covectors over an odd prime
field. -/
def claim61200 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Odd p →
    ∀ {A B : Type*}
      [AddCommGroup A] [Module (ZMod p) A]
      [FiniteDimensional (ZMod p) A]
      [AddCommGroup B] [Module (ZMod p) B]
      [FiniteDimensional (ZMod p) B],
      ∀ {I : Type*} [Fintype I] [DecidableEq I]
        (d : I → B) (u : I → Module.Dual (ZMod p) A),
        (∀ i, d i ≠ 0 ∧ u i ≠ 0) →
        let a : ℕ := Module.finrank (ZMod p) A
        let b : ℕ := Module.finrank (ZMod p) B
        0 < a →
        0 < b →
        ∀ (J : Finset I) (j : Fin a → I)
          (epsilon : Fin a → Module.Dual (ZMod p) B)
          (c : I → Fin a → ZMod p),
          J = Finset.univ.image j →
          Function.Injective j →
          LinearIndependent (ZMod p) (fun k => u (j k)) →
          Submodule.span (ZMod p) (Set.range (fun k => u (j k))) = ⊤ →
          (∀ k, epsilon k (d (j k)) = 1) →
          (∀ i, u i = ∑ k : Fin a, c i k • u (j k)) →
          ∃ r : ∀ k : Fin a, B → (LinearMap.ker (epsilon k)),
            (∀ k x,
              (r k x : B) = x - (epsilon k x) • d (j k)) ∧
            let H : Fin a → Submodule (ZMod p) B :=
              fun k => LinearMap.ker (epsilon k)
            let originalCondition :
                (B → A) → (I → ZMod p) → Prop :=
              fun s lambda =>
                ∀ i x, (u i) (s (x + d i) - s x) = lambda i
            let reducedCondition :
                (∀ k : Fin a, H k → ZMod p) →
                  (I → ZMod p) → Prop :=
              fun h lambda =>
                ∀ i, i ∉ J → ∀ x,
                  ∑ k : Fin a,
                      c i k *
                        (h k (r k (x + d i)) - h k (r k x) +
                          epsilon k (d i) * lambda (j k)) =
                    lambda i
            let Original : Type _ :=
              {z : (B → A) × (I → ZMod p) //
                originalCondition z.1 z.2}
            let Reduced : Type _ :=
              {z : (∀ k : Fin a, H k → ZMod p) × (I → ZMod p) //
                reducedCondition z.1 z.2}
            let coordinateFormula : Original → Reduced → Prop :=
              fun z w =>
                w.1.2 = z.1.2 ∧
                  ∀ k x,
                    (u (j k)) (z.1.1 x) =
                      w.1.1 k (r k x) +
                        epsilon k x * z.1.2 (j k)
            let shearImage : Set (I → ZMod p) :=
              Set.range (fun L : B →ₗ[ZMod p] A =>
                fun i => (u i) (L (d i)))
            (∃ e : Original ≃ Reduced,
                (∀ z, coordinateFormula z (e z)) ∧
                (∀ e' : Original ≃ Reduced,
                  (∀ z, coordinateFormula z (e' z)) → e' = e)) ∧
            Nat.card ((Fin a × B) ⊕ I) =
                a * p ^ b + Nat.card I ∧
            Nat.card (I × B) = Nat.card I * p ^ b ∧
            Nat.card ((Σ k : Fin a, H k) ⊕ I) =
                a * p ^ (b - 1) + Nat.card I ∧
            Nat.card (({i : I // i ∉ J}) × B) =
                (Nat.card I - a) * p ^ b ∧
            (∀ (rho : I → ZMod p),
              (∑ i : I,
                  rho i • TensorProduct.tmul (ZMod p) (u i) (d i) = 0) →
              ∀ (h : ∀ k : Fin a, H k → ZMod p)
                (lambda : I → ZMod p),
                reducedCondition h lambda →
                (∑ i : I, rho i * lambda i = 1) →
                lambda ∉ shearImage) ∧
            ((∃ (s : B → A) (lambda : I → ZMod p),
                originalCondition s lambda ∧ lambda ∉ shearImage) ↔
              ∃ (rho : I → ZMod p)
                (h : ∀ k : Fin a, H k → ZMod p)
                (lambda : I → ZMod p),
                (∑ i : I,
                    rho i • TensorProduct.tmul (ZMod p) (u i) (d i) = 0) ∧
                  reducedCondition h lambda ∧
                  ∑ i : I, rho i * lambda i = 1) ∧
            ∀ (s : B → A) (lambda : I → ZMod p),
              originalCondition s lambda →
              let sOdd : B → A :=
                fun x => (2 : ZMod p)⁻¹ • (s x - s (-x))
              sOdd 0 = 0 ∧
                (∀ x, sOdd (-x) = -sOdd x) ∧
                ∀ i x,
                  (u i) (sOdd (x + d i) - sOdd x) = lambda i

end MathlibPlus.Open.Research.CIElementaryAbelianOddResidualRanksFullSlopeCompression
