import MathlibPlus.Open.ResearchFormalization.R2614Claims42815_42818

namespace MathlibPlus.Open.ResearchFormalization.R2614Claim42810

noncomputable section

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.R2614Claims42815_42818

/-- The `(1+T_i)` operator on integer-indexed row functions. -/
def intOnePlusShiftOperator {m : ℕ} (i : Fin m)
    (F : IntFunction m) : IntFunction m :=
  fun q => F q + F (lowerInt q i)

/-- The exact positive operator on the right of the weighted intertwining:
`(1+T_i) partial_i^(R-1) + T_i + 2 T_i^2`. -/
def intIntertwiningOperator {m : ℕ} (R : ℕ) (i : Fin m)
    (F : IntFunction m) : IntFunction m :=
  fun q =>
    intPartialOperator (R - 1) i F q +
        intPartialOperator (R - 1) i F (lowerInt q i) +
      F (lowerInt q i) +
        2 * F (lowerInt (lowerInt q i) i)

/-- Apply the selected lower-slack partial operators and then apply one shift
for each coordinate in `S`, with one additional shift for each coordinate in
`B`.  The separate `B` list records the second occurrence in `T_i^2`; it is
not absorbed into a `Finset` union. -/
def intShiftThenPartialWithDouble {m : ℕ} (R : ℕ)
    (S B J : Finset (Fin m)) (F : IntFunction m) : IntFunction m :=
  applyIntRatOperators
    (S.toList.map (fun i => intShiftOperator i) ++
      B.toList.map (fun i => intShiftOperator i))
    (applyIntRatOperators
      (J.toList.map (fun i => intPartialOperator R i)) F)

def kernelMinorFunction {m : ℕ} (R : ℕ) (offsets : Fin m → ℤ) : IntFunction m :=
  fun q => kernelMinorRows R offsets q

/-- The operator product in Record 8, with the outside coordinates applied
before the coordinates in `I`. -/
def intIntertwiningExpansion {m : ℕ} (R : ℕ)
    (offsets : Fin m → ℤ) (I : Finset (Fin m)) : IntFunction m :=
  applyIntRatOperators
    ((Finset.univ \ I).toList.map (fun i => intOnePlusShiftOperator i))
    (applyIntRatOperators
      (I.toList.map (fun i => intIntertwiningOperator R i))
      (kernelMinorFunction (R - 1) offsets))

/-- The literal positive-integer expansion of the Record 8 product.  `J` is
the retained derivative set; `A` chooses the lowering branch of
`(1+T_i) partial_i`; `B` chooses the coefficient-2 `T_i^2` branch; and `C`
chooses the outside-coordinate lowering branch.  The second `B` occurrence in
`intShiftThenPartialWithDouble` is the double lowering required by `T_i^2`. -/
def intPositiveExpansion {m : ℕ} (R : ℕ)
    (offsets : Fin m → ℤ) (I : Finset (Fin m)) : IntFunction m :=
  fun q =>
    Finset.sum I.powerset (fun J =>
      Finset.sum J.powerset (fun A =>
        Finset.sum (I \ J).powerset (fun B =>
          Finset.sum (Finset.univ \ I).powerset (fun C =>
            ((2 ^ B.card : ℕ) : ℚ) •
              intShiftThenPartialWithDouble (R - 1)
                (A ∪ (I \ J) ∪ C) B J
                (kernelMinorFunction (R - 1) offsets) q))))

/-- Claim 42810: the exact weighted operator product and its expansion as a
positive-integer sum of shifted lower-slack mixed partials. -/
def claim42810 : Prop :=
  ∀ (m R : ℕ) (offsets : Fin m → ℤ) (I : Finset (Fin m))
    (q : Fin m → ℤ),
    1 ≤ R →
      (∀ j : Fin m, 0 ≤ (R : ℤ) + offsets j - 2) →
        admissibleKernelCube q I →
          mixedIntPartial R I (kernelMinorFunction R offsets) q =
              intIntertwiningExpansion R offsets I q ∧
            mixedIntPartial R I (kernelMinorFunction R offsets) q =
              intPositiveExpansion R offsets I q

end

end MathlibPlus.Open.ResearchFormalization.R2614Claim42810
