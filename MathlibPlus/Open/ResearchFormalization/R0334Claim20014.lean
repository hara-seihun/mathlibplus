import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0334

/-- The exact frequency, deficit, and singleton-fiber toggle data for the
113-member common-core construction in `R-0334`.  Coordinates are the bits
`(t₀,t₁,t₂,z,a₁,a₂,a₃,b₁,b₂,b₃,c)` in that order. -/
def claim20014 : Prop :=
  let expandMask : ℕ → ℕ := fun mask =>
    (if mask.testBit 0 = true then 1 else 0) +
      (if mask.testBit 1 = true then 14 else 0) +
      (if mask.testBit 2 = true then 112 else 0) +
      (if mask.testBit 3 = true then 128 else 0)
  let base : Fin 8 → Finset ℕ :=
    ![
      ({0, 2, 4, 6, 13, 15} : Finset ℕ),
      ({2, 4, 6, 13, 15} : Finset ℕ),
      ({2, 4, 6, 13, 15} : Finset ℕ),
      ({2, 4, 6, 13, 15} : Finset ℕ),
      ({2, 6, 13, 14, 15} : Finset ℕ),
      ({2, 6, 13, 14, 15} : Finset ℕ),
      ({2, 6, 13, 14, 15} : Finset ℕ),
      ({2, 6, 13, 14, 15} : Finset ℕ)
    ]
  let common : Finset ℕ := {22, 30, 50, 54, 62, 114, 118, 243, 247}
  let fiber : Fin 8 → Finset ℕ := fun trace =>
    (base trace).image expandMask ∪ common
  let family : Finset ℕ :=
    Finset.univ.biUnion (fun trace =>
      (fiber trace).image (fun outside => trace.val + 8 * outside))
  let frequency : Fin 11 → ℤ := fun coordinate =>
    Int.ofNat ((family.filter (fun member =>
      (member.testBit coordinate.val) = true)).card)
  let deficit : Fin 11 → ℤ := fun coordinate =>
    (family.card : ℤ) - 2 * frequency coordinate
  let singletonTrace : Fin 3 → Fin 8 :=
    ![(1 : Fin 8), (2 : Fin 8), (4 : Fin 8)]
  let orBitZero : ℕ → ℕ := fun mask =>
    Nat.bitwise (fun left right => left || right) mask 1
  let toggle : Fin 3 → ℕ := fun index =>
    ((fiber (singletonTrace index)).filter (fun outside =>
      outside.testBit 0 = false ∧
        orBitZero outside ∈ fiber (singletonTrace index))).card
  family.card = 113 ∧
    (∀ coordinate : Fin 11,
      frequency coordinate =
        (![56, 56, 56, 32, 100, 76, 44, 104, 88, 64, 36] : Fin 11 → ℤ)
          coordinate) ∧
    (∀ coordinate : Fin 11,
      deficit coordinate =
        (![1, 1, 1, 49, -87, -39, 25, -95, -63, -15, 41] : Fin 11 → ℤ)
          coordinate) ∧
    (∀ index : Fin 3,
      toggle index = (![0, 0, 1] : Fin 3 → ℕ) index)

end MathlibPlus.Open.ResearchFormalization.R0334
