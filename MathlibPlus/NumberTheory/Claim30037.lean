import MathlibPlus.Basic

namespace MathlibPlus.NumberTheory.Claim30037

/-!
Claim 30037, the marked unit-exponent split for `C₁₅`.  The character data
are represented by their generator-power evaluations in `F₇`: the two
faithful order-three generator values are `2` and `4`, and the two filtered
sets retain the unit condition and distinguish preservation from reversal of
that ordered pair.  This avoids silently identifying the two marked
characters merely because the underlying unmarked cyclic subgroup is the
same.
-/
theorem markReversalExponents :
    let chiPlusAt : ZMod 15 → ZMod 7 := fun e => (2 : ZMod 7) ^ (ZMod.val e)
    let chiMinusAt : ZMod 15 → ZMod 7 := fun e => (4 : ZMod 7) ^ (ZMod.val e)
    let unitResidues : Finset (ZMod 15) :=
      Finset.univ.filter (fun e => Nat.Coprime (ZMod.val e) 15)
    let markPreserving : Finset (ZMod 15) :=
      unitResidues.filter (fun e =>
        chiPlusAt e = chiPlusAt 1 ∧ chiMinusAt e = chiMinusAt 1)
    let markReversing : Finset (ZMod 15) :=
      unitResidues.filter (fun e =>
        chiPlusAt e = chiMinusAt 1 ∧ chiMinusAt e = chiPlusAt 1)
    chiPlusAt 1 = 2 ∧
      chiMinusAt 1 = 4 ∧
      chiPlusAt 1 ^ 3 = 1 ∧
      chiMinusAt 1 ^ 3 = 1 ∧
      chiPlusAt 1 ≠ 1 ∧
      chiMinusAt 1 ≠ 1 ∧
      markPreserving = ({1, 4, 7, 13} : Finset (ZMod 15)) ∧
      markReversing = ({2, 8, 11, 14} : Finset (ZMod 15)) := by
  decide

end MathlibPlus.NumberTheory.Claim30037
