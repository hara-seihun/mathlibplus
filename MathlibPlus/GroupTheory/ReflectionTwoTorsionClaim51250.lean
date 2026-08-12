import Mathlib

namespace MathlibPlus.GroupTheory.Claim51250

/-- The reflection with parameter `a` in an additive abelian group. -/
def reflection {G : Type*} [AddGroup G] (a : G) : G → G :=
  fun x => a - x

/-- Translation by an additive parameter. -/
def translation {G : Type*} [AddGroup G] (a : G) : G → G :=
  fun x => a + x

/-- The two-torsion set `G[2]`. -/
def twoTorsionSet (G : Type*) [AddGroup G] : Set G :=
  {x | x + x = 0}

/-- The doubling image `2G`, written as a set. -/
def doubleSet (G : Type*) [AddGroup G] : Set G :=
  {a | ∃ x, x + x = a}

/-- The fixed-point equation for a reflection, written without suppressing
its additive doubling condition. -/
theorem reflection_fixed_iff
    {G : Type*} [Fintype G] [AddCommGroup G] (a x : G) :
    reflection a x = x ↔ x + x = a := by
  constructor
  · intro h
    dsimp [reflection] at h
    calc
      x + x = (a - x) + x := by rw [h]
      _ = a := by abel
  · intro h
    dsimp [reflection]
    calc
      a - x = (x + x) - x := by rw [h]
      _ = x := by abel

/-- The product of two reflections is the translation by the difference of
 their parameters. -/
theorem reflection_comp_reflection
    {G : Type*} [Fintype G] [AddCommGroup G] (a b x : G) :
    reflection a (reflection b x) = translation (a - b) x := by
  dsimp [reflection, translation]
  abel

/-- Whenever the fixed set is nonempty, it is exactly one coset of `G[2]`. -/
theorem reflection_fixedSet_eq_twoTorsion_coset
    {G : Type*} [Fintype G] [AddCommGroup G] (a x₀ : G) (hx₀ : x₀ + x₀ = a) :
    {x : G | reflection a x = x} =
      (fun y : G => x₀ + y) '' twoTorsionSet G := by
  ext x
  constructor
  · intro hx
    have hfix : reflection a x = x := hx
    refine ⟨x - x₀, ?_, ?_⟩
    · change (x - x₀) + (x - x₀) = 0
      have hxx : x + x = a := (reflection_fixed_iff a x).1 hfix
      calc
        (x - x₀) + (x - x₀) = (x + x) - (x₀ + x₀) := by abel
        _ = 0 := by rw [hxx, hx₀]; simp
    · dsimp
      abel
  · rintro ⟨y, hy, rfl⟩
    have hy' : y + y = 0 := by
      exact hy
    apply (reflection_fixed_iff a (x₀ + y)).2
    calc
      (x₀ + y) + (x₀ + y) = (x₀ + x₀) + (y + y) := by abel
      _ = a := by rw [hx₀, hy']; simp

/-- A fixed set is nonempty exactly when its parameter is in the doubling
image. -/
theorem reflection_fixedSet_nonempty_iff
    {G : Type*} [Fintype G] [AddCommGroup G] (a : G) :
    ({x : G | reflection a x = x}).Nonempty ↔ a ∈ doubleSet G := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (reflection_fixed_iff a x).1 hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (reflection_fixed_iff a x).2 hx⟩

/-- The parameters of products of reflections whose parameters lie in `2G`
are exactly `2G` itself.  Together with the product formula, this is the
set-level form of the generation assertion in the claim. -/
theorem doubleSet_sub_doubleSet_eq_doubleSet
    {G : Type*} [Fintype G] [AddCommGroup G] :
    {d : G | ∃ a ∈ doubleSet G, ∃ b ∈ doubleSet G, d = a - b} =
      doubleSet G := by
  ext d
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    change (∃ x, x + x = a) at ha
    change (∃ y, y + y = b) at hb
    rcases ha with ⟨x, rfl⟩
    rcases hb with ⟨y, rfl⟩
    exact ⟨x - y, by abel⟩
  · intro hd
    change ∃ x, x + x = d at hd
    rcases hd with ⟨x, hx⟩
    refine ⟨d, ⟨x, hx⟩, 0, ⟨0, by simp⟩, ?_⟩
    simp

end MathlibPlus.GroupTheory.Claim51250
