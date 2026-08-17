import Mathlib

open scoped BigOperators
open Classical
noncomputable section

namespace MathlibPlus.Open.ProjectsResearch

/-- The exact orbit-type carrier from the three blocks of sizes `3, 10, 10`
and one Boolean outside coordinate. -/
abbrev orbitType45108 := Fin 4 × Fin 11 × Fin 11 × Bool

/-- The admissible orbit types: nonempty and containing a complete minimum
block. The finite coordinates carry the displayed bounds. -/
def orbitTypeSet45108 : Finset orbitType45108 :=
  Finset.univ.filter (fun t =>
    (t.1.val ≠ 0 ∨ t.2.1.val ≠ 0 ∨ t.2.2.1.val ≠ 0 ∨ t.2.2.2 = true) ∧
      (t.1.val = 3 ∨ t.2.1.val = 10 ∨ t.2.2.1.val = 10))

def blockValue45108 (t : orbitType45108) (i : Fin 3) : ℕ :=
  if i = 0 then t.1.val
  else if i = 1 then t.2.1.val
  else t.2.2.1.val

def blockCapacity45108 (i : Fin 3) : ℕ :=
  if i = 0 then 3 else 10

def intervalValues45108
    (a b : orbitType45108) (i : Fin 3) : Finset ℕ :=
  Finset.Icc
    (max (blockValue45108 a i) (blockValue45108 b i))
    (min (blockCapacity45108 i)
      (blockValue45108 a i + blockValue45108 b i))

/-- The cardinality-relaxation feasibility predicate. It is deliberately a
coordinatewise predicate rather than a labelled-family realization. -/
def feasibleOrbitType45108
    (a b c : orbitType45108) : Prop :=
  c ∈ orbitTypeSet45108 ∧
    (∀ i : Fin 3,
      max (blockValue45108 a i) (blockValue45108 b i) ≤ blockValue45108 c i ∧
        blockValue45108 c i ≤
          min (blockCapacity45108 i)
            (blockValue45108 a i + blockValue45108 b i)) ∧
    c.2.2.2 = max a.2.2.2 b.2.2.2

def feasibleOrbitTypes45108
    (a b : orbitType45108) : Finset orbitType45108 :=
  orbitTypeSet45108.filter (fun c =>
    (∀ i : Fin 3,
      max (blockValue45108 a i) (blockValue45108 b i) ≤ blockValue45108 c i ∧
        blockValue45108 c i ≤
          min (blockCapacity45108 i)
            (blockValue45108 a i + blockValue45108 b i)) ∧
    c.2.2.2 = max a.2.2.2 b.2.2.2)

def feasibleBlockValues45108
    (a b : orbitType45108) (i : Fin 3) : Finset ℕ :=
  (feasibleOrbitTypes45108 a b).image (fun c => blockValue45108 c i)

/-- Claim R-2682.2. The feasible tuples are exactly the displayed
coordinatewise max/min choices on the exact carrier, and each coordinate
interval is fully represented. No joint-realizability assertion is made. -/
def claim45108 : Prop :=
  ∀ a ∈ orbitTypeSet45108, ∀ b ∈ orbitTypeSet45108,
    (∀ c : orbitType45108,
      c ∈ feasibleOrbitTypes45108 a b ↔
        feasibleOrbitType45108 a b c) ∧
    (∀ i : Fin 3,
      feasibleBlockValues45108 a b i = intervalValues45108 a b i)

end MathlibPlus.Open.ProjectsResearch
