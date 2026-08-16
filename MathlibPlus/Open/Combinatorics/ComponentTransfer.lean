import Mathlib

namespace MathlibPlus.Open.Combinatorics

private def denseComponent : Finset (Finset (Fin 5)) :=
  ((Finset.univ : Finset (Fin 5 × Fin 5)).filter
    (fun e =>
      e.1 ≠ e.2 ∧
      ¬ (e.1 = (3 : Fin 5) ∧ e.2 = (4 : Fin 5)) ∧
      ¬ (e.1 = (4 : Fin 5) ∧ e.2 = (3 : Fin 5)))).image
    (fun e => ({e.1, e.2} : Finset (Fin 5)))

private def singletonComponent : Finset (Finset (Fin 5)) :=
  {({(3 : Fin 5), (4 : Fin 5)} : Finset (Fin 5))}

private def componentDegree (component : Finset (Finset (Fin 5))) (v : Fin 5) : Nat :=
  (component.filter (fun edge => v ∈ edge)).card

private def fixtureSignature (v : Fin 5) : Nat × Nat :=
  (componentDegree denseComponent v, componentDegree singletonComponent v)

private def pi3 : Fin 5 → Fin 5 := fun v =>
  if v = 0 then 1 else
  if v = 1 then 4 else
  if v = 2 then 2 else
  if v = 3 then 3 else 0

private def pi4 : Fin 5 → Fin 5 := fun v =>
  if v = 0 then 1 else
  if v = 1 then 2 else
  if v = 2 then 3 else
  if v = 3 then 0 else 4

private def totalDegree (v : Fin 5) : Nat :=
  componentDegree denseComponent v + componentDegree singletonComponent v

private def leftComponents : Fin 2 → Finset (Finset (Fin 5)) := fun i =>
  if i = 0 then denseComponent else singletonComponent

private def rightComponents : Fin 2 → Finset (Finset (Fin 5)) := fun i =>
  if i = 0 then denseComponent else singletonComponent

/-- Exact component-degree signatures in the two-component fixture. -/
def exactComponentDegreeSignatures : Prop :=
  fixtureSignature 0 = (4, 0) ∧
  fixtureSignature 1 = (4, 0) ∧
  fixtureSignature 2 = (4, 0) ∧
  fixtureSignature 3 = (3, 1) ∧
  fixtureSignature 4 = (3, 1)

/-- The prescribed local maps cross the two signature classes by one unit. -/
def prescribedMapsCrossSignatureBoundary : Prop :=
  pi3 1 = 4 ∧
  pi3 4 = 0 ∧
  pi4 2 = 3 ∧
  pi4 3 = 0 ∧
  fixtureSignature 1 = (4, 0) ∧
  fixtureSignature (pi3 1) = (3, 1) ∧
  fixtureSignature 4 = (3, 1) ∧
  fixtureSignature (pi3 4) = (4, 0) ∧
  fixtureSignature 2 = (4, 0) ∧
  fixtureSignature (pi4 2) = (3, 1) ∧
  fixtureSignature 3 = (3, 1) ∧
  fixtureSignature (pi4 3) = (4, 0) ∧
  componentDegree denseComponent 1 = componentDegree denseComponent (pi3 1) + 1 ∧
  componentDegree singletonComponent 1 + 1 = componentDegree singletonComponent (pi3 1) ∧
  componentDegree denseComponent 4 + 1 = componentDegree denseComponent (pi3 4) ∧
  componentDegree singletonComponent 4 = componentDegree singletonComponent (pi3 4) + 1 ∧
  componentDegree denseComponent 2 = componentDegree denseComponent (pi4 2) + 1 ∧
  componentDegree singletonComponent 2 + 1 = componentDegree singletonComponent (pi4 2) ∧
  componentDegree denseComponent 3 + 1 = componentDegree denseComponent (pi4 3) ∧
  componentDegree singletonComponent 3 = componentDegree singletonComponent (pi4 3) + 1 ∧
  (∀ v : Fin 5, totalDegree v = totalDegree (pi3 v)) ∧
  (∀ v : Fin 5, totalDegree v = totalDegree (pi4 v))

/-- The coordinatewise-identical component partitions admit the identity pairing. -/
def trivialGlobalComponentPairing : Prop :=
  leftComponents 0 = rightComponents 0 ∧
  leftComponents 1 = rightComponents 1 ∧
  (Function.Bijective (fun v : Fin 5 => v)) ∧
  (∀ (i : Fin 2) (edge : Finset (Fin 5)),
    edge ∈ leftComponents i ↔
      edge.image (fun v : Fin 5 => v) ∈ rightComponents i) ∧
  pi3 1 = 4 ∧
  pi4 2 = 3 ∧
  fixtureSignature 1 = (4, 0) ∧
  fixtureSignature (pi3 1) = (3, 1) ∧
  fixtureSignature 2 = (4, 0) ∧
  fixtureSignature (pi4 2) = (3, 1)

end MathlibPlus.Open.Combinatorics
