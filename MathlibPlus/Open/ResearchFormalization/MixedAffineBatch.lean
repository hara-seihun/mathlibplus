import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.MixedAffineBatch

abbrev F3 := ZMod 3
abbrev Plane := F3 × F3
abbrev Vec3 := Fin 3 → F3
abbrev E := F3 × (Plane × Vec3)

def dot (u v : Vec3) : F3 := ∑ k, u k * v k

def quadraticPeriod (x : Plane) : Vec3 :=
  let i := x.1
  let j := x.2
  ![i * (i - 1), (2 * i - 1) * j, j ^ 2]

def mixedTransporter (f : Plane → F3) (F : Plane → Vec3) (e : E) : E :=
  let z := e.1
  let x := e.2.1
  let u := e.2.2
  (z + f x + dot (F x) u, (x, u + quadraticPeriod x))

/-- Claim 30107: the normalized mixed affine transporter family. -/
def claim30107 : Prop :=
  ∀ (f : Plane → F3) (F : Plane → Vec3),
    f 0 = 0 → F 0 = 0 → Function.Bijective (mixedTransporter f F)

end MathlibPlus.Open.ResearchFormalization.MixedAffineBatch
