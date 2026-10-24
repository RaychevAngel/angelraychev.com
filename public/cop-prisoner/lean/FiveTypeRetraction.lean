import FiveTypeWindow

/-! Collision coverage via a represented-state retraction. This replaces
quadratic finite collision tables without discarding any initial cop. -/
namespace Delivery.FiveTypeRetraction
open LocalArena

theorem collision_iff {V R C : Type} (A : Arena R C)
    (embed : R → V) (project : V → C) (decode : C → V)
    (localCop : R → C) (outside : C)
    (alignment : ∀ r c, A.collision r c ↔ c=localCop r)
    (inside : ∀ r, localCop r≠outside)
    (project_embed : ∀ r, project (embed r)=localCop r)
    (decode_embed : ∀ r, decode (localCop r)=embed r)
    (retraction : ∀ c, project c≠outside → decode (project c)=c) :
    ∀ r c, A.collision r (project c) ↔ embed r=c := by
  intro r c
  constructor
  · intro collision
    have eq := (alignment r (project c)).mp collision
    have represented : project c≠outside := by rw [eq];exact inside r
    calc
      embed r=decode (localCop r) := (decode_embed r).symm
      _=decode (project c) := congrArg decode eq.symm
      _=c := retraction c represented
  · intro same
    exact (alignment r (project c)).mpr (same ▸ project_embed r)

#print axioms collision_iff
end Delivery.FiveTypeRetraction
