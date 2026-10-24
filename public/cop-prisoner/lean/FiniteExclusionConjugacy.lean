import FiniteExclusionKernel
import GraphRelabeling

/-! Transport the unconstrained second permutation while normalizing only the
first. This proves that cycle normalization preserves the entire represented
graph family and its actual game, rather than merely its first factor. -/
namespace Delivery.FiniteExclusion
open FiniteGame Extremal

structure Conjugacy {n : Nat} (a d : Assignment n) where
  toFun : Assignment n
  invFun : Assignment n
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  commute : ∀ x, toFun (a x) = d (toFun x)

namespace Conjugacy
variable {n : Nat} {a d : Assignment n} (e : Conjugacy a d)

theorem injective {x y : Fin n} (same : e.toFun x = e.toFun y) : x = y := by
  have h := congrArg e.invFun same
  simpa only [e.left_inv] using h

def push (b : Assignment n) : Assignment n := fun y => e.toFun (b (e.invFun y))

@[simp] theorem push_apply (b : Assignment n) (s : Fin n) :
    e.push b (e.toFun s) = e.toFun (b s) := by
  simp only [push,e.left_inv]

theorem valid_push (b : Assignment n) (valid : Valid a b) : Valid d (e.push b) := by
  constructor
  · intro x y same
    have inverseSame : e.invFun x = e.invFun y := valid.1 _ _ (e.injective same)
    have h := congrArg e.toFun inverseSame
    simpa only [e.right_inv] using h
  · intro y
    constructor
    · intro same
      have eq : b (e.invFun y) = e.invFun y :=
        e.injective (same.trans (e.right_inv y).symm)
      exact (valid.2 (e.invFun y)).1 eq
    · intro same
      have first : e.toFun (a (e.invFun y)) = d y := by
        rw [e.commute,e.right_inv]
      have eq : b (e.invFun y) = a (e.invFun y) := e.injective (same.trans first.symm)
      exact (valid.2 (e.invFun y)).2 eq

def graphIso (b : Assignment n) :
    GraphRelabeling.Iso (edgeOf a b) (edgeOf d (e.push b)) where
  toFun := e.toFun
  invFun := e.invFun
  left_inv := e.left_inv
  right_inv := e.right_inv
  edge_iff := by
    intro s t
    constructor
    · rintro (first | second)
      · exact Or.inl ((congrArg e.toFun first).trans (e.commute s))
      · exact Or.inr ((congrArg e.toFun second).trans (e.push_apply b s).symm)
    · rintro (first | second)
      · exact Or.inl (e.injective (first.trans (e.commute s).symm))
      · exact Or.inr (e.injective (second.trans (e.push_apply b s)))

theorem score_eq (b : Assignment n) :
    score (edgeOf a b) = score (edgeOf d (e.push b)) :=
  GraphRelabeling.score_eq (e.graphIso b)

end Conjugacy
#print axioms Conjugacy.valid_push
#print axioms Conjugacy.graphIso
#print axioms Conjugacy.score_eq
end Delivery.FiniteExclusion
