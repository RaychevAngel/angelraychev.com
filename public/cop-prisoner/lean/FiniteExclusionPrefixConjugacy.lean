import FiniteExclusionBounds
import FiniteExclusionConjugacy

/-! Reuse a checked prefix upper bound after an explicitly verified
permutation of the vertices commuting with the first factor. -/
namespace Delivery.FiniteExclusion.PrefixConjugacy
open Bounds

def MapOK {n : Nat} {a d : Assignment n} (e : Conjugacy a d)
    (p q : List (Fin n)) : Prop :=
  ∀ i : Fin n, ∀ hi : i.val<q.length,
    ∃ hp : (e.invFun i).val<p.length, e.toFun p[(e.invFun i).val]=q[i.val]

instance {n : Nat} {a d : Assignment n} (e : Conjugacy a d)
    (p q : List (Fin n)) : Decidable (MapOK e p q) :=
  inferInstanceAs (Decidable (∀ _i : Fin n, ∀ _hi : _ < _, ∃ _hp : _ < _, _))

theorem upper {n : Nat} {a d : Assignment n} (e : Conjugacy a d)
    (p q : List (Fin n)) (bound : Nat) (mapped : MapOK e p q)
    (child : UpperPrefix d q bound) : UpperPrefix a p bound := by
  intro b valid agrees
  rw [e.score_eq b]
  apply child (e.push b) (e.valid_push b valid)
  intro i hi
  obtain ⟨hp,same⟩ := mapped i hi
  change e.toFun (b (e.invFun i))=q[i.val]
  rw [agrees (e.invFun i) hp]
  exact same

#print axioms upper
end Delivery.FiniteExclusion.PrefixConjugacy
