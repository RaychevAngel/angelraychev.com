import FiveFinite65Target0
import FiveFinite65Target1
import FiveFinite65Target2
import FiveFinite65Target3
import FiveFinite65Target4
namespace Delivery.FiveFinite65
open FiniteGame Extremal FiveFinite65Base

theorem representatives (t : Fin 65) (small : t.val<5) (G : Graph (Fin 65))
    (low : RobustTwoMove.Subgraph lower G) (high : RobustTwoMove.Subgraph G upper)
    (s : Fin 65) : Guaranteed G s t := by
  have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by
    have values : t.val=0 ∨ t.val=1 ∨ t.val=2 ∨ t.val=3 ∨ t.val=4 := by omega
    rcases values with h|h|h|h|h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))
  rcases cases with rfl|rfl|rfl|rfl|rfl
  · exact FiveFinite65Target0.guaranteed low high s
  · exact FiveFinite65Target1.guaranteed low high s
  · exact FiveFinite65Target2.guaranteed low high s
  · exact FiveFinite65Target3.guaranteed low high s
  · exact FiveFinite65Target4.guaranteed low high s
theorem delivers : GuaranteedPrefix.Delivers lower upper := by
  apply EnvelopeSymmetry.delivers lower upper (fun t => t.val<5) representatives
  intro t
  exact ⟨representative t,representative_small t,rotation t,upper_invariant t,target_cover t⟩
theorem maximum {m : Nat} (low : 130≤m) (high : m≤195) :
    IsMaximum 65 m (65*(65-1)-m) :=
  GuaranteedPrefix.maximum lower upper inclusion loopless delivers
    (by rw [counts.1];exact low) (by rw [counts.2];exact high)
#print axioms delivers
#print axioms maximum
end Delivery.FiveFinite65
