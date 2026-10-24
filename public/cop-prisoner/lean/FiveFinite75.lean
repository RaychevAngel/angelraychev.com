import FiveFinite75Target0
import FiveFinite75Target1
import FiveFinite75Target2
import FiveFinite75Target3
import FiveFinite75Target4
namespace Delivery.FiveFinite75
open FiniteGame Extremal FiveFinite75Base

theorem representatives (t : Fin 75) (small : t.val<5) (G : Graph (Fin 75))
    (low : RobustTwoMove.Subgraph lower G) (high : RobustTwoMove.Subgraph G upper)
    (s : Fin 75) : Guaranteed G s t := by
  have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by
    have values : t.val=0 ∨ t.val=1 ∨ t.val=2 ∨ t.val=3 ∨ t.val=4 := by omega
    rcases values with h|h|h|h|h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))
  rcases cases with rfl|rfl|rfl|rfl|rfl
  · exact FiveFinite75Target0.guaranteed low high s
  · exact FiveFinite75Target1.guaranteed low high s
  · exact FiveFinite75Target2.guaranteed low high s
  · exact FiveFinite75Target3.guaranteed low high s
  · exact FiveFinite75Target4.guaranteed low high s
theorem delivers : GuaranteedPrefix.Delivers lower upper := by
  apply EnvelopeSymmetry.delivers lower upper (fun t => t.val<5) representatives
  intro t
  exact ⟨representative t,representative_small t,rotation t,upper_invariant t,target_cover t⟩
theorem maximum {m : Nat} (low : 150≤m) (high : m≤225) :
    IsMaximum 75 m (75*(75-1)-m) :=
  GuaranteedPrefix.maximum lower upper inclusion loopless delivers
    (by rw [counts.1];exact low) (by rw [counts.2];exact high)
#print axioms delivers
#print axioms maximum
end Delivery.FiveFinite75
