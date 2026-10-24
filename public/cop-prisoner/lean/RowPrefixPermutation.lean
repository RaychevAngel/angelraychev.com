import RowPrefixSymmetry

/-! A checked prefix relabeling may permute completed rows. This allows a DAG
of isomorphic prefixes without dropping any row choices. -/
namespace Delivery.RowPrefix
open FiniteGame Extremal DenseCombinatorics SparseSupport

theorem card_bijection (f g : Fin n → Fin n)
    (gf : ∀ x, g (f x) = x) (fg : ∀ x, f (g x) = x) (P : Fin n → Prop) :
    card (fun x => P (f x)) = card P := by
  apply Nat.le_antisymm
  · apply card_injection f (fun _ h => h)
    intro x y _ _ same
    have eq := congrArg g same
    simpa only [gf] using eq
  · apply card_injection g (fun x h => by simpa only [fg] using h)
    intro x y _ _ same
    have eq := congrArg f same
    simpa only [fg] using eq

def PermMapOK (D R : Fin n → Nat) (p q : List Nat) (f g : Fin n → Fin n) : Prop :=
  (∀ x, g (f x) = x ∧ f (g x) = x) ∧
  (∀ x, D (f x) = D x ∧ R (f x) = R x) ∧
  (∀ s : Fin n, s.val < q.length → (f s).val < p.length) ∧
  (∀ s : Fin n, ∀ hq : s.val < q.length, ∀ hp : (f s).val < p.length, ∀ t,
    bit p[(f s).val] (f t) ↔ bit q[s.val] t)
instance (D R : Fin n → Nat) (p q : List Nat) (f g : Fin n → Fin n) :
    Decidable (PermMapOK D R p q f g) := inferInstanceAs (Decidable (_ ∧ _))

theorem permutation_upper (D R : Fin n → Nat) (p q : List Nat)
    (f g : Fin n → Fin n) (bound : Nat) (checked : PermMapOK D R p q f g)
    (child : Upper D R q bound) : Upper D R p bound := by
  intro E valid agrees
  let F : Graph (Fin n) := fun s t => E (f s) (f t)
  have gf : ∀ x, g (f x) = x := fun x => (checked.1 x).1
  have fg : ∀ x, f (g x) = x := fun x => (checked.1 x).2
  let iso : GraphRelabeling.Iso E F := {
    toFun := g
    invFun := f
    left_inv := fg
    right_inv := gf
    edge_iff := fun s t => by simp only [F,fg] }
  have prescribed : Prescribed D R F := by
    refine ⟨iso.loopless valid.1,?_,?_⟩
    · intro s
      change card (fun t => E (f s) (f t)) = D s
      rw [card_bijection f g gf fg]
      exact (valid.2.1 (f s)).trans (checked.2.1 s).1
    · intro t
      change card (fun s => E (f s) (f t)) = R t
      rw [card_bijection f g gf fg (fun s => E s (f t))]
      exact (valid.2.2 (f t)).trans (checked.2.1 t).2
  have mapped : Agrees q F := by
    intro s hq t
    have hp := checked.2.2.1 s hq
    change E (f s) (f t) ↔ bit q[s.val] t
    rw [agrees (f s) hp (f t)]
    exact checked.2.2.2 s hq hp t
  rw [GraphRelabeling.score_eq iso]
  exact child F prescribed mapped

#print axioms permutation_upper
end Delivery.RowPrefix
