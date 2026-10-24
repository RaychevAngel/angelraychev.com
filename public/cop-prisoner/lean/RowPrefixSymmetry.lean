import RowPrefixKernel

/-! Explicit checked involutions route every possible next row to a retained
child. They preserve degrees, completed rows, and all incoming prefix bits. -/
namespace Delivery.RowPrefix
open FiniteGame Extremal DenseCombinatorics SparseSupport

theorem card_pullback {n : Nat} (f : Fin n → Fin n)
    (inverse : ∀ x, f (f x) = x) (P : Fin n → Prop) :
    card (fun x => P (f x)) = card P := by
  apply Nat.le_antisymm
  · apply card_injection f (fun _ h => h)
    intro x y _ _ same
    have eq := congrArg f same
    simpa only [inverse] using eq
  · apply card_injection f (fun x h => by simpa only [inverse] using h)
    intro x y _ _ same
    have eq := congrArg f same
    simpa only [inverse] using eq

def MapOK {n : Nat} (D R : Fin n → Nat) (p q : List Nat) (f : Fin n → Fin n) : Prop :=
  (∀ x, f (f x) = x) ∧
  (∀ x, D (f x) = D x ∧ R (f x) = R x) ∧
  p.length = q.length ∧
  (∀ s : Fin n, s.val < p.length → f s = s) ∧
  (∀ s : Fin n, ∀ hp : s.val < p.length, ∀ hq : s.val < q.length, ∀ t,
    bit p[s.val] t ↔ bit q[s.val] (f t))
instance {n : Nat} (D R : Fin n → Nat) (p q : List Nat) (f : Fin n → Fin n) :
    Decidable (MapOK D R p q f) := inferInstanceAs (Decidable (_ ∧ _))

theorem map_upper {n : Nat} (D R : Fin n → Nat) (p q : List Nat)
    (f : Fin n → Fin n) (bound : Nat) (checked : MapOK D R p q f)
    (child : Upper D R q bound) : Upper D R p bound := by
  intro E valid agrees
  let F : Graph (Fin n) := fun s t => E (f s) (f t)
  have inverse := checked.1
  let iso : GraphRelabeling.Iso E F := {
    toFun := f
    invFun := f
    left_inv := inverse
    right_inv := inverse
    edge_iff := fun s t => by simp only [F,inverse] }
  have prescribed : Prescribed D R F := by
    refine ⟨iso.loopless valid.1,?_,?_⟩
    · intro s
      change card (fun t => E (f s) (f t)) = D s
      rw [card_pullback f inverse]
      exact (valid.2.1 (f s)).trans (checked.2.1 s).1
    · intro t
      change card (fun s => E (f s) (f t)) = R t
      rw [card_pullback f inverse (fun s => E s (f t))]
      exact (valid.2.2 (f t)).trans (checked.2.1 t).2
  have mapped : Agrees q F := by
    intro s hq t
    have length := checked.2.2.1
    have hp : s.val < p.length := by omega
    change E (f s) (f t) ↔ bit q[s.val] t
    rw [checked.2.2.2.1 s hp,agrees s hp (f t)]
    simpa only [inverse] using checked.2.2.2.2 s hp hq (f t)
  rw [GraphRelabeling.score_eq iso]
  exact child F prescribed mapped

abbrev Route (n : Nat) := Nat → Nat × (Fin n → Fin n)

def RoutesOK {n : Nat} (D R : Fin n → Nat) (p : List Nat)
    (rows representatives : List Nat) (route : Route n) : Prop :=
  ∀ mask ∈ rows,
    ¬PrefixOK D R (p++[mask]) ∨
    ((route mask).1 ∈ representatives ∧
      MapOK D R (p++[mask]) (p++[(route mask).1]) (route mask).2)
instance {n : Nat} (D R : Fin n → Nat) (p : List Nat)
    (rows representatives : List Nat) (route : Route n) :
    Decidable (RoutesOK D R p rows representatives route) :=
  inferInstanceAs (Decidable (∀ mask ∈ rows, _))

theorem routed_branch {n : Nat} (D R : Fin n → Nat) (p : List Nat) (bound : Nat)
    (h : p.length < n) (rows representatives : List Nat) (route : Route n)
    (cover : RowCover n (D ⟨p.length,h⟩) rows)
    (checked : RoutesOK D R p rows representatives route)
    (children : ∀ mask ∈ representatives, Upper D R (p++[mask]) bound) :
    Upper D R p bound := by
  apply branch_upper D R p bound h rows cover
  intro mask member
  rcases checked mask member with invalid | ⟨listed,mapping⟩
  · exact invalid_upper D R _ bound invalid
  · exact map_upper D R _ _ (route mask).2 bound mapping
      (children (route mask).1 listed)

#print axioms map_upper
#print axioms routed_branch
end Delivery.RowPrefix
