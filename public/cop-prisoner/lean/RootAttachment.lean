import FunctionalEndpoint

/-! Attaching missing pairs to roots of a functional complement. The statements
below give actual two-move delivery strategies, including pursuers in the added
part. The explicit finite construction is supplied separately. -/
namespace Delivery.RootAttachment
open FiniteGame Extremal

structure Data (V : Type) where
  old : V → Prop
  f : V → V
  roots : V → Prop
  pair : V → V → Prop
  core_closed : ∀ c, old c → old (f c)
  core_fixed : ∀ c, old c → f c ≠ c
  roots_old : ∀ u, roots u → old u
  roots_absent : ∀ c, old c → ∀ u, roots u → f c ≠ u
  pair_roots : ∀ c, ¬ old c → ∀ u, pair c u → roots u
  separate : ∀ s c, ¬ old s → ¬ old c → c ≠ s →
    ∃ u, pair c u ∧ ¬ pair s u
  spare : ∀ c, ¬ old c → ∀ s, roots s → ∃ u, pair c u ∧ u ≠ s

namespace Data
variable {V : Type} (D : Data V)

def missing (s t : V) : Prop :=
  (D.old s ∧ D.f s = t) ∨ (¬ D.old s ∧ D.pair s t)

def edge : Graph V := DenseCounting.complement D.missing

theorem missing_loopless : ∀ s, ¬ D.missing s s := by
  intro s h
  rcases h with h | h
  · exact D.core_fixed s h.1 h.2
  · exact h.1 (D.roots_old s (D.pair_roots s h.1 s h.2))

theorem loopless : Loopless D.edge := fun _ h => h.1 rfl

theorem old_edge {s t : V} (hs : D.old s) (different : s ≠ t)
    (notImage : D.f s ≠ t) : D.edge s t := by
  refine ⟨different,?_⟩
  intro h
  rcases h with h | h
  · exact notImage h.2
  · exact h.1 hs

theorem new_edge {s t : V} (hs : ¬ D.old s) (different : s ≠ t)
    (notPair : ¬ D.pair s t) : D.edge s t := by
  refine ⟨different,?_⟩
  intro h
  rcases h with h | h
  · exact hs h.1
  · exact notPair h.2

theorem old_two_move {s : V} (root : D.roots s)
    (unique : ∀ c, D.old c → D.f c = D.f s → c = s) :
    Universal D.edge (D.f s) 2 s := by
  intro c initial
  by_cases hc : D.old c
  · have first : D.edge s (D.f c) := D.old_edge (D.roots_old s root)
      (Ne.symm (D.roots_absent c hc s root))
      (fun h => initial (unique c hc h.symm))
    have last : D.edge (D.f c) (D.f s) := D.old_edge (D.core_closed c hc)
      (fun h => initial (unique c hc h))
      (fun h => D.roots_absent c hc s root (unique (D.f c) (D.core_closed c hc) h))
    exact DenseCounting.safe_intermediate_winning (Ne.symm initial) first last
      (DenseCounting.missing_arc_unreachable D.missing_loopless (Or.inl ⟨hc,rfl⟩))
  · obtain ⟨u,pu,us⟩ := D.spare c hc s root
    have ru := D.pair_roots c hc u pu
    have ou := D.roots_old u ru
    have first := D.old_edge (D.roots_old s root) (Ne.symm us)
      (D.roots_absent s (D.roots_old s root) u ru)
    have last := D.old_edge ou
      (Ne.symm (D.roots_absent s (D.roots_old s root) u ru))
      (fun h => us (unique u ou h))
    exact DenseCounting.safe_intermediate_winning (Ne.symm initial) first last
      (DenseCounting.missing_arc_unreachable D.missing_loopless (Or.inr ⟨hc,pu⟩))

theorem new_two_move {s t : V} (hs : ¬ D.old s) (target : D.pair s t) :
    Universal D.edge t 2 s := by
  intro c initial
  have rt := D.pair_roots s hs t target
  by_cases hc : D.old c
  · have ou := D.core_closed c hc
    have first : D.edge s (D.f c) := D.new_edge hs
      (fun h => hs (h ▸ ou))
      (fun h => D.roots_absent c hc (D.f c) (D.pair_roots s hs (D.f c) h) rfl)
    have last := D.old_edge ou (D.roots_absent c hc t rt)
      (D.roots_absent (D.f c) ou t rt)
    exact DenseCounting.safe_intermediate_winning (Ne.symm initial) first last
      (DenseCounting.missing_arc_unreachable D.missing_loopless (Or.inl ⟨hc,rfl⟩))
  · obtain ⟨u,pu,notPu⟩ := D.separate s c hs hc initial
    have ru := D.pair_roots c hc u pu
    have ou := D.roots_old u ru
    have first := D.new_edge hs (fun h => hs (h ▸ ou)) notPu
    have ut : u ≠ t := fun h => notPu (h ▸ target)
    have last := D.old_edge ou ut (D.roots_absent u ou t rt)
    exact DenseCounting.safe_intermediate_winning (Ne.symm initial) first last
      (DenseCounting.missing_arc_unreachable D.missing_loopless (Or.inr ⟨hc,pu⟩))

theorem old_indirect {s : V} (root : D.roots s)
    (unique : ∀ c, D.old c → D.f c = D.f s → c = s) :
    Indirect D.edge s (D.f s) :=
  ⟨Ne.symm (D.core_fixed s (D.roots_old s root)),
    fun h => h.2 (Or.inl ⟨D.roots_old s root,rfl⟩),
    universal_guaranteed (D.old_two_move root unique)⟩

theorem new_indirect {s t : V} (hs : ¬ D.old s) (target : D.pair s t) :
    Indirect D.edge s t :=
  ⟨fun h => hs (h ▸ D.roots_old t (D.pair_roots s hs t target)),
    fun h => h.2 (Or.inr ⟨hs,target⟩),
    universal_guaranteed (D.new_two_move hs target)⟩

#print axioms old_two_move
#print axioms new_two_move
end Data
end Delivery.RootAttachment
