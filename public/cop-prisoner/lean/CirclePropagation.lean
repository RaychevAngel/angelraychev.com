import RobustLayers
import CyclicOrbit

/-! The five-offset circle propagation, with all alternating-game steps.
The only exposed construction obligations are three local escape properties
and finite orbit coverage; concrete envelope arithmetic is separate. -/
namespace Delivery.CirclePropagation
open CyclicArithmetic RobustTwoMove

def Compulsory (h d : Nat) : Prop :=
  d = 1 ∨ d = h-3 ∨ d = h-2 ∨ d = h ∨ d = h+2

def Base {n : Nat} (h : Nat) (s t : Fin n) : Prop :=
  ∃ d, Compulsory h d ∧ t = shift s d

def Escape {n : Nat} (E : Graph (Fin n)) (h : Nat) : Prop :=
  (∀ s c, c ≠ s → ¬ (Legal E c (shift s h) ∧ Legal E c (shift s 1))) ∧
  (∀ s c, c ≠ s → ¬ (Legal E c (shift s h) ∧
    Legal E c (shift s (h-3)) ∧ Legal E c (shift s (h-2)))) ∧
  (∀ s c, c ≠ s → ¬ (Legal E c (shift s h) ∧
    Legal E c (shift s (h-2)) ∧ Legal E c (shift s (h+2))))

def retreat {n : Nat} (x : Fin n) (d : Nat) : Fin n := shift x (n-d)

theorem retreat_cancel {n d : Nat} (x : Fin n) (small : d ≤ n) :
    shift (retreat x d) d = x := by
  rw [retreat,shift_add,show n-d+d=n by omega,shift_period]

theorem retreat_offsets {n r a d b : Nat} (x : Fin n) (small : r ≤ n)
    (offsets : a+d = r+b) : shift (shift (retreat x r) a) d = shift x b := by
  rw [shift_add,offsets,← shift_add,retreat_cancel x small]

variable {n h : Nat} {B E G : Graph (Fin n)}

/-- A pair or triple of winning alternatives needs only their maximum rank. -/
theorem two_successors {t s a b : Fin n} {K : Nat}
    (lower : Subgraph B G) (upper : Subgraph G E)
    (ea : B s a) (eb : B s b)
    (escape : ∀ c, c ≠ s → ¬ (Legal E c a ∧ Legal E c b))
    (wa : Universal G t K a) (wb : Universal G t K b) : Universal G t (K+1) s := by
  intro c initial
  by_cases safe : ¬ Legal E c a
  · exact safe_successor (Ne.symm initial) (lower _ _ ea)
      (fun move => safe (move.elim Or.inl (fun edge => Or.inr (upper _ _ edge)))) wa
  · have reachable : Legal E c a := Classical.byContradiction safe
    have sb : ¬ Legal E c b := fun hb => escape c initial ⟨reachable,hb⟩
    exact safe_successor (Ne.symm initial) (lower _ _ eb)
      (fun move => sb (move.elim Or.inl (fun edge => Or.inr (upper _ _ edge)))) wb

theorem three_successors {t s a b d : Fin n} {K : Nat}
    (lower : Subgraph B G) (upper : Subgraph G E)
    (ea : B s a) (eb : B s b) (ed : B s d)
    (escape : ∀ c, c ≠ s → ¬ (Legal E c a ∧ Legal E c b ∧ Legal E c d))
    (wa : Universal G t K a) (wb : Universal G t K b) (wd : Universal G t K d) :
    Universal G t (K+1) s := by
  intro c initial
  by_cases sa : ¬ Legal E c a
  · exact safe_successor (Ne.symm initial) (lower _ _ ea)
      (fun move => sa (move.elim Or.inl (fun edge => Or.inr (upper _ _ edge)))) wa
  by_cases sb : ¬ Legal E c b
  · exact safe_successor (Ne.symm initial) (lower _ _ eb)
      (fun move => sb (move.elim Or.inl (fun edge => Or.inr (upper _ _ edge)))) wb
  have sd : ¬ Legal E c d := fun hd => escape c initial
    ⟨Classical.byContradiction sa,Classical.byContradiction sb,hd⟩
  exact safe_successor (Ne.symm initial) (lower _ _ ed)
    (fun move => sd (move.elim Or.inl (fun edge => Or.inr (upper _ _ edge)))) wd

def Pattern (G : Graph (Fin n)) (t : Fin n) (K : Nat) (w : Fin n) : Prop :=
  Universal G t K w ∧ Universal G t K (shift w 1) ∧
    Universal G t K (shift w 2) ∧ Universal G t K (shift w 4)

theorem base_move (s : Fin n) (d : Nat) (member : Compulsory h d) : Base h s (shift s d) :=
  ⟨d,member,rfl⟩

theorem pattern_step (hh : 7 ≤ h) (small : h ≤ n)
    (lower : Subgraph (Base h) G) (upper : Subgraph G E) (escapes : Escape E h)
    {t w : Fin n} {K : Nat} (wins : Pattern G t K w) :
    Pattern G t (K+3) (retreat w h) := by
  have h1 : Compulsory h 1 := Or.inl rfl
  have hm3 : Compulsory h (h-3) := Or.inr (Or.inl rfl)
  have hm2 : Compulsory h (h-2) := Or.inr (Or.inr (Or.inl rfl))
  have hh0 : Compulsory h h := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have hp2 : Compulsory h (h+2) := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  let v := retreat w h
  have step4 : Universal G t (K+1) (shift v 4) := by
    apply three_successors lower upper (base_move _ _ hh0) (base_move _ _ hm3)
      (base_move _ _ hm2) (escapes.2.1 (shift v 4))
    · simpa only [v,retreat_offsets w small (show 4+h=h+4 by omega)] using wins.2.2.2
    · simpa only [v,retreat_offsets w small (show 4+(h-3)=h+1 by omega)] using wins.2.1
    · simpa only [v,retreat_offsets w small (show 4+(h-2)=h+2 by omega)] using wins.2.2.1
  have step2 : Universal G t (K+1) (shift v 2) := by
    apply three_successors lower upper (base_move _ _ hh0) (base_move _ _ hm2)
      (base_move _ _ hp2) (escapes.2.2 (shift v 2))
    · simpa only [v,retreat_offsets w small (show 2+h=h+2 by omega)] using wins.2.2.1
    · simpa only [v,retreat_offsets w small (show 2+(h-2)=h+0 by omega),shift_zero] using wins.1
    · simpa only [v,retreat_offsets w small (show 2+(h+2)=h+4 by omega)] using wins.2.2.2
  have step1 : Universal G t (K+2) (shift v 1) := by
    apply two_successors lower upper (base_move _ _ hh0) (base_move _ _ h1)
      (escapes.1 (shift v 1))
    · apply universal_mono (k := K) ?_ (by omega)
      simpa only [v,retreat_offsets w small (show 1+h=h+1 by omega)] using wins.2.1
    · simpa only [shift_add] using step2
  have step0 : Universal G t (K+3) v := by
    apply two_successors lower upper (base_move _ _ hh0) (base_move _ _ h1) (escapes.1 v)
    · apply universal_mono (k := K) ?_ (by omega)
      simpa only [v,retreat_cancel w small] using wins.1
    · exact step1
  exact ⟨step0,universal_mono step1 (by omega),universal_mono step2 (by omega),
    universal_mono step4 (by omega)⟩

theorem initial_pattern (hh : 7 ≤ h) (small : h+2 ≤ n)
    (lower : Subgraph (Base h) G) (upper : Subgraph G E) (escapes : Escape E h)
    (t : Fin n) : Pattern G t 2 (retreat t (h+2)) := by
  have h1 : Compulsory h 1 := Or.inl rfl
  have hm2 : Compulsory h (h-2) := Or.inr (Or.inr (Or.inl rfl))
  have hh0 : Compulsory h h := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have hp2 : Compulsory h (h+2) := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  let w := retreat t (h+2)
  have direct0 : Universal G t 1 w := by
    have arrow := lower w (shift w (h+2)) (base_move _ _ hp2)
    simpa only [w,retreat_cancel t small] using universal_direct arrow
  have direct2 : Universal G t 1 (shift w 2) := by
    have arrow := lower (shift w 2) (shift (shift w 2) h) (base_move _ _ hh0)
    simpa only [w,retreat_offsets t small (show 2+h=(h+2)+0 by omega),shift_zero]
      using universal_direct arrow
  have direct4 : Universal G t 1 (shift w 4) := by
    have arrow := lower (shift w 4) (shift (shift w 4) (h-2)) (base_move _ _ hm2)
    simpa only [w,retreat_offsets t small (show 4+(h-2)=(h+2)+0 by omega),shift_zero]
      using universal_direct arrow
  have indirect1 : Universal G t 2 (shift w 1) := by
    apply two_successors lower upper (base_move _ _ hh0) (base_move _ _ h1)
      (escapes.1 (shift w 1))
    · have arrow := lower (shift (shift w 1) h) (shift (shift (shift w 1) h) 1) (base_move _ _ h1)
      have endAt : shift (shift (shift w 1) h) 1 = t := by
        rw [shift_add]
        simp only [w,retreat_offsets t small (show 1+(h+1)=(h+2)+0 by omega),shift_zero]
      rw [endAt] at arrow
      exact universal_direct arrow
    · simpa only [shift_add] using direct2
  exact ⟨universal_mono direct0 (by omega),indirect1,
    universal_mono direct2 (by omega),universal_mono direct4 (by omega)⟩


theorem iterated_pattern (hh : 7 ≤ h) (small : h+2 ≤ n)
    (lower : Subgraph (Base h) G) (upper : Subgraph G E) (escapes : Escape E h)
    (t : Fin n) (j : Nat) :
    Pattern G t (2+3*j) (shift (retreat t (h+2)) (j*(n-h))) := by
  induction j with
  | zero => simpa using initial_pattern hh small lower upper escapes t
  | succ j ih =>
    have step := pattern_step hh (by omega : h ≤ n) lower upper escapes ih
    have rankEq : 2+3*(j+1) = (2+3*j)+3 := by omega
    have advance : (j+1)*(n-h) = j*(n-h)+(n-h) := Nat.succ_mul j (n-h)
    rw [rankEq,advance]
    simpa only [retreat,shift_add,Nat.add_assoc] using step

/-- Any proved coverage of the retreat orbit closes the finite propagation.
The resulting uniform rank is at most 3n−1 messenger moves. -/
theorem universal_of_orbit (hh : 7 ≤ h) (small : h+2 ≤ n)
    (lower : Subgraph (Base h) G) (upper : Subgraph G E) (escapes : Escape E h)
    (orbit : ∀ a b : Fin n, ∃ j : Fin n, shift a (j.val*(n-h)) = b)
    (t s : Fin n) : Universal G t (3*n-1) s := by
  obtain ⟨j,atSource⟩ := orbit (retreat t (h+2)) s
  have win := (iterated_pattern hh small lower upper escapes t j.val).1
  rw [atSource] at win
  exact universal_mono win (by have := j.isLt; omega)


/-- The complete five-offset propagation theorem. No rank or orbit certificate
is supplied: coprimality and the three local escape checks suffice. -/
theorem universal (hh : 7 ≤ h) (small : h+2 ≤ n) (coprime : Nat.Coprime n h)
    (lower : Subgraph (Base h) G) (upper : Subgraph G E) (escapes : Escape E h)
    (t s : Fin n) : Universal G t (3*n-1) s :=
  universal_of_orbit hh small lower upper escapes
    (CyclicOrbit.retreat_orbit coprime (by omega)) t s

#print axioms pattern_step
#print axioms universal

end Delivery.CirclePropagation
