import SparseSupported

/-! Padding by sinks preserves every old indirect pair. If each added sink has
at most one predecessor, it creates no new indirect pair. The proof treats a
pursuer entering or starting at an added sink explicitly. -/
namespace Delivery.GraphPadding
open FiniteGame Extremal DenseCombinatorics ConstructionCounts SparseSupport
open GraphRestriction

def extension {V W : Type} (E : Graph V) (A : V → W → Prop) : Graph (Sum V W)
  | .inl s, .inl t => E s t
  | .inl s, .inr t => A s t
  | .inr _, _ => False

theorem legal_old {V W : Type} (E : Graph V) (A : V → W → Prop) (s t : V) :
    Legal (extension E A) (.inl s) (.inl t) ↔ Legal E s t := by
  constructor
  · rintro (same | edge)
    · exact Or.inl (Sum.inl.inj same)
    · exact Or.inr edge
  · rintro (same | edge)
    · exact Or.inl (congrArg Sum.inl same)
    · exact Or.inr edge

/-- Follow stationary replies in an old winning tree. Against a trapped cop
these supply a valid route with the same rank bound. -/
theorem winning_trapped {V W : Type} {E : Graph V} (A : V → W → Prop)
    {t r c : V} {k : Nat} (win : Winning E t k r c) (w : W) :
    Winning (extension E A) (.inl t) k (.inl r) (.inr w) := by
  induction win with
  | delivered => exact Winning.delivered
  | finish _ move =>
    exact Winning.finish (by intro same; cases same) ((legal_old E A _ _).mpr move)
  | @step k r c z _ move _ _ next ih =>
    apply Winning.step (z := Sum.inl z) (by intro same; cases same)
      ((legal_old E A _ _).mpr move) (by intro same; cases same)
    · intro c' reply same
      rcases reply with equal | edge
      · cases equal; cases same
      · exact False.elim edge
    · intro c' reply
      rcases reply with equal | edge
      · cases equal; exact ih c (legal_wait E c)
      · exact False.elim edge

theorem winning_lift {V W : Type} {E : Graph V} (A : V → W → Prop)
    {t r c : V} {k : Nat} (win : Winning E t k r c) :
    Winning (extension E A) (.inl t) k (.inl r) (.inl c) := by
  induction win with
  | delivered => exact Winning.delivered
  | finish distinct move =>
    exact Winning.finish (fun same => distinct (Sum.inl.inj same))
      ((legal_old E A _ _).mpr move)
  | @step k r c z distinct move safeNow safeReply next ih =>
    apply Winning.step (z := Sum.inl z) (fun same => distinct (Sum.inl.inj same))
      ((legal_old E A _ _).mpr move) (fun same => safeNow (Sum.inl.inj same))
    · intro c' reply same
      cases c' with
      | inl c' => exact safeReply c' ((legal_old E A _ _).mp reply) (Sum.inl.inj same)
      | inr _ => cases same
    · intro c' reply
      cases c' with
      | inl c' => exact ih c' ((legal_old E A _ _).mp reply)
      | inr w => exact winning_trapped A (next c (legal_wait E c)) w

def Old {V W : Type} : Sum V W → Prop
  | .inl _ => True
  | .inr _ => False

theorem old_backward {V W : Type} (E : Graph V) (A : V → W → Prop) :
    BackwardClosed (extension E A) Old := by
  intro x y target edge
  cases x with
  | inl _ => trivial
  | inr _ => exact False.elim edge

def oldIso {V W : Type} (E : Graph V) (A : V → W → Prop) :
    GraphRelabeling.Iso E (induced (extension E A) Old) where
  toFun := fun x => ⟨.inl x,trivial⟩
  invFun := fun x => match x with
    | ⟨.inl v,_⟩ => v
    | ⟨.inr _,impossible⟩ => False.elim impossible
  left_inv := by intro x; rfl
  right_inv := by
    intro x
    rcases x with ⟨x,hx⟩
    cases x with
    | inl _ => rfl
    | inr _ => exact False.elim hx
  edge_iff := by intro x y; rfl

theorem winning_restrict_old {V W : Type} {E : Graph V} (A : V → W → Prop)
    {t r c : V} {k : Nat}
    (win : Winning (extension E A) (.inl t) k (.inl r) (.inl c)) : Winning E t k r c := by
  have restricted := winning_backward (old_backward E A) win trivial trivial trivial
  exact (oldIso E A).symm.winning restricted

theorem old_indirect_iff {V W : Type} (E : Graph V) (A : V → W → Prop) (s t : V) :
    Indirect (extension E A) (.inl s) (.inl t) ↔ Indirect E s t := by
  constructor
  · intro pair
    refine ⟨fun same => pair.1 (congrArg Sum.inl same),pair.2.1,?_⟩
    intro c initial
    obtain ⟨k,win⟩ := pair.2.2 (.inl c) (fun same => initial (Sum.inl.inj same))
    exact ⟨k,winning_restrict_old A win⟩
  · intro pair
    refine ⟨fun same => pair.1 (Sum.inl.inj same),pair.2.1,?_⟩
    intro c initial
    cases c with
    | inl c =>
      obtain ⟨k,win⟩ := pair.2.2 c (fun same => initial (congrArg Sum.inl same))
      exact ⟨k,winning_lift A win⟩
    | inr w =>
      obtain ⟨k,win⟩ := pair.2.2 t (Ne.symm pair.1)
      exact ⟨k,winning_trapped A win w⟩

theorem no_new_source {V W : Type} (E : Graph V) (A : V → W → Prop)
    (s : W) (t : Sum V W) : ¬ Indirect (extension E A) (.inr s) t :=
  no_indirect_from_sink (.inr s) (fun _ h => h) t

theorem no_new_target {V W : Type} (E : Graph V) (A : V → W → Prop)
    (unique : ∀ t a b, A a t → A b t → a=b) (s : Sum V W) (t : W) :
    ¬ Indirect (extension E A) s (.inr t) := by
  intro pair
  obtain ⟨a,b,ha,hb,different⟩ := live_recipient_two_predecessors pair
  cases a with
  | inr _ => exact ha
  | inl a =>
    cases b with
    | inr _ => exact hb
    | inl b => exact different (congrArg Sum.inl (unique t a b ha hb))

def graph {n k : Nat} (E : Graph (Fin n)) (A : Fin n → Fin k → Prop) : Graph (Fin (n+k)) :=
  fun s t => extension E A (ComplementarySum.decode s) (ComplementarySum.decode t)

def graphIso {n k : Nat} (E : Graph (Fin n)) (A : Fin n → Fin k → Prop) :
    GraphRelabeling.Iso (extension E A) (graph E A) where
  toFun := ComplementarySum.encode
  invFun := ComplementarySum.decode
  left_inv := ComplementarySum.decode_encode
  right_inv := ComplementarySum.encode_decode
  edge_iff := by intro s t; simp [graph]

theorem loopless {n k : Nat} {E : Graph (Fin n)} (h : Loopless E)
    (A : Fin n → Fin k → Prop) : Loopless (graph E A) := by
  apply (graphIso E A).loopless
  intro x edge
  cases x with
  | inl x => exact h x edge
  | inr _ => exact edge

theorem graph_old_indirect_iff {n k : Nat} (E : Graph (Fin n))
    (A : Fin n → Fin k → Prop) (s t : Fin n) :
    Indirect (graph E A) (ComplementarySum.left n k s) (ComplementarySum.left n k t) ↔
      Indirect E s t :=
  ((graphIso E A).indirect_iff (.inl s) (.inl t)).symm.trans (old_indirect_iff E A s t)

theorem graph_no_new_source {n k : Nat} (E : Graph (Fin n))
    (A : Fin n → Fin k → Prop) (s : Fin k) (t : Fin (n+k)) :
    ¬ Indirect (graph E A) (ComplementarySum.right n k s) t := by
  intro pair
  have old := (graphIso E A).symm.indirect_iff _ _ |>.mp pair
  change Indirect (extension E A) ((graphIso E A).invFun (ComplementarySum.right n k s))
    ((graphIso E A).invFun t) at old
  have same : (graphIso E A).invFun (ComplementarySum.right n k s)=Sum.inr s :=
    ComplementarySum.decode_right s
  rw [same] at old
  exact no_new_source E A s _ old

theorem graph_no_new_target {n k : Nat} (E : Graph (Fin n))
    (A : Fin n → Fin k → Prop) (unique : ∀ t a b, A a t → A b t → a=b)
    (s : Fin (n+k)) (t : Fin k) :
    ¬ Indirect (graph E A) s (ComplementarySum.right n k t) := by
  intro pair
  have old := (graphIso E A).symm.indirect_iff _ _ |>.mp pair
  change Indirect (extension E A) ((graphIso E A).invFun s)
    ((graphIso E A).invFun (ComplementarySum.right n k t)) at old
  have same : (graphIso E A).invFun (ComplementarySum.right n k t)=Sum.inr t :=
    ComplementarySum.decode_right t
  rw [same] at old
  exact no_new_target E A unique _ t old

theorem sum_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map fun x => f x+g x).sum=(xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,ih]
    omega

theorem sum_zero {α : Type} (xs : List α) : (xs.map fun _ => 0).sum=0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih,Nat.zero_add]

theorem arc_count {n k : Nat} (E : Graph (Fin n)) (A : Fin n → Fin k → Prop) :
    arcCount (graph E A) = arcCount E + ((List.finRange n).map fun s => card (A s)).sum := by
  have oldRow (s : Fin n) : card (graph E A (ComplementarySum.left n k s)) =
      card (E s)+card (A s) := by
    rw [ComplementarySum.card_split]
    simp only [graph,ComplementarySum.decode_left,ComplementarySum.decode_right,extension]
  have newRow (s : Fin k) : card (graph E A (ComplementarySum.right n k s))=0 := by
    apply card_eq_zero.mpr
    intro t edge
    simp only [graph,ComplementarySum.decode_right,extension] at edge
  rw [arc_rows,ComplementarySum.sum_split]
  simp only [oldRow,newRow,sum_zero,Nat.add_zero]
  rw [sum_add,← arc_rows]

/-- Exact preservation, not merely a lower bound: old pairs are equivalent
and every added row or column is empty of indirect guarantees. -/
theorem score_eq {n k : Nat} (E : Graph (Fin n)) (A : Fin n → Fin k → Prop)
    (unique : ∀ t a b, A a t → A b t → a=b) : score (graph E A)=score E := by
  have oldRow (s : Fin n) : card (Indirect (graph E A) (ComplementarySum.left n k s))=
      card (Indirect E s) := by
    rw [ComplementarySum.card_split]
    have old := card_congr (graph_old_indirect_iff E A s)
    have new : card (fun t => Indirect (graph E A)
        (ComplementarySum.left n k s) (ComplementarySum.right n k t))=0 :=
      card_eq_zero.mpr (graph_no_new_target E A unique _)
    omega
  have newRow (s : Fin k) : card (Indirect (graph E A) (ComplementarySum.right n k s))=0 :=
    card_eq_zero.mpr (graph_no_new_source E A s)
  rw [score_rows,ComplementarySum.sum_split]
  simp only [oldRow,newRow,sum_zero,Nat.add_zero]
  exact (score_rows E).symm

def isolates {n : Nat} (E : Graph (Fin n)) (k : Nat) : Graph (Fin (n+k)) :=
  graph E (fun _ _ => False)

theorem isolates_loopless {n : Nat} {E : Graph (Fin n)} (h : Loopless E) (k : Nat) :
    Loopless (isolates E k) := loopless h _

theorem isolates_arcs {n : Nat} (E : Graph (Fin n)) (k : Nat) :
    arcCount (isolates E k)=arcCount E := by
  unfold isolates
  rw [arc_count]
  simp only [card_false,sum_zero,Nat.add_zero]

theorem isolates_score {n : Nat} (E : Graph (Fin n)) (k : Nat) :
    score (isolates E k)=score E := score_eq E _ (fun _ _ _ h => False.elim h)

/-- Every added vertex is a sink with its unique incoming arrow from v. -/
def sinks {n : Nat} (E : Graph (Fin n)) (v : Fin n) (k : Nat) : Graph (Fin (n+k)) :=
  graph E (fun s _ => s=v)

theorem sinks_loopless {n : Nat} {E : Graph (Fin n)} (h : Loopless E) (v : Fin n) (k : Nat) :
    Loopless (sinks E v k) := loopless h _

theorem sinks_arcs {n : Nat} (E : Graph (Fin n)) (v : Fin n) (k : Nat) :
    arcCount (sinks E v k)=arcCount E+k := by
  classical
  unfold sinks
  rw [arc_count]
  have row (s : Fin n) : card (fun _ : Fin k => s=v) = if s=v then k else 0 := by
    by_cases same : s=v
    · simp only [same,if_true,card_true]
    · simp only [same,if_false,card_false]
  simp only [row]
  rw [indicator_sum,SparseDeletion.card_singleton,Nat.mul_one]

theorem sinks_score {n : Nat} (E : Graph (Fin n)) (v : Fin n) (k : Nat) :
    score (sinks E v k)=score E := score_eq E _ (fun _ _ _ a b => a.trans b.symm)

theorem pad_to_order {n N : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (order : n ≤ N) : ∃ F : Graph (Fin N), Loopless F ∧ arcCount F=arcCount E ∧ score F=score E := by
  have result : ∃ F : Graph (Fin (n+(N-n))), Loopless F ∧ arcCount F=arcCount E ∧ score F=score E :=
    ⟨isolates E (N-n),isolates_loopless loopless _,isolates_arcs E _,isolates_score E _⟩
  have size : n+(N-n)=N := by omega
  rw [size] at result
  exact result

theorem add_one_arrow {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E) (v : Fin n) :
    ∃ F : Graph (Fin (n+1)), Loopless F ∧ arcCount F=arcCount E+1 ∧ score F=score E :=
  ⟨sinks E v 1,sinks_loopless loopless v 1,sinks_arcs E v 1,sinks_score E v 1⟩

#print axioms winning_trapped
#print axioms winning_lift
#print axioms old_indirect_iff
#print axioms score_eq
#print axioms isolates_score
#print axioms sinks_score
#print axioms pad_to_order
#print axioms add_one_arrow
end Delivery.GraphPadding
