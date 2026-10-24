import ConstructionCounts
import DenseCounting
import GraphRelabeling

/-! Joining two delivery graphs by every arrow between their vertex sets.
Two-move guarantees survive if each graph has a missing outgoing pair at
every vertex. Counts refer to the resulting literal graph on Fin (r+k). -/
namespace Delivery.ComplementarySum
open FiniteGame Extremal DenseCombinatorics ConstructionCounts

theorem winning_one_legal {V : Type} {E : Graph V} {s t c : V}
    (win : Winning E t 1 s c) : Legal E s t := by
  cases win with
  | delivered => exact Or.inl rfl
  | finish _ move => exact move
  | step _ move _ _ next =>
    have terminal := next c (legal_wait E c)
    cases terminal
    exact move

theorem two_move_witness {V : Type} {E : Graph V} {s t c : V}
    (win : Winning E t 2 s c) (different : s ≠ t) (missing : ¬ E s t) :
    ∃ u, E s u ∧ E u t ∧ ¬ Legal E c u := by
  cases win with
  | delivered => exact False.elim (different rfl)
  | finish _ move => exact False.elim (move.elim different missing)
  | @step k r c u _ move _ safe next =>
    have last := winning_one_legal (next c (legal_wait E c))
    have firstEdge : E s u := by
      rcases move with same | edge
      · exact False.elim ((same ▸ last).elim different missing)
      · exact edge
    have lastEdge : E u t := by
      rcases last with same | edge
      · exact False.elim (missing (same ▸ firstEdge))
      · exact edge
    exact ⟨u,firstEdge,lastEdge,fun legal => safe u legal rfl⟩

def sumGraph {V W : Type} (A : Graph V) (B : Graph W) : Graph (Sum V W)
  | .inl s, .inl t => A s t
  | .inr s, .inr t => B s t
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True

theorem left_universal {V W : Type} {A : Graph V} {B : Graph W}
    (positive : ∀ c, ∃ u, c ≠ u ∧ ¬ B c u) {s t : V}
    (win : Universal A t 2 s) : Universal (sumGraph A B) (.inl t) 2 (.inl s) := by
  intro c initial
  by_cases same : s = t
  · subst t; exact Winning.delivered
  by_cases direct : A s t
  · exact Winning.finish (Ne.symm initial) (Or.inr direct)
  cases c with
  | inl c =>
    have cs : c ≠ s := fun h => initial (congrArg Sum.inl h)
    obtain ⟨u,first,last,unreachable⟩ := two_move_witness (win c cs) same direct
    apply DenseCounting.safe_intermediate_winning (u := Sum.inl u) (Ne.symm initial)
      (show sumGraph A B (.inl s) (.inl u) from first)
      (show sumGraph A B (.inl u) (.inl t) from last)
    intro legal
    rcases legal with equal | edge
    · exact unreachable (Or.inl (Sum.inl.inj equal))
    · exact unreachable (Or.inr edge)
  | inr c =>
    obtain ⟨u,different,missing⟩ := positive c
    apply DenseCounting.safe_intermediate_winning (u := Sum.inr u) (Ne.symm initial)
      (show sumGraph A B (.inl s) (.inr u) from trivial)
      (show sumGraph A B (.inr u) (.inl t) from trivial)
    intro legal
    rcases legal with same | edge
    · exact different (Sum.inr.inj same)
    · exact missing edge

def swapIso {V W : Type} (A : Graph V) (B : Graph W) :
    GraphRelabeling.Iso (sumGraph A B) (sumGraph B A) where
  toFun := Sum.swap
  invFun := Sum.swap
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x <;> rfl
  edge_iff := by intro x y; cases x <;> cases y <;> rfl

theorem right_universal {V W : Type} {A : Graph V} {B : Graph W}
    (positive : ∀ c, ∃ u, c ≠ u ∧ ¬ A c u) {s t : W}
    (win : Universal B t 2 s) : Universal (sumGraph A B) (.inr t) 2 (.inr s) := by
  intro c initial
  have cs : c.swap ≠ Sum.inl s := by
    intro equal
    have := congrArg Sum.swap equal
    cases c <;> simp_all
  have result := (swapIso B A).winning (left_universal positive win c.swap cs)
  cases c <;> exact result

def left (r k : Nat) (s : Fin r) : Fin (r+k) := ⟨s.val,by have := s.isLt; omega⟩
def right (r k : Nat) (s : Fin k) : Fin (r+k) := ⟨r+s.val,by have := s.isLt; omega⟩

def encode {r k : Nat} : Sum (Fin r) (Fin k) → Fin (r+k)
  | .inl s => left r k s
  | .inr s => right r k s

def decode {r k : Nat} (s : Fin (r+k)) : Sum (Fin r) (Fin k) :=
  if h : s.val < r then .inl ⟨s.val,h⟩ else .inr ⟨s.val-r,by have := s.isLt; omega⟩

@[simp] theorem decode_encode {r k : Nat} (s : Sum (Fin r) (Fin k)) : decode (encode s) = s := by
  cases s with
  | inl s => simp [decode,encode,left,s.isLt]
  | inr s =>
    have h : ¬ r+s.val < r := by omega
    simp [decode,encode,right,h]

@[simp] theorem encode_decode {r k : Nat} (s : Fin (r+k)) : encode (decode s) = s := by
  unfold decode
  split
  · rfl
  · apply Fin.ext; dsimp [encode,right]; omega

theorem encode_injective {r k : Nat} {s t : Sum (Fin r) (Fin k)}
    (same : encode s = encode t) : s = t := by
  simpa only [decode_encode] using congrArg decode same

theorem split_perm (r k : Nat) :
    (List.finRange (r+k)).Perm
      ((List.finRange r).map (left r k) ++ (List.finRange k).map (right r k)) := by
  have leftND : ((List.finRange r).map (left r k)).Nodup := by
    apply List.pairwise_map.mpr
    apply (List.nodup_finRange r).imp
    intro x y different same
    exact different (Fin.ext (congrArg (fun z : Fin (r+k) => z.val) same))
  have rightND : ((List.finRange k).map (right r k)).Nodup := by
    apply List.pairwise_map.mpr
    apply (List.nodup_finRange k).imp
    intro x y different same
    apply different
    apply Fin.ext
    have := congrArg Fin.val same
    dsimp [right] at this
    omega
  have disjoint : ∀ x, x ∈ (List.finRange r).map (left r k) →
      x ∈ (List.finRange k).map (right r k) → False := by
    intro x hx hy
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨t,_,same⟩ := List.mem_map.mp hy
    have := congrArg Fin.val same
    have := s.isLt
    dsimp [left,right] at *
    omega
  apply (List.perm_ext_iff_of_nodup (List.nodup_finRange _) ?_).mpr
  · intro s
    simp only [List.mem_finRange,true_iff,List.mem_append,List.mem_map]
    by_cases hs : s.val < r
    · exact Or.inl ⟨⟨s.val,hs⟩,trivial,rfl⟩
    · refine Or.inr ⟨⟨s.val-r,by have := s.isLt; omega⟩,trivial,?_⟩
      apply Fin.ext
      dsimp [right]
      omega
  · exact List.nodup_append.mpr ⟨leftND,rightND,fun a ha b hb same => disjoint a ha (same ▸ hb)⟩

theorem sum_split {r k : Nat} (f : Fin (r+k) → Nat) :
    ((List.finRange (r+k)).map f).sum =
      ((List.finRange r).map fun s => f (left r k s)).sum +
      ((List.finRange k).map fun s => f (right r k s)).sum := by
  have perm := (split_perm r k).map f
  have sumPerm {xs ys : List Nat} (p : xs.Perm ys) : xs.sum = ys.sum := by
    induction p with
    | nil => rfl
    | cons _ _ ih => simp [ih]
    | swap => simp [Nat.add_left_comm]
    | trans _ _ ih1 ih2 => exact ih1.trans ih2
  simpa only [List.map_append,List.map_map,List.sum_append,Function.comp_def] using sumPerm perm

theorem card_split {r k : Nat} (P : Fin (r+k) → Prop) :
    card P = card (fun s => P (left r k s)) + card (fun s => P (right r k s)) := by
  classical
  have perm := (split_perm r k).filter (fun s => decide (P s))
  simpa only [card,elems,List.filter_append,List.length_append,List.filter_map,
    List.length_map,Function.comp_def] using perm.length_eq

def graph {r k : Nat} (A : Graph (Fin r)) (B : Graph (Fin k)) : Graph (Fin (r+k)) :=
  fun s t => sumGraph A B (decode s) (decode t)

def graphIso {r k : Nat} (A : Graph (Fin r)) (B : Graph (Fin k)) :
    GraphRelabeling.Iso (sumGraph A B) (graph A B) where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode
  edge_iff := by intro s t; simp [graph]

@[simp] theorem decode_left {r k : Nat} (s : Fin r) : decode (left r k s) = Sum.inl s :=
  decode_encode (.inl s)
@[simp] theorem decode_right {r k : Nat} (s : Fin k) : decode (right r k s) = Sum.inr s :=
  decode_encode (.inr s)

theorem loopless {r k : Nat} {A : Graph (Fin r)} {B : Graph (Fin k)}
    (a : Loopless A) (b : Loopless B) : Loopless (graph A B) := by
  intro s edge
  unfold graph at edge
  cases h : decode s with
  | inl x => rw [h] at edge; exact a x edge
  | inr x => rw [h] at edge; exact b x edge

theorem left_ne_iff {r k : Nat} (s t : Fin r) : left r k s ≠ left r k t ↔ s ≠ t := by
  constructor
  · intro different same; exact different (congrArg (left r k) same)
  · intro different same
    exact different (Fin.ext (congrArg (fun x : Fin (r+k) => x.val) same))

theorem right_ne_iff {r k : Nat} (s t : Fin k) : right r k s ≠ right r k t ↔ s ≠ t := by
  constructor
  · intro different same; exact different (congrArg (right r k) same)
  · intro different same
    have eq := encode_injective (s := Sum.inr s) (t := Sum.inr t) same
    exact different (Sum.inr.inj eq)

theorem missing_left_row {r k : Nat} (A : Graph (Fin r)) (B : Graph (Fin k)) (s : Fin r) :
    card (fun t => left r k s ≠ t ∧ ¬ graph A B (left r k s) t) =
      card (fun t => s ≠ t ∧ ¬ A s t) := by
  rw [card_split]
  have l : card (fun t => left r k s ≠ left r k t ∧ ¬ graph A B (left r k s) (left r k t)) =
      card (fun t => s ≠ t ∧ ¬ A s t) := by
    apply card_congr
    intro t
    simp only [graph,decode_left,sumGraph,left_ne_iff]
  have z : card (fun t => left r k s ≠ right r k t ∧ ¬ graph A B (left r k s) (right r k t)) = 0 := by
    apply card_eq_zero.mpr
    intro t h
    exact h.2 (by simp [graph,decode_left,decode_right,sumGraph])
  rw [l,z,Nat.add_zero]

theorem missing_right_row {r k : Nat} (A : Graph (Fin r)) (B : Graph (Fin k)) (s : Fin k) :
    card (fun t => right r k s ≠ t ∧ ¬ graph A B (right r k s) t) =
      card (fun t => s ≠ t ∧ ¬ B s t) := by
  rw [card_split]
  have z : card (fun t => right r k s ≠ left r k t ∧ ¬ graph A B (right r k s) (left r k t)) = 0 := by
    apply card_eq_zero.mpr
    intro t h
    exact h.2 (by simp [graph,decode_left,decode_right,sumGraph])
  have q : card (fun t => right r k s ≠ right r k t ∧ ¬ graph A B (right r k s) (right r k t)) =
      card (fun t => s ≠ t ∧ ¬ B s t) := by
    apply card_congr
    intro t
    simp only [graph,decode_right,sumGraph,right_ne_iff]
  rw [z,q,Nat.zero_add]

theorem missing_count {r k : Nat} (A : Graph (Fin r)) (B : Graph (Fin k)) :
    missingCount (graph A B) = missingCount A + missingCount B := by
  rw [missing_rows,sum_split]
  simp only [missing_left_row,missing_right_row]
  rw [← missing_rows,← missing_rows]

theorem left_indirect {r k : Nat} {A : Graph (Fin r)} {B : Graph (Fin k)}
    (positive : ∀ c, ∃ u, c ≠ u ∧ ¬ B c u) {s t : Fin r}
    (pair : Indirect A s t) (win : Universal A t 2 s) :
    Indirect (graph A B) (left r k s) (left r k t) := by
  have sup : Indirect (sumGraph A B) (.inl s) (.inl t) :=
    ⟨fun h => pair.1 (Sum.inl.inj h),pair.2.1,
      universal_guaranteed (left_universal positive win)⟩
  exact ((graphIso A B).indirect_iff (.inl s) (.inl t)).mp sup

theorem right_indirect {r k : Nat} {A : Graph (Fin r)} {B : Graph (Fin k)}
    (positive : ∀ c, ∃ u, c ≠ u ∧ ¬ A c u) {s t : Fin k}
    (pair : Indirect B s t) (win : Universal B t 2 s) :
    Indirect (graph A B) (right r k s) (right r k t) := by
  have sup : Indirect (sumGraph A B) (.inr s) (.inr t) :=
    ⟨fun h => pair.1 (Sum.inr.inj h),pair.2.1,
      universal_guaranteed (right_universal positive win)⟩
  exact ((graphIso A B).indirect_iff (.inr s) (.inr t)).mp sup

theorem score_lower {r k : Nat} {A : Graph (Fin r)} {B : Graph (Fin k)}
    (positiveA : ∀ c, ∃ u, c ≠ u ∧ ¬ A c u)
    (positiveB : ∀ c, ∃ u, c ≠ u ∧ ¬ B c u)
    (twoA : ∀ s t, Indirect A s t → Universal A t 2 s)
    (twoB : ∀ s t, Indirect B s t → Universal B t 2 s) :
    score A + score B ≤ score (graph A B) := by
  have leftBound (s : Fin r) : card (Indirect A s) ≤ card (Indirect (graph A B) (left r k s)) := by
    rw [card_split]
    have b := card_mono (P := Indirect A s)
      (Q := fun t => Indirect (graph A B) (left r k s) (left r k t))
      (fun t h => left_indirect positiveB h (twoA s t h))
    omega
  have rightBound (s : Fin k) : card (Indirect B s) ≤ card (Indirect (graph A B) (right r k s)) := by
    rw [card_split]
    have b := card_mono (P := Indirect B s)
      (Q := fun t => Indirect (graph A B) (right r k s) (right r k t))
      (fun t h => right_indirect positiveA h (twoB s t h))
    omega
  have lb := sum_mono (List.finRange r) leftBound
  have rb := sum_mono (List.finRange k) rightBound
  rw [score_rows,score_rows,score_rows,sum_split]
  omega

#print axioms two_move_witness
#print axioms left_universal
#print axioms card_split
#print axioms missing_count
#print axioms score_lower
end Delivery.ComplementarySum
