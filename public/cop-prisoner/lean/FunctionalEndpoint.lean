import DenseZero
import DenseCounting
import DenseStaircase

/-! Exact pair characterization for complements of fixed-point-free functions.
This is the dense endpoint construction, including actual game strategies. -/
namespace Delivery.FunctionalEndpoint
open FiniteGame Extremal

variable {V : Type}

def edge (f : V → V) : Graph V := fun s t => s ≠ t ∧ f s ≠ t

def Root (f : V → V) (s : V) : Prop :=
  (∀ c, f c ≠ s) ∧ (∀ c, f c = f s → c = s)

theorem loopless (f : V → V) : Loopless (edge f) := fun _ h => h.1 rfl

theorem legal_iff {f : V → V} (fixed : ∀ c, f c ≠ c) (c z : V) :
    Legal (edge f) c z ↔ f c ≠ z := by
  constructor
  · rintro (same | h)
    · simpa only [← same] using fixed c
    · exact h.2
  · intro h
    by_cases same : c = z
    · exact Or.inl same
    · exact Or.inr ⟨same,h⟩

theorem root_two_move {f : V → V} (fixed : ∀ c, f c ≠ c)
    {s : V} (root : Root f s) : Universal (edge f) (f s) 2 s := by
  intro c initial
  have cs : f c ≠ s := root.1 c
  have ct : f c ≠ f s := fun same => initial (root.2 c same)
  have next : f (f c) ≠ f s := fun same => cs (root.2 (f c) same)
  exact DenseCounting.safe_intermediate_winning (Ne.symm initial)
    ⟨Ne.symm cs,Ne.symm ct⟩ ⟨ct,next⟩
    (fun legal => (legal_iff fixed c (f c)).mp legal rfl)

theorem guaranteed_root {f : V → V} (fixed : ∀ c, f c ≠ c) {s : V}
    (guaranteed : Guaranteed (edge f) s (f s)) : Root f s := by
  have different : s ≠ f s := Ne.symm (fixed s)
  have missing : ¬ edge f s (f s) := fun h => h.2 rfl
  constructor
  · intro c same
    have initial : c ≠ s := by
      intro eq; subst c; exact fixed s same
    obtain ⟨k,win⟩ := guaranteed c initial
    apply VertexBound.source_camping different missing (k := k) (E := edge f) _ win
    intro z move
    apply (legal_iff fixed c z).mpr
    simpa only [same] using move.1
  · intro c same
    apply Classical.byContradiction
    intro initial
    obtain ⟨k,win⟩ := guaranteed c initial
    apply VertexBound.source_camping different missing (k := k) (E := edge f) _ win
    intro z move
    apply (legal_iff fixed c z).mpr
    simpa only [same] using move.2

theorem guaranteed_iff_root {f : V → V} (fixed : ∀ c, f c ≠ c) (s : V) :
    Guaranteed (edge f) s (f s) ↔ Root f s :=
  ⟨guaranteed_root fixed, fun h => universal_guaranteed (root_two_move fixed h)⟩

theorem indirect_iff {f : V → V} (fixed : ∀ c, f c ≠ c) (s t : V) :
    Indirect (edge f) s t ↔ t = f s ∧ Root f s := by
  constructor
  · rintro ⟨different,missing,guaranteed⟩
    have target : t = f s := by
      apply Classical.byContradiction
      intro h
      exact missing ⟨different,Ne.symm h⟩
    subst t
    exact ⟨rfl,guaranteed_root fixed guaranteed⟩
  · rintro ⟨rfl,root⟩
    exact ⟨Ne.symm (fixed s),fun h => h.2 rfl,
      universal_guaranteed (root_two_move fixed root)⟩

def Paired {n : Nat} (s : Fin n) : Prop :=
  2 ≤ s.val ∧ s.val % 2 = 0 ∧ s.val + 1 < n

instance {n : Nat} (s : Fin n) : Decidable (Paired s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A two-cycle on 0,1; each subsequent complete pair points towards 0.
An unpaired final vertex also points to 0. -/
def partner (n : Nat) (hn : 2 ≤ n) (s : Fin n) : Fin n :=
  if zero : s.val = 0 then ⟨1,by omega⟩
  else if paired : s.val % 2 = 0 ∧ s.val + 1 < n then ⟨s.val+1,paired.2⟩
  else ⟨0,by omega⟩

theorem partner_fixed {n : Nat} (hn : 2 ≤ n) (s : Fin n) :
    partner n hn s ≠ s := by
  intro equal
  have val := congrArg Fin.val equal
  unfold partner at val
  split at val <;> try dsimp only at val
  · omega
  · split at val <;> try dsimp only at val <;> omega

theorem partner_root {n : Nat} (hn : 2 ≤ n) (s : Fin n) :
    Root (partner n hn) s ↔ Paired s := by
  constructor
  · intro root
    have one : (partner n hn ⟨1,by omega⟩).val = 0 := by simp [partner]
    have zero : (partner n hn ⟨0,by omega⟩).val = 1 := by simp [partner]
    have notZero : s.val ≠ 0 := by
      intro h
      exact root.1 ⟨1,by omega⟩ (Fin.ext (by omega))
    have notOne : s.val ≠ 1 := by
      intro h
      exact root.1 ⟨0,by omega⟩ (Fin.ext (by omega))
    have low : 2 ≤ s.val := by omega
    refine ⟨low,?_⟩
    by_cases paired : s.val % 2 = 0 ∧ s.val+1<n
    · exact paired
    · have value : (partner n hn s).val = 0 := by simp [partner,notZero,paired]
      have same := root.2 ⟨1,by omega⟩ (Fin.ext (by omega))
      have : 1 = s.val := congrArg Fin.val same
      omega
  · rintro ⟨low,even,room⟩
    have nz : s.val ≠ 0 := by omega
    have value : (partner n hn s).val = s.val + 1 := by simp [partner,nz,even,room]
    constructor
    · intro c same
      have val := congrArg Fin.val same
      unfold partner at val
      split at val <;> try dsimp only at val
      · omega
      · split at val <;> try dsimp only at val <;> omega
    · intro c same
      have val := congrArg Fin.val same
      rw [value] at val
      unfold partner at val
      split at val <;> try dsimp only at val
      · omega
      · split at val <;> try dsimp only at val
        · apply Fin.ext; omega
        · omega

def rootVertex (n : Nat) (i : Fin ((n-2)/2)) : Fin n :=
  ⟨2*i.val+2,by have := i.isLt; omega⟩

theorem rootVertex_injective {n : Nat} {i j : Fin ((n-2)/2)}
    (same : rootVertex n i = rootVertex n j) : i = j := by
  apply Fin.ext
  have := congrArg Fin.val same
  simp only [rootVertex] at this
  omega

theorem rootVertex_mem {n : Nat} (s : Fin n) :
    s ∈ (List.finRange ((n-2)/2)).map (rootVertex n) ↔ Paired s := by
  constructor
  · intro member
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp member
    have := i.isLt
    simp only [Paired, rootVertex]
    omega
  · rintro ⟨low,even,room⟩
    apply List.mem_map.mpr
    refine ⟨⟨(s.val-2)/2,by omega⟩,List.mem_finRange _,?_⟩
    apply Fin.ext
    simp only [rootVertex]
    omega

theorem paired_count (n : Nat) :
    ((List.finRange n).filter fun s => decide (Paired s)).length = (n-2)/2 := by
  have nd : ((List.finRange ((n-2)/2)).map (rootVertex n)).Nodup := by
    apply List.pairwise_map.mpr
    exact (List.nodup_finRange _).imp (fun h same => h (rootVertex_injective same))
  have perm := (List.perm_ext_iff_of_nodup
    ((List.nodup_finRange n).filter (fun s => decide (Paired s))) nd).mpr
    (fun s => by simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq];
                 exact (rootVertex_mem s).symm)
  simpa only [List.length_map,List.length_finRange] using perm.length_eq

theorem singleton_count {n : Nat} (t : Fin n) :
    ((List.finRange n).filter fun x => decide (x = t)).length = 1 := by
  simp [List.filter_eq, (List.nodup_finRange n).count]

theorem pair_count {n : Nat} (s t : Fin n) (different : s ≠ t) :
    ((List.finRange n).filter fun x => decide (x = s ∨ x = t)).length = 2 := by
  have nd : [s,t].Nodup := by simp [different]
  have perm := (List.perm_ext_iff_of_nodup
    ((List.nodup_finRange n).filter (fun x => decide (x = s ∨ x = t))) nd).mpr
    (fun x => by simp)
  simpa using perm.length_eq

theorem arc_count {n : Nat} (f : Fin n → Fin n) (fixed : ∀ s, f s ≠ s) :
    arcCount (edge f) = n*(n-2) := by
  classical
  have row (s : Fin n) :
      ((List.finRange n).filter fun t => decide (edge f s t)).length = n-2 := by
    have split := VertexBound.filter_partition (List.finRange n)
      (fun t => decide (edge f s t))
    have rejected : (fun t => !(decide (edge f s t))) =
        (fun t => decide (t = s ∨ t = f s)) := by
      funext t
      by_cases st : s = t <;> by_cases ft : f s = t <;>
        simp [edge,st,ft,eq_comm]
      exact Ne.symm ft
    rw [rejected,pair_count s (f s) (Ne.symm (fixed s)),List.length_finRange] at split
    omega
  unfold arcCount allPairs
  rw [List.filter_flatMap,List.length_flatMap]
  simp only [List.filter_map,List.length_map,Function.comp_def,row]
  have constant (xs : List (Fin n)) :
      (xs.map fun _ => n-2).sum = xs.length*(n-2) := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [ih,Nat.add_mul,Nat.add_comm]
  simpa using constant (List.finRange n)

theorem missing_count {n : Nat} (f : Fin n → Fin n) (fixed : ∀ s, f s ≠ s) :
    missingCount (edge f) = n := by
  classical
  have row (s : Fin n) :
      ((List.finRange n).filter fun t => decide (s ≠ t ∧ ¬ edge f s t)).length = 1 := by
    have same : (fun t => decide (s ≠ t ∧ ¬ edge f s t)) =
        (fun t => decide (t = f s)) := by
      funext t
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨st,h⟩
        apply Classical.byContradiction
        intro neq
        exact h ⟨st,Ne.symm neq⟩
      · rintro rfl
        exact ⟨Ne.symm (fixed s),fun h => h.2 rfl⟩
    rw [same,singleton_count]
  unfold missingCount allPairs
  rw [List.filter_flatMap,List.length_flatMap]
  simp only [List.filter_map,List.length_map,Function.comp_def,row]
  have ones (xs : List (Fin n)) : (xs.map fun _ => 1).sum = xs.length := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp [ih,Nat.add_comm]
  simpa using ones (List.finRange n)

theorem sum_indicator {α : Type} (xs : List α) (p : α → Bool) :
    (xs.map fun x => if p x then 1 else 0).sum = (xs.filter p).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp,ih,Nat.add_comm]

theorem attaining_score {n : Nat} (hn : 2 ≤ n) :
    score (edge (partner n hn)) = (n-2)/2 := by
  classical
  have row (s : Fin n) :
      ((List.finRange n).filter fun t => decide (Indirect (edge (partner n hn)) s t)).length =
      if Paired s then 1 else 0 := by
    have same : (fun t => decide (Indirect (edge (partner n hn)) s t)) =
        (fun t => decide (t = partner n hn s ∧ Paired s)) := by
      funext t
      apply decide_eq_decide.mpr
      rw [indirect_iff (partner_fixed hn),partner_root hn]
    rw [same]
    by_cases h : Paired s
    · simp only [h,and_true,if_true]
      exact singleton_count _
    · simp [h]
  unfold score allPairs
  rw [List.filter_flatMap,List.length_flatMap]
  simp only [List.filter_map,List.length_map,Function.comp_def,row]
  have indicator := sum_indicator (List.finRange n) (fun s => decide (Paired s))
  simp only [decide_eq_true_eq] at indicator
  rw [indicator]
  exact paired_count n

/-- The dense endpoint, including a concrete graph at every order. -/
theorem maximum_endpoint {n : Nat} (hn : 2 ≤ n) :
    IsMaximum n (n*(n-2)) ((n-2)/2) := by
  constructor
  · intro E noLoops arrows
    have partition := DenseCombinatorics.arcCount_add_missingCount E noLoops
    have count : n*(n-1) = n*(n-2)+n := by
      have one : n-1 = (n-2)+1 := by omega
      rw [one,Nat.mul_add,Nat.mul_one]
    have missing : missingCount E = n := by omega
    have upper := DenseStaircase.bound_missing E noLoops hn
      (by omega) (by omega)
    rw [missing] at upper
    unfold DenseCounting.ceilHalf at upper
    omega
  · exact ⟨edge (partner n hn),loopless _,arc_count _ (partner_fixed hn),
      attaining_score hn⟩

#print axioms root_two_move
#print axioms indirect_iff
#print axioms partner_root
#print axioms paired_count
#print axioms arc_count
#print axioms missing_count
#print axioms attaining_score
#print axioms maximum_endpoint
end Delivery.FunctionalEndpoint
