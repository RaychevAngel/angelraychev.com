import FourCubeTimeCounter
import FourCubeProfileGeometry
import FourCubeCriticalLower

namespace Princess.FourCubeCompression
open Princess.CaptureRecurrence Princess.LadderCardinality Princess.StrategyCompression
attribute [local irreducible] Princess.ProductCompression.iterateMap

theorem part_next_profile (p : Bool) (A S : Region Room)
    (closed : Closed (fun v => A v ∧ ¬S v)) :
    FourCubeTimeCounter.profile (card (part A p)-card (part S p))≤
      card (part (next adj A S) (!p)) := by
  let R : Region Room := fun v => A v ∧ ¬S v
  have removal := part_probe_bound p A S
  have mon := FourCubeTimeCounter.profile_mono (card (part A p)-card (part S p))
    (card (part R p)) (by dsimp [R]; omega) (part_card_bound p R)
  have bound := profile_lower p (part R p) (fun _ h => h.2) (closed_part p R closed)
  rw [← move_part] at bound
  exact Nat.le_trans mon bound

noncomputable def countRank (kind : Fin 10) (A : Region Room) : Nat :=
  FourCubeTimeCounter.rank kind (card (part A false)) (card (part A true))

theorem countRank_step (kind : Fin 10) (A S : Region Room)
    (closed : Closed (fun v => A v ∧ ¬S v)) (budget : card S≤FourCubeTimeCounter.budget kind) :
    countRank kind A≤1+countRank kind (next adj A S) := by
  have h0 := part_next_profile false A S closed
  have h1 := part_next_profile true A S closed
  simp only [Bool.not_false,Bool.not_true] at h0 h1
  have sums := card_parts S
  exact FourCubeTimeCounter.physical_step kind _ _ _ _ _ _
    (part_card_bound false A) (part_card_bound true A)
    (part_card_bound false (next adj A S)) (part_card_bound true (next adj A S))
    (by omega) h1 h0

theorem countRank_empty (kind : Fin 10) (A : Region Room) (empty : Empty A) : countRank kind A=0 := by
  rw [countRank,part_card_empty false A empty,part_card_empty true A empty]
  exact FourCubeTimeCounter.rank_empty kind

theorem countRank_full (kind : Fin 10) : countRank kind (fun _ => True)=FourCubeTimeCounter.turns kind := by
  rw [countRank,full_part_card,full_part_card]
  exact FourCubeTimeCounter.rank_full kind

theorem normal_count_lower (kind : Fin 10) (ms : List Nat) (A : Region Room)
    (budgets : ∀ m∈ms, m≤FourCubeTimeCounter.budget kind)
    (win : fixedWins adj normalizer ms A) : countRank kind A≤ms.length := by
  induction ms generalizing A with
  | nil => rw [countRank_empty kind A win.2]; exact Nat.le_refl 0
  | cons m ms ih =>
      obtain ⟨_,S,budget,rfix,tail⟩ := win
      have htail := ih (next adj A S) (fun k hk => budgets k (List.mem_cons_of_mem m hk)) tail
      have hstep := countRank_step kind A S (fixed_down_mask _ rfix)
        (Nat.le_trans budget (budgets m List.mem_cons_self))
      simp only [List.length_cons]
      omega

theorem actual_endpoint_lower (kind : Fin 10) (last : Nat) (shots : Nat → Region Room)
    (budget : ∀ t, t<last+1 → card (shots t)≤FourCubeTimeCounter.budget kind)
    (capture : GuaranteesAt adj (fun _ => True) shots last) : FourCubeTimeCounter.turns kind≤last+1 := by
  have normal := (actual_capture_iff_normal_form (FourCubeTimeCounter.budget kind) last).mp ⟨shots,budget,capture⟩
  have bound := normal_count_lower kind (List.replicate (last+1) (FourCubeTimeCounter.budget kind))
    (fun _ => True) (by intro m hm; have := List.eq_of_mem_replicate hm; omega) normal
  rw [countRank_full,List.length_replicate] at bound
  exact bound

theorem preserves_21 (p : Bool) (A S : Region Room)
    (closed : Closed (fun v => A v ∧ ¬S v)) (budget : card S≤7)
    (large : 21≤card (part A p)) : 21≤card (part (next adj A S) (!p)) := by
  have shots := card_mono (part S p) S (fun _ h => h.1)
  have prev := part_card_bound p A
  have atLeast : 14≤card (part A p)-card (part S p) := by omega
  have mono := FourCubeTimeCounter.profile_mono 14 (card (part A p)-card (part S p)) atLeast (by omega)
  rw [FourCubeTimeCounter.profile14] at mono
  exact Nat.le_trans mono (part_next_profile p A S closed)

theorem normal_impossible_7 (ms : List Nat) (A : Region Room)
    (budgets : ∀ m∈ms, m≤7) (large : ∀ p : Bool, 21≤card (part A p)) :
    ¬fixedWins adj normalizer ms A := by
  intro win
  induction ms generalizing A with
  | nil =>
      have count := part_card_empty false A win.2
      have h := large false
      omega
  | cons m ms ih =>
      obtain ⟨_,S,budget,rfix,tail⟩ := win
      apply ih (next adj A S) (fun k hk => budgets k (List.mem_cons_of_mem m hk)) _ tail
      intro p
      have h := preserves_21 (!p) A S (fixed_down_mask _ rfix)
        (Nat.le_trans budget (budgets m List.mem_cons_self)) (large (!p))
      simpa only [Bool.not_not] using h

theorem actual_impossible_7 (last : Nat) (shots : Nat → Region Room)
    (budget : ∀ t, t<last+1 → card (shots t)≤7)
    (capture : GuaranteesAt adj (fun _ => True) shots last) : False := by
  have normal := (actual_capture_iff_normal_form 7 last).mp ⟨shots,budget,capture⟩
  apply normal_impossible_7 (List.replicate (last+1) 7) (fun _ => True) _ _ normal
  · intro m hm; have := List.eq_of_mem_replicate hm; omega
  · intro p; rw [full_part_card]; omega

theorem actual_lower_two (m last : Nat) (shots : Nat → Region Room)
    (small : m<64) (budget : ∀ t, t<last+1 → card (shots t)≤m)
    (capture : GuaranteesAt adj (fun _ => True) shots last) : 2≤last+1 := by
  by_cases hlast : last=0
  · subst last
    have all : ∀ v, shots 0 v := fun v => capture v (Princess.Reachable.start trivial)
    have full := (card_full_iff (shots 0)).mpr all
    have cap := budget 0 (by omega)
    omega
  · omega

end Princess.FourCubeCompression
#print axioms Princess.FourCubeCompression.actual_endpoint_lower
#print axioms Princess.FourCubeCompression.actual_impossible_7
