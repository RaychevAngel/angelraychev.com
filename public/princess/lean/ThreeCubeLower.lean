import ThreeCubeTrap
import LadderCardinality

/-! Complete cardinality bridge for the four-probe obstruction on the 3-cube.
No belief-state enumeration is used: three surviving vertices suffice.
-/

namespace Princess.ThreeCubeLower

open Princess.ThreeCubeTrap
open Princess.LadderCardinality
open Princess.CaptureRecurrence

noncomputable def members (B : Region Room) : List Room := by
  classical
  exact (List.finRange 27).filter (fun v => decide (B v))

theorem mem_members (B : Region Room) (v : Room) : v ∈ members B ↔ B v := by
  classical
  simp [members]

theorem members_card (B : Region Room) : (members B).length = card B := by
  classical
  exact List.countP_eq_length_filter.symm

theorem members_nodup (B : Region Room) : (members B).Nodup := by
  classical
  exact List.filter_sublist.nodup (List.nodup_finRange 27)

theorem three_members (B : Region Room) (size : 3 ≤ card B) :
    ∃ a b c : Room, B a ∧ B b ∧ B c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have hsize : 3 ≤ (members B).length := by rw [members_card]; exact size
  have hn := members_nodup B
  cases hA : members B with
  | nil => simp [hA] at hsize
  | cons a rest =>
      cases hB : rest with
      | nil => simp [hA, hB] at hsize
      | cons b rest' =>
          cases hC : rest' with
          | nil => simp [hA, hB, hC] at hsize
          | cons c tail =>
              have heq : members B = a :: b :: c :: tail := by rw [hA, hB, hC]
              rw [heq] at hn
              have ha := (List.nodup_cons.mp hn).1
              have hb := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
              refine ⟨a, b, c, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact (mem_members B a).mp (by simp [heq])
              · exact (mem_members B b).mp (by simp [heq])
              · exact (mem_members B c).mp (by simp [heq])
              · intro eq; subst b; exact ha (by simp)
              · intro eq; subst c; exact ha (by simp)
              · intro eq; subst c; exact hb (by simp)

def monochrome (B : Region Room) : Prop :=
  ∃ p : Nat, ∀ v, B v → color v = p

def barriers (B : Region Room) : Prop := monochrome B ∧ 7 ≤ card B

def atMost (m : Nat) (S : Region Room) : Prop := card S ≤ m

theorem adj_flips : ∀ u v : Room, adj u v → color v = (color u + 1) % 2 := by
  decide

theorem move_monochrome (B S : Region Room) (hB : monochrome B) :
    monochrome (next adj B S) := by
  obtain ⟨p, hp⟩ := hB
  refine ⟨(p + 1) % 2, ?_⟩
  rintro v ⟨u, ⟨hu, _⟩, hadj⟩
  rw [adj_flips u v hadj, hp u hu]

theorem triple_card (a b c : Room) :
    card (fun v => adj a v ∨ adj b v ∨ adj c v) = tripleNeighbors a b c := by
  classical
  apply List.countP_congr
  intro v _
  simp

theorem barrier_step (B S : Region Room) (hB : barriers B) (hS : atMost 4 S) :
    barriers (next adj B S) := by
  constructor
  · exact move_monochrome B S hB.1
  · let R : Region Room := fun v => B v ∧ ¬ S v
    have removed := probes_remove_at_most B S
    have hR : 3 ≤ card R := by
      change card S ≤ 4 at hS
      change card B ≤ card R + card S at removed
      have := hB.2
      omega
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := three_members R hR
    obtain ⟨p, hp⟩ := hB.1
    have expansion := triple_neighborhood_seven a b c hab hac hbc
      ((hp a ha.1).trans (hp b hb.1).symm) ((hp a ha.1).trans (hp c hc.1).symm)
    have incl := card_mono (fun v => adj a v ∨ adj b v ∨ adj c v)
      (next adj B S) (by
        intro v hv
        rcases hv with h | h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
        · exact ⟨c, hc, h⟩)
    rw [triple_card] at incl
    omega

theorem barrier_trap : Trap adj (atMost 4) barriers := by
  constructor
  · intro B hB hempty
    obtain ⟨v, hv⟩ := (card_pos B).mp (by have := hB.2; omega)
    exact hempty v hv
  · exact fun B S hB hS => barrier_step B S hB hS

def evenCount : Nat := (List.finRange 27).countP (fun v => decide (color v = 0))

theorem even_size : card (fun v : Room => color v = 0) = 14 := by
  classical
  have heq : card (fun v : Room => color v = 0) = evenCount := by
    apply List.countP_congr
    intro v _
    simp
  rw [heq]
  exact (by decide : evenCount = 14)

theorem full_board_four_impossible : losing adj (atMost 4) (fun _ => True) := by
  have evenLoses : losing adj (atMost 4) (fun v => color v = 0) := by
    apply every_trap_subset_losing adj (atMost 4) barriers barrier_trap
    exact ⟨⟨0, fun _ h => h⟩, by rw [even_size]; decide⟩
  exact losing_upward adj (atMost 4) (fun v => color v = 0) (fun _ => True)
    (fun _ _ => True.intro) evenLoses

theorem list_bounds_card (S : Region Room) (rooms : List Room)
    (enumerates : ∀ v, S v ↔ v ∈ rooms) : card S ≤ rooms.length := by
  rw [← members_card]
  exact (members_nodup S).length_le_of_subset (fun v hv =>
    (enumerates v).mp ((mem_members S v).mp hv))

theorem five_legal_card (S : Region Room) (h : ThreeCubeTrap.legal S) : atMost 5 S := by
  obtain ⟨rooms, size, enumerates⟩ := h
  exact Nat.le_trans (list_bounds_card S rooms enumerates) size

/-- Five probes suffice, with actual trajectories and the same cardinality
budget used in the four-probe impossibility theorem. -/
theorem full_board_five_actual_capture :
    ∃ probes : Nat → Region Room,
      (∀ i, i < 18 → atMost 5 (probes i)) ∧
      Princess.GuaranteesAt adj (fun _ => True) probes 17 := by
  obtain ⟨probes, budget, capture⟩ := ThreeCubeTrap.full_board_actual_capture
  exact ⟨probes, fun i hi => five_legal_card (probes i) (budget i hi), capture⟩

theorem full_board_four_actual_impossible (probes : Nat → Region Room)
    (budget : ∀ i, atMost 4 (probes i)) (t : Nat) :
    ¬ Princess.GuaranteesAt adj (fun _ => True) probes t := by
  intro capture
  apply full_board_four_impossible (t + 1)
  exact (winning_iff_guarantees adj (atMost 4) no_dead_ends t (fun _ => True)).mpr
    ⟨probes, fun i _ => budget i, capture⟩

/-- Exact feasibility classification for every natural daily budget.
The witness supplies an eighteen-round construction, not a time-optimality claim. -/
theorem feasible_iff_five_le (m : Nat) :
    (∃ t : Nat, ∃ probes : Nat → Region Room,
      (∀ i, i < t + 1 → atMost m (probes i)) ∧
      Princess.GuaranteesAt adj (fun _ => True) probes t) ↔ 5 ≤ m := by
  constructor
  · rintro ⟨t, probes, budget, capture⟩
    apply Classical.byContradiction
    intro hm
    have hm4 : m ≤ 4 := by omega
    apply full_board_four_impossible (t + 1)
    exact (winning_iff_guarantees adj (atMost 4) no_dead_ends t (fun _ => True)).mpr
      ⟨probes, fun i hi => Nat.le_trans (budget i hi) hm4, capture⟩
  · intro hm
    obtain ⟨probes, budget, capture⟩ := full_board_five_actual_capture
    exact ⟨17, probes, fun i hi => Nat.le_trans (budget i hi) hm, capture⟩

end Princess.ThreeCubeLower

#print axioms Princess.ThreeCubeLower.barrier_trap
#print axioms Princess.ThreeCubeLower.full_board_four_impossible
#print axioms Princess.ThreeCubeLower.full_board_five_actual_capture
#print axioms Princess.ThreeCubeLower.full_board_four_actual_impossible
#print axioms Princess.ThreeCubeLower.feasible_iff_five_le
