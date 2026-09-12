import CaptureRecurrence
import LadderCardinality

/-!
Compression of entire capture strategies. The hypotheses are properties of a
set operator, not assumed optimality of a restricted strategy. Arbitrary daily
budgets are retained. The final constant-budget equivalence connects this
normal form to the established actual-walk semantics.
-/

namespace Princess.StrategyCompression

open Princess.CaptureRecurrence Princess.LadderCardinality

abbrev Board (n : Nat) := Region (Fin n)

structure Compression {n : Nat} (adj : Fin n → Fin n → Prop) where
  map : Board n → Board n
  mono : ∀ A B, Subset A B → Subset (map A) (map B)
  size : ∀ A, card (map A) = card A
  neighbors : ∀ A, Subset (move adj (map A)) (map (move adj A))

def Fixed {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (A : Board n) : Prop := C.map A = A

theorem card_congr {n : Nat} (A B : Board n) (h : ∀ x, A x ↔ B x) :
    card A = card B := cardOn_congr _ _ _ (fun x _ => h x)

theorem subset_equal {n : Nat} (A B : Board n)
    (inc : Subset A B) (eqcard : card A = card B) : A = B := by
  classical
  funext x
  apply propext
  constructor
  · exact inc x
  · intro hb
    apply Classical.byContradiction
    intro ha
    have h := cardOn_strict (List.finRange n) A B
      (fun v _ => inc v) ⟨x, List.mem_finRange x, hb, ha⟩
    change card A < card B at h
    omega

theorem map_empty {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (A : Board n) (hA : Empty A) : Empty (C.map A) := by
  intro v hv
  have hpos := (card_pos (C.map A)).mpr ⟨v, hv⟩
  rw [C.size] at hpos
  obtain ⟨u, hu⟩ := (card_pos A).mp hpos
  exact hA u hu

theorem fixed_intersection {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (A B : Board n) (hA : Fixed C A) (hB : Fixed C B) :
    Fixed C (fun x => A x ∧ B x) := by
  apply subset_equal
  · intro x hx
    have ha := C.mono (fun x => A x ∧ B x) A (fun _ h => h.1) x hx
    have hb := C.mono (fun x => A x ∧ B x) B (fun _ h => h.2) x hx
    rw [hA] at ha
    rw [hB] at hb
    exact ⟨ha, hb⟩
  · exact C.size _

theorem fixed_neighbors {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (A : Board n) (hA : Fixed C A) :
    Fixed C (move adj A) := by
  apply Eq.symm
  apply subset_equal
  · have h := C.neighbors A
    rw [hA] at h
    exact h
  · exact (C.size _).symm

def wins {n : Nat} (adj : Fin n → Fin n → Prop) : List Nat → Board n → Prop
  | [], A => Empty A
  | m :: ms, A => ∃ S, card S ≤ m ∧ wins adj ms (next adj A S)

def fixedWins {n : Nat} (adj : Fin n → Fin n → Prop) (C : Compression adj) :
    List Nat → Board n → Prop
  | [], A => Fixed C A ∧ Empty A
  | m :: ms, A => Fixed C A ∧ ∃ S, card S ≤ m ∧
      Fixed C (fun x => A x ∧ ¬ S x) ∧ fixedWins adj C ms (next adj A S)

theorem reduced_probe_bound {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (A B S : Board n) (inc : Subset B (C.map A)) :
    card (fun x => B x ∧ ¬ C.map (fun x => A x ∧ ¬ S x) x) ≤ card S := by
  let R : Board n := fun x => A x ∧ ¬ S x
  have incR : Subset R A := fun _ h => h.1
  have incC := C.mono R A incR
  have hle := card_mono (fun x => B x ∧ ¬ C.map R x)
    (fun x => C.map A x ∧ ¬ C.map R x) (fun x h => ⟨inc x h.1, h.2⟩)
  have partition := cardOn_split (List.finRange n) (C.map A) (C.map R)
  have intersection := card_congr (fun x => C.map A x ∧ C.map R x) (C.map R)
    (fun x => ⟨And.right, fun h => ⟨incC x h, h⟩⟩)
  change card (C.map A) = card (fun x => C.map A x ∧ C.map R x) +
    card (fun x => C.map A x ∧ ¬ C.map R x) at partition
  rw [intersection, C.size A, C.size R] at partition
  have removed := probes_remove_at_most A S
  change card A ≤ card R + card S at removed
  change card (fun x => B x ∧ ¬ C.map R x) ≤ card S
  omega

theorem reduced_step {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (A B S : Board n) :
    Subset (next adj B (fun x => B x ∧ ¬ C.map (fun x => A x ∧ ¬ S x) x))
      (C.map (next adj A S)) := by
  classical
  intro v hv
  obtain ⟨u, ⟨hu, hq⟩, he⟩ := hv
  apply C.neighbors (fun x => A x ∧ ¬ S x)
  refine ⟨u, ?_, he⟩
  apply Classical.byContradiction
  intro hr
  exact hq ⟨hu, hr⟩

theorem wins_compressed {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (ms : List Nat) (A B : Board n)
    (inc : Subset B (C.map A)) (h : wins adj ms A) : wins adj ms B := by
  induction ms generalizing A B with
  | nil => exact fun x hx => map_empty C A h x (inc x hx)
  | cons m ms ih =>
      obtain ⟨S, hS, hw⟩ := h
      refine ⟨fun x => B x ∧ ¬ C.map (fun x => A x ∧ ¬ S x) x,
        Nat.le_trans (reduced_probe_bound C A B S inc) hS, ?_⟩
      exact ih _ _ (reduced_step C A B S) hw

theorem optimal_fixed_normal_form {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (idem : ∀ A, C.map (C.map A) = C.map A)
    (ms : List Nat) (A B : Board n) (inc : Subset B (C.map A))
    (hB : Fixed C B) (h : wins adj ms A) : fixedWins adj C ms B := by
  classical
  induction ms generalizing A B with
  | nil => exact ⟨hB, fun x hx => map_empty C A h x (inc x hx)⟩
  | cons m ms ih =>
      obtain ⟨S, hS, hw⟩ := h
      let R : Board n := fun x => A x ∧ ¬ S x
      let Q : Board n := fun x => B x ∧ ¬ C.map R x
      have survivors : (fun x => B x ∧ ¬ Q x) = (fun x => B x ∧ C.map R x) := by
        funext x
        apply propext
        simp only [Q]
        constructor
        · rintro ⟨hb, hq⟩
          refine ⟨hb, ?_⟩
          apply Classical.byContradiction
          intro hr
          exact hq ⟨hb, hr⟩
        · rintro ⟨hb, hr⟩
          exact ⟨hb, fun h => h.2 hr⟩
      have hr : Fixed C (fun x => B x ∧ ¬ Q x) := by
        rw [survivors]
        exact fixed_intersection C B (C.map R) hB (idem R)
      have hn : Fixed C (next adj B Q) := fixed_neighbors C _ hr
      refine ⟨hB, Q, Nat.le_trans (reduced_probe_bound C A B S inc) hS, hr, ?_⟩
      exact ih _ _ (reduced_step C A B S) hn hw

theorem fixedWins_implies_wins {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (ms : List Nat) (A : Board n)
    (h : fixedWins adj C ms A) : wins adj ms A := by
  induction ms generalizing A with
  | nil => exact h.2
  | cons m ms ih =>
      obtain ⟨_, S, hS, _, hw⟩ := h
      exact ⟨S, hS, ih _ hw⟩

theorem fixed_winning_iff {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (idem : ∀ A, C.map (C.map A) = C.map A)
    (ms : List Nat) (A : Board n) (hA : Fixed C A) :
    wins adj ms A ↔ fixedWins adj C ms A := by
  constructor
  · exact optimal_fixed_normal_form C idem ms A A (by rw [hA]; exact fun _ h => h) hA
  · exact fixedWins_implies_wins C ms A

theorem constant_wins {n : Nat} (adj : Fin n → Fin n → Prop) (m t : Nat)
    (A : Board n) : wins adj (List.replicate t m) A ↔
      winning adj (fun S => card S ≤ m) t A := by
  induction t generalizing A with
  | zero => rfl
  | succ t ih =>
      simp only [List.replicate_succ, wins, winning]
      constructor
      · rintro ⟨S, hS, hw⟩
        exact ⟨S, hS, (ih _).mp hw⟩
      · rintro ⟨S, hS, hw⟩
        exact ⟨S, hS, (ih _).mpr hw⟩

theorem fixed_iff_actual_capture {n : Nat} (adj : Fin n → Fin n → Prop)
    (noDeadEnds : ∀ v, ∃ w, adj v w) (C : Compression adj)
    (idem : ∀ A, C.map (C.map A) = C.map A) (m t : Nat)
    (A : Board n) (hA : Fixed C A) :
    fixedWins adj C (List.replicate (t + 1) m) A ↔
      ∃ probes : Nat → Board n,
        (∀ i, i < t + 1 → card (probes i) ≤ m) ∧ GuaranteesAt adj A probes t := by
  rw [← fixed_winning_iff C idem _ A hA, constant_wins]
  exact winning_iff_guarantees adj (fun S => card S ≤ m) noDeadEnds t A

end Princess.StrategyCompression

#print axioms Princess.StrategyCompression.wins_compressed
#print axioms Princess.StrategyCompression.optimal_fixed_normal_form
#print axioms Princess.StrategyCompression.fixed_iff_actual_capture
