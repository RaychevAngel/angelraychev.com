import PathLowerGeometry

/-! The two initial parity cohorts under an arbitrary physical probe schedule.
No prescribed sweep or restriction on the schedule is assumed.
-/

namespace Princess.PathCohorts

open Princess.PathGeometry
open Princess.PathSweep
open Princess.LadderCardinality
open Princess.CaptureRecurrence

def belief {n : Nat} (probes : Nat → Region (Fin n)) (p t : Nat) : Region (Fin n) :=
  Princess.possible adj (fullParity p) probes t

def shots {n : Nat} (probes : Nat → Region (Fin n)) (p t : Nat) : Region (Fin n) :=
  fun v => probes t v ∧ (v.val + 1) % 2 = (p + t) % 2

theorem belief_parity {n : Nat} (probes : Nat → Region (Fin n)) (p t : Nat)
    (hp : p < 2) : ∀ v, belief probes p t v → (v.val + 1) % 2 = (p + t) % 2 := by
  induction t with
  | zero =>
      intro v hv
      change (v.val + 1) % 2 = p at hv
      simpa only [Nat.add_zero, Nat.mod_eq_of_lt hp] using hv
  | succ t ih =>
      rintro v ⟨u, ⟨hu, _⟩, hadj⟩
      have hpar := ih u hu
      have opp := adj_parity u v hadj
      omega

theorem belief_step {n : Nat} (probes : Nat → Region (Fin n)) (p t : Nat)
    (hp : p < 2) :
    belief probes p (t + 1) = next adj (belief probes p t) (shots probes p t) := by
  funext v
  apply propext
  constructor
  · rintro ⟨u, ⟨hu, hs⟩, hadj⟩
    exact ⟨u, ⟨hu, fun h => hs h.1⟩, hadj⟩
  · rintro ⟨u, ⟨hu, hs⟩, hadj⟩
    exact ⟨u, ⟨hu, fun h => hs ⟨h, belief_parity probes p t hp u hu⟩⟩, hadj⟩

theorem shots_partition {n : Nat} (probes : Nat → Region (Fin n)) (t : Nat) :
    card (shots probes 0 t) + card (shots probes 1 t) = card (probes t) := by
  have h := cardOn_split (List.finRange n) (probes t)
    (fun v => (v.val + 1) % 2 = t % 2)
  have first : (fun v : Fin n => probes t v ∧ (v.val + 1) % 2 = t % 2) =
      shots probes 0 t := by
    funext v
    apply propext
    change (probes t v ∧ (v.val + 1) % 2 = t % 2) ↔
      (probes t v ∧ (v.val + 1) % 2 = (0 + t) % 2)
    simp [Nat.zero_add]
  have second : (fun v : Fin n => probes t v ∧ ¬ (v.val + 1) % 2 = t % 2) =
      shots probes 1 t := by
    funext v
    apply propext
    have parity : (¬ (v.val + 1) % 2 = t % 2) ↔
        (v.val + 1) % 2 = (1 + t) % 2 := by omega
    exact and_congr_right (fun _ => parity)
  change card (probes t) = card _ + card _ at h
  rw [first, second] at h
  exact h.symm

theorem full_parity_card (n p : Nat) (hp : p < 2) :
    card (fullParity (n := n) p) = (n + p) / 2 := by
  have eq : fullParity (n := n) p = (fun v : Fin n => v.val % 2 = (p + 1) % 2) := by
    funext v
    apply propext
    unfold fullParity
    omega
  rw [eq, card_parity n ((p + 1) % 2) (by omega)]
  omega

theorem empty_card {n : Nat} (B : Region (Fin n)) (empty : Empty B) : card B = 0 := by
  have eq : B = (fun _ => False) := by
    funext v
    exact propext ⟨empty v, False.elim⟩
  rw [eq, card_empty]

theorem full_empty_implies_cohort {n : Nat} (probes : Nat → Region (Fin n))
    (p t : Nat) (h : Empty (Princess.possible adj (fun _ => True) probes t)) :
    Empty (belief probes p t) := by
  intro v hv
  exact h v (Princess.possible_mono_initial adj (fullParity p) (fun _ => True)
    probes (fun _ _ => True.intro) t v hv)

end Princess.PathCohorts
