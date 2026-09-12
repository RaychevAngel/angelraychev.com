import ThreeCubeTimeUpper

/-! Exact capture times on the actual 3×3×3 grid, for every positive budget.
The lower bound tracks both physical color classes under arbitrary probes;
finite isoperimetric certificates and counter potentials imply its progress
inequality. No compression, interval, or prescribed-strategy hypothesis is used. -/
namespace Princess.ThreeCubeTimeClassification
open Princess.ThreeCubeTrap Princess.ThreeCubeLower Princess.LadderCardinality
open Princess.CaptureRecurrence


def slice (B : Region Room) (p : Nat) : Region Room := fun v => B v ∧ color v = p

theorem color_lt (v : Room) : color v < 2 := Nat.mod_lt _ (by decide)

theorem slice_partition (B : Region Room) :
    card (slice B 0) + card (slice B 1) = card B := by
  have h := cardOn_split (List.finRange 27) B (fun v => color v = 0)
  have heq : (fun v => B v ∧ ¬ color v = 0) = slice B 1 := by
    funext v
    apply propext
    have hc := color_lt v
    change (B v ∧ color v ≠ 0) ↔ (B v ∧ color v = 1)
    constructor <;> intro hv <;> exact ⟨hv.1, by have := hv.2; omega⟩
  change card B = card (slice B 0) + card (fun v => B v ∧ ¬ color v = 0) at h
  rw [heq] at h
  exact h.symm

theorem full_card : card (fun _ : Room => True) = 27 :=
  (card_full_iff _).mpr (fun _ => True.intro)

theorem full_even : card (slice (fun _ => True) 0) = 14 := by
  have heq : slice (fun _ => True) 0 = (fun v => color v = 0) := by
    funext v; exact propext (by simp [slice])
  rw [heq, even_size]

theorem full_odd : card (slice (fun _ => True) 1) = 13 := by
  have h := slice_partition (fun _ => True)
  rw [full_even, full_card] at h
  omega

theorem even_le (B : Region Room) : card (slice B 0) ≤ 14 := by
  have h := card_mono (slice B 0) (slice (fun _ => True) 0)
    (fun _ hv => ⟨True.intro, hv.2⟩)
  rw [full_even] at h
  exact h

theorem odd_le (B : Region Room) : card (slice B 1) ≤ 13 := by
  have h := card_mono (slice B 1) (slice (fun _ => True) 1)
    (fun _ hv => ⟨True.intro, hv.2⟩)
  rw [full_odd] at h
  exact h

theorem next_slice (B S : Region Room) (p : Nat) (hp : p < 2) :
    slice (next adj B S) (1 - p) = next adj (slice B p) (slice S p) := by
  funext v
  apply propext
  constructor
  · rintro ⟨⟨u, ⟨hu, hs⟩, hadj⟩, hvp⟩
    have hc := adj_flips u v hadj
    have hup : color u = p := by have := color_lt u; omega
    exact ⟨u, ⟨⟨hu, hup⟩, fun h => hs h.1⟩, hadj⟩
  · rintro ⟨u, ⟨⟨hu, hup⟩, hs⟩, hadj⟩
    refine ⟨⟨u, ⟨hu, fun h => hs ⟨h, hup⟩⟩, hadj⟩, ?_⟩
    have hc := adj_flips u v hadj
    omega

theorem empty_card (B : Region Room) (h : Empty B) : card B = 0 := by
  have heq : B = (fun _ => False) := by
    funext v; exact propext ⟨h v, False.elim⟩
  rw [heq]
  classical
  simp [card, cardOn]

end Princess.ThreeCubeTimeClassification
