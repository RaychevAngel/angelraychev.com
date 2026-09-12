import FourCubeTimeCounter0
import FourCubeTimeCounter1
import FourCubeTimeCounter2
import FourCubeTimeCounter3
import FourCubeTimeCounter4
import FourCubeTimeCounter5
import FourCubeTimeCounter6
import FourCubeTimeCounter7
import FourCubeTimeCounter8
import FourCubeTimeCounter9

namespace Princess.FourCubeTimeCounter
theorem rank_left : ∀ kind : Fin 10, ∀ a : Fin 32, ∀ b : Fin 33, rank kind a.val b.val≤rank kind (a.val+1) b.val := by
  intro kind
  have h : kind=0 ∨ kind=1 ∨ kind=2 ∨ kind=3 ∨ kind=4 ∨ kind=5 ∨ kind=6 ∨ kind=7 ∨ kind=8 ∨ kind=9 := by have := kind.isLt; omega
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst kind; exact rank_left_0
  · subst kind; exact rank_left_1
  · subst kind; exact rank_left_2
  · subst kind; exact rank_left_3
  · subst kind; exact rank_left_4
  · subst kind; exact rank_left_5
  · subst kind; exact rank_left_6
  · subst kind; exact rank_left_7
  · subst kind; exact rank_left_8
  · subst kind; exact rank_left_9
theorem rank_right : ∀ kind : Fin 10, ∀ a : Fin 33, ∀ b : Fin 32, rank kind a.val b.val≤rank kind a.val (b.val+1) := by
  intro kind
  have h : kind=0 ∨ kind=1 ∨ kind=2 ∨ kind=3 ∨ kind=4 ∨ kind=5 ∨ kind=6 ∨ kind=7 ∨ kind=8 ∨ kind=9 := by have := kind.isLt; omega
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst kind; exact rank_right_0
  · subst kind; exact rank_right_1
  · subst kind; exact rank_right_2
  · subst kind; exact rank_right_3
  · subst kind; exact rank_right_4
  · subst kind; exact rank_right_5
  · subst kind; exact rank_right_6
  · subst kind; exact rank_right_7
  · subst kind; exact rank_right_8
  · subst kind; exact rank_right_9
theorem rank_step : ∀ kind : Fin 10, ∀ a b : Fin 33, ∀ p : Fin 32, p.val≤budget kind → rank kind a.val b.val≤1+rank kind (profile (b.val-(budget kind-p.val))) (profile (a.val-p.val)) := by
  intro kind
  have h : kind=0 ∨ kind=1 ∨ kind=2 ∨ kind=3 ∨ kind=4 ∨ kind=5 ∨ kind=6 ∨ kind=7 ∨ kind=8 ∨ kind=9 := by have := kind.isLt; omega
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst kind; exact rank_step_0
  · subst kind; exact rank_step_1
  · subst kind; exact rank_step_2
  · subst kind; exact rank_step_3
  · subst kind; exact rank_step_4
  · subst kind; exact rank_step_5
  · subst kind; exact rank_step_6
  · subst kind; exact rank_step_7
  · subst kind; exact rank_step_8
  · subst kind; exact rank_step_9

theorem mono_from_adjacent (f : Nat → Nat) (cap : Nat)
    (h : ∀ k, k<cap → f k≤f (k+1)) (a b : Nat) (hab : a≤b) (hb : b≤cap) : f a≤f b := by
  induction hab with
  | refl => exact Nat.le_refl _
  | @step b hab ih => exact Nat.le_trans (ih (by omega)) (h b (by omega))

theorem profile_mono (a b : Nat) (hab : a≤b) (hb : b≤32) : profile a≤profile b := by
  apply mono_from_adjacent profile 32 _ a b hab hb
  intro k hk
  exact profile_mono_checked ⟨k,hk⟩

theorem rank_mono (kind : Fin 10) (a b a' b' : Nat)
    (ha : a≤a') (hb : b≤b') (ha' : a'≤32) (hb' : b'≤32) : rank kind a b≤rank kind a' b' := by
  have h1 : rank kind a b≤rank kind a' b := by
    apply mono_from_adjacent (fun k => rank kind k b) 32 _ a a' ha ha'
    intro k hk; exact rank_left kind ⟨k,hk⟩ ⟨b,by omega⟩
  have h2 : rank kind a' b≤rank kind a' b' := by
    apply mono_from_adjacent (fun k => rank kind a' k) 32 _ b b' hb hb'
    intro k hk; exact rank_right kind ⟨a',by omega⟩ ⟨k,hk⟩
  exact Nat.le_trans h1 h2

theorem budget_bound : ∀ kind : Fin 10, budget kind≤31 := by decide

theorem physical_step (kind : Fin 10) (a b a' b' p q : Nat)
    (ha : a≤32) (hb : b≤32) (ha' : a'≤32) (hb' : b'≤32)
    (shots : p+q≤budget kind) (nextA : profile (b-q)≤a') (nextB : profile (a-p)≤b') :
    rank kind a b≤1+rank kind a' b' := by
  have cap := budget_bound kind
  have hp : p≤budget kind := by omega
  have hs := rank_step kind ⟨a,by omega⟩ ⟨b,by omega⟩ ⟨p,by omega⟩ hp
  have hmono := profile_mono (b-(budget kind-p)) (b-q) (by omega) (by omega)
  have compare := rank_mono kind (profile (b-(budget kind-p))) (profile (a-p)) a' b'
    (Nat.le_trans hmono nextA) nextB ha' hb'
  exact Nat.le_trans hs (Nat.add_le_add_left compare 1)

end Princess.FourCubeTimeCounter
#print axioms Princess.FourCubeTimeCounter.physical_step
