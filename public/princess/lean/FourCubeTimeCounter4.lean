import FourCubeTimeCounterData
namespace Princess.FourCubeTimeCounter
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rank_left_4 : ∀ a : Fin 32, ∀ b : Fin 33,
    rank 4 a.val b.val ≤ rank 4 (a.val+1) b.val := by decide +kernel

theorem rank_right_4 : ∀ a : Fin 33, ∀ b : Fin 32,
    rank 4 a.val b.val ≤ rank 4 a.val (b.val+1) := by decide +kernel

theorem rank_step_4 : ∀ a b : Fin 33, ∀ p : Fin 32, p.val≤budget 4 →
    rank 4 a.val b.val ≤ 1+rank 4
      (profile (b.val-(budget 4-p.val))) (profile (a.val-p.val)) := by decide +kernel

end Princess.FourCubeTimeCounter
