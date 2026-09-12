import FourCubeTimeCounterData
namespace Princess.FourCubeTimeCounter
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rank_left_1 : ∀ a : Fin 32, ∀ b : Fin 33,
    rank 1 a.val b.val ≤ rank 1 (a.val+1) b.val := by decide +kernel

theorem rank_right_1 : ∀ a : Fin 33, ∀ b : Fin 32,
    rank 1 a.val b.val ≤ rank 1 a.val (b.val+1) := by decide +kernel

theorem rank_step_1 : ∀ a b : Fin 33, ∀ p : Fin 32, p.val≤budget 1 →
    rank 1 a.val b.val ≤ 1+rank 1
      (profile (b.val-(budget 1-p.val))) (profile (a.val-p.val)) := by decide +kernel

end Princess.FourCubeTimeCounter
