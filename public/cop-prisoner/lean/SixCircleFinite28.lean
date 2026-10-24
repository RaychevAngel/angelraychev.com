import CircularSourceRanks
/- Retained row 28 of research/six-circle-recipes.json.
Source SHA256: 1b166f2df88b1cba803777c5bd6c15a7cf4347c017840e0495cddc2408cb2d6a.
Ranks are supplied data, checked against every cop location at recipient zero;
CircularSourceRanks.rotate_ranks proves all recipients by rotation. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixCircleFinite28
open CircularSourceRanks RobustLayers Extremal FiniteGame
 def core : List Nat := [1,4,5,7,8,9]
 def envelope : List Nat := [0,1,4,5,7,8,9,13,15,18,19,22,23,24,27,28,31,32,33]
 def rank (s : Fin 36) : Nat := (if s.val < 18 then (if s.val < 9 then (if s.val < 4 then (if s.val < 2 then (if s.val < 1 then 0 else 11) else (if s.val < 3 then 16 else 10)) else (if s.val < 6 then (if s.val < 5 then 16 else 21) else (if s.val < 7 then 10 else (if s.val < 8 then 9 else 8)))) else (if s.val < 13 then (if s.val < 11 then (if s.val < 10 then 15 else 7) else (if s.val < 12 then 15 else 20)) else (if s.val < 15 then (if s.val < 14 then 7 else 6) else (if s.val < 16 then 5 else (if s.val < 17 then 14 else 4))))) else (if s.val < 27 then (if s.val < 22 then (if s.val < 20 then (if s.val < 19 then 14 else 19) else (if s.val < 21 then 4 else 3)) else (if s.val < 24 then (if s.val < 23 then 2 else 13) else (if s.val < 25 then 2 else (if s.val < 26 then 13 else 18)))) else (if s.val < 31 then (if s.val < 29 then (if s.val < 28 then 1 else 1) else (if s.val < 30 then 1 else 12)) else (if s.val < 33 then (if s.val < 32 then 1 else 1) else (if s.val < 34 then 17 else (if s.val < 35 then 22 else 1))))))
 theorem subset : ∀ d∈core, d∈envelope := by decide +kernel
 theorem local_checked : Checked (n:=36) (by decide) core envelope rank := by
   unfold Checked
   decide +kernel
 theorem checked : SourceRanks (arc core) (arc envelope) (⟨0,by decide⟩ : Fin 36) rank :=
   checked_ranks (by decide) core envelope rank local_checked
 theorem counts : arcCount (arc (n:=36) core)=216 ∧
     arcCount (arc (n:=36) envelope)=648 := by
   constructor <;> rw [arcCount_eq] <;> decide +kernel
 theorem maximum {m : Nat} (low : 216≤m) (high : m≤648) :
     IsMaximum 36 m (1260-m) :=
   CircularSourceRanks.maximum (by decide) core envelope rank subset checked
     (counts.1 ▸ low) (counts.2 ▸ high)
 #print axioms maximum
end Delivery.SixCircleFinite28
