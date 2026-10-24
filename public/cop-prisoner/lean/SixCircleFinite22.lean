import CircularSourceRanks
/- Retained row 22 of research/six-circle-recipes.json.
Source SHA256: 1b166f2df88b1cba803777c5bd6c15a7cf4347c017840e0495cddc2408cb2d6a.
Ranks are supplied data, checked against every cop location at recipient zero;
CircularSourceRanks.rotate_ranks proves all recipients by rotation. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixCircleFinite22
open CircularSourceRanks RobustLayers Extremal FiniteGame
 def core : List Nat := [1,4,5,7,8,9]
 def envelope : List Nat := [0,1,4,5,7,8,9,12,13,16,17,18,21,22,25,26,27]
 def rank (s : Fin 30) : Nat := (if s.val < 15 then (if s.val < 7 then (if s.val < 3 then (if s.val < 1 then 0 else (if s.val < 2 then 9 else 8)) else (if s.val < 5 then (if s.val < 4 then 13 else 7) else (if s.val < 6 then 13 else 13))) else (if s.val < 11 then (if s.val < 9 then (if s.val < 8 then 7 else 6) else (if s.val < 10 then 5 else 12)) else (if s.val < 13 then (if s.val < 12 then 4 else 12) else (if s.val < 14 then 12 else 4)))) else (if s.val < 22 then (if s.val < 18 then (if s.val < 16 then 3 else (if s.val < 17 then 2 else 11)) else (if s.val < 20 then (if s.val < 19 then 2 else 11) else (if s.val < 21 then 11 else 1))) else (if s.val < 26 then (if s.val < 24 then (if s.val < 23 then 1 else 1) else (if s.val < 25 then 10 else 1)) else (if s.val < 28 then (if s.val < 27 then 1 else 10) else (if s.val < 29 then 14 else 1)))))
 theorem subset : ∀ d∈core, d∈envelope := by decide +kernel
 theorem local_checked : Checked (n:=30) (by decide) core envelope rank := by
   unfold Checked
   decide +kernel
 theorem checked : SourceRanks (arc core) (arc envelope) (⟨0,by decide⟩ : Fin 30) rank :=
   checked_ranks (by decide) core envelope rank local_checked
 theorem counts : arcCount (arc (n:=30) core)=180 ∧
     arcCount (arc (n:=30) envelope)=480 := by
   constructor <;> rw [arcCount_eq] <;> decide +kernel
 theorem maximum {m : Nat} (low : 180≤m) (high : m≤480) :
     IsMaximum 30 m (870-m) :=
   CircularSourceRanks.maximum (by decide) core envelope rank subset checked
     (counts.1 ▸ low) (counts.2 ▸ high)
 #print axioms maximum
end Delivery.SixCircleFinite22
