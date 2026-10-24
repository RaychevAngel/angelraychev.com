import CircularSourceRanks
/- Retained row 18 of research/six-circle-recipes.json.
Source SHA256: 1b166f2df88b1cba803777c5bd6c15a7cf4347c017840e0495cddc2408cb2d6a.
Ranks are supplied data, checked against every cop location at recipient zero;
CircularSourceRanks.rotate_ranks proves all recipients by rotation. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixCircleFinite18
open CircularSourceRanks RobustLayers Extremal FiniteGame
 def core : List Nat := [1,4,5,7,8,9]
 def envelope : List Nat := [0,1,4,5,7,8,9,12,14,17,18,22,23,26]
 def rank (s : Fin 27) : Nat := (if s.val < 13 then (if s.val < 6 then (if s.val < 3 then (if s.val < 1 then 0 else (if s.val < 2 then 7 else 11)) else (if s.val < 4 then 11 else (if s.val < 5 then 7 else 6))) else (if s.val < 9 then (if s.val < 7 then 5 else (if s.val < 8 then 10 else 4)) else (if s.val < 11 then (if s.val < 10 then 10 else 10) else (if s.val < 12 then 4 else 3)))) else (if s.val < 20 then (if s.val < 16 then (if s.val < 14 then 2 else (if s.val < 15 then 9 else 2)) else (if s.val < 18 then (if s.val < 17 then 9 else 9) else (if s.val < 19 then 1 else 1))) else (if s.val < 23 then (if s.val < 21 then 1 else (if s.val < 22 then 8 else 1)) else (if s.val < 25 then (if s.val < 24 then 1 else 8) else (if s.val < 26 then 7 else 1)))))
 theorem subset : ∀ d∈core, d∈envelope := by decide +kernel
 theorem local_checked : Checked (n:=27) (by decide) core envelope rank := by
   unfold Checked
   decide +kernel
 theorem checked : SourceRanks (arc core) (arc envelope) (⟨0,by decide⟩ : Fin 27) rank :=
   checked_ranks (by decide) core envelope rank local_checked
 theorem counts : arcCount (arc (n:=27) core)=162 ∧
     arcCount (arc (n:=27) envelope)=351 := by
   constructor <;> rw [arcCount_eq] <;> decide +kernel
 theorem maximum {m : Nat} (low : 162≤m) (high : m≤351) :
     IsMaximum 27 m (702-m) :=
   CircularSourceRanks.maximum (by decide) core envelope rank subset checked
     (counts.1 ▸ low) (counts.2 ▸ high)
 #print axioms maximum
end Delivery.SixCircleFinite18
