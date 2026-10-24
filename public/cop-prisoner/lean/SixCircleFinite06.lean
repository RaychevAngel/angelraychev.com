import CircularSourceRanks
/- Retained row 6 of research/six-circle-recipes.json.
Source SHA256: 1b166f2df88b1cba803777c5bd6c15a7cf4347c017840e0495cddc2408cb2d6a.
Ranks are supplied data, checked against every cop location at recipient zero;
CircularSourceRanks.rotate_ranks proves all recipients by rotation. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixCircleFinite06
open CircularSourceRanks RobustLayers Extremal FiniteGame
 def core : List Nat := [2,3,5,7,8,9,12,13,16,17]
 def envelope : List Nat := [0,1,2,3,4,5,7,8,9,12,13,16,17]
 def rank (s : Fin 20) : Nat := (if s.val < 10 then (if s.val < 5 then (if s.val < 2 then (if s.val < 1 then 0 else 3) else (if s.val < 3 then 3 else (if s.val < 4 then 1 else 1))) else (if s.val < 7 then (if s.val < 6 then 2 else 4) else (if s.val < 8 then 1 else (if s.val < 9 then 1 else 3)))) else (if s.val < 15 then (if s.val < 12 then (if s.val < 11 then 2 else 1) else (if s.val < 13 then 1 else (if s.val < 14 then 1 else 4))) else (if s.val < 17 then (if s.val < 16 then 1 else 3) else (if s.val < 18 then 1 else (if s.val < 19 then 1 else 4)))))
 theorem subset : ∀ d∈core, d∈envelope := by decide +kernel
 theorem local_checked : Checked (n:=20) (by decide) core envelope rank := by
   unfold Checked
   decide +kernel
 theorem checked : SourceRanks (arc core) (arc envelope) (⟨0,by decide⟩ : Fin 20) rank :=
   checked_ranks (by decide) core envelope rank local_checked
 theorem counts : arcCount (arc (n:=20) core)=200 ∧
     arcCount (arc (n:=20) envelope)=240 := by
   constructor <;> rw [arcCount_eq] <;> decide +kernel
 theorem maximum {m : Nat} (low : 200≤m) (high : m≤240) :
     IsMaximum 20 m (380-m) :=
   CircularSourceRanks.maximum (by decide) core envelope rank subset checked
     (counts.1 ▸ low) (counts.2 ▸ high)
 #print axioms maximum
end Delivery.SixCircleFinite06
