import CircularSourceRanks
/- Retained row 3 of research/six-circle-recipes.json.
Source SHA256: 1b166f2df88b1cba803777c5bd6c15a7cf4347c017840e0495cddc2408cb2d6a.
Ranks are supplied data, checked against every cop location at recipient zero;
CircularSourceRanks.rotate_ranks proves all recipients by rotation. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixCircleFinite03
open CircularSourceRanks RobustLayers Extremal FiniteGame
 def core : List Nat := [1,5,6,8,9,10]
 def envelope : List Nat := [0,1,5,6,8,9,10,13,15,18]
 def rank (s : Fin 19) : Nat := (if s.val < 9 then (if s.val < 4 then (if s.val < 2 then (if s.val < 1 then 0 else 4) else (if s.val < 3 then 3 else 2)) else (if s.val < 6 then (if s.val < 5 then 6 else 2) else (if s.val < 7 then 6 else (if s.val < 8 then 8 else 5)))) else (if s.val < 14 then (if s.val < 11 then (if s.val < 10 then 1 else 1) else (if s.val < 12 then 1 else (if s.val < 13 then 5 else 1))) else (if s.val < 16 then (if s.val < 15 then 1 else 7) else (if s.val < 17 then 4 else (if s.val < 18 then 7 else 1)))))
 theorem subset : ∀ d∈core, d∈envelope := by decide +kernel
 theorem local_checked : Checked (n:=19) (by decide) core envelope rank := by
   unfold Checked
   decide +kernel
 theorem checked : SourceRanks (arc core) (arc envelope) (⟨0,by decide⟩ : Fin 19) rank :=
   checked_ranks (by decide) core envelope rank local_checked
 theorem counts : arcCount (arc (n:=19) core)=114 ∧
     arcCount (arc (n:=19) envelope)=171 := by
   constructor <;> rw [arcCount_eq] <;> decide +kernel
 theorem maximum {m : Nat} (low : 114≤m) (high : m≤171) :
     IsMaximum 19 m (342-m) :=
   CircularSourceRanks.maximum (by decide) core envelope rank subset checked
     (counts.1 ▸ low) (counts.2 ▸ high)
 #print axioms maximum
end Delivery.SixCircleFinite03
