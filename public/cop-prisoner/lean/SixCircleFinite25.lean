import CircularSourceRanks
/- Retained row 25 of research/six-circle-recipes.json.
Source SHA256: 1b166f2df88b1cba803777c5bd6c15a7cf4347c017840e0495cddc2408cb2d6a.
Ranks are supplied data, checked against every cop location at recipient zero;
CircularSourceRanks.rotate_ranks proves all recipients by rotation. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixCircleFinite25
open CircularSourceRanks RobustLayers Extremal FiniteGame
 def core : List Nat := [1,4,5,7,8,9]
 def envelope : List Nat := [0,1,4,5,7,8,9,12,13,16,17,20,21,24,25,28,29,32]
 def rank (s : Fin 33) : Nat := (if s.val < 16 then (if s.val < 8 then (if s.val < 4 then (if s.val < 2 then (if s.val < 1 then 0 else 17) else (if s.val < 3 then 16 else 10)) else (if s.val < 6 then (if s.val < 5 then 9 else 8) else (if s.val < 7 then 21 else 7))) else (if s.val < 12 then (if s.val < 10 then (if s.val < 9 then 16 else 15) else (if s.val < 11 then 7 else 6)) else (if s.val < 14 then (if s.val < 13 then 5 else 20) else (if s.val < 15 then 4 else 15)))) else (if s.val < 24 then (if s.val < 20 then (if s.val < 18 then (if s.val < 17 then 14 else 4) else (if s.val < 19 then 3 else 2)) else (if s.val < 22 then (if s.val < 21 then 19 else 2) else (if s.val < 23 then 14 else 13))) else (if s.val < 28 then (if s.val < 26 then (if s.val < 25 then 1 else 1) else (if s.val < 27 then 1 else 18)) else (if s.val < 30 then (if s.val < 29 then 1 else 1) else (if s.val < 31 then 12 else (if s.val < 32 then 11 else 1))))))
 theorem subset : ∀ d∈core, d∈envelope := by decide +kernel
 theorem local_checked : Checked (n:=33) (by decide) core envelope rank := by
   unfold Checked
   decide +kernel
 theorem checked : SourceRanks (arc core) (arc envelope) (⟨0,by decide⟩ : Fin 33) rank :=
   checked_ranks (by decide) core envelope rank local_checked
 theorem counts : arcCount (arc (n:=33) core)=198 ∧
     arcCount (arc (n:=33) envelope)=561 := by
   constructor <;> rw [arcCount_eq] <;> decide +kernel
 theorem maximum {m : Nat} (low : 198≤m) (high : m≤561) :
     IsMaximum 33 m (1056-m) :=
   CircularSourceRanks.maximum (by decide) core envelope rank subset checked
     (counts.1 ▸ low) (counts.2 ▸ high)
 #print axioms maximum
end Delivery.SixCircleFinite25
