import CircularSourceRanks
/- Retained row 20 of research/six-circle-recipes.json.
Source SHA256: 1b166f2df88b1cba803777c5bd6c15a7cf4347c017840e0495cddc2408cb2d6a.
Ranks are supplied data, checked against every cop location at recipient zero;
CircularSourceRanks.rotate_ranks proves all recipients by rotation. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixCircleFinite20
open CircularSourceRanks RobustLayers Extremal FiniteGame
 def core : List Nat := [1,14,15,17,18,19]
 def envelope : List Nat := [0,1,4,5,8,9,10,14,15,17,18,19,22,23,24,27]
 def rank (s : Fin 28) : Nat := (if s.val < 14 then (if s.val < 7 then (if s.val < 3 then (if s.val < 1 then 0 else (if s.val < 2 then 9 else 14)) else (if s.val < 5 then (if s.val < 4 then 7 else 6) else (if s.val < 6 then 5 else 12))) else (if s.val < 10 then (if s.val < 8 then 4 else (if s.val < 9 then 12 else 1)) else (if s.val < 12 then (if s.val < 11 then 1 else 1) else (if s.val < 13 then 10 else 1)))) else (if s.val < 21 then (if s.val < 17 then (if s.val < 15 then 1 else (if s.val < 16 then 9 else 8)) else (if s.val < 19 then (if s.val < 18 then 13 else 6) else (if s.val < 20 then 13 else 4))) else (if s.val < 24 then (if s.val < 22 then 3 else (if s.val < 23 then 2 else 11)) else (if s.val < 26 then (if s.val < 25 then 2 else 11) else (if s.val < 27 then 10 else 1)))))
 theorem subset : ∀ d∈core, d∈envelope := by decide +kernel
 theorem local_checked : Checked (n:=28) (by decide) core envelope rank := by
   unfold Checked
   decide +kernel
 theorem checked : SourceRanks (arc core) (arc envelope) (⟨0,by decide⟩ : Fin 28) rank :=
   checked_ranks (by decide) core envelope rank local_checked
 theorem counts : arcCount (arc (n:=28) core)=168 ∧
     arcCount (arc (n:=28) envelope)=420 := by
   constructor <;> rw [arcCount_eq] <;> decide +kernel
 theorem maximum {m : Nat} (low : 168≤m) (high : m≤420) :
     IsMaximum 28 m (756-m) :=
   CircularSourceRanks.maximum (by decide) core envelope rank subset checked
     (counts.1 ▸ low) (counts.2 ▸ high)
 #print axioms maximum
end Delivery.SixCircleFinite20
