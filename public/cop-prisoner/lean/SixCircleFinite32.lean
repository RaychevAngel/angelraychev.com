import CircularSourceRanks
/- Retained row 32 of research/six-circle-recipes.json.
Source SHA256: 1b166f2df88b1cba803777c5bd6c15a7cf4347c017840e0495cddc2408cb2d6a.
Ranks are supplied data, checked against every cop location at recipient zero;
CircularSourceRanks.rotate_ranks proves all recipients by rotation. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixCircleFinite32
open CircularSourceRanks RobustLayers Extremal FiniteGame
 def core : List Nat := [1,4,5,7,8,9]
 def envelope : List Nat := [0,1,4,5,7,8,9,12,16,17,20,21,24,25,28,29,32,33,36,37]
 def rank (s : Fin 40) : Nat := (if s.val < 20 then (if s.val < 10 then (if s.val < 5 then (if s.val < 2 then (if s.val < 1 then 0 else 21) else (if s.val < 3 then 20 else (if s.val < 4 then 13 else 12))) else (if s.val < 7 then (if s.val < 6 then 11 else 26) else (if s.val < 8 then 10 else (if s.val < 9 then 20 else 19)))) else (if s.val < 15 then (if s.val < 12 then (if s.val < 11 then 10 else 9) else (if s.val < 13 then 8 else (if s.val < 14 then 25 else 7))) else (if s.val < 17 then (if s.val < 16 then 19 else 18) else (if s.val < 18 then 7 else (if s.val < 19 then 6 else 5))))) else (if s.val < 30 then (if s.val < 25 then (if s.val < 22 then (if s.val < 21 then 24 else 4) else (if s.val < 23 then 18 else (if s.val < 24 then 17 else 4))) else (if s.val < 27 then (if s.val < 26 then 3 else 2) else (if s.val < 28 then 23 else (if s.val < 29 then 2 else 17)))) else (if s.val < 35 then (if s.val < 32 then (if s.val < 31 then 16 else 1) else (if s.val < 33 then 1 else (if s.val < 34 then 1 else 22))) else (if s.val < 37 then (if s.val < 36 then 1 else 1) else (if s.val < 38 then 15 else (if s.val < 39 then 14 else 1))))))
 theorem subset : ∀ d∈core, d∈envelope := by decide +kernel
 theorem local_checked : Checked (n:=40) (by decide) core envelope rank := by
   unfold Checked
   decide +kernel
 theorem checked : SourceRanks (arc core) (arc envelope) (⟨0,by decide⟩ : Fin 40) rank :=
   checked_ranks (by decide) core envelope rank local_checked
 theorem counts : arcCount (arc (n:=40) core)=240 ∧
     arcCount (arc (n:=40) envelope)=760 := by
   constructor <;> rw [arcCount_eq] <;> decide +kernel
 theorem maximum {m : Nat} (low : 240≤m) (high : m≤760) :
     IsMaximum 40 m (1560-m) :=
   CircularSourceRanks.maximum (by decide) core envelope rank subset checked
     (counts.1 ▸ low) (counts.2 ▸ high)
 #print axioms maximum
end Delivery.SixCircleFinite32
