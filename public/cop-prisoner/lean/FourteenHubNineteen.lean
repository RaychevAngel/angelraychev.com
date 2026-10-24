import RobustLayers
import GuaranteedPrefix
/- Literal instance of the existing fourteen-hub recipe, parameters g=3,b=2,r=2.
Adjacency source src/main_interval_layered.py SHA256 a72f0e7c27e06126ebdd930e7c1e3a3c48017b484700ff84bb5accdaf42dc4b7.
Every source/recipient/cop rank obligation and both exact arc counts are checked. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.FourteenHubNineteen
open FiniteGame Extremal RobustLayers RobustTwoMove
 def baseRow (s : Fin 19) : Nat := (if s.val < 9 then (if s.val < 4 then (if s.val < 2 then (if s.val < 1 then 515966 else 523901) else (if s.val < 3 then 523515 else 522743)) else (if s.val < 6 then (if s.val < 5 then 521199 else 518111) else (if s.val < 7 then 511935 else (if s.val < 8 then 524079 else 523998)))) else (if s.val < 14 then (if s.val < 11 then (if s.val < 10 then 523709 else 523258) else (if s.val < 12 then 522229 else (if s.val < 13 then 520171 else 516055))) else (if s.val < 16 then (if s.val < 15 then 13695 else 11007) else (if s.val < 17 then 5631 else (if s.val < 18 then 60083 else 92851)))))
 def upperRow (s : Fin 19) : Nat := (if s.val < 9 then (if s.val < 4 then (if s.val < 2 then (if s.val < 1 then 515966 else 523901) else (if s.val < 3 then 523515 else 522743)) else (if s.val < 6 then (if s.val < 5 then 521199 else 518111) else (if s.val < 7 then 511935 else (if s.val < 8 then 524079 else 523998)))) else (if s.val < 14 then (if s.val < 11 then (if s.val < 10 then 523709 else 523258) else (if s.val < 12 then 522229 else (if s.val < 13 then 520171 else 516055))) else (if s.val < 16 then (if s.val < 15 then 406911 else 404223) else (if s.val < 17 then 398847 else (if s.val < 18 then 322227 else 223923)))))
 def base (s t : Fin 19) : Prop := (baseRow s).testBit t.val=true
 def upper (s t : Fin 19) : Prop := (upperRow s).testBit t.val=true
 instance (s t : Fin 19) : Decidable (base s t) := inferInstanceAs (Decidable (_=true))
 instance (s t : Fin 19) : Decidable (upper s t) := inferInstanceAs (Decidable (_=true))
 def rank (t s : Fin 19) : Nat := if s=t then 0 else if base s t then 1 else if s.val<17 then 2 else 3
 theorem checked : ∀ t, SourceRanks base upper t (rank t) := by
   unfold SourceRanks Legal
   decide +kernel
 theorem subset : Subgraph base upper := by unfold Subgraph; decide +kernel
 theorem loopless : Loopless upper := by unfold Loopless; decide +kernel
 theorem counts : arcCount base=277 ∧ arcCount upper=285 := by
   constructor <;> rw [arcCount_eq] <;> decide +kernel
 theorem maximum {m : Nat} (low : 277≤m) (high : m≤285) : IsMaximum 19 m (342-m) := by
   apply GuaranteedPrefix.maximum base upper subset loopless
   · intro G lower higher s t
     exact universal_guaranteed (ranked_envelope_universal lower higher (checked t) s)
   · rw [counts.1]; exact low
   · rw [counts.2]; exact high
 #print axioms maximum
end Delivery.FourteenHubNineteen
