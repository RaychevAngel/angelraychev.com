import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0097

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19560 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 133 28 56 288 70 198 326), lower := (rows 35 67 133 28 56 288 64 128 256), losses := [] }

theorem u19560 : Upper (D 6) (R 6) [34,65,129,20,40,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19560 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19561 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 28 88 34 356 420 292), lower := (rows 35 67 133 28 88 34 64 128 256), losses := [] }

theorem u19561 : Upper (D 6) (R 6) [34,65,129,20,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19562 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 5, region := 323, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 67 133 28 88 36 354 418 290), lower := (rows 35 67 133 28 88 36 64 128 256), losses := [] }

theorem u19562 : Upper (D 6) (R 6) [34,65,129,20,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19563 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 133 28 88 288 102 166 294), lower := (rows 35 67 133 28 88 288 64 128 256), losses := [] }

theorem u19563 : Upper (D 6) (R 6) [34,65,129,20,72,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19563 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19564 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 28 112 34 332 396 268), lower := (rows 35 67 133 28 112 34 64 128 256), losses := [] }

theorem u19564 : Upper (D 6) (R 6) [34,65,129,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19565 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 3, targets := 4 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 35 67 133 28 112 36 330 394 266), lower := (rows 35 67 133 28 112 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 44 21 44 65 129 257), good := (rows 506 466 508 60 120 60 64 128 256) }] }

theorem u19565 : Upper (D 6) (R 6) [34,65,129,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19566 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 133 28 112 40 326 390 262), lower := (rows 35 67 133 28 112 40 64 128 256), losses := [] }

theorem u19566 : Upper (D 6) (R 6) [34,65,129,20,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19566 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19567 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 3, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 133 28 112 288 78 142 270), lower := (rows 35 67 133 28 112 288 64 128 256), losses := [] }

theorem u19567 : Upper (D 6) (R 6) [34,65,129,20,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19567 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19568 : Route 9 := (fun mask => (mask,id))

def c19568 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19568 : Upper (D 6) (R 6) [34,65,129,20,258,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,20,258,4] 13 (by decide) (choices 1) [8,32] r19568 c19568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5846
  · exact u5847

def b19569 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 133 28 274 40 100 228 356), lower := (rows 35 67 133 28 274 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 24 16 56 89 153 281), good := (rows 485 453 453 508 508 488 64 128 256) }] }

theorem u19569 : Upper (D 6) (R 6) [34,65,129,20,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19569 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19570 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 28 274 96 108 172 300), lower := (rows 35 67 133 28 274 96 64 128 256), losses := [] }

theorem u19570 : Upper (D 6) (R 6) [34,65,129,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19571 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 28 280 34 100 228 356), lower := (rows 35 67 133 28 280 34 64 128 256), losses := [] }

theorem u19571 : Upper (D 6) (R 6) [34,65,129,20,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19572 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 67, targets := 4 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 35 67 133 28 280 36 98 226 354), lower := (rows 35 67 133 28 280 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 44 21 44 65 129 257), good := (rows 506 466 508 60 312 60 64 128 256) }] }

theorem u19572 : Upper (D 6) (R 6) [34,65,129,20,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19573 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 28 280 96 102 166 294), lower := (rows 35 67 133 28 280 96 64 128 256), losses := [] }

theorem u19573 : Upper (D 6) (R 6) [34,65,129,20,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19574 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 28 304 34 76 204 332), lower := (rows 35 67 133 28 304 34 64 128 256), losses := [] }

theorem u19574 : Upper (D 6) (R 6) [34,65,129,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19575 : Route 9 := (fun mask => (mask,id))

def c19575 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19575 : Upper (D 6) (R 6) [34,65,129,20,288,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,20,288,4] 13 (by decide) (choices 1) [2,8] r19575 c19575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5848
  · exact u5849

def b19576 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 133 28 304 40 70 198 326), lower := (rows 35 67 133 28 304 40 64 128 256), losses := [] }

theorem u19576 : Upper (D 6) (R 6) [34,65,129,20,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19576 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19577 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 28 304 96 78 142 270), lower := (rows 35 67 133 28 304 96 64 128 256), losses := [] }

theorem u19577 : Upper (D 6) (R 6) [34,65,129,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19578 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 28 336 34 108 172 300), lower := (rows 35 67 133 28 336 34 64 128 256), losses := [] }

theorem u19578 : Upper (D 6) (R 6) [34,65,129,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19579 : Route 9 := (fun mask => (mask,id))

def c19579 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19579 : Upper (D 6) (R 6) [34,65,129,20,320,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,20,320,4] 13 (by decide) (choices 1) [2,8,32] r19579 c19579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5850
  · exact u5851
  · exact u5852

def r19580 : Route 9 := (fun mask => (mask,id))

def c19580 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19580 : Upper (D 6) (R 6) [34,65,129,20,320,8] 13 := by
  apply FastRouting.sound _ _ [34,65,129,20,320,8] 13 (by decide) (choices 1) [2,4,32] r19580 c19580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5853
  · exact u5854
  · exact u5855

def b19581 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 44 84 34 344 408 280), lower := (rows 35 67 133 44 84 34 64 128 256), losses := [] }

theorem u19581 : Upper (D 6) (R 6) [34,65,129,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19582 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 133 44 84 40 338 402 274), lower := (rows 35 67 133 44 84 40 64 128 256), losses := [] }

theorem u19582 : Upper (D 6) (R 6) [34,65,129,36,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19582 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19583 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 133 44 84 48 330 394 266), lower := (rows 35 67 133 44 84 48 64 128 256), losses := [] }

theorem u19583 : Upper (D 6) (R 6) [34,65,129,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19583 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19584 : Route 9 := (fun mask => (mask,id))

def c19584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19584 : Upper (D 6) (R 6) [34,65,129,36,68,256] 13 := by
  apply FastRouting.sound _ _ [34,65,129,36,68,256] 13 (by decide) (choices 1) [2,8,16] r19584 c19584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5856
  · exact u5857
  · exact u5858

def b19585 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 44 88 34 340 404 276), lower := (rows 35 67 133 44 88 34 64 128 256), losses := [] }

theorem u19585 : Upper (D 6) (R 6) [34,65,129,36,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19586 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 67 133 44 88 36 338 402 274), lower := (rows 35 67 133 44 88 36 64 128 256), losses := [] }

theorem u19586 : Upper (D 6) (R 6) [34,65,129,36,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19587 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 133 44 88 48 326 390 262), lower := (rows 35 67 133 44 88 48 64 128 256), losses := [] }

theorem u19587 : Upper (D 6) (R 6) [34,65,129,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19587 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19588 : Route 9 := (fun mask => (mask,id))

def c19588 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19588 : Upper (D 6) (R 6) [34,65,129,36,72,256] 13 := by
  apply FastRouting.sound _ _ [34,65,129,36,72,256] 13 (by decide) (choices 1) [2,4,16] r19588 c19588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5859
  · exact u5860
  · exact u5861

def b19589 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 67 133 44 274 36 88 216 344), lower := (rows 35 67 133 44 274 36 64 128 256), losses := [] }

theorem u19589 : Upper (D 6) (R 6) [34,65,129,36,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19590 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 133 44 274 40 84 212 340), lower := (rows 35 67 133 44 274 40 64 128 256), losses := [] }

theorem u19590 : Upper (D 6) (R 6) [34,65,129,36,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19590 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19591 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 133 44 274 48 76 204 332), lower := (rows 35 67 133 44 274 48 64 128 256), losses := [] }

theorem u19591 : Upper (D 6) (R 6) [34,65,129,36,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19591 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19592 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 44 274 96 92 156 284), lower := (rows 35 67 133 44 274 96 64 128 256), losses := [] }

theorem u19592 : Upper (D 6) (R 6) [34,65,129,36,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19593 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 44 276 34 88 216 344), lower := (rows 35 67 133 44 276 34 64 128 256), losses := [] }

theorem u19593 : Upper (D 6) (R 6) [34,65,129,36,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19594 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 133 44 276 40 82 210 338), lower := (rows 35 67 133 44 276 40 64 128 256), losses := [] }

theorem u19594 : Upper (D 6) (R 6) [34,65,129,36,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19594 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19595 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 133 44 276 48 74 202 330), lower := (rows 35 67 133 44 276 48 64 128 256), losses := [] }

theorem u19595 : Upper (D 6) (R 6) [34,65,129,36,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19595 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19596 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 44 276 96 90 154 282), lower := (rows 35 67 133 44 276 96 64 128 256), losses := [] }

theorem u19596 : Upper (D 6) (R 6) [34,65,129,36,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19597 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 44 280 34 84 212 340), lower := (rows 35 67 133 44 280 34 64 128 256), losses := [] }

theorem u19597 : Upper (D 6) (R 6) [34,65,129,36,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19598 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 67 133 44 280 36 82 210 338), lower := (rows 35 67 133 44 280 36 64 128 256), losses := [] }

theorem u19598 : Upper (D 6) (R 6) [34,65,129,36,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19599 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 133 44 280 48 70 198 326), lower := (rows 35 67 133 44 280 48 64 128 256), losses := [] }

theorem u19599 : Upper (D 6) (R 6) [34,65,129,36,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19599 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19600 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 44 280 96 86 150 278), lower := (rows 35 67 133 44 280 96 64 128 256), losses := [] }

theorem u19600 : Upper (D 6) (R 6) [34,65,129,36,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19601 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 44 336 34 92 156 284), lower := (rows 35 67 133 44 336 34 64 128 256), losses := [] }

theorem u19601 : Upper (D 6) (R 6) [34,65,129,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19602 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 67 133 44 336 36 90 154 282), lower := (rows 35 67 133 44 336 36 64 128 256), losses := [] }

theorem u19602 : Upper (D 6) (R 6) [34,65,129,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19603 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 133 44 336 40 86 150 278), lower := (rows 35 67 133 44 336 40 64 128 256), losses := [] }

theorem u19603 : Upper (D 6) (R 6) [34,65,129,36,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19603 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19604 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 133 44 336 48 78 142 270), lower := (rows 35 67 133 44 336 48 64 128 256), losses := [] }

theorem u19604 : Upper (D 6) (R 6) [34,65,129,36,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19604 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19605 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 56 84 34 332 396 268), lower := (rows 35 67 133 56 84 34 64 128 256), losses := [] }

theorem u19605 : Upper (D 6) (R 6) [34,65,129,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19606 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 67 133 56 84 36 330 394 266), lower := (rows 35 67 133 56 84 36 64 128 256), losses := [] }

theorem u19606 : Upper (D 6) (R 6) [34,65,129,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19607 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 133 56 84 40 326 390 262), lower := (rows 35 67 133 56 84 40 64 128 256), losses := [] }

theorem u19607 : Upper (D 6) (R 6) [34,65,129,48,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19607 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19608 : Route 9 := (fun mask => (mask,id))

def c19608 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19608 : Upper (D 6) (R 6) [34,65,129,48,68,256] 13 := by
  apply FastRouting.sound _ _ [34,65,129,48,68,256] 13 (by decide) (choices 1) [2,4,8] r19608 c19608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5862
  · exact u5863
  · exact u5864

def r19609 : Route 9 := (fun mask => (mask,id))

def c19609 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19609 : Upper (D 6) (R 6) [34,65,129,48,258,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,48,258,4] 13 (by decide) (choices 1) [4,8] r19609 c19609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5865
  · exact u5866

def b19610 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 67 133 56 274 40 68 196 324), lower := (rows 35 67 133 56 274 40 64 128 256), losses := [] }

theorem u19610 : Upper (D 6) (R 6) [34,65,129,48,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19610 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19611 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 56 274 96 76 140 268), lower := (rows 35 67 133 56 274 96 64 128 256), losses := [] }

theorem u19611 : Upper (D 6) (R 6) [34,65,129,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19612 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 56 276 34 76 204 332), lower := (rows 35 67 133 56 276 34 64 128 256), losses := [] }

theorem u19612 : Upper (D 6) (R 6) [34,65,129,48,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19613 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 67 133 56 276 36 74 202 330), lower := (rows 35 67 133 56 276 36 64 128 256), losses := [] }

theorem u19613 : Upper (D 6) (R 6) [34,65,129,48,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19614 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 133 56 276 40 70 198 326), lower := (rows 35 67 133 56 276 40 64 128 256), losses := [] }

theorem u19614 : Upper (D 6) (R 6) [34,65,129,48,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19614 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19615 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 56 276 96 78 142 270), lower := (rows 35 67 133 56 276 96 64 128 256), losses := [] }

theorem u19615 : Upper (D 6) (R 6) [34,65,129,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19616 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 56 280 34 68 196 324), lower := (rows 35 67 133 56 280 34 64 128 256), losses := [] }

theorem u19616 : Upper (D 6) (R 6) [34,65,129,48,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19617 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 67 133 56 280 36 70 198 326), lower := (rows 35 67 133 56 280 36 64 128 256), losses := [{ target := 5, region := (rows 1 7 7 8 24 0 103 167 295), good := (rows 455 455 455 472 280 454 64 128 256) }] }

theorem u19617 : Upper (D 6) (R 6) [34,65,129,48,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19618 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 56 280 96 70 134 262), lower := (rows 35 67 133 56 280 96 64 128 256), losses := [] }

theorem u19618 : Upper (D 6) (R 6) [34,65,129,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19619 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 56 336 34 76 140 268), lower := (rows 35 67 133 56 336 34 64 128 256), losses := [] }

theorem u19619 : Upper (D 6) (R 6) [34,65,129,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u19619
end Delivery.IrregularNine14.P06
