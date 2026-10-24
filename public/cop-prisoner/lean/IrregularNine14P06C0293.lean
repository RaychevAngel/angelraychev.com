import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0081

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17580 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 84 328 22 36 97 161 289), lower := (rows 11 162 84 328 22 36 64 128 256), losses := [] }

theorem u17580 : Upper (D 6) (R 6) [10,160,80,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17581 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 162 84 328 49 33 70 134 262), lower := (rows 11 162 84 328 49 33 64 128 256), losses := [] }

theorem u17581 : Upper (D 6) (R 6) [10,160,80,320,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17582 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 162 84 328 49 34 69 133 261), lower := (rows 11 162 84 328 49 34 64 128 256), losses := [] }

theorem u17582 : Upper (D 6) (R 6) [10,160,80,320,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17583 : Route 9 := (fun mask => (mask,id))

def c17583 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17583 : Upper (D 6) (R 6) [10,160,80,320,33,4] 13 := by
  apply FastRouting.sound _ _ [10,160,80,320,33,4] 13 (by decide) (choices 1) [1,2,4] r17583 c17583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4874
  · exact u4875
  · exact u4876

def r17584 : Route 9 := (fun mask => (mask,id))

def c17584 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17584 : Upper (D 6) (R 6) [10,160,80,320,36,1] 13 := by
  apply FastRouting.sound _ _ [10,160,80,320,36,1] 13 (by decide) (choices 1) [1,2,4] r17584 c17584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4877
  · exact u4878
  · exact u4879

def b17585 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 84 328 52 34 69 133 261), lower := (rows 11 162 84 328 52 34 64 128 256), losses := [] }

theorem u17585 : Upper (D 6) (R 6) [10,160,80,320,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17586 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 84 328 52 36 67 131 259), lower := (rows 11 162 84 328 52 36 64 128 256), losses := [] }

theorem u17586 : Upper (D 6) (R 6) [10,160,80,320,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17587 : PairBound 9 := { available := 276, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 13 81 34 340 404 276), lower := (rows 11 162 100 13 81 34 64 128 256), losses := [] }

theorem u17587 : Upper (D 6) (R 6) [10,160,96,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17588 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 11 162 100 13 81 36 338 402 274), lower := (rows 11 162 100 13 81 36 64 128 256), losses := [] }

theorem u17588 : Upper (D 6) (R 6) [10,160,96,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17589 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 100 13 81 48 326 390 262), lower := (rows 11 162 100 13 81 48 64 128 256), losses := [] }

theorem u17589 : Upper (D 6) (R 6) [10,160,96,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17589 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17590 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 100 13 81 288 86 150 278), lower := (rows 11 162 100 13 81 288 64 128 256), losses := [] }

theorem u17590 : Upper (D 6) (R 6) [10,160,96,5,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17590 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17591 : PairBound 9 := { available := 276, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 100 13 82 33 340 404 276), lower := (rows 11 162 100 13 82 33 64 128 256), losses := [] }

theorem u17591 : Upper (D 6) (R 6) [10,160,96,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17592 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 11 162 100 13 82 36 337 401 273), lower := (rows 11 162 100 13 82 36 64 128 256), losses := [] }

theorem u17592 : Upper (D 6) (R 6) [10,160,96,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17593 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 100 13 82 48 325 389 261), lower := (rows 11 162 100 13 82 48 64 128 256), losses := [] }

theorem u17593 : Upper (D 6) (R 6) [10,160,96,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17593 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17594 : Route 9 := (fun mask => (mask,id))

def c17594 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17594 : Upper (D 6) (R 6) [10,160,96,5,66,256] 13 := by
  apply FastRouting.sound _ _ [10,160,96,5,66,256] 13 (by decide) (choices 1) [1,4,16] r17594 c17594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4880
  · exact u4881
  · exact u4882

def b17595 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 13 273 34 84 212 340), lower := (rows 11 162 100 13 273 34 64 128 256), losses := [] }

theorem u17595 : Upper (D 6) (R 6) [10,160,96,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17596 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 11 162 100 13 273 36 82 210 338), lower := (rows 11 162 100 13 273 36 64 128 256), losses := [] }

theorem u17596 : Upper (D 6) (R 6) [10,160,96,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17597 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 100 13 273 48 70 198 326), lower := (rows 11 162 100 13 273 48 64 128 256), losses := [] }

theorem u17597 : Upper (D 6) (R 6) [10,160,96,5,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17597 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17598 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 100 13 273 96 86 150 278), lower := (rows 11 162 100 13 273 96 64 128 256), losses := [] }

theorem u17598 : Upper (D 6) (R 6) [10,160,96,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17599 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 100 13 274 33 84 212 340), lower := (rows 11 162 100 13 274 33 64 128 256), losses := [] }

theorem u17599 : Upper (D 6) (R 6) [10,160,96,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17600 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 11 162 100 13 274 36 81 209 337), lower := (rows 11 162 100 13 274 36 64 128 256), losses := [] }

theorem u17600 : Upper (D 6) (R 6) [10,160,96,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17601 : Route 9 := (fun mask => (mask,id))

def c17601 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17601 : Upper (D 6) (R 6) [10,160,96,5,258,16] 13 := by
  apply FastRouting.sound _ _ [10,160,96,5,258,16] 13 (by decide) (choices 1) [1,4] r17601 c17601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4883
  · exact u4884

def b17602 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 100 13 274 96 85 149 277), lower := (rows 11 162 100 13 274 96 64 128 256), losses := [] }

theorem u17602 : Upper (D 6) (R 6) [10,160,96,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17603 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 100 13 276 33 82 210 338), lower := (rows 11 162 100 13 276 33 64 128 256), losses := [] }

theorem u17603 : Upper (D 6) (R 6) [10,160,96,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17604 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 13 276 34 81 209 337), lower := (rows 11 162 100 13 276 34 64 128 256), losses := [] }

theorem u17604 : Upper (D 6) (R 6) [10,160,96,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17605 : Route 9 := (fun mask => (mask,id))

def c17605 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17605 : Upper (D 6) (R 6) [10,160,96,5,260,16] 13 := by
  apply FastRouting.sound _ _ [10,160,96,5,260,16] 13 (by decide) (choices 1) [1,2] r17605 c17605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4885
  · exact u4886

def b17606 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 100 13 276 96 83 147 275), lower := (rows 11 162 100 13 276 96 64 128 256), losses := [] }

theorem u17606 : Upper (D 6) (R 6) [10,160,96,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17607 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 100 13 336 33 86 150 278), lower := (rows 11 162 100 13 336 33 64 128 256), losses := [] }

theorem u17607 : Upper (D 6) (R 6) [10,160,96,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17608 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 13 336 34 85 149 277), lower := (rows 11 162 100 13 336 34 64 128 256), losses := [] }

theorem u17608 : Upper (D 6) (R 6) [10,160,96,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17609 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 11 162 100 13 336 36 83 147 275), lower := (rows 11 162 100 13 336 36 64 128 256), losses := [] }

theorem u17609 : Upper (D 6) (R 6) [10,160,96,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17610 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 100 13 336 48 71 135 263), lower := (rows 11 162 100 13 336 48 64 128 256), losses := [] }

theorem u17610 : Upper (D 6) (R 6) [10,160,96,5,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17610 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17611 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 100 25 276 33 70 198 326), lower := (rows 11 162 100 25 276 33 64 128 256), losses := [] }

theorem u17611 : Upper (D 6) (R 6) [10,160,96,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17612 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 25 276 34 69 197 325), lower := (rows 11 162 100 25 276 34 64 128 256), losses := [] }

theorem u17612 : Upper (D 6) (R 6) [10,160,96,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17613 : Route 9 := (fun mask => (mask,id))

def c17613 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17613 : Upper (D 6) (R 6) [10,160,96,17,260,4] 13 := by
  apply FastRouting.sound _ _ [10,160,96,17,260,4] 13 (by decide) (choices 1) [1,2] r17613 c17613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4887
  · exact u4888

def b17614 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 100 25 276 96 71 135 263), lower := (rows 11 162 100 25 276 96 64 128 256), losses := [] }

theorem u17614 : Upper (D 6) (R 6) [10,160,96,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17615 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 100 25 336 33 70 134 262), lower := (rows 11 162 100 25 336 33 64 128 256), losses := [] }

theorem u17615 : Upper (D 6) (R 6) [10,160,96,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17616 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 25 336 34 69 133 261), lower := (rows 11 162 100 25 336 34 64 128 256), losses := [] }

theorem u17616 : Upper (D 6) (R 6) [10,160,96,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17617 : Route 9 := (fun mask => (mask,id))

def c17617 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17617 : Upper (D 6) (R 6) [10,160,96,17,320,4] 13 := by
  apply FastRouting.sound _ _ [10,160,96,17,320,4] 13 (by decide) (choices 1) [1,2,4] r17617 c17617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4889
  · exact u4890
  · exact u4891

def b17618 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 4, region := 36, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 11 162 100 28 81 33 326 390 262), lower := (rows 11 162 100 28 81 33 64 128 256), losses := [] }

theorem u17618 : Upper (D 6) (R 6) [10,160,96,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17619 : PairBound 9 := { available := 261, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 28 81 34 325 389 261), lower := (rows 11 162 100 28 81 34 64 128 256), losses := [] }

theorem u17619 : Upper (D 6) (R 6) [10,160,96,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17620 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 162 100 28 81 36 323 387 259), lower := (rows 11 162 100 28 81 36 64 128 256), losses := [] }

theorem u17620 : Upper (D 6) (R 6) [10,160,96,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17621 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 100 28 81 288 71 135 263), lower := (rows 11 162 100 28 81 288 64 128 256), losses := [] }

theorem u17621 : Upper (D 6) (R 6) [10,160,96,20,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17621 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17622 : Route 9 := (fun mask => (mask,id))

def c17622 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17622 : Upper (D 6) (R 6) [10,160,96,20,257,1] 13 := by
  apply FastRouting.sound _ _ [10,160,96,20,257,1] 13 (by decide) (choices 1) [2,4] r17622 c17622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4892
  · exact u4893

def b17623 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 28 273 34 69 197 325), lower := (rows 11 162 100 28 273 34 64 128 256), losses := [] }

theorem u17623 : Upper (D 6) (R 6) [10,160,96,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17623 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17624 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 11 162 100 28 273 36 67 195 323), lower := (rows 11 162 100 28 273 36 64 128 256), losses := [] }

theorem u17624 : Upper (D 6) (R 6) [10,160,96,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17625 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 100 28 273 96 71 135 263), lower := (rows 11 162 100 28 273 96 64 128 256), losses := [] }

theorem u17625 : Upper (D 6) (R 6) [10,160,96,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17626 : Route 9 := (fun mask => (mask,id))

def c17626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17626 : Upper (D 6) (R 6) [10,160,96,20,258,1] 13 := by
  apply FastRouting.sound _ _ [10,160,96,20,258,1] 13 (by decide) (choices 1) [1,4] r17626 c17626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4894
  · exact u4895

def b17627 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 11 162 100 28 274 36 65 193 321), lower := (rows 11 162 100 28 274 36 64 128 256), losses := [] }

theorem u17627 : Upper (D 6) (R 6) [10,160,96,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17628 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 100 28 274 96 69 133 261), lower := (rows 11 162 100 28 274 96 64 128 256), losses := [] }

theorem u17628 : Upper (D 6) (R 6) [10,160,96,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17629 : Route 9 := (fun mask => (mask,id))

def c17629 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17629 : Upper (D 6) (R 6) [10,160,96,20,320,1] 13 := by
  apply FastRouting.sound _ _ [10,160,96,20,320,1] 13 (by decide) (choices 1) [1,2,4] r17629 c17629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4896
  · exact u4897
  · exact u4898

def b17630 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 28 336 34 69 133 261), lower := (rows 11 162 100 28 336 34 64 128 256), losses := [] }

theorem u17630 : Upper (D 6) (R 6) [10,160,96,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17630 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17631 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 162 100 28 336 36 67 131 259), lower := (rows 11 162 100 28 336 36 64 128 256), losses := [] }

theorem u17631 : Upper (D 6) (R 6) [10,160,96,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17632 : PairBound 9 := { available := 276, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 100 73 22 33 340 404 276), lower := (rows 11 162 100 73 22 33 64 128 256), losses := [] }

theorem u17632 : Upper (D 6) (R 6) [10,160,96,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17633 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 100 73 22 36 337 401 273), lower := (rows 11 162 100 73 22 36 64 128 256), losses := [] }

theorem u17633 : Upper (D 6) (R 6) [10,160,96,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17634 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 100 73 22 48 325 389 261), lower := (rows 11 162 100 73 22 48 64 128 256), losses := [] }

theorem u17634 : Upper (D 6) (R 6) [10,160,96,65,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17634 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17635 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 100 73 22 288 85 149 277), lower := (rows 11 162 100 73 22 288 64 128 256), losses := [] }

theorem u17635 : Upper (D 6) (R 6) [10,160,96,65,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17635 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17636 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 73 273 34 84 148 276), lower := (rows 11 162 100 73 273 34 64 128 256), losses := [] }

theorem u17636 : Upper (D 6) (R 6) [10,160,96,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17637 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 162 100 73 273 36 86 150 278), lower := (rows 11 162 100 73 273 36 64 128 256), losses := [] }

theorem u17637 : Upper (D 6) (R 6) [10,160,96,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17638 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 100 73 273 48 70 134 262), lower := (rows 11 162 100 73 273 48 64 128 256), losses := [] }

theorem u17638 : Upper (D 6) (R 6) [10,160,96,65,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17638 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17639 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 100 73 274 33 84 148 276), lower := (rows 11 162 100 73 274 33 64 128 256), losses := [] }

theorem u17639 : Upper (D 6) (R 6) [10,160,96,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u17639
end Delivery.IrregularNine14.P06
