import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0081
import IrregularNine14P06C0082

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r17640 : Route 9 := (fun mask => (mask,id))

def c17640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17640 : Upper (D 6) (R 6) [10,160,96,65,258,4] 13 := by
  apply FastRouting.sound _ _ [10,160,96,65,258,4] 13 (by decide) (choices 1) [1,4,16] r17640 c17640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4899
  · exact u4900
  · exact u4901

def r17641 : Route 9 := (fun mask => (mask,id))

def c17641 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17641 : Upper (D 6) (R 6) [10,160,96,65,258,16] 13 := by
  apply FastRouting.sound _ _ [10,160,96,65,258,16] 13 (by decide) (choices 1) [1,4] r17641 c17641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4902
  · exact u4903

def b17642 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 100 73 276 33 86 150 278), lower := (rows 11 162 100 73 276 33 64 128 256), losses := [] }

theorem u17642 : Upper (D 6) (R 6) [10,160,96,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17643 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 73 276 34 85 149 277), lower := (rows 11 162 100 73 276 34 64 128 256), losses := [] }

theorem u17643 : Upper (D 6) (R 6) [10,160,96,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17644 : Route 9 := (fun mask => (mask,id))

def c17644 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17644 : Upper (D 6) (R 6) [10,160,96,65,260,4] 13 := by
  apply FastRouting.sound _ _ [10,160,96,65,260,4] 13 (by decide) (choices 1) [1,2,16] r17644 c17644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4904
  · exact u4905
  · exact u4906

def r17645 : Route 9 := (fun mask => (mask,id))

def c17645 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17645 : Upper (D 6) (R 6) [10,160,96,65,260,16] 13 := by
  apply FastRouting.sound _ _ [10,160,96,65,260,16] 13 (by decide) (choices 1) [1,2,4] r17645 c17645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4907
  · exact u4908
  · exact u4909

def b17646 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 454, targets := 1 },{ cop := 2, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 100 88 21 33 326 390 262), lower := (rows 11 162 100 88 21 33 64 128 256), losses := [] }

theorem u17646 : Upper (D 6) (R 6) [10,160,96,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17647 : PairBound 9 := { available := 261, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 88 21 34 325 389 261), lower := (rows 11 162 100 88 21 34 64 128 256), losses := [] }

theorem u17647 : Upper (D 6) (R 6) [10,160,96,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17648 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6),(2,0),(2,1)], upper := (rows 11 162 100 88 21 36 323 387 259), lower := (rows 11 162 100 88 21 36 64 128 256), losses := [] }

theorem u17648 : Upper (D 6) (R 6) [10,160,96,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17649 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 418, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 100 88 21 288 71 135 263), lower := (rows 11 162 100 88 21 288 64 128 256), losses := [{ target := 6, region := (rows 9 26 4 8 16 312 0 144 272), good := (rows 43 162 36 443 439 288 0 128 288) }] }

theorem u17649 : Upper (D 6) (R 6) [10,160,96,80,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17649 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17650 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 198, targets := 1 },{ cop := 2, region := 130, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 100 88 273 33 70 134 262), lower := (rows 11 162 100 88 273 33 64 128 256), losses := [] }

theorem u17650 : Upper (D 6) (R 6) [10,160,96,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17651 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 88 273 34 69 133 261), lower := (rows 11 162 100 88 273 34 64 128 256), losses := [] }

theorem u17651 : Upper (D 6) (R 6) [10,160,96,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17652 : Route 9 := (fun mask => (mask,id))

def c17652 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17652 : Upper (D 6) (R 6) [10,160,96,80,257,4] 13 := by
  apply FastRouting.sound _ _ [10,160,96,80,257,4] 13 (by decide) (choices 1) [1,2,4] r17652 c17652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4910
  · exact u4911
  · exact u4912

def r17653 : Route 9 := (fun mask => (mask,id))

def c17653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17653 : Upper (D 6) (R 6) [10,160,96,80,258,1] 13 := by
  apply FastRouting.sound _ _ [10,160,96,80,258,1] 13 (by decide) (choices 1) [1,4] r17653 c17653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4913
  · exact u4914

def r17654 : Route 9 := (fun mask => (mask,id))

def c17654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17654 : Upper (D 6) (R 6) [10,160,96,80,258,4] 13 := by
  apply FastRouting.sound _ _ [10,160,96,80,258,4] 13 (by decide) (choices 1) [1,4] r17654 c17654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4915
  · exact u4916

def r17655 : Route 9 := (fun mask => (mask,id))

def c17655 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17655 : Upper (D 6) (R 6) [10,160,96,80,260,1] 13 := by
  apply FastRouting.sound _ _ [10,160,96,80,260,1] 13 (by decide) (choices 1) [1,2,4] r17655 c17655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4917
  · exact u4918
  · exact u4919

def b17656 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 88 276 34 69 133 261), lower := (rows 11 162 100 88 276 34 64 128 256), losses := [] }

theorem u17656 : Upper (D 6) (R 6) [10,160,96,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17657 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 11 162 100 88 276 36 67 131 259), lower := (rows 11 162 100 88 276 36 64 128 256), losses := [{ target := 6, region := (rows 9 10 4 8 16 52 0 137 265), good := (rows 395 162 36 443 308 36 0 128 256) }] }

theorem u17657 : Upper (D 6) (R 6) [10,160,96,80,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17658 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 265 21 34 84 212 340), lower := (rows 11 162 100 265 21 34 64 128 256), losses := [] }

theorem u17658 : Upper (D 6) (R 6) [10,160,96,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17659 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 162 100 265 21 36 82 210 338), lower := (rows 11 162 100 265 21 36 64 128 256), losses := [] }

theorem u17659 : Upper (D 6) (R 6) [10,160,96,257,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17660 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 100 265 21 48 70 198 326), lower := (rows 11 162 100 265 21 48 64 128 256), losses := [] }

theorem u17660 : Upper (D 6) (R 6) [10,160,96,257,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17660 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17661 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 100 265 21 96 86 150 278), lower := (rows 11 162 100 265 21 96 64 128 256), losses := [] }

theorem u17661 : Upper (D 6) (R 6) [10,160,96,257,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17662 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 100 265 22 33 84 212 340), lower := (rows 11 162 100 265 22 33 64 128 256), losses := [] }

theorem u17662 : Upper (D 6) (R 6) [10,160,96,257,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17663 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 100 265 22 36 81 209 337), lower := (rows 11 162 100 265 22 36 64 128 256), losses := [] }

theorem u17663 : Upper (D 6) (R 6) [10,160,96,257,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17664 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 100 265 22 48 69 197 325), lower := (rows 11 162 100 265 22 48 64 128 256), losses := [] }

theorem u17664 : Upper (D 6) (R 6) [10,160,96,257,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17664 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17665 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 100 265 22 96 85 149 277), lower := (rows 11 162 100 265 22 96 64 128 256), losses := [] }

theorem u17665 : Upper (D 6) (R 6) [10,160,96,257,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17666 : PairBound 9 := { available := 20, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 265 81 34 84 148 276), lower := (rows 11 162 100 265 81 34 64 128 256), losses := [] }

theorem u17666 : Upper (D 6) (R 6) [10,160,96,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17667 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 162 100 265 81 36 86 150 278), lower := (rows 11 162 100 265 81 36 64 128 256), losses := [] }

theorem u17667 : Upper (D 6) (R 6) [10,160,96,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17668 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 100 265 81 48 70 134 262), lower := (rows 11 162 100 265 81 48 64 128 256), losses := [] }

theorem u17668 : Upper (D 6) (R 6) [10,160,96,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17668 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17669 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 100 265 82 33 84 148 276), lower := (rows 11 162 100 265 82 33 64 128 256), losses := [] }

theorem u17669 : Upper (D 6) (R 6) [10,160,96,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17670 : Route 9 := (fun mask => (mask,id))

def c17670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17670 : Upper (D 6) (R 6) [10,160,96,257,66,4] 13 := by
  apply FastRouting.sound _ _ [10,160,96,257,66,4] 13 (by decide) (choices 1) [1,4,16] r17670 c17670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4920
  · exact u4921
  · exact u4922

def b17671 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 100 265 82 48 69 133 261), lower := (rows 11 162 100 265 82 48 64 128 256), losses := [] }

theorem u17671 : Upper (D 6) (R 6) [10,160,96,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17671 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17672 : Route 9 := (fun mask => (mask,id))

def c17672 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17672 : Upper (D 6) (R 6) [10,160,96,260,5,1] 13 := by
  apply FastRouting.sound _ _ [10,160,96,260,5,1] 13 (by decide) (choices 1) [2,16] r17672 c17672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4923
  · exact u4924

def b17673 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 268 21 34 81 209 337), lower := (rows 11 162 100 268 21 34 64 128 256), losses := [] }

theorem u17673 : Upper (D 6) (R 6) [10,160,96,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17674 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(3,5)], upper := (rows 11 162 100 268 21 48 67 195 323), lower := (rows 11 162 100 268 21 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 65 129 257), good := (rows 459 130 68 268 477 24 64 128 256) }] }

theorem u17674 : Upper (D 6) (R 6) [10,160,96,260,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17674 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17675 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 100 268 21 96 83 147 275), lower := (rows 11 162 100 268 21 96 64 128 256), losses := [] }

theorem u17675 : Upper (D 6) (R 6) [10,160,96,260,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17676 : Route 9 := (fun mask => (mask,id))

def c17676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17676 : Upper (D 6) (R 6) [10,160,96,260,6,1] 13 := by
  apply FastRouting.sound _ _ [10,160,96,260,6,1] 13 (by decide) (choices 1) [1,16] r17676 c17676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4925
  · exact u4926

def b17677 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 329, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 100 268 22 48 65 193 321), lower := (rows 11 162 100 268 22 48 64 128 256), losses := [] }

theorem u17677 : Upper (D 6) (R 6) [10,160,96,260,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17677 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17678 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 100 268 22 96 81 145 273), lower := (rows 11 162 100 268 22 96 64 128 256), losses := [] }

theorem u17678 : Upper (D 6) (R 6) [10,160,96,260,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17679 : Route 9 := (fun mask => (mask,id))

def c17679 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17679 : Upper (D 6) (R 6) [10,160,96,260,65,1] 13 := by
  apply FastRouting.sound _ _ [10,160,96,260,65,1] 13 (by decide) (choices 1) [2,4,16] r17679 c17679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4927
  · exact u4928
  · exact u4929

def b17680 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 268 81 34 85 149 277), lower := (rows 11 162 100 268 81 34 64 128 256), losses := [] }

theorem u17680 : Upper (D 6) (R 6) [10,160,96,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17681 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 11 162 100 268 81 36 83 147 275), lower := (rows 11 162 100 268 81 36 64 128 256), losses := [] }

theorem u17681 : Upper (D 6) (R 6) [10,160,96,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17682 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 100 268 81 48 71 135 263), lower := (rows 11 162 100 268 81 48 64 128 256), losses := [] }

theorem u17682 : Upper (D 6) (R 6) [10,160,96,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17682 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17683 : Route 9 := (fun mask => (mask,id))

def c17683 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17683 : Upper (D 6) (R 6) [10,160,96,260,66,1] 13 := by
  apply FastRouting.sound _ _ [10,160,96,260,66,1] 13 (by decide) (choices 1) [1,4,16] r17683 c17683
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4930
  · exact u4931
  · exact u4932

def b17684 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 11 162 100 268 82 36 81 145 273), lower := (rows 11 162 100 268 82 36 64 128 256), losses := [] }

theorem u17684 : Upper (D 6) (R 6) [10,160,96,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17685 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 100 268 82 48 69 133 261), lower := (rows 11 162 100 268 82 48 64 128 256), losses := [] }

theorem u17685 : Upper (D 6) (R 6) [10,160,96,260,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17685 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17686 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 162 100 280 21 33 70 198 326), lower := (rows 11 162 100 280 21 33 64 128 256), losses := [{ target := 0, region := (rows 0 38 38 24 16 32 119 183 311), good := (rows 462 486 486 472 478 486 64 128 256) }] }

theorem u17686 : Upper (D 6) (R 6) [10,160,96,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17687 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 280 21 34 69 197 325), lower := (rows 11 162 100 280 21 34 64 128 256), losses := [] }

theorem u17687 : Upper (D 6) (R 6) [10,160,96,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17688 : PairBound 9 := { available := 67, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,2)], upper := (rows 11 162 100 280 21 36 67 195 323), lower := (rows 11 162 100 280 21 36 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 32 65 129 257), good := (rows 459 162 96 280 473 32 64 128 256) }] }

theorem u17688 : Upper (D 6) (R 6) [10,160,96,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17688 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17689 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 100 280 21 96 71 135 263), lower := (rows 11 162 100 280 21 96 64 128 256), losses := [] }

theorem u17689 : Upper (D 6) (R 6) [10,160,96,272,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17690 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 198, targets := 1 },{ cop := 2, region := 130, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 100 280 81 33 70 134 262), lower := (rows 11 162 100 280 81 33 64 128 256), losses := [] }

theorem u17690 : Upper (D 6) (R 6) [10,160,96,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17691 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 280 81 34 69 133 261), lower := (rows 11 162 100 280 81 34 64 128 256), losses := [] }

theorem u17691 : Upper (D 6) (R 6) [10,160,96,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17692 : Route 9 := (fun mask => (mask,id))

def c17692 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17692 : Upper (D 6) (R 6) [10,160,96,272,65,4] 13 := by
  apply FastRouting.sound _ _ [10,160,96,272,65,4] 13 (by decide) (choices 1) [1,2,4] r17692 c17692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4933
  · exact u4934
  · exact u4935

def r17693 : Route 9 := (fun mask => (mask,id))

def c17693 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17693 : Upper (D 6) (R 6) [10,160,96,272,66,1] 13 := by
  apply FastRouting.sound _ _ [10,160,96,272,66,1] 13 (by decide) (choices 1) [1,4] r17693 c17693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4936
  · exact u4937

def r17694 : Route 9 := (fun mask => (mask,id))

def c17694 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17694 : Upper (D 6) (R 6) [10,160,96,272,66,4] 13 := by
  apply FastRouting.sound _ _ [10,160,96,272,66,4] 13 (by decide) (choices 1) [1,4] r17694 c17694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4938
  · exact u4939

def r17695 : Route 9 := (fun mask => (mask,id))

def c17695 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17695 : Upper (D 6) (R 6) [10,160,96,320,5,1] 13 := by
  apply FastRouting.sound _ _ [10,160,96,320,5,1] 13 (by decide) (choices 1) [2,4,16] r17695 c17695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4940
  · exact u4941
  · exact u4942

def b17696 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 100 328 21 34 85 149 277), lower := (rows 11 162 100 328 21 34 64 128 256), losses := [] }

theorem u17696 : Upper (D 6) (R 6) [10,160,96,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17696 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17697 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6),(2,0),(2,1)], upper := (rows 11 162 100 328 21 36 83 147 275), lower := (rows 11 162 100 328 21 36 64 128 256), losses := [] }

theorem u17697 : Upper (D 6) (R 6) [10,160,96,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17698 : Route 9 := (fun mask => (mask,id))

def c17698 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17698 : Upper (D 6) (R 6) [10,160,96,320,5,16] 13 := by
  apply FastRouting.sound _ _ [10,160,96,320,5,16] 13 (by decide) (choices 1) [1,2,4] r17698 c17698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4943
  · exact u4944
  · exact u4945

def r17699 : Route 9 := (fun mask => (mask,id))

def c17699 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17699 : Upper (D 6) (R 6) [10,160,96,320,6,1] 13 := by
  apply FastRouting.sound _ _ [10,160,96,320,6,1] 13 (by decide) (choices 1) [1,4,16] r17699 c17699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4946
  · exact u4947
  · exact u4948

#print axioms u17699
end Delivery.IrregularNine14.P06
