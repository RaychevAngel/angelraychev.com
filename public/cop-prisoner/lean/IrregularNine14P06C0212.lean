import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0041
import IrregularNine14P06C0042

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12720 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 73 84 34 340 404 276), lower := (rows 11 35 164 73 84 34 64 128 256), losses := [] }

theorem u12720 : Upper (D 6) (R 6) [10,33,160,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12721 : PairBound 9 := { available := 274, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 73 84 36 338 402 274), lower := (rows 11 35 164 73 84 36 64 128 256), losses := [] }

theorem u12721 : Upper (D 6) (R 6) [10,33,160,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12722 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 164 73 84 48 326 390 262), lower := (rows 11 35 164 73 84 48 64 128 256), losses := [] }

theorem u12722 : Upper (D 6) (R 6) [10,33,160,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12722 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12723 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 164 73 84 288 86 150 278), lower := (rows 11 35 164 73 84 288 64 128 256), losses := [] }

theorem u12723 : Upper (D 6) (R 6) [10,33,160,65,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12723 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12724 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 73 276 34 84 212 340), lower := (rows 11 35 164 73 276 34 64 128 256), losses := [] }

theorem u12724 : Upper (D 6) (R 6) [10,33,160,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12725 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 73 276 36 82 210 338), lower := (rows 11 35 164 73 276 36 64 128 256), losses := [] }

theorem u12725 : Upper (D 6) (R 6) [10,33,160,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12726 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 164 73 276 48 70 198 326), lower := (rows 11 35 164 73 276 48 64 128 256), losses := [] }

theorem u12726 : Upper (D 6) (R 6) [10,33,160,65,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12726 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12727 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 164 73 276 96 86 150 278), lower := (rows 11 35 164 73 276 96 64 128 256), losses := [] }

theorem u12727 : Upper (D 6) (R 6) [10,33,160,65,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12728 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 73 336 34 84 148 276), lower := (rows 11 35 164 73 336 34 64 128 256), losses := [] }

theorem u12728 : Upper (D 6) (R 6) [10,33,160,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12729 : PairBound 9 := { available := 22, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 73 336 36 86 150 278), lower := (rows 11 35 164 73 336 36 64 128 256), losses := [] }

theorem u12729 : Upper (D 6) (R 6) [10,33,160,65,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12730 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 164 73 336 48 70 134 262), lower := (rows 11 35 164 73 336 48 64 128 256), losses := [] }

theorem u12730 : Upper (D 6) (R 6) [10,33,160,65,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12730 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12731 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 164 76 21 34 336 464 336), lower := (rows 11 35 164 76 21 34 64 128 256), losses := [] }

theorem u12731 : Upper (D 6) (R 6) [10,33,160,68,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12732 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 164 76 21 48 322 450 322), lower := (rows 11 35 164 76 21 48 64 128 256), losses := [] }

theorem u12732 : Upper (D 6) (R 6) [10,33,160,68,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12732 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12733 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 164 76 21 96 338 402 274), lower := (rows 11 35 164 76 21 96 64 128 256), losses := [] }

theorem u12733 : Upper (D 6) (R 6) [10,33,160,68,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12734 : Route 9 := (fun mask => (mask,id))

def c12734 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12734 : Upper (D 6) (R 6) [10,33,160,68,5,256] 13 := by
  apply FastRouting.sound _ _ [10,33,160,68,5,256] 13 (by decide) (choices 1) [2,16] r12734 c12734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2517
  · exact u2518

def b12735 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 164 76 22 33 336 464 336), lower := (rows 11 35 164 76 22 33 64 128 256), losses := [] }

theorem u12735 : Upper (D 6) (R 6) [10,33,160,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12736 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 164 76 22 48 321 449 321), lower := (rows 11 35 164 76 22 48 64 128 256), losses := [] }

theorem u12736 : Upper (D 6) (R 6) [10,33,160,68,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12736 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12737 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 164 76 22 96 337 401 273), lower := (rows 11 35 164 76 22 96 64 128 256), losses := [] }

theorem u12737 : Upper (D 6) (R 6) [10,33,160,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12738 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 35 164 76 22 288 81 209 337), lower := (rows 11 35 164 76 22 288 64 128 256), losses := [] }

theorem u12738 : Upper (D 6) (R 6) [10,33,160,68,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12738 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12739 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 164 76 81 34 340 404 276), lower := (rows 11 35 164 76 81 34 64 128 256), losses := [] }

theorem u12739 : Upper (D 6) (R 6) [10,33,160,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12740 : PairBound 9 := { available := 274, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 76 81 36 338 402 274), lower := (rows 11 35 164 76 81 36 64 128 256), losses := [] }

theorem u12740 : Upper (D 6) (R 6) [10,33,160,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12741 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 164 76 81 48 326 390 262), lower := (rows 11 35 164 76 81 48 64 128 256), losses := [] }

theorem u12741 : Upper (D 6) (R 6) [10,33,160,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12741 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12742 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 35 164 76 81 288 86 150 278), lower := (rows 11 35 164 76 81 288 64 128 256), losses := [] }

theorem u12742 : Upper (D 6) (R 6) [10,33,160,68,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12742 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12743 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 164 76 82 33 340 404 276), lower := (rows 11 35 164 76 82 33 64 128 256), losses := [] }

theorem u12743 : Upper (D 6) (R 6) [10,33,160,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12744 : PairBound 9 := { available := 273, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 76 82 36 337 401 273), lower := (rows 11 35 164 76 82 36 64 128 256), losses := [] }

theorem u12744 : Upper (D 6) (R 6) [10,33,160,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12745 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 164 76 82 48 325 389 261), lower := (rows 11 35 164 76 82 48 64 128 256), losses := [] }

theorem u12745 : Upper (D 6) (R 6) [10,33,160,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12745 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12746 : Route 9 := (fun mask => (mask,id))

def c12746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12746 : Upper (D 6) (R 6) [10,33,160,68,66,256] 13 := by
  apply FastRouting.sound _ _ [10,33,160,68,66,256] 13 (by decide) (choices 1) [1,4,16] r12746 c12746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2519
  · exact u2520
  · exact u2521

def b12747 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 76 273 34 84 212 340), lower := (rows 11 35 164 76 273 34 64 128 256), losses := [] }

theorem u12747 : Upper (D 6) (R 6) [10,33,160,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12748 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 76 273 36 82 210 338), lower := (rows 11 35 164 76 273 36 64 128 256), losses := [] }

theorem u12748 : Upper (D 6) (R 6) [10,33,160,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12749 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 164 76 273 48 70 198 326), lower := (rows 11 35 164 76 273 48 64 128 256), losses := [] }

theorem u12749 : Upper (D 6) (R 6) [10,33,160,68,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12749 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12750 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 164 76 273 96 86 150 278), lower := (rows 11 35 164 76 273 96 64 128 256), losses := [] }

theorem u12750 : Upper (D 6) (R 6) [10,33,160,68,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12751 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 76 274 33 84 212 340), lower := (rows 11 35 164 76 274 33 64 128 256), losses := [] }

theorem u12751 : Upper (D 6) (R 6) [10,33,160,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12752 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 76 274 36 81 209 337), lower := (rows 11 35 164 76 274 36 64 128 256), losses := [] }

theorem u12752 : Upper (D 6) (R 6) [10,33,160,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12753 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 35 164 76 274 48 69 197 325), lower := (rows 11 35 164 76 274 48 64 128 256), losses := [] }

theorem u12753 : Upper (D 6) (R 6) [10,33,160,68,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12753 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12754 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 164 76 274 96 85 149 277), lower := (rows 11 35 164 76 274 96 64 128 256), losses := [] }

theorem u12754 : Upper (D 6) (R 6) [10,33,160,68,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12755 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 76 276 33 82 210 338), lower := (rows 11 35 164 76 276 33 64 128 256), losses := [] }

theorem u12755 : Upper (D 6) (R 6) [10,33,160,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12756 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 76 276 34 81 209 337), lower := (rows 11 35 164 76 276 34 64 128 256), losses := [] }

theorem u12756 : Upper (D 6) (R 6) [10,33,160,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12757 : Route 9 := (fun mask => (mask,id))

def c12757 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12757 : Upper (D 6) (R 6) [10,33,160,68,260,16] 13 := by
  apply FastRouting.sound _ _ [10,33,160,68,260,16] 13 (by decide) (choices 1) [1,2] r12757 c12757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2522
  · exact u2523

def b12758 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 164 76 276 96 83 147 275), lower := (rows 11 35 164 76 276 96 64 128 256), losses := [] }

theorem u12758 : Upper (D 6) (R 6) [10,33,160,68,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12759 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 76 336 33 86 150 278), lower := (rows 11 35 164 76 336 33 64 128 256), losses := [] }

theorem u12759 : Upper (D 6) (R 6) [10,33,160,68,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12760 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 76 336 34 85 149 277), lower := (rows 11 35 164 76 336 34 64 128 256), losses := [] }

theorem u12760 : Upper (D 6) (R 6) [10,33,160,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12761 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 76 336 36 83 147 275), lower := (rows 11 35 164 76 336 36 64 128 256), losses := [] }

theorem u12761 : Upper (D 6) (R 6) [10,33,160,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12762 : Route 9 := (fun mask => (mask,id))

def c12762 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12762 : Upper (D 6) (R 6) [10,33,160,68,320,16] 13 := by
  apply FastRouting.sound _ _ [10,33,160,68,320,16] 13 (by decide) (choices 1) [1,2,4] r12762 c12762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2524
  · exact u2525
  · exact u2526

def b12763 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 88 21 34 324 452 324), lower := (rows 11 35 164 88 21 34 64 128 256), losses := [] }

theorem u12763 : Upper (D 6) (R 6) [10,33,160,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12764 : PairBound 9 := { available := 322, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 88 21 36 322 450 322), lower := (rows 11 35 164 88 21 36 64 128 256), losses := [] }

theorem u12764 : Upper (D 6) (R 6) [10,33,160,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12765 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 164 88 21 96 326 390 262), lower := (rows 11 35 164 88 21 96 64 128 256), losses := [] }

theorem u12765 : Upper (D 6) (R 6) [10,33,160,80,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12766 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 484, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 35 164 88 21 288 70 198 326), lower := (rows 11 35 164 88 21 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 307 67 131 259), good := (rows 494 486 164 124 508 288 64 128 288) }] }

theorem u12766 : Upper (D 6) (R 6) [10,33,160,80,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12766 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12767 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 88 273 34 68 196 324), lower := (rows 11 35 164 88 273 34 64 128 256), losses := [] }

theorem u12767 : Upper (D 6) (R 6) [10,33,160,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12768 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 88 273 36 70 198 326), lower := (rows 11 35 164 88 273 36 64 128 256), losses := [] }

theorem u12768 : Upper (D 6) (R 6) [10,33,160,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12769 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 164 88 273 96 70 134 262), lower := (rows 11 35 164 88 273 96 64 128 256), losses := [] }

theorem u12769 : Upper (D 6) (R 6) [10,33,160,80,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12770 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 88 274 33 68 196 324), lower := (rows 11 35 164 88 274 33 64 128 256), losses := [] }

theorem u12770 : Upper (D 6) (R 6) [10,33,160,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12771 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 88 274 36 69 197 325), lower := (rows 11 35 164 88 274 36 64 128 256), losses := [] }

theorem u12771 : Upper (D 6) (R 6) [10,33,160,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12772 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 164 88 274 96 69 133 261), lower := (rows 11 35 164 88 274 96 64 128 256), losses := [] }

theorem u12772 : Upper (D 6) (R 6) [10,33,160,80,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12773 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 88 276 33 70 198 326), lower := (rows 11 35 164 88 276 33 64 128 256), losses := [] }

theorem u12773 : Upper (D 6) (R 6) [10,33,160,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12774 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 88 276 34 69 197 325), lower := (rows 11 35 164 88 276 34 64 128 256), losses := [] }

theorem u12774 : Upper (D 6) (R 6) [10,33,160,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12775 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 88 276 36 67 195 323), lower := (rows 11 35 164 88 276 36 64 128 256), losses := [] }

theorem u12775 : Upper (D 6) (R 6) [10,33,160,80,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12776 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 164 88 276 96 71 135 263), lower := (rows 11 35 164 88 276 96 64 128 256), losses := [] }

theorem u12776 : Upper (D 6) (R 6) [10,33,160,80,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12777 : PairBound 9 := { available := 84, camps := [{ cop := 8, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 164 265 84 34 84 212 340), lower := (rows 11 35 164 265 84 34 64 128 256), losses := [] }

theorem u12777 : Upper (D 6) (R 6) [10,33,160,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12778 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 164 265 84 36 82 210 338), lower := (rows 11 35 164 265 84 36 64 128 256), losses := [] }

theorem u12778 : Upper (D 6) (R 6) [10,33,160,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12779 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 244, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 164 265 84 48 70 198 326), lower := (rows 11 35 164 265 84 48 64 128 256), losses := [] }

theorem u12779 : Upper (D 6) (R 6) [10,33,160,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12779 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u12779
end Delivery.IrregularNine14.P06
