import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0106

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r21720 : Route 9 := (fun mask => (mask,id))

def c21720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21720 : Upper (D 6) (R 6) [34,129,40,68,66,256] 13 := by
  apply FastRouting.sound _ _ [34,129,40,68,66,256] 13 (by decide) (choices 1) [1,4,16] r21720 c21720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6378
  · exact u6379
  · exact u6380

def b21721 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 76 273 34 84 212 340), lower := (rows 35 131 44 76 273 34 64 128 256), losses := [] }

theorem u21721 : Upper (D 6) (R 6) [34,129,40,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21722 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 44 76 273 36 82 210 338), lower := (rows 35 131 44 76 273 36 64 128 256), losses := [] }

theorem u21722 : Upper (D 6) (R 6) [34,129,40,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21723 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 44 76 273 48 70 198 326), lower := (rows 35 131 44 76 273 48 64 128 256), losses := [] }

theorem u21723 : Upper (D 6) (R 6) [34,129,40,68,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21723 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21724 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 12, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 76 273 96 86 150 278), lower := (rows 35 131 44 76 273 96 64 128 256), losses := [] }

theorem u21724 : Upper (D 6) (R 6) [34,129,40,68,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21725 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 76 274 33 84 212 340), lower := (rows 35 131 44 76 274 33 64 128 256), losses := [] }

theorem u21725 : Upper (D 6) (R 6) [34,129,40,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21726 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 44 76 274 36 81 209 337), lower := (rows 35 131 44 76 274 36 64 128 256), losses := [] }

theorem u21726 : Upper (D 6) (R 6) [34,129,40,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21727 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 44 76 274 48 69 197 325), lower := (rows 35 131 44 76 274 48 64 128 256), losses := [] }

theorem u21727 : Upper (D 6) (R 6) [34,129,40,68,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21727 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21728 : PairBound 9 := { available := 21, camps := [{ cop := 5, region := 12, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 76 274 96 85 149 277), lower := (rows 35 131 44 76 274 96 64 128 256), losses := [] }

theorem u21728 : Upper (D 6) (R 6) [34,129,40,68,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21729 : PairBound 9 := { available := 82, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 76 276 33 82 210 338), lower := (rows 35 131 44 76 276 33 64 128 256), losses := [] }

theorem u21729 : Upper (D 6) (R 6) [34,129,40,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21730 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 76 276 34 81 209 337), lower := (rows 35 131 44 76 276 34 64 128 256), losses := [] }

theorem u21730 : Upper (D 6) (R 6) [34,129,40,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21731 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 194, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 131 44 76 276 48 67 195 323), lower := (rows 35 131 44 76 276 48 64 128 256), losses := [] }

theorem u21731 : Upper (D 6) (R 6) [34,129,40,68,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21731 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21732 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 12, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 44 76 276 96 83 147 275), lower := (rows 35 131 44 76 276 96 64 128 256), losses := [] }

theorem u21732 : Upper (D 6) (R 6) [34,129,40,68,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21733 : PairBound 9 := { available := 22, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 76 336 33 86 150 278), lower := (rows 35 131 44 76 336 33 64 128 256), losses := [] }

theorem u21733 : Upper (D 6) (R 6) [34,129,40,68,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21734 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 76 336 34 85 149 277), lower := (rows 35 131 44 76 336 34 64 128 256), losses := [] }

theorem u21734 : Upper (D 6) (R 6) [34,129,40,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21735 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 44 76 336 36 83 147 275), lower := (rows 35 131 44 76 336 36 64 128 256), losses := [] }

theorem u21735 : Upper (D 6) (R 6) [34,129,40,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21736 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 76 336 48 71 135 263), lower := (rows 35 131 44 76 336 48 64 128 256), losses := [] }

theorem u21736 : Upper (D 6) (R 6) [34,129,40,68,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21736 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21737 : PairBound 9 := { available := 324, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 88 21 34 324 452 324), lower := (rows 35 131 44 88 21 34 64 128 256), losses := [] }

theorem u21737 : Upper (D 6) (R 6) [34,129,40,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21738 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 131 44 88 21 36 322 450 322), lower := (rows 35 131 44 88 21 36 64 128 256), losses := [] }

theorem u21738 : Upper (D 6) (R 6) [34,129,40,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21739 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 44 88 21 96 326 390 262), lower := (rows 35 131 44 88 21 96 64 128 256), losses := [] }

theorem u21739 : Upper (D 6) (R 6) [34,129,40,80,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21740 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 131 44 88 21 288 70 198 326), lower := (rows 35 131 44 88 21 288 64 128 256), losses := [] }

theorem u21740 : Upper (D 6) (R 6) [34,129,40,80,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21740 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21741 : PairBound 9 := { available := 324, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 88 22 33 324 452 324), lower := (rows 35 131 44 88 22 33 64 128 256), losses := [] }

theorem u21741 : Upper (D 6) (R 6) [34,129,40,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21742 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 88 22 36 321 449 321), lower := (rows 35 131 44 88 22 36 64 128 256), losses := [] }

theorem u21742 : Upper (D 6) (R 6) [34,129,40,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21743 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 44 88 22 96 325 389 261), lower := (rows 35 131 44 88 22 96 64 128 256), losses := [] }

theorem u21743 : Upper (D 6) (R 6) [34,129,40,80,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21744 : Route 9 := (fun mask => (mask,id))

def c21744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21744 : Upper (D 6) (R 6) [34,129,40,80,6,256] 13 := by
  apply FastRouting.sound _ _ [34,129,40,80,6,256] 13 (by decide) (choices 1) [1,4] r21744 c21744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6381
  · exact u6382

def b21745 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 88 273 34 68 196 324), lower := (rows 35 131 44 88 273 34 64 128 256), losses := [] }

theorem u21745 : Upper (D 6) (R 6) [34,129,40,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21746 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 88 273 36 70 198 326), lower := (rows 35 131 44 88 273 36 64 128 256), losses := [] }

theorem u21746 : Upper (D 6) (R 6) [34,129,40,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21747 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 44 88 273 96 70 134 262), lower := (rows 35 131 44 88 273 96 64 128 256), losses := [] }

theorem u21747 : Upper (D 6) (R 6) [34,129,40,80,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21748 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 88 274 33 68 196 324), lower := (rows 35 131 44 88 274 33 64 128 256), losses := [] }

theorem u21748 : Upper (D 6) (R 6) [34,129,40,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21749 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 88 274 36 69 197 325), lower := (rows 35 131 44 88 274 36 64 128 256), losses := [] }

theorem u21749 : Upper (D 6) (R 6) [34,129,40,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21749 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21750 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 44 88 274 96 69 133 261), lower := (rows 35 131 44 88 274 96 64 128 256), losses := [] }

theorem u21750 : Upper (D 6) (R 6) [34,129,40,80,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21751 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 88 276 33 70 198 326), lower := (rows 35 131 44 88 276 33 64 128 256), losses := [] }

theorem u21751 : Upper (D 6) (R 6) [34,129,40,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21752 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 88 276 34 69 197 325), lower := (rows 35 131 44 88 276 34 64 128 256), losses := [] }

theorem u21752 : Upper (D 6) (R 6) [34,129,40,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21753 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 88 276 36 67 195 323), lower := (rows 35 131 44 88 276 36 64 128 256), losses := [] }

theorem u21753 : Upper (D 6) (R 6) [34,129,40,80,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21754 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 131 44 88 276 96 71 135 263), lower := (rows 35 131 44 88 276 96 64 128 256), losses := [] }

theorem u21754 : Upper (D 6) (R 6) [34,129,40,80,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21755 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 265 22 36 80 208 336), lower := (rows 35 131 44 265 22 36 64 128 256), losses := [] }

theorem u21755 : Upper (D 6) (R 6) [34,129,40,257,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21756 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 44 265 22 48 68 196 324), lower := (rows 35 131 44 265 22 48 64 128 256), losses := [] }

theorem u21756 : Upper (D 6) (R 6) [34,129,40,257,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21756 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21757 : Route 9 := (fun mask => (mask,id))

def c21757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21757 : Upper (D 6) (R 6) [34,129,40,257,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,257,6,64] 13 (by decide) (choices 1) [4,16] r21757 c21757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6383
  · exact u6384

def b21758 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 265 82 36 84 212 340), lower := (rows 35 131 44 265 82 36 64 128 256), losses := [] }

theorem u21758 : Upper (D 6) (R 6) [34,129,40,257,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21759 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 44 265 82 48 68 196 324), lower := (rows 35 131 44 265 82 48 64 128 256), losses := [] }

theorem u21759 : Upper (D 6) (R 6) [34,129,40,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21759 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21760 : Route 9 := (fun mask => (mask,id))

def c21760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21760 : Upper (D 6) (R 6) [34,129,40,257,66,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,257,66,64] 13 (by decide) (choices 1) [4,16] r21760 c21760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6385
  · exact u6386

def b21761 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 265 84 34 84 212 340), lower := (rows 35 131 44 265 84 34 64 128 256), losses := [] }

theorem u21761 : Upper (D 6) (R 6) [34,129,40,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21762 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 265 84 36 82 210 338), lower := (rows 35 131 44 265 84 36 64 128 256), losses := [] }

theorem u21762 : Upper (D 6) (R 6) [34,129,40,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21763 : Route 9 := (fun mask => (mask,id))

def c21763 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21763 : Upper (D 6) (R 6) [34,129,40,257,68,16] 13 := by
  apply FastRouting.sound _ _ [34,129,40,257,68,16] 13 (by decide) (choices 1) [2,4] r21763 c21763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6387
  · exact u6388

def r21764 : Route 9 := (fun mask => (mask,id))

def c21764 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21764 : Upper (D 6) (R 6) [34,129,40,257,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,257,68,64] 13 (by decide) (choices 1) [2,4,16] r21764 c21764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6389
  · exact u6390
  · exact u6391

def b21765 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 131 44 266 21 36 80 208 336), lower := (rows 35 131 44 266 21 36 64 128 256), losses := [] }

theorem u21765 : Upper (D 6) (R 6) [34,129,40,258,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21766 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 131 44 266 21 48 68 196 324), lower := (rows 35 131 44 266 21 48 64 128 256), losses := [] }

theorem u21766 : Upper (D 6) (R 6) [34,129,40,258,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21766 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21767 : Route 9 := (fun mask => (mask,id))

def c21767 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21767 : Upper (D 6) (R 6) [34,129,40,258,5,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,258,5,64] 13 (by decide) (choices 1) [4,16] r21767 c21767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6392
  · exact u6393

def b21768 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 44 266 81 36 84 212 340), lower := (rows 35 131 44 266 81 36 64 128 256), losses := [] }

theorem u21768 : Upper (D 6) (R 6) [34,129,40,258,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21769 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 44 266 81 48 68 196 324), lower := (rows 35 131 44 266 81 48 64 128 256), losses := [] }

theorem u21769 : Upper (D 6) (R 6) [34,129,40,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21769 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21770 : Route 9 := (fun mask => (mask,id))

def c21770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21770 : Upper (D 6) (R 6) [34,129,40,258,65,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,258,65,64] 13 (by decide) (choices 1) [4,16] r21770 c21770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6394
  · exact u6395

def b21771 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 266 84 33 84 212 340), lower := (rows 35 131 44 266 84 33 64 128 256), losses := [] }

theorem u21771 : Upper (D 6) (R 6) [34,129,40,258,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21772 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 44 266 84 36 81 209 337), lower := (rows 35 131 44 266 84 36 64 128 256), losses := [] }

theorem u21772 : Upper (D 6) (R 6) [34,129,40,258,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21773 : Route 9 := (fun mask => (mask,id))

def c21773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21773 : Upper (D 6) (R 6) [34,129,40,258,68,16] 13 := by
  apply FastRouting.sound _ _ [34,129,40,258,68,16] 13 (by decide) (choices 1) [1,4] r21773 c21773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6396
  · exact u6397

def r21774 : Route 9 := (fun mask => (mask,id))

def c21774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21774 : Upper (D 6) (R 6) [34,129,40,258,68,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,258,68,64] 13 (by decide) (choices 1) [1,4,16] r21774 c21774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6398
  · exact u6399
  · exact u6400

def b21775 : PairBound 9 := { available := 80, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 268 22 33 80 208 336), lower := (rows 35 131 44 268 22 33 64 128 256), losses := [] }

theorem u21775 : Upper (D 6) (R 6) [34,129,40,260,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21776 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 44 268 22 48 65 193 321), lower := (rows 35 131 44 268 22 48 64 128 256), losses := [] }

theorem u21776 : Upper (D 6) (R 6) [34,129,40,260,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21776 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21777 : Route 9 := (fun mask => (mask,id))

def c21777 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21777 : Upper (D 6) (R 6) [34,129,40,260,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,40,260,6,64] 13 (by decide) (choices 1) [1,16] r21777 c21777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6401
  · exact u6402

def b21778 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 44 268 81 34 84 212 340), lower := (rows 35 131 44 268 81 34 64 128 256), losses := [] }

theorem u21778 : Upper (D 6) (R 6) [34,129,40,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21779 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 44 268 81 36 82 210 338), lower := (rows 35 131 44 268 81 36 64 128 256), losses := [] }

theorem u21779 : Upper (D 6) (R 6) [34,129,40,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u21779
end Delivery.IrregularNine14.P06
