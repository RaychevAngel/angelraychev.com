import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0115
import IrregularNine14P06C0116

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22740 : PairBound 9 := { available := 25, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 131 292 74 84 36 89 153 281), lower := (rows 35 131 292 74 84 36 64 128 256), losses := [] }

theorem u22740 : Upper (D 6) (R 6) [34,129,288,66,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22741 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 292 74 84 40 85 149 277), lower := (rows 35 131 292 74 84 40 64 128 256), losses := [] }

theorem u22741 : Upper (D 6) (R 6) [34,129,288,66,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22741 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22742 : Route 9 := (fun mask => (mask,id))

def c22742 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22742 : Upper (D 6) (R 6) [34,129,288,66,68,16] 13 := by
  apply FastRouting.sound _ _ [34,129,288,66,68,16] 13 (by decide) (choices 1) [1,4,8] r22742 c22742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6942
  · exact u6943
  · exact u6944

def b22743 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 324 13 22 40 112 240 368), lower := (rows 35 131 324 13 22 40 64 128 256), losses := [] }

theorem u22743 : Upper (D 6) (R 6) [34,129,320,5,6,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22743 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22744 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 324 13 22 48 104 232 360), lower := (rows 35 131 324 13 22 48 64 128 256), losses := [] }

theorem u22744 : Upper (D 6) (R 6) [34,129,320,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22744 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22745 : Route 9 := (fun mask => (mask,id))

def c22745 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22745 : Upper (D 6) (R 6) [34,129,320,5,6,64] 13 := by
  apply FastRouting.sound _ _ [34,129,320,5,6,64] 13 (by decide) (choices 1) [8,16,32] r22745 c22745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6945
  · exact u6946
  · exact u6947

def b22746 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 356, targets := 3 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 324 13 26 36 112 240 368), lower := (rows 35 131 324 13 26 36 64 128 256), losses := [{ target := 6, region := (rows 17 2 4 8 16 44 0 128 256), good := (rows 35 131 292 45 59 36 0 128 256) }] }

theorem u22746 : Upper (D 6) (R 6) [34,129,320,5,10,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22747 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 324 13 26 48 100 228 356), lower := (rows 35 131 324 13 26 48 64 128 256), losses := [] }

theorem u22747 : Upper (D 6) (R 6) [34,129,320,5,10,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22747 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22748 : Route 9 := (fun mask => (mask,id))

def c22748 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22748 : Upper (D 6) (R 6) [34,129,320,5,10,64] 13 := by
  apply FastRouting.sound _ _ [34,129,320,5,10,64] 13 (by decide) (choices 1) [4,16,32] r22748 c22748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6948
  · exact u6949
  · exact u6950

def b22749 : PairBound 9 := { available := 88, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 13 52 34 88 216 344), lower := (rows 35 131 324 13 52 34 64 128 256), losses := [] }

theorem u22749 : Upper (D 6) (R 6) [34,129,320,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22749 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22750 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 324 13 52 40 82 210 338), lower := (rows 35 131 324 13 52 40 64 128 256), losses := [] }

theorem u22750 : Upper (D 6) (R 6) [34,129,320,5,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22750 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22751 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 324 13 52 48 74 202 330), lower := (rows 35 131 324 13 52 48 64 128 256), losses := [] }

theorem u22751 : Upper (D 6) (R 6) [34,129,320,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22751 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22752 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 324 13 52 96 90 154 282), lower := (rows 35 131 324 13 52 96 64 128 256), losses := [] }

theorem u22752 : Upper (D 6) (R 6) [34,129,320,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22753 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 13 56 34 84 212 340), lower := (rows 35 131 324 13 56 34 64 128 256), losses := [] }

theorem u22753 : Upper (D 6) (R 6) [34,129,320,5,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22754 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 131 324 13 56 36 82 210 338), lower := (rows 35 131 324 13 56 36 64 128 256), losses := [] }

theorem u22754 : Upper (D 6) (R 6) [34,129,320,5,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22755 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 324 13 56 48 70 198 326), lower := (rows 35 131 324 13 56 48 64 128 256), losses := [] }

theorem u22755 : Upper (D 6) (R 6) [34,129,320,5,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22755 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22756 : PairBound 9 := { available := 22, camps := [], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 131 324 13 56 96 86 150 278), lower := (rows 35 131 324 13 56 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 100 64 128 256), good := (rows 34 130 356 60 56 96 96 128 256) },{ target := 1, region := (rows 1 0 4 8 24 100 64 128 256), good := (rows 33 129 356 61 56 96 96 128 256) },{ target := 2, region := (rows 1 2 0 8 24 100 64 128 256), good := (rows 35 131 352 57 56 96 96 128 256) }] }

theorem u22756 : Upper (D 6) (R 6) [34,129,320,5,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22757 : Route 9 := (fun mask => (mask,id))

def c22757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22757 : Upper (D 6) (R 6) [34,129,320,5,66,4] 13 := by
  apply FastRouting.sound _ _ [34,129,320,5,66,4] 13 (by decide) (choices 1) [8,16,32] r22757 c22757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6951
  · exact u6952
  · exact u6953

def b22758 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 324 13 82 40 116 180 308), lower := (rows 35 131 324 13 82 40 64 128 256), losses := [] }

theorem u22758 : Upper (D 6) (R 6) [34,129,320,5,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22758 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22759 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 324 13 82 48 108 172 300), lower := (rows 35 131 324 13 82 48 64 128 256), losses := [] }

theorem u22759 : Upper (D 6) (R 6) [34,129,320,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22759 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22760 : PairBound 9 := { available := 52, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 13 88 34 116 180 308), lower := (rows 35 131 324 13 88 34 64 128 256), losses := [] }

theorem u22760 : Upper (D 6) (R 6) [34,129,320,5,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22761 : Route 9 := (fun mask => (mask,id))

def c22761 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22761 : Upper (D 6) (R 6) [34,129,320,5,72,4] 13 := by
  apply FastRouting.sound _ _ [34,129,320,5,72,4] 13 (by decide) (choices 1) [2,16,32] r22761 c22761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6954
  · exact u6955
  · exact u6956

def b22762 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 324, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 324 13 88 48 102 166 294), lower := (rows 35 131 324 13 88 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 15 8 24 56 65 129 257), good := (rows 486 454 324 508 124 48 64 128 256) }] }

theorem u22762 : Upper (D 6) (R 6) [34,129,320,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22762 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22763 : PairBound 9 := { available := 28, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 13 112 34 92 156 284), lower := (rows 35 131 324 13 112 34 64 128 256), losses := [] }

theorem u22763 : Upper (D 6) (R 6) [34,129,320,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22764 : Route 9 := (fun mask => (mask,id))

def c22764 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22764 : Upper (D 6) (R 6) [34,129,320,5,96,4] 13 := by
  apply FastRouting.sound _ _ [34,129,320,5,96,4] 13 (by decide) (choices 1) [2,8,16] r22764 c22764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6957
  · exact u6958
  · exact u6959

def b22765 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 324 13 112 40 86 150 278), lower := (rows 35 131 324 13 112 40 64 128 256), losses := [] }

theorem u22765 : Upper (D 6) (R 6) [34,129,320,5,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22765 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22766 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 324 13 112 48 78 142 270), lower := (rows 35 131 324 13 112 48 64 128 256), losses := [] }

theorem u22766 : Upper (D 6) (R 6) [34,129,320,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22766 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22767 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 49, targets := 64 },{ cop := 4, region := 356, targets := 1 }], pairs := [(0,6),(2,0),(4,6)], upper := (rows 35 131 324 14 25 36 112 240 368), lower := (rows 35 131 324 14 25 36 64 128 256), losses := [] }

theorem u22767 : Upper (D 6) (R 6) [34,129,320,6,9,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22768 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 324 14 25 48 100 228 356), lower := (rows 35 131 324 14 25 48 64 128 256), losses := [] }

theorem u22768 : Upper (D 6) (R 6) [34,129,320,6,9,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22768 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22769 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 356, targets := 3 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 324 14 25 96 116 180 308), lower := (rows 35 131 324 14 25 96 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 24 100 64 128 256), good := (rows 35 131 352 59 25 96 96 128 256) }] }

theorem u22769 : Upper (D 6) (R 6) [34,129,320,6,9,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22770 : PairBound 9 := { available := 88, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 14 52 33 88 216 344), lower := (rows 35 131 324 14 52 33 64 128 256), losses := [] }

theorem u22770 : Upper (D 6) (R 6) [34,129,320,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22771 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 324 14 52 40 81 209 337), lower := (rows 35 131 324 14 52 40 64 128 256), losses := [] }

theorem u22771 : Upper (D 6) (R 6) [34,129,320,6,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22771 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22772 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 324 14 52 48 73 201 329), lower := (rows 35 131 324 14 52 48 64 128 256), losses := [] }

theorem u22772 : Upper (D 6) (R 6) [34,129,320,6,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22772 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22773 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 324 14 52 96 89 153 281), lower := (rows 35 131 324 14 52 96 64 128 256), losses := [] }

theorem u22773 : Upper (D 6) (R 6) [34,129,320,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22774 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 131 324 14 56 33 84 212 340), lower := (rows 35 131 324 14 56 33 64 128 256), losses := [] }

theorem u22774 : Upper (D 6) (R 6) [34,129,320,6,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22775 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 131 324 14 56 36 81 209 337), lower := (rows 35 131 324 14 56 36 64 128 256), losses := [] }

theorem u22775 : Upper (D 6) (R 6) [34,129,320,6,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22776 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 324 14 56 48 69 197 325), lower := (rows 35 131 324 14 56 48 64 128 256), losses := [] }

theorem u22776 : Upper (D 6) (R 6) [34,129,320,6,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22776 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22777 : PairBound 9 := { available := 21, camps := [], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 131 324 14 56 96 85 149 277), lower := (rows 35 131 324 14 56 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 100 64 128 256), good := (rows 34 130 356 62 56 96 96 128 256) },{ target := 1, region := (rows 1 0 4 8 24 100 64 128 256), good := (rows 33 129 356 60 56 96 96 128 256) },{ target := 2, region := (rows 9 2 0 8 24 100 64 128 256), good := (rows 35 131 352 59 57 96 96 128 256) }] }

theorem u22777 : Upper (D 6) (R 6) [34,129,320,6,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22778 : Route 9 := (fun mask => (mask,id))

def c22778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22778 : Upper (D 6) (R 6) [34,129,320,6,65,4] 13 := by
  apply FastRouting.sound _ _ [34,129,320,6,65,4] 13 (by decide) (choices 1) [8,16,32] r22778 c22778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6960
  · exact u6961
  · exact u6962

def b22779 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 324 14 81 40 116 180 308), lower := (rows 35 131 324 14 81 40 64 128 256), losses := [] }

theorem u22779 : Upper (D 6) (R 6) [34,129,320,6,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22779 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22780 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 324 14 81 48 108 172 300), lower := (rows 35 131 324 14 81 48 64 128 256), losses := [] }

theorem u22780 : Upper (D 6) (R 6) [34,129,320,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22780 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22781 : PairBound 9 := { available := 52, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 14 88 33 116 180 308), lower := (rows 35 131 324 14 88 33 64 128 256), losses := [] }

theorem u22781 : Upper (D 6) (R 6) [34,129,320,6,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22782 : Route 9 := (fun mask => (mask,id))

def c22782 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22782 : Upper (D 6) (R 6) [34,129,320,6,72,4] 13 := by
  apply FastRouting.sound _ _ [34,129,320,6,72,4] 13 (by decide) (choices 1) [1,16,32] r22782 c22782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6963
  · exact u6964
  · exact u6965

def r22783 : Route 9 := (fun mask => (mask,id))

def c22783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22783 : Upper (D 6) (R 6) [34,129,320,6,72,16] 13 := by
  apply FastRouting.sound _ _ [34,129,320,6,72,16] 13 (by decide) (choices 1) [1,4,32] r22783 c22783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6966
  · exact u6967
  · exact u6968

def b22784 : PairBound 9 := { available := 28, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 14 112 33 92 156 284), lower := (rows 35 131 324 14 112 33 64 128 256), losses := [] }

theorem u22784 : Upper (D 6) (R 6) [34,129,320,6,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22785 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 131 324 14 112 36 89 153 281), lower := (rows 35 131 324 14 112 36 64 128 256), losses := [] }

theorem u22785 : Upper (D 6) (R 6) [34,129,320,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22786 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 324 14 112 40 85 149 277), lower := (rows 35 131 324 14 112 40 64 128 256), losses := [] }

theorem u22786 : Upper (D 6) (R 6) [34,129,320,6,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22786 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22787 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 131 324 14 112 48 77 141 269), lower := (rows 35 131 324 14 112 48 64 128 256), losses := [] }

theorem u22787 : Upper (D 6) (R 6) [34,129,320,6,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22787 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22788 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 25 28 34 100 228 356), lower := (rows 35 131 324 25 28 34 64 128 256), losses := [] }

theorem u22788 : Upper (D 6) (R 6) [34,129,320,17,12,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22789 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 195, targets := 4 },{ cop := 0, region := 324, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 324 25 28 36 98 226 354), lower := (rows 35 131 324 25 28 36 64 128 256), losses := [] }

theorem u22789 : Upper (D 6) (R 6) [34,129,320,17,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22790 : Route 9 := (fun mask => (mask,id))

def c22790 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22790 : Upper (D 6) (R 6) [34,129,320,17,12,64] 13 := by
  apply FastRouting.sound _ _ [34,129,320,17,12,64] 13 (by decide) (choices 1) [2,4,32] r22790 c22790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6969
  · exact u6970
  · exact u6971

def b22791 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 25 52 34 76 204 332), lower := (rows 35 131 324 25 52 34 64 128 256), losses := [] }

theorem u22791 : Upper (D 6) (R 6) [34,129,320,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22792 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 131 324 25 52 36 74 202 330), lower := (rows 35 131 324 25 52 36 64 128 256), losses := [] }

theorem u22792 : Upper (D 6) (R 6) [34,129,320,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22793 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 324 25 52 40 70 198 326), lower := (rows 35 131 324 25 52 40 64 128 256), losses := [] }

theorem u22793 : Upper (D 6) (R 6) [34,129,320,17,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22793 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22794 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 324 25 52 96 78 142 270), lower := (rows 35 131 324 25 52 96 64 128 256), losses := [] }

theorem u22794 : Upper (D 6) (R 6) [34,129,320,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22795 : Route 9 := (fun mask => (mask,id))

def c22795 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22795 : Upper (D 6) (R 6) [34,129,320,17,66,4] 13 := by
  apply FastRouting.sound _ _ [34,129,320,17,66,4] 13 (by decide) (choices 1) [4,8,32] r22795 c22795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6972
  · exact u6973
  · exact u6974

def b22796 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 324 25 82 40 100 164 292), lower := (rows 35 131 324 25 82 40 64 128 256), losses := [] }

theorem u22796 : Upper (D 6) (R 6) [34,129,320,17,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22796 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22797 : PairBound 9 := { available := 12, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 25 112 34 76 140 268), lower := (rows 35 131 324 25 112 34 64 128 256), losses := [] }

theorem u22797 : Upper (D 6) (R 6) [34,129,320,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22798 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(4,0),(4,1)], upper := (rows 35 131 324 25 112 36 78 142 270), lower := (rows 35 131 324 25 112 36 64 128 256), losses := [] }

theorem u22798 : Upper (D 6) (R 6) [34,129,320,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22799 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 324 25 112 40 70 134 262), lower := (rows 35 131 324 25 112 40 64 128 256), losses := [] }

theorem u22799 : Upper (D 6) (R 6) [34,129,320,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22799 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u22799
end Delivery.IrregularNine14.P06
