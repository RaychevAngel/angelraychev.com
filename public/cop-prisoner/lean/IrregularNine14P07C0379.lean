import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0116
import IrregularNine14P07C0117

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r22740 : Route 9 := (fun mask => (mask,id))

def c22740 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22740 : Upper (D 7) (R 7) [36,72,17,34,258,128] 13 := by
  apply FastRouting.sound _ _ [36,72,17,34,258,128] 13 (by decide) (choices 1) [1,128] r22740 c22740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6972
  · exact u6973

def b22741 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 74 21 42 336 33 194 130 386), lower := (rows 37 74 21 42 336 33 64 128 256), losses := [] }

theorem u22741 : Upper (D 7) (R 7) [36,72,17,34,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22742 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 74 21 42 336 34 193 129 385), lower := (rows 37 74 21 42 336 34 64 128 256), losses := [] }

theorem u22742 : Upper (D 7) (R 7) [36,72,17,34,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22743 : Route 9 := (fun mask => (mask,id))

def c22743 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22743 : Upper (D 7) (R 7) [36,72,17,34,320,128] 13 := by
  apply FastRouting.sound _ _ [36,72,17,34,320,128] 13 (by decide) (choices 1) [1,2,128] r22743 c22743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6974
  · exact u6975
  · exact u6976

def b22744 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 42 400 33 194 194 450), lower := (rows 37 74 21 42 400 33 64 128 256), losses := [] }

theorem u22744 : Upper (D 7) (R 7) [36,72,17,34,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22745 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 74 21 42 400 34 193 193 449), lower := (rows 37 74 21 42 400 34 64 128 256), losses := [] }

theorem u22745 : Upper (D 7) (R 7) [36,72,17,34,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22746 : PairBound 9 := { available := 131, camps := [{ cop := 5, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 74 21 42 400 96 195 131 387), lower := (rows 37 74 21 42 400 96 64 128 256), losses := [] }

theorem u22746 : Upper (D 7) (R 7) [36,72,17,34,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22747 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 21 42 400 160 67 195 323), lower := (rows 37 74 21 42 400 160 64 128 256), losses := [] }

theorem u22747 : Upper (D 7) (R 7) [36,72,17,34,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22748 : PairBound 9 := { available := 290, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(3,6),(4,0)], upper := (rows 37 74 21 137 208 34 354 418 290), lower := (rows 37 74 21 137 208 34 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 16 34 0 162 290), good := (rows 429 426 29 137 144 418 0 128 256) }] }

theorem u22748 : Upper (D 7) (R 7) [36,72,17,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22749 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 74 21 137 208 288 98 162 290), lower := (rows 37 74 21 137 208 288 64 128 256), losses := [] }

theorem u22749 : Upper (D 7) (R 7) [36,72,17,129,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22749 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22750 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 21 137 274 34 224 224 480), lower := (rows 37 74 21 137 274 34 64 128 256), losses := [] }

theorem u22750 : Upper (D 7) (R 7) [36,72,17,129,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22751 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 370, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 74 21 137 274 96 226 162 418), lower := (rows 37 74 21 137 274 96 64 128 256), losses := [{ target := 1, region := (rows 17 0 20 8 16 98 64 128 256), good := (rows 37 104 21 137 309 96 96 128 256) }] }

theorem u22751 : Upper (D 7) (R 7) [36,72,17,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22752 : Route 9 := (fun mask => (mask,id))

def c22752 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22752 : Upper (D 7) (R 7) [36,72,17,129,258,128] 13 := by
  apply FastRouting.sound _ _ [36,72,17,129,258,128] 13 (by decide) (choices 1) [2,32] r22752 c22752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6977
  · exact u6978

def r22753 : Route 9 := (fun mask => (mask,id))

def c22753 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u22753 : Upper (D 7) (R 7) [36,72,17,129,320,2] 13 := by
  apply FastRouting.sound _ _ [36,72,17,129,320,2] 13 (by decide) (choices 1) [2,32,128] r22753 c22753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6979
  · exact u6980
  · exact u6981

def r22754 : Route 9 := (fun mask => (mask,id))

def c22754 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22754 : Upper (D 7) (R 7) [36,72,17,129,320,128] 13 := by
  apply FastRouting.sound _ _ [36,72,17,129,320,128] 13 (by decide) (choices 1) [2,32] r22754 c22754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6982
  · exact u6983

def r22755 : Route 9 := (fun mask => (mask,id))

def c22755 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22755 : Upper (D 7) (R 7) [36,72,17,129,384,2] 13 := by
  apply FastRouting.sound _ _ [36,72,17,129,384,2] 13 (by decide) (choices 1) [2,32] r22755 c22755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6984
  · exact u6985

def r22756 : Route 9 := (fun mask => (mask,id))

def c22756 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22756 : Upper (D 7) (R 7) [36,72,17,129,384,64] 13 := by
  apply FastRouting.sound _ _ [36,72,17,129,384,64] 13 (by decide) (choices 1) [2,32] r22756 c22756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6986
  · exact u6987

def b22757 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 21 138 274 33 224 224 480), lower := (rows 37 74 21 138 274 33 64 128 256), losses := [] }

theorem u22757 : Upper (D 7) (R 7) [36,72,17,130,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22758 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 21 138 274 96 225 161 417), lower := (rows 37 74 21 138 274 96 64 128 256), losses := [{ target := 7, region := (rows 17 2 20 8 16 98 64 0 256), good := (rows 37 106 21 42 311 96 96 0 256) }] }

theorem u22758 : Upper (D 7) (R 7) [36,72,17,130,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22759 : Route 9 := (fun mask => (mask,id))

def c22759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22759 : Upper (D 7) (R 7) [36,72,17,130,258,128] 13 := by
  apply FastRouting.sound _ _ [36,72,17,130,258,128] 13 (by decide) (choices 1) [1,32] r22759 c22759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6988
  · exact u6989

def b22760 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 138 336 33 226 162 418), lower := (rows 37 74 21 138 336 33 64 128 256), losses := [] }

theorem u22760 : Upper (D 7) (R 7) [36,72,17,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22761 : Route 9 := (fun mask => (mask,id))

def c22761 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u22761 : Upper (D 7) (R 7) [36,72,17,130,320,2] 13 := by
  apply FastRouting.sound _ _ [36,72,17,130,320,2] 13 (by decide) (choices 1) [1,32,128] r22761 c22761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6990
  · exact u6991
  · exact u6992

def r22762 : Route 9 := (fun mask => (mask,id))

def c22762 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22762 : Upper (D 7) (R 7) [36,72,17,130,320,128] 13 := by
  apply FastRouting.sound _ _ [36,72,17,130,320,128] 13 (by decide) (choices 1) [1,2,32] r22762 c22762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6993
  · exact u6994
  · exact u6995

def b22763 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 138 400 33 98 226 354), lower := (rows 37 74 21 138 400 33 64 128 256), losses := [] }

theorem u22763 : Upper (D 7) (R 7) [36,72,17,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22764 : Route 9 := (fun mask => (mask,id))

def c22764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22764 : Upper (D 7) (R 7) [36,72,17,130,384,2] 13 := by
  apply FastRouting.sound _ _ [36,72,17,130,384,2] 13 (by decide) (choices 1) [1,32] r22764 c22764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6996
  · exact u6997

def r22765 : Route 9 := (fun mask => (mask,id))

def c22765 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22765 : Upper (D 7) (R 7) [36,72,17,130,384,64] 13 := by
  apply FastRouting.sound _ _ [36,72,17,130,384,64] 13 (by decide) (choices 1) [1,2,32] r22765 c22765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6998
  · exact u6999
  · exact u7000

def b22766 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 21 168 146 33 322 450 322), lower := (rows 37 74 21 168 146 33 64 128 256), losses := [] }

theorem u22766 : Upper (D 7) (R 7) [36,72,17,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22767 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,6)], upper := (rows 37 74 21 168 146 34 321 449 321), lower := (rows 37 74 21 168 146 34 64 128 256), losses := [] }

theorem u22767 : Upper (D 7) (R 7) [36,72,17,160,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22768 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 357, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(3,0)], upper := (rows 37 74 21 168 146 96 323 387 259), lower := (rows 37 74 21 168 146 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 98 64 128 256), good := (rows 36 106 28 168 186 96 96 128 256) },{ target := 1, region := (rows 17 0 20 24 16 98 64 128 256), good := (rows 37 104 29 168 189 96 96 128 256) }] }

theorem u22768 : Upper (D 7) (R 7) [36,72,17,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22769 : Route 9 := (fun mask => (mask,id))

def c22769 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22769 : Upper (D 7) (R 7) [36,72,17,160,130,256] 13 := by
  apply FastRouting.sound _ _ [36,72,17,160,130,256] 13 (by decide) (choices 1) [1,2] r22769 c22769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7001
  · exact u7002

def b22770 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 21 168 208 33 322 386 258), lower := (rows 37 74 21 168 208 33 64 128 256), losses := [] }

theorem u22770 : Upper (D 7) (R 7) [36,72,17,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22771 : Route 9 := (fun mask => (mask,id))

def c22771 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u22771 : Upper (D 7) (R 7) [36,72,17,160,192,2] 13 := by
  apply FastRouting.sound _ _ [36,72,17,160,192,2] 13 (by decide) (choices 1) [1,2,256] r22771 c22771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7003
  · exact u7004
  · exact u7005

def r22772 : Route 9 := (fun mask => (mask,id))

def c22772 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22772 : Upper (D 7) (R 7) [36,72,17,160,192,256] 13 := by
  apply FastRouting.sound _ _ [36,72,17,160,192,256] 13 (by decide) (choices 1) [1,2] r22772 c22772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7006
  · exact u7007

def b22773 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 168 274 33 194 194 450), lower := (rows 37 74 21 168 274 33 64 128 256), losses := [] }

theorem u22773 : Upper (D 7) (R 7) [36,72,17,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22774 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 21 168 274 34 193 193 449), lower := (rows 37 74 21 168 274 34 64 128 256), losses := [] }

theorem u22774 : Upper (D 7) (R 7) [36,72,17,160,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22775 : PairBound 9 := { available := 131, camps := [], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 21 168 274 96 195 131 387), lower := (rows 37 74 21 168 274 96 64 128 256), losses := [{ target := 1, region := (rows 17 0 20 8 16 98 64 128 256), good := (rows 37 104 21 168 309 96 96 128 256) },{ target := 7, region := (rows 17 2 20 8 16 98 64 0 256), good := (rows 37 106 21 40 311 96 96 0 256) }] }

theorem u22775 : Upper (D 7) (R 7) [36,72,17,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22776 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 21 168 274 160 67 195 323), lower := (rows 37 74 21 168 274 160 64 128 256), losses := [] }

theorem u22776 : Upper (D 7) (R 7) [36,72,17,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22777 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 168 336 33 194 130 386), lower := (rows 37 74 21 168 336 33 64 128 256), losses := [] }

theorem u22777 : Upper (D 7) (R 7) [36,72,17,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22778 : Route 9 := (fun mask => (mask,id))

def c22778 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22778 : Upper (D 7) (R 7) [36,72,17,160,320,2] 13 := by
  apply FastRouting.sound _ _ [36,72,17,160,320,2] 13 (by decide) (choices 1) [1,2,128] r22778 c22778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7008
  · exact u7009
  · exact u7010

def b22779 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 21 168 336 160 67 131 259), lower := (rows 37 74 21 168 336 160 64 128 256), losses := [] }

theorem u22779 : Upper (D 7) (R 7) [36,72,17,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22780 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 21 168 400 33 66 194 322), lower := (rows 37 74 21 168 400 33 64 128 256), losses := [] }

theorem u22780 : Upper (D 7) (R 7) [36,72,17,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22781 : Route 9 := (fun mask => (mask,id))

def c22781 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22781 : Upper (D 7) (R 7) [36,72,17,160,384,2] 13 := by
  apply FastRouting.sound _ _ [36,72,17,160,384,2] 13 (by decide) (choices 1) [1,2] r22781 c22781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7011
  · exact u7012

def r22782 : Route 9 := (fun mask => (mask,id))

def c22782 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22782 : Upper (D 7) (R 7) [36,72,17,160,384,64] 13 := by
  apply FastRouting.sound _ _ [36,72,17,160,384,64] 13 (by decide) (choices 1) [1,2] r22782 c22782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7013
  · exact u7014

def b22783 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 21 265 146 34 224 224 480), lower := (rows 37 74 21 265 146 34 64 128 256), losses := [] }

theorem u22783 : Upper (D 7) (R 7) [36,72,17,257,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22784 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 242, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 74 21 265 146 96 226 162 418), lower := (rows 37 74 21 265 146 96 64 128 256), losses := [{ target := 1, region := (rows 17 0 20 8 16 98 64 128 256), good := (rows 37 104 21 265 181 96 96 128 256) }] }

theorem u22784 : Upper (D 7) (R 7) [36,72,17,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22785 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 21 265 146 160 98 226 354), lower := (rows 37 74 21 265 146 160 64 128 256), losses := [] }

theorem u22785 : Upper (D 7) (R 7) [36,72,17,257,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22786 : Route 9 := (fun mask => (mask,id))

def c22786 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u22786 : Upper (D 7) (R 7) [36,72,17,257,192,2] 13 := by
  apply FastRouting.sound _ _ [36,72,17,257,192,2] 13 (by decide) (choices 1) [2,32,128] r22786 c22786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7015
  · exact u7016
  · exact u7017

def b22787 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 21 265 208 160 98 162 290), lower := (rows 37 74 21 265 208 160 64 128 256), losses := [] }

theorem u22787 : Upper (D 7) (R 7) [36,72,17,257,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22788 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 21 266 146 33 224 224 480), lower := (rows 37 74 21 266 146 33 64 128 256), losses := [] }

theorem u22788 : Upper (D 7) (R 7) [36,72,17,258,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22789 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 21 266 146 96 225 161 417), lower := (rows 37 74 21 266 146 96 64 128 256), losses := [{ target := 7, region := (rows 17 2 20 8 16 98 64 0 256), good := (rows 37 106 21 298 55 96 96 0 256) }] }

theorem u22789 : Upper (D 7) (R 7) [36,72,17,258,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22790 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(1,7),(2,1),(3,7)], upper := (rows 37 74 21 266 146 160 97 225 353), lower := (rows 37 74 21 266 146 160 64 128 256), losses := [] }

theorem u22790 : Upper (D 7) (R 7) [36,72,17,258,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22791 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 266 208 33 226 162 418), lower := (rows 37 74 21 266 208 33 64 128 256), losses := [] }

theorem u22791 : Upper (D 7) (R 7) [36,72,17,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22792 : Route 9 := (fun mask => (mask,id))

def c22792 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u22792 : Upper (D 7) (R 7) [36,72,17,258,192,2] 13 := by
  apply FastRouting.sound _ _ [36,72,17,258,192,2] 13 (by decide) (choices 1) [1,32,128] r22792 c22792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7018
  · exact u7019
  · exact u7020

def b22793 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 21 266 208 160 99 163 291), lower := (rows 37 74 21 266 208 160 64 128 256), losses := [] }

theorem u22793 : Upper (D 7) (R 7) [36,72,17,258,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22794 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 296 146 33 194 194 450), lower := (rows 37 74 21 296 146 33 64 128 256), losses := [] }

theorem u22794 : Upper (D 7) (R 7) [36,72,17,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22795 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 21 296 146 34 193 193 449), lower := (rows 37 74 21 296 146 34 64 128 256), losses := [] }

theorem u22795 : Upper (D 7) (R 7) [36,72,17,288,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22796 : PairBound 9 := { available := 131, camps := [], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 21 296 146 96 195 131 387), lower := (rows 37 74 21 296 146 96 64 128 256), losses := [{ target := 1, region := (rows 17 0 20 8 16 98 64 128 256), good := (rows 37 104 21 296 181 96 96 128 256) },{ target := 7, region := (rows 17 2 20 8 16 98 64 0 256), good := (rows 37 106 21 296 55 96 96 0 256) }] }

theorem u22796 : Upper (D 7) (R 7) [36,72,17,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22797 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 21 296 146 160 67 195 323), lower := (rows 37 74 21 296 146 160 64 128 256), losses := [] }

theorem u22797 : Upper (D 7) (R 7) [36,72,17,288,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22798 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 21 296 208 33 194 130 386), lower := (rows 37 74 21 296 208 33 64 128 256), losses := [] }

theorem u22798 : Upper (D 7) (R 7) [36,72,17,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22799 : Route 9 := (fun mask => (mask,id))

def c22799 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22799 : Upper (D 7) (R 7) [36,72,17,288,192,2] 13 := by
  apply FastRouting.sound _ _ [36,72,17,288,192,2] 13 (by decide) (choices 1) [1,2,128] r22799 c22799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7021
  · exact u7022
  · exact u7023

#print axioms u22799
end Delivery.IrregularNine14.P07
