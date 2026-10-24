import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0188
import IrregularNine14P06C0189

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29760 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 24, targets := 32 },{ cop := 0, region := 8, targets := 64 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 162 292 14 25 113 81 209 337), lower := (rows 7 162 292 14 25 32 64 128 256), losses := [] }

theorem u29760 : Upper (D 6) (R 6) [6,160,288,6,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29760
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29761 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0),(3,5),(4,5)], upper := (rows 7 162 292 14 81 121 89 217 345), lower := (rows 7 162 292 14 81 32 64 128 256), losses := [] }

theorem u29761 : Upper (D 6) (R 6) [6,160,288,6,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29761
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29762 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0),(3,5),(4,5)], upper := (rows 7 162 292 14 88 113 81 209 337), lower := (rows 7 162 292 14 88 32 64 128 256), losses := [] }

theorem u29762 : Upper (D 6) (R 6) [6,160,288,6,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29762
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29763 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 162 292 25 25 102 70 198 326), lower := (rows 7 162 292 25 25 32 64 128 256), losses := [] }

theorem u29763 : Upper (D 6) (R 6) [6,160,288,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29763
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29764 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 162 292 25 26 101 69 197 325), lower := (rows 7 162 292 25 26 32 64 128 256), losses := [] }

theorem u29764 : Upper (D 6) (R 6) [6,160,288,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29764
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29765 : PairBound 9 := { available := 78, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 162 292 25 81 110 78 206 334), lower := (rows 7 162 292 25 81 32 64 128 256), losses := [] }

theorem u29765 : Upper (D 6) (R 6) [6,160,288,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29765
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29766 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 3, region := 356, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 162 292 25 82 109 77 205 333), lower := (rows 7 162 292 25 82 32 64 128 256), losses := [] }

theorem u29766 : Upper (D 6) (R 6) [6,160,288,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29766
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m29767_4 : Upper (D 6) (R 6) [6,160,288,17,72,4] 13 :=
  permutation_upper _ _ _ [6,160,288,17,72,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11321

def r29767 : Route 9 := (fun mask => (mask,id))

def c29767 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29767 : Upper (D 6) (R 6) [6,160,288,17,72] 13 := by
  apply FastRouting.sound _ _ [6,160,288,17,72] 13 (by decide) (choices 1) [1,2,4,64] r29767 c29767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11320
  · exact u11321
  · exact m29767_4
  · exact u11322

def b29768 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 24, targets := 1 },{ cop := 0, region := 24, targets := 32 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 7 162 292 26 28 97 65 193 321), lower := (rows 7 162 292 26 28 32 64 128 256), losses := [] }

theorem u29768 : Upper (D 6) (R 6) [6,160,288,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29768
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29769 : Route 9 := (fun mask => (mask,id))

def c29769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29769 : Upper (D 6) (R 6) [6,160,288,18,65] 13 := by
  apply FastRouting.sound _ _ [6,160,288,18,65] 13 (by decide) (choices 1) [1,4,8,64] r29769 c29769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11323
  · exact u11324
  · exact u11325
  · exact u11326

def r29770 : Route 9 := (fun mask => (mask,id))

def c29770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29770 : Upper (D 6) (R 6) [6,160,288,18,68] 13 := by
  apply FastRouting.sound _ _ [6,160,288,18,68] 13 (by decide) (choices 1) [1,8,64] r29770 c29770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11327
  · exact u11328
  · exact u11329

def b29771 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 162 292 26 88 101 69 197 325), lower := (rows 7 162 292 26 88 32 64 128 256), losses := [] }

theorem u29771 : Upper (D 6) (R 6) [6,160,288,18,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29771
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29772 : PairBound 9 := { available := 30, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 7 162 292 73 81 62 94 158 286), lower := (rows 7 162 292 73 81 32 64 128 256), losses := [] }

theorem u29772 : Upper (D 6) (R 6) [6,160,288,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29772
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29773 : Route 9 := (fun mask => (mask,id))

def c29773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29773 : Upper (D 6) (R 6) [6,160,288,65,66] 13 := by
  apply FastRouting.sound _ _ [6,160,288,65,66] 13 (by decide) (choices 1) [1,4,8,16] r29773 c29773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11330
  · exact u11331
  · exact u11332
  · exact u11333

def b29774 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 162 292 73 88 55 87 151 279), lower := (rows 7 162 292 73 88 32 64 128 256), losses := [] }

theorem u29774 : Upper (D 6) (R 6) [6,160,288,65,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29774
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m29775_16 : Upper (D 6) (R 6) [6,160,288,66,68,16] 13 :=
  permutation_upper _ _ _ [6,160,288,66,68,8] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11335

def r29775 : Route 9 := (fun mask => (mask,id))

def c29775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29775 : Upper (D 6) (R 6) [6,160,288,66,68] 13 := by
  apply FastRouting.sound _ _ [6,160,288,66,68] 13 (by decide) (choices 1) [1,8,16] r29775 c29775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11334
  · exact u11335
  · exact m29775_16

def b29776 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 162 292 74 88 53 85 149 277), lower := (rows 7 162 292 74 88 32 64 128 256), losses := [] }

theorem u29776 : Upper (D 6) (R 6) [6,160,288,66,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29776
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29777 : PairBound 9 := { available := 7, camps := [{ cop := 6, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 162 292 88 88 39 71 135 263), lower := (rows 7 162 292 88 88 32 64 128 256), losses := [] }

theorem u29777 : Upper (D 6) (R 6) [6,160,288,80,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29777
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29778 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 162 324 11 25 116 116 244 372), lower := (rows 7 162 324 11 25 32 64 128 256), losses := [] }

theorem u29778 : Upper (D 6) (R 6) [6,160,320,3,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29778
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29779 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 162 324 11 28 113 113 241 369), lower := (rows 7 162 324 11 28 32 64 128 256), losses := [] }

theorem u29779 : Upper (D 6) (R 6) [6,160,320,3,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29779
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29780 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 162 324 11 49 124 92 220 348), lower := (rows 7 162 324 11 49 32 64 128 256), losses := [] }

theorem u29780 : Upper (D 6) (R 6) [6,160,320,3,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29780
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29781 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 162 324 11 52 121 89 217 345), lower := (rows 7 162 324 11 52 32 64 128 256), losses := [] }

theorem u29781 : Upper (D 6) (R 6) [6,160,320,3,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29781
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29782 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 162 324 11 56 117 85 213 341), lower := (rows 7 162 324 11 56 32 64 128 256), losses := [] }

theorem u29782 : Upper (D 6) (R 6) [6,160,320,3,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29782
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29783 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 162 324 11 81 60 124 188 316), lower := (rows 7 162 324 11 81 32 64 128 256), losses := [] }

theorem u29783 : Upper (D 6) (R 6) [6,160,320,3,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29783
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29784 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 162 324 11 88 53 117 181 309), lower := (rows 7 162 324 11 88 32 64 128 256), losses := [] }

theorem u29784 : Upper (D 6) (R 6) [6,160,320,3,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29784
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29785 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 162 324 11 112 61 93 157 285), lower := (rows 7 162 324 11 112 32 64 128 256), losses := [] }

theorem u29785 : Upper (D 6) (R 6) [6,160,320,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29785
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29786 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 162 324 14 25 113 113 241 369), lower := (rows 7 162 324 14 25 32 64 128 256), losses := [] }

theorem u29786 : Upper (D 6) (R 6) [6,160,320,6,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29786
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29787 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 162 324 14 49 121 89 217 345), lower := (rows 7 162 324 14 49 32 64 128 256), losses := [] }

theorem u29787 : Upper (D 6) (R 6) [6,160,320,6,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29787
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29788 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 162 324 14 56 113 81 209 337), lower := (rows 7 162 324 14 56 32 64 128 256), losses := [] }

theorem u29788 : Upper (D 6) (R 6) [6,160,320,6,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29788
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29789 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 162 324 14 112 57 89 153 281), lower := (rows 7 162 324 14 112 32 64 128 256), losses := [] }

theorem u29789 : Upper (D 6) (R 6) [6,160,320,6,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29789
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29790 : PairBound 9 := { available := 102, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 162 324 25 25 102 102 230 358), lower := (rows 7 162 324 25 25 32 64 128 256), losses := [] }

theorem u29790 : Upper (D 6) (R 6) [6,160,320,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29790
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29791 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 162 324 25 26 101 101 229 357), lower := (rows 7 162 324 25 26 32 64 128 256), losses := [] }

theorem u29791 : Upper (D 6) (R 6) [6,160,320,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29791
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29792 : PairBound 9 := { available := 78, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 162 324 25 49 110 78 206 334), lower := (rows 7 162 324 25 49 32 64 128 256), losses := [] }

theorem u29792 : Upper (D 6) (R 6) [6,160,320,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29792
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29793 : PairBound 9 := { available := 77, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 162 324 25 50 109 77 205 333), lower := (rows 7 162 324 25 50 32 64 128 256), losses := [] }

theorem u29793 : Upper (D 6) (R 6) [6,160,320,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29793
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29794 : Route 9 := (fun mask => (mask,id))

def c29794 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29794 : Upper (D 6) (R 6) [6,160,320,17,36] 13 := by
  apply FastRouting.sound _ _ [6,160,320,17,36] 13 (by decide) (choices 1) [1,2,8,64] r29794 c29794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11336
  · exact u11337
  · exact u11338
  · exact u11339

def r29795 : Route 9 := (fun mask => (mask,id))

def c29795 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29795 : Upper (D 6) (R 6) [6,160,320,17,40] 13 := by
  apply FastRouting.sound _ _ [6,160,320,17,40] 13 (by decide) (choices 1) [1,2,4,64] r29795 c29795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11340
  · exact u11341
  · exact u11342
  · exact u11343

def r29796 : Route 9 := (fun mask => (mask,id))

def c29796 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29796 : Upper (D 6) (R 6) [6,160,320,17,96] 13 := by
  apply FastRouting.sound _ _ [6,160,320,17,96] 13 (by decide) (choices 1) [1,2,4,8] r29796 c29796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11344
  · exact u11345
  · exact u11346
  · exact u11347

def b29797 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 162 324 26 28 97 97 225 353), lower := (rows 7 162 324 26 28 32 64 128 256), losses := [] }

theorem u29797 : Upper (D 6) (R 6) [6,160,320,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29797
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29798 : Route 9 := (fun mask => (mask,id))

def c29798 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29798 : Upper (D 6) (R 6) [6,160,320,18,33] 13 := by
  apply FastRouting.sound _ _ [6,160,320,18,33] 13 (by decide) (choices 1) [1,4,8,64] r29798 c29798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11348
  · exact u11349
  · exact u11350
  · exact u11351

def r29799 : Route 9 := (fun mask => (mask,id))

def c29799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29799 : Upper (D 6) (R 6) [6,160,320,18,36] 13 := by
  apply FastRouting.sound _ _ [6,160,320,18,36] 13 (by decide) (choices 1) [1,8,64] r29799 c29799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11352
  · exact u11353
  · exact u11354

def b29800 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 24, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 162 324 26 56 101 69 197 325), lower := (rows 7 162 324 26 56 32 64 128 256), losses := [] }

theorem u29800 : Upper (D 6) (R 6) [6,160,320,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29800
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29801 : Route 9 := (fun mask => (mask,id))

def c29801 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29801 : Upper (D 6) (R 6) [6,160,320,18,65] 13 := by
  apply FastRouting.sound _ _ [6,160,320,18,65] 13 (by decide) (choices 1) [1,4,8] r29801 c29801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11355
  · exact u11356
  · exact u11357

def b29802 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 162 324 26 84 41 105 169 297), lower := (rows 7 162 324 26 84 32 64 128 256), losses := [] }

theorem u29802 : Upper (D 6) (R 6) [6,160,320,18,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29802
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29803 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 7 162 324 26 88 37 101 165 293), lower := (rows 7 162 324 26 88 32 64 128 256), losses := [] }

theorem u29803 : Upper (D 6) (R 6) [6,160,320,18,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29803
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29804 : Route 9 := (fun mask => (mask,id))

def c29804 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29804 : Upper (D 6) (R 6) [6,160,320,18,96] 13 := by
  apply FastRouting.sound _ _ [6,160,320,18,96] 13 (by decide) (choices 1) [1,4,8] r29804 c29804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11358
  · exact u11359
  · exact u11360

def r29805 : Route 9 := (fun mask => (mask,id))

def c29805 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29805 : Upper (D 6) (R 6) [6,160,320,33,65] 13 := by
  apply FastRouting.sound _ _ [6,160,320,33,65] 13 (by decide) (choices 1) [2,4,8,16] r29805 c29805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11361
  · exact u11362
  · exact u11363
  · exact u11364

def r29806 : Route 9 := (fun mask => (mask,id))

def c29806 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29806 : Upper (D 6) (R 6) [6,160,320,33,66] 13 := by
  apply FastRouting.sound _ _ [6,160,320,33,66] 13 (by decide) (choices 1) [1,4,8,16] r29806 c29806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11365
  · exact u11366
  · exact u11367
  · exact u11368

def b29807 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 162 324 41 84 59 91 155 283), lower := (rows 7 162 324 41 84 32 64 128 256), losses := [] }

theorem u29807 : Upper (D 6) (R 6) [6,160,320,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29807
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29808 : Route 9 := (fun mask => (mask,id))

def c29808 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29808 : Upper (D 6) (R 6) [6,160,320,33,72] 13 := by
  apply FastRouting.sound _ _ [6,160,320,33,72] 13 (by decide) (choices 1) [1,2,4,16] r29808 c29808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11369
  · exact u11370
  · exact u11371
  · exact u11372

def b29809 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 162 324 42 88 53 85 149 277), lower := (rows 7 162 324 42 88 32 64 128 256), losses := [] }

theorem u29809 : Upper (D 6) (R 6) [6,160,320,34,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29809
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29810 : Route 9 := (fun mask => (mask,id))

def c29810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29810 : Upper (D 6) (R 6) [6,160,320,36,66] 13 := by
  apply FastRouting.sound _ _ [6,160,320,36,66] 13 (by decide) (choices 1) [1,8,16] r29810 c29810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11373
  · exact u11374
  · exact u11375

def r29811 : Route 9 := (fun mask => (mask,id))

def c29811 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29811 : Upper (D 6) (R 6) [6,160,320,36,72] 13 := by
  apply FastRouting.sound _ _ [6,160,320,36,72] 13 (by decide) (choices 1) [1,2,16] r29811 c29811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11376
  · exact u11377
  · exact u11378

def b29812 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 325, targets := 32 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 162 324 56 88 39 71 135 263), lower := (rows 7 162 324 56 88 32 64 128 256), losses := [] }

theorem u29812 : Upper (D 6) (R 6) [6,160,320,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29812
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29813 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 19, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 37 76 22 480 480 480 480), lower := (rows 11 19 37 76 22 32 64 128 256), losses := [] }

theorem u29813 : Upper (D 6) (R 6) [10,17,33,68,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29813
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29814 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 18, targets := 4 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 11 19 37 76 50 484 452 452 452), lower := (rows 11 19 37 76 50 32 64 128 256), losses := [] }

theorem u29814 : Upper (D 6) (R 6) [10,17,33,68,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29814
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29815 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 19 37 76 52 482 450 450 450), lower := (rows 11 19 37 76 52 32 64 128 256), losses := [] }

theorem u29815 : Upper (D 6) (R 6) [10,17,33,68,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29815
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29816 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 19, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 19 37 76 82 420 484 420 420), lower := (rows 11 19 37 76 82 32 64 128 256), losses := [] }

theorem u29816 : Upper (D 6) (R 6) [10,17,33,68,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29816
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29817 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 19 37 76 84 418 482 418 418), lower := (rows 11 19 37 76 84 32 64 128 256), losses := [] }

theorem u29817 : Upper (D 6) (R 6) [10,17,33,68,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29817
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29818 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c29818 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u29818 : Upper (D 6) (R 6) [10,17,33,68,96] 13 := by
  apply FastRouting.sound _ _ [10,17,33,68,96] 13 (by decide) (choices 1) [2,4,128] r29818 c29818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11379
  · exact u11380
  · exact u11381

def b29819 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 328, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 19 37 76 146 356 356 484 356), lower := (rows 11 19 37 76 146 32 64 128 256), losses := [] }

theorem u29819 : Upper (D 6) (R 6) [10,17,33,68,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29819
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u29819
end Delivery.IrregularNine14.P06
