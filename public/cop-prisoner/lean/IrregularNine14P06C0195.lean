import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0032
import IrregularNine14P06C0033

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11700 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 100 137 274 33 100 228 356), lower := (rows 11 22 100 137 274 33 64 128 256), losses := [] }

theorem u11700 : Upper (D 6) (R 6) [10,20,96,129,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11700
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11701 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 22 100 137 274 36 97 225 353), lower := (rows 11 22 100 137 274 36 64 128 256), losses := [] }

theorem u11701 : Upper (D 6) (R 6) [10,20,96,129,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11701
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11702 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 22 100 137 274 96 101 165 293), lower := (rows 11 22 100 137 274 96 64 128 256), losses := [] }

theorem u11702 : Upper (D 6) (R 6) [10,20,96,129,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11702
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11703 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 100 137 304 33 70 198 326), lower := (rows 11 22 100 137 304 33 64 128 256), losses := [] }

theorem u11703 : Upper (D 6) (R 6) [10,20,96,129,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11703
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11704 : Route 9 := (fun mask => (mask,id))

def c11704 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11704 : Upper (D 6) (R 6) [10,20,96,129,288,2] 13 := by
  apply FastRouting.sound _ _ [10,20,96,129,288,2] 13 (by decide) (choices 1) [1,4] r11704 c11704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1978
  · exact u1979

def b11705 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 201, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 22 100 137 304 36 67 195 323), lower := (rows 11 22 100 137 304 36 64 128 256), losses := [] }

theorem u11705 : Upper (D 6) (R 6) [10,20,96,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11705
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11706 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 22 100 137 304 96 71 135 263), lower := (rows 11 22 100 137 304 96 64 128 256), losses := [] }

theorem u11706 : Upper (D 6) (R 6) [10,20,96,129,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11706
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11707 : Route 9 := (fun mask => (mask,id))

def c11707 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11707 : Upper (D 6) (R 6) [10,20,96,132,257,1] 13 := by
  apply FastRouting.sound _ _ [10,20,96,132,257,1] 13 (by decide) (choices 1) [2,32] r11707 c11707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1980
  · exact u1981

theorem m11708_1 : Upper (D 6) (R 6) [10,20,96,132,257,2,1] 13 :=
  permutation_upper _ _ _ [10,20,96,132,257,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1980

def r11708 : Route 9 := (fun mask => (mask,id))

def c11708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11708 : Upper (D 6) (R 6) [10,20,96,132,257,2] 13 := by
  apply FastRouting.sound _ _ [10,20,96,132,257,2] 13 (by decide) (choices 1) [1,32] r11708 c11708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11708_1
  · exact u1982

def b11709 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 22 100 140 273 96 99 163 291), lower := (rows 11 22 100 140 273 96 64 128 256), losses := [] }

theorem u11709 : Upper (D 6) (R 6) [10,20,96,132,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11709
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11710 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 4, region := 36, targets := 2 }], pairs := [(0,6),(2,1),(3,6)], upper := (rows 11 22 100 168 81 33 326 390 262), lower := (rows 11 22 100 168 81 33 64 128 256), losses := [] }

theorem u11710 : Upper (D 6) (R 6) [10,20,96,160,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11710
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11711 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 4, region := 38, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 22 100 168 81 34 325 389 261), lower := (rows 11 22 100 168 81 34 64 128 256), losses := [] }

theorem u11711 : Upper (D 6) (R 6) [10,20,96,160,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11711
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11712 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 1, region := 425, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 22 100 168 81 36 323 387 259), lower := (rows 11 22 100 168 81 36 64 128 256), losses := [] }

theorem u11712 : Upper (D 6) (R 6) [10,20,96,160,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11712
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11713 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 425, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 22 100 168 81 288 71 135 263), lower := (rows 11 22 100 168 81 288 64 128 256), losses := [] }

theorem u11713 : Upper (D 6) (R 6) [10,20,96,160,65,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11713
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11714 : Route 9 := (fun mask => (mask,id))

def c11714 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11714 : Upper (D 6) (R 6) [10,20,96,160,257,1] 13 := by
  apply FastRouting.sound _ _ [10,20,96,160,257,1] 13 (by decide) (choices 1) [2,4] r11714 c11714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1983
  · exact u1984

def r11715 : Route 9 := (fun mask => (mask,id))

def c11715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11715 : Upper (D 6) (R 6) [10,20,96,160,257,2] 13 := by
  apply FastRouting.sound _ _ [10,20,96,160,257,2] 13 (by decide) (choices 1) [1,4] r11715 c11715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1985
  · exact u1986

def b11716 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 11 22 100 168 273 36 67 195 323), lower := (rows 11 22 100 168 273 36 64 128 256), losses := [] }

theorem u11716 : Upper (D 6) (R 6) [10,20,96,160,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11716
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11717 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 22 100 168 273 96 71 135 263), lower := (rows 11 22 100 168 273 96 64 128 256), losses := [] }

theorem u11717 : Upper (D 6) (R 6) [10,20,96,160,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11717
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11718 : Route 9 := (fun mask => (mask,id))

def c11718 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11718 : Upper (D 6) (R 6) [10,20,96,160,258,1] 13 := by
  apply FastRouting.sound _ _ [10,20,96,160,258,1] 13 (by decide) (choices 1) [1,4] r11718 c11718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1987
  · exact u1988

def b11719 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 100 168 274 36 65 193 321), lower := (rows 11 22 100 168 274 36 64 128 256), losses := [] }

theorem u11719 : Upper (D 6) (R 6) [10,20,96,160,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11719
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11720 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 22 100 168 274 96 69 133 261), lower := (rows 11 22 100 168 274 96 64 128 256), losses := [] }

theorem u11720 : Upper (D 6) (R 6) [10,20,96,160,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11720
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11721 : Route 9 := (fun mask => (mask,id))

def c11721 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11721 : Upper (D 6) (R 6) [10,20,96,160,320,1] 13 := by
  apply FastRouting.sound _ _ [10,20,96,160,320,1] 13 (by decide) (choices 1) [1,2,4] r11721 c11721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1989
  · exact u1990
  · exact u1991

def b11722 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 169, targets := 64 },{ cop := 4, region := 38, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 22 100 168 336 34 69 133 261), lower := (rows 11 22 100 168 336 34 64 128 256), losses := [] }

theorem u11722 : Upper (D 6) (R 6) [10,20,96,160,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11722
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11723 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 1, region := 169, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 22 100 168 336 36 67 131 259), lower := (rows 11 22 100 168 336 36 64 128 256), losses := [] }

theorem u11723 : Upper (D 6) (R 6) [10,20,96,160,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11723
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11724 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 22 100 392 49 33 70 198 326), lower := (rows 11 22 100 392 49 33 64 128 256), losses := [] }

theorem u11724 : Upper (D 6) (R 6) [10,20,96,384,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11724
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11725 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 1, region := 457, targets := 32 }], pairs := [(0,5),(4,2),(4,6)], upper := (rows 11 22 100 392 49 34 69 197 325), lower := (rows 11 22 100 392 49 34 64 128 256), losses := [] }

theorem u11725 : Upper (D 6) (R 6) [10,20,96,384,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11725
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11726 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 22 100 392 49 36 67 195 323), lower := (rows 11 22 100 392 49 36 64 128 256), losses := [] }

theorem u11726 : Upper (D 6) (R 6) [10,20,96,384,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11726
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11727 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 22 100 392 49 96 71 135 263), lower := (rows 11 22 100 392 49 96 64 128 256), losses := [] }

theorem u11727 : Upper (D 6) (R 6) [10,20,96,384,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11727
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11728 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 133 41 336 34 100 228 356), lower := (rows 11 22 133 41 336 34 64 128 256), losses := [] }

theorem u11728 : Upper (D 6) (R 6) [10,20,129,33,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11728
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11729 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 2, region := 370, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 22 133 41 336 36 98 226 354), lower := (rows 11 22 133 41 336 36 64 128 256), losses := [] }

theorem u11729 : Upper (D 6) (R 6) [10,20,129,33,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11729
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11730 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 370, targets := 1 }], pairs := [(0,2),(1,0),(4,0)], upper := (rows 11 22 133 41 336 96 102 166 294), lower := (rows 11 22 133 41 336 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 10 16 112 64 128 256), good := (rows 11 59 129 41 368 96 96 128 256) }] }

theorem u11730 : Upper (D 6) (R 6) [10,20,129,33,320,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11730
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11731 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(3,6),(4,2)], upper := (rows 11 22 133 44 81 34 352 480 352), lower := (rows 11 22 133 44 81 34 64 128 256), losses := [] }

theorem u11731 : Upper (D 6) (R 6) [10,20,129,36,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11731
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11732 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 1, region := 360, targets := 1 }], pairs := [(3,0),(3,1),(4,2)], upper := (rows 11 22 133 44 81 96 354 418 290), lower := (rows 11 22 133 44 81 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 16 112 64 128 256), good := (rows 9 60 133 44 113 96 96 128 256) }] }

theorem u11732 : Upper (D 6) (R 6) [10,20,129,36,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11732
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11733 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 1, region := 360, targets := 1 }], pairs := [(3,0),(4,2)], upper := (rows 11 22 133 44 81 288 98 226 354), lower := (rows 11 22 133 44 81 288 64 128 256), losses := [] }

theorem u11733 : Upper (D 6) (R 6) [10,20,129,36,65,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11733
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11734 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 338, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 22 133 44 112 33 322 450 322), lower := (rows 11 22 133 44 112 33 64 128 256), losses := [] }

theorem u11734 : Upper (D 6) (R 6) [10,20,129,36,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11734
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11735 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(2,1),(2,5)], upper := (rows 11 22 133 44 112 34 321 449 321), lower := (rows 11 22 133 44 112 34 64 128 256), losses := [] }

theorem u11735 : Upper (D 6) (R 6) [10,20,129,36,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11735
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11736 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 133 44 112 96 323 387 259), lower := (rows 11 22 133 44 112 96 64 128 256), losses := [] }

theorem u11736 : Upper (D 6) (R 6) [10,20,129,36,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11736
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11737 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(4,2)], upper := (rows 11 22 133 44 112 288 67 195 323), lower := (rows 11 22 133 44 112 288 64 128 256), losses := [] }

theorem u11737 : Upper (D 6) (R 6) [10,20,129,36,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11737
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11738 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(3,6),(4,2)], upper := (rows 11 22 133 44 273 34 96 224 352), lower := (rows 11 22 133 44 273 34 64 128 256), losses := [] }

theorem u11738 : Upper (D 6) (R 6) [10,20,129,36,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11738
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11739 : Route 9 := (fun mask => (mask,id))

def c11739 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11739 : Upper (D 6) (R 6) [10,20,129,36,257,64] 13 := by
  apply FastRouting.sound _ _ [10,20,129,36,257,64] 13 (by decide) (choices 1) [2,32] r11739 c11739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1992
  · exact u1993

def b11740 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 338, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 22 133 44 304 33 66 194 322), lower := (rows 11 22 133 44 304 33 64 128 256), losses := [] }

theorem u11740 : Upper (D 6) (R 6) [10,20,129,36,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11740
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11741 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(2,1),(2,5)], upper := (rows 11 22 133 44 304 34 65 193 321), lower := (rows 11 22 133 44 304 34 64 128 256), losses := [] }

theorem u11741 : Upper (D 6) (R 6) [10,20,129,36,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11741
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11742 : Route 9 := (fun mask => (mask,id))

def c11742 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11742 : Upper (D 6) (R 6) [10,20,129,36,288,64] 13 := by
  apply FastRouting.sound _ _ [10,20,129,36,288,64] 13 (by decide) (choices 1) [1,2] r11742 c11742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1994
  · exact u1995

def b11743 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 338, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 22 133 44 336 33 98 226 354), lower := (rows 11 22 133 44 336 33 64 128 256), losses := [] }

theorem u11743 : Upper (D 6) (R 6) [10,20,129,36,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11743
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11744 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(3,6),(4,2)], upper := (rows 11 22 133 44 336 34 97 225 353), lower := (rows 11 22 133 44 336 34 64 128 256), losses := [] }

theorem u11744 : Upper (D 6) (R 6) [10,20,129,36,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11744
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11745 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 368, targets := 4 }], pairs := [(3,0),(3,1),(4,2)], upper := (rows 11 22 133 44 336 96 99 163 291), lower := (rows 11 22 133 44 336 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 112 64 128 256), good := (rows 10 62 132 44 368 96 96 128 256) },{ target := 1, region := (rows 1 0 4 10 16 112 64 128 256), good := (rows 9 60 133 44 368 96 96 128 256) }] }

theorem u11745 : Upper (D 6) (R 6) [10,20,129,36,320,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11745
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11746 : Route 9 := (fun mask => (mask,id))

def c11746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11746 : Upper (D 6) (R 6) [10,20,129,96,257,2] 13 := by
  apply FastRouting.sound _ _ [10,20,129,96,257,2] 13 (by decide) (choices 1) [4,32] r11746 c11746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1996
  · exact u1997

theorem m11747_2 : Upper (D 6) (R 6) [10,20,129,96,257,4,2] 13 :=
  permutation_upper _ _ _ [10,20,129,96,257,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1996

def r11747 : Route 9 := (fun mask => (mask,id))

def c11747 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11747 : Upper (D 6) (R 6) [10,20,129,96,257,4] 13 := by
  apply FastRouting.sound _ _ [10,20,129,96,257,4] 13 (by decide) (choices 1) [2,32] r11747 c11747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11747_2
  · exact u1998

def b11748 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 133 104 273 96 102 166 294), lower := (rows 11 22 133 104 273 96 64 128 256), losses := [] }

theorem u11748 : Upper (D 6) (R 6) [10,20,129,96,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11748
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11749 : Route 9 := (fun mask => (mask,id))

def c11749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11749 : Upper (D 6) (R 6) [10,20,129,96,258,1] 13 := by
  apply FastRouting.sound _ _ [10,20,129,96,258,1] 13 (by decide) (choices 1) [4,32] r11749 c11749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1999
  · exact u2000

theorem m11750_1 : Upper (D 6) (R 6) [10,20,129,96,258,4,1] 13 :=
  permutation_upper _ _ _ [10,20,129,96,258,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1999

def r11750 : Route 9 := (fun mask => (mask,id))

def c11750 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11750 : Upper (D 6) (R 6) [10,20,129,96,258,4] 13 := by
  apply FastRouting.sound _ _ [10,20,129,96,258,4] 13 (by decide) (choices 1) [1,32] r11750 c11750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11750_1
  · exact u2001

def b11751 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 133 104 274 96 101 165 293), lower := (rows 11 22 133 104 274 96 64 128 256), losses := [] }

theorem u11751 : Upper (D 6) (R 6) [10,20,129,96,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11751
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11752 : Route 9 := (fun mask => (mask,id))

def c11752 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11752 : Upper (D 6) (R 6) [10,20,129,96,288,1] 13 := by
  apply FastRouting.sound _ _ [10,20,129,96,288,1] 13 (by decide) (choices 1) [2,4] r11752 c11752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2002
  · exact u2003

def r11753 : Route 9 := (fun mask => (mask,id))

def c11753 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11753 : Upper (D 6) (R 6) [10,20,129,96,288,2] 13 := by
  apply FastRouting.sound _ _ [10,20,129,96,288,2] 13 (by decide) (choices 1) [1,4] r11753 c11753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2004
  · exact u2005

def r11754 : Route 9 := (fun mask => (mask,id))

def c11754 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11754 : Upper (D 6) (R 6) [10,20,129,96,288,4] 13 := by
  apply FastRouting.sound _ _ [10,20,129,96,288,4] 13 (by decide) (choices 1) [1,2] r11754 c11754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2006
  · exact u2007

def b11755 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 133 104 304 96 71 135 263), lower := (rows 11 22 133 104 304 96 64 128 256), losses := [] }

theorem u11755 : Upper (D 6) (R 6) [10,20,129,96,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11755
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11756 : Route 9 := (fun mask => (mask,id))

def c11756 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11756 : Upper (D 6) (R 6) [10,20,129,257,96,2] 13 := by
  apply FastRouting.sound _ _ [10,20,129,257,96,2] 13 (by decide) (choices 1) [4,32] r11756 c11756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2008
  · exact u2009

theorem m11757_2 : Upper (D 6) (R 6) [10,20,129,257,96,4,2] 13 :=
  permutation_upper _ _ _ [10,20,129,257,96,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2008

def r11757 : Route 9 := (fun mask => (mask,id))

def c11757 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11757 : Upper (D 6) (R 6) [10,20,129,257,96,4] 13 := by
  apply FastRouting.sound _ _ [10,20,129,257,96,4] 13 (by decide) (choices 1) [2,32] r11757 c11757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11757_2
  · exact u2010

def b11758 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 133 265 112 96 102 166 294), lower := (rows 11 22 133 265 112 96 64 128 256), losses := [] }

theorem u11758 : Upper (D 6) (R 6) [10,20,129,257,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11758
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11759 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 22 133 268 49 34 96 224 352), lower := (rows 11 22 133 268 49 34 64 128 256), losses := [] }

theorem u11759 : Upper (D 6) (R 6) [10,20,129,260,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11759
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u11759
end Delivery.IrregularNine14.P06
