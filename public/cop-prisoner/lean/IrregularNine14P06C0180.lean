import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0024

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10800 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 133 56 336 40 71 135 263), lower := (rows 7 98 133 56 336 40 64 128 256), losses := [] }

theorem u10800 : Upper (D 6) (R 6) [6,96,129,48,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10800
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10801 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 56, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 7 98 140 25 52 33 322 450 322), lower := (rows 7 98 140 25 52 33 64 128 256), losses := [] }

theorem u10801 : Upper (D 6) (R 6) [6,96,136,17,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10801
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10802 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 56, targets := 64 },{ cop := 3, region := 452, targets := 2 }], pairs := [(2,1),(3,6),(4,6)], upper := (rows 7 98 140 25 52 34 321 449 321), lower := (rows 7 98 140 25 52 34 64 128 256), losses := [] }

theorem u10802 : Upper (D 6) (R 6) [6,96,136,17,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10802
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10803 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 25 52 96 323 387 259), lower := (rows 7 98 140 25 52 96 64 128 256), losses := [] }

theorem u10803 : Upper (D 6) (R 6) [6,96,136,17,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10803
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10804 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 354, targets := 4 }], pairs := [(1,2),(2,5)], upper := (rows 7 98 140 25 52 288 67 195 323), lower := (rows 7 98 140 25 52 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 65 129 257), good := (rows 455 66 140 477 20 256 64 128 256) }] }

theorem u10804 : Upper (D 6) (R 6) [6,96,136,17,36,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10804
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10805 : Route 9 := (fun mask => (mask,id))

def c10805 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10805 : Upper (D 6) (R 6) [6,96,136,17,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,258,1] 13 (by decide) (choices 1) [4,32] r10805 c10805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1456
  · exact u1457

theorem m10806_1 : Upper (D 6) (R 6) [6,96,136,17,258,4,1] 13 :=
  permutation_upper _ _ _ [6,96,136,17,258,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1456

def r10806 : Route 9 := (fun mask => (mask,id))

def c10806 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10806 : Upper (D 6) (R 6) [6,96,136,17,258,4] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,258,4] 13 (by decide) (choices 1) [1,32] r10806 c10806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m10806_1
  · exact u1458

def b10807 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 25 274 96 101 165 293), lower := (rows 7 98 140 25 274 96 64 128 256), losses := [] }

theorem u10807 : Upper (D 6) (R 6) [6,96,136,17,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10807
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10808 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 66, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 140 25 276 33 98 226 354), lower := (rows 7 98 140 25 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 8 17 32 98 162 290), good := (rows 470 482 140 24 276 498 64 128 256) }] }

theorem u10808 : Upper (D 6) (R 6) [6,96,136,17,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10808
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m10809_1 : Upper (D 6) (R 6) [6,96,136,17,260,2,1] 13 :=
  permutation_upper _ _ _ [6,96,136,17,260,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1459

def r10809 : Route 9 := (fun mask => (mask,id))

def c10809 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10809 : Upper (D 6) (R 6) [6,96,136,17,260,2] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,260,2] 13 (by decide) (choices 1) [1,32] r10809 c10809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m10809_1
  · exact u1460

def b10810 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 25 276 96 99 163 291), lower := (rows 7 98 140 25 276 96 64 128 256), losses := [] }

theorem u10810 : Upper (D 6) (R 6) [6,96,136,17,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10810
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10811 : PairBound 9 := { available := 70, camps := [], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 98 140 25 304 33 70 198 326), lower := (rows 7 98 140 25 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 12 8 48 32 65 129 257), good := (rows 454 114 140 476 306 498 64 128 256) }] }

theorem u10811 : Upper (D 6) (R 6) [6,96,136,17,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10811
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10812 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 7 98 140 25 304 34 69 197 325), lower := (rows 7 98 140 25 304 34 64 128 256), losses := [] }

theorem u10812 : Upper (D 6) (R 6) [6,96,136,17,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10812
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10813 : Route 9 := (fun mask => (mask,id))

def c10813 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10813 : Upper (D 6) (R 6) [6,96,136,17,288,4] 13 := by
  apply FastRouting.sound _ _ [6,96,136,17,288,4] 13 (by decide) (choices 1) [1,2] r10813 c10813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1461
  · exact u1462

def b10814 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 25 304 96 71 135 263), lower := (rows 7 98 140 25 304 96 64 128 256), losses := [] }

theorem u10814 : Upper (D 6) (R 6) [6,96,136,17,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10814
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10815 : Route 9 := (fun mask => (mask,id))

def c10815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10815 : Upper (D 6) (R 6) [6,96,136,18,257,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,18,257,1] 13 (by decide) (choices 1) [4,32] r10815 c10815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1463
  · exact u1464

theorem m10816_1 : Upper (D 6) (R 6) [6,96,136,18,257,4,1] 13 :=
  permutation_upper _ _ _ [6,96,136,18,257,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1463

def r10816 : Route 9 := (fun mask => (mask,id))

def c10816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10816 : Upper (D 6) (R 6) [6,96,136,18,257,4] 13 := by
  apply FastRouting.sound _ _ [6,96,136,18,257,4] 13 (by decide) (choices 1) [1,32] r10816 c10816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m10816_1
  · exact u1465

def b10817 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 26 273 96 101 165 293), lower := (rows 7 98 140 26 273 96 64 128 256), losses := [] }

theorem u10817 : Upper (D 6) (R 6) [6,96,136,18,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10817
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10818 : Route 9 := (fun mask => (mask,id))

def c10818 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10818 : Upper (D 6) (R 6) [6,96,136,18,260,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,18,260,1] 13 (by decide) (choices 1) [1,32] r10818 c10818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1466
  · exact u1467

def b10819 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 26 276 96 97 161 289), lower := (rows 7 98 140 26 276 96 64 128 256), losses := [] }

theorem u10819 : Upper (D 6) (R 6) [6,96,136,18,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10819
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10820 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 5, region := 66, targets := 1 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 7 98 140 28 273 33 98 226 354), lower := (rows 7 98 140 28 273 33 64 128 256), losses := [] }

theorem u10820 : Upper (D 6) (R 6) [6,96,136,20,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10820
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10821 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 7 98 140 28 273 34 97 225 353), lower := (rows 7 98 140 28 273 34 64 128 256), losses := [] }

theorem u10821 : Upper (D 6) (R 6) [6,96,136,20,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10821
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10822 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 28 273 96 99 163 291), lower := (rows 7 98 140 28 273 96 64 128 256), losses := [] }

theorem u10822 : Upper (D 6) (R 6) [6,96,136,20,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10822
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10823 : Route 9 := (fun mask => (mask,id))

def c10823 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10823 : Upper (D 6) (R 6) [6,96,136,20,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,20,258,1] 13 (by decide) (choices 1) [1,32] r10823 c10823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1468
  · exact u1469

def b10824 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 28 274 96 97 161 289), lower := (rows 7 98 140 28 274 96 64 128 256), losses := [] }

theorem u10824 : Upper (D 6) (R 6) [6,96,136,20,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10824
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10825 : Route 9 := (fun mask => (mask,id))

def c10825 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10825 : Upper (D 6) (R 6) [6,96,136,20,288,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,20,288,1] 13 (by decide) (choices 1) [1,2] r10825 c10825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1470
  · exact u1471

def b10826 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 7 98 140 28 304 34 65 193 321), lower := (rows 7 98 140 28 304 34 64 128 256), losses := [] }

theorem u10826 : Upper (D 6) (R 6) [6,96,136,20,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10826
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10827 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 28 304 96 67 131 259), lower := (rows 7 98 140 28 304 96 64 128 256), losses := [] }

theorem u10827 : Upper (D 6) (R 6) [6,96,136,20,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10827
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10828 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 98 140 41 81 34 340 404 276), lower := (rows 7 98 140 41 81 34 64 128 256), losses := [] }

theorem u10828 : Upper (D 6) (R 6) [6,96,136,33,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10828
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10829 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(3,1),(3,6),(4,2)], upper := (rows 7 98 140 41 81 36 338 402 274), lower := (rows 7 98 140 41 81 36 64 128 256), losses := [] }

theorem u10829 : Upper (D 6) (R 6) [6,96,136,33,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10829
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10830 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 140 41 81 48 326 390 262), lower := (rows 7 98 140 41 81 48 64 128 256), losses := [] }

theorem u10830 : Upper (D 6) (R 6) [6,96,136,33,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10830
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10831 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 80, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 7 98 140 41 81 288 86 150 278), lower := (rows 7 98 140 41 81 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 25 0 65 129 257), good := (rows 471 66 156 477 465 256 64 128 256) }] }

theorem u10831 : Upper (D 6) (R 6) [6,96,136,33,65,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10831
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10832 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 98 140 41 84 33 338 402 274), lower := (rows 7 98 140 41 84 33 64 128 256), losses := [] }

theorem u10832 : Upper (D 6) (R 6) [6,96,136,33,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10832
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10833 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 98 140 41 84 34 337 401 273), lower := (rows 7 98 140 41 84 34 64 128 256), losses := [] }

theorem u10833 : Upper (D 6) (R 6) [6,96,136,33,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10833
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10834 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 140 41 84 48 323 387 259), lower := (rows 7 98 140 41 84 48 64 128 256), losses := [] }

theorem u10834 : Upper (D 6) (R 6) [6,96,136,33,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10834
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10835 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 80, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 7 98 140 41 84 288 83 147 275), lower := (rows 7 98 140 41 84 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 25 0 65 129 257), good := (rows 471 66 156 477 84 256 64 128 256) }] }

theorem u10835 : Upper (D 6) (R 6) [6,96,136,33,68,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10835
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10836 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 98 140 41 273 34 84 212 340), lower := (rows 7 98 140 41 273 34 64 128 256), losses := [] }

theorem u10836 : Upper (D 6) (R 6) [6,96,136,33,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10836
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10837 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(3,1),(3,6),(4,2)], upper := (rows 7 98 140 41 273 36 82 210 338), lower := (rows 7 98 140 41 273 36 64 128 256), losses := [] }

theorem u10837 : Upper (D 6) (R 6) [6,96,136,33,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10837
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10838 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 98 140 41 273 48 70 198 326), lower := (rows 7 98 140 41 273 48 64 128 256), losses := [] }

theorem u10838 : Upper (D 6) (R 6) [6,96,136,33,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10838
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10839 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 41 273 96 86 150 278), lower := (rows 7 98 140 41 273 96 64 128 256), losses := [] }

theorem u10839 : Upper (D 6) (R 6) [6,96,136,33,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10839
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10840 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 98 140 41 274 33 84 212 340), lower := (rows 7 98 140 41 274 33 64 128 256), losses := [] }

theorem u10840 : Upper (D 6) (R 6) [6,96,136,33,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10840
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10841 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(3,1),(3,6),(4,2)], upper := (rows 7 98 140 41 274 36 81 209 337), lower := (rows 7 98 140 41 274 36 64 128 256), losses := [] }

theorem u10841 : Upper (D 6) (R 6) [6,96,136,33,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10841
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10842 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 196, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 98 140 41 274 48 69 197 325), lower := (rows 7 98 140 41 274 48 64 128 256), losses := [] }

theorem u10842 : Upper (D 6) (R 6) [6,96,136,33,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10842
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10843 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 41 274 96 85 149 277), lower := (rows 7 98 140 41 274 96 64 128 256), losses := [] }

theorem u10843 : Upper (D 6) (R 6) [6,96,136,33,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10843
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10844 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 98 140 41 276 33 82 210 338), lower := (rows 7 98 140 41 276 33 64 128 256), losses := [] }

theorem u10844 : Upper (D 6) (R 6) [6,96,136,33,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10844
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10845 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 98 140 41 276 34 81 209 337), lower := (rows 7 98 140 41 276 34 64 128 256), losses := [] }

theorem u10845 : Upper (D 6) (R 6) [6,96,136,33,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10845
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10846 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 336, targets := 32 },{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2),(4,5)], upper := (rows 7 98 140 41 276 48 67 195 323), lower := (rows 7 98 140 41 276 48 64 128 256), losses := [] }

theorem u10846 : Upper (D 6) (R 6) [6,96,136,33,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10846
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10847 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 41 276 96 83 147 275), lower := (rows 7 98 140 41 276 96 64 128 256), losses := [] }

theorem u10847 : Upper (D 6) (R 6) [6,96,136,33,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10847
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10848 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 98 140 41 336 33 86 150 278), lower := (rows 7 98 140 41 336 33 64 128 256), losses := [] }

theorem u10848 : Upper (D 6) (R 6) [6,96,136,33,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10848
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10849 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 98 140 41 336 34 85 149 277), lower := (rows 7 98 140 41 336 34 64 128 256), losses := [] }

theorem u10849 : Upper (D 6) (R 6) [6,96,136,33,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10849
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10850 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 40, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(3,1),(3,6),(4,2)], upper := (rows 7 98 140 41 336 36 83 147 275), lower := (rows 7 98 140 41 336 36 64 128 256), losses := [] }

theorem u10850 : Upper (D 6) (R 6) [6,96,136,33,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10850
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10851 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 140 41 336 48 71 135 263), lower := (rows 7 98 140 41 336 48 64 128 256), losses := [] }

theorem u10851 : Upper (D 6) (R 6) [6,96,136,33,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10851
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10852 : Route 9 := (fun mask => (mask,id))

def c10852 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u10852 : Upper (D 6) (R 6) [6,96,136,48,68,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,68,1] 13 (by decide) (choices 1) [1,2,256] r10852 c10852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1472
  · exact u1473
  · exact u1474

def b10853 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 140 56 84 34 321 385 257), lower := (rows 7 98 140 56 84 34 64 128 256), losses := [] }

theorem u10853 : Upper (D 6) (R 6) [6,96,136,48,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10853
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10854 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 354, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(1,2),(4,5)], upper := (rows 7 98 140 56 84 288 67 131 259), lower := (rows 7 98 140 56 84 288 64 128 256), losses := [] }

theorem u10854 : Upper (D 6) (R 6) [6,96,136,48,68,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10854
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10855 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 98 140 56 273 33 70 198 326), lower := (rows 7 98 140 56 273 33 64 128 256), losses := [] }

theorem u10855 : Upper (D 6) (R 6) [6,96,136,48,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10855
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10856 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 336, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 7 98 140 56 273 34 69 197 325), lower := (rows 7 98 140 56 273 34 64 128 256), losses := [] }

theorem u10856 : Upper (D 6) (R 6) [6,96,136,48,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10856
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10857 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 336, targets := 36 }], pairs := [(3,0),(4,2),(4,5)], upper := (rows 7 98 140 56 273 36 67 195 323), lower := (rows 7 98 140 56 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 37 64 128 256), good := (rows 38 98 172 56 312 36 64 128 256) }] }

theorem u10857 : Upper (D 6) (R 6) [6,96,136,48,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10857
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10858 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 140 56 273 96 71 135 263), lower := (rows 7 98 140 56 273 96 64 128 256), losses := [] }

theorem u10858 : Upper (D 6) (R 6) [6,96,136,48,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10858
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10859 : Route 9 := (fun mask => (mask,id))

def c10859 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10859 : Upper (D 6) (R 6) [6,96,136,48,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,136,48,258,1] 13 (by decide) (choices 1) [1,4] r10859 c10859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1475
  · exact u1476

#print axioms u10859
end Delivery.IrregularNine14.P06
