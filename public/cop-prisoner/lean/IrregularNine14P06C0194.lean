import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0032

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r11640 : Route 9 := (fun mask => (mask,id))

def c11640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11640 : Upper (D 6) (R 6) [10,20,34,65,192,256] 13 := by
  apply FastRouting.sound _ _ [10,20,34,65,192,256] 13 (by decide) (choices 1) [1,4,32] r11640 c11640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1951
  · exact u1952
  · exact u1953

def b11641 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 38 73 400 33 100 228 356), lower := (rows 11 22 38 73 400 33 64 128 256), losses := [] }

theorem u11641 : Upper (D 6) (R 6) [10,20,34,65,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11641
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11642 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 73 400 36 97 225 353), lower := (rows 11 22 38 73 400 36 64 128 256), losses := [] }

theorem u11642 : Upper (D 6) (R 6) [10,20,34,65,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11642
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11643 : Route 9 := (fun mask => (mask,id))

def c11643 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11643 : Upper (D 6) (R 6) [10,20,34,65,384,64] 13 := by
  apply FastRouting.sound _ _ [10,20,34,65,384,64] 13 (by decide) (choices 1) [1,4,32] r11643 c11643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1954
  · exact u1955
  · exact u1956

def b11644 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 496, targets := 6 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(4,1),(4,2)], upper := (rows 11 22 38 76 400 33 97 225 353), lower := (rows 11 22 38 76 400 33 64 128 256), losses := [] }

theorem u11644 : Upper (D 6) (R 6) [10,20,34,68,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11644
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11645 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 496, targets := 6 }], pairs := [(2,0),(4,1),(4,2)], upper := (rows 11 22 38 76 400 96 97 161 289), lower := (rows 11 22 38 76 400 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 104 64 128 256), good := (rows 46 22 38 108 400 96 96 128 256) }] }

theorem u11645 : Upper (D 6) (R 6) [10,20,34,68,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11645
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11646 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 456, targets := 3 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 22 38 104 81 33 452 388 388), lower := (rows 11 22 38 104 81 33 64 128 256), losses := [] }

theorem u11646 : Upper (D 6) (R 6) [10,20,34,96,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11646
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11647 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 464, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 22 38 104 81 36 449 385 385), lower := (rows 11 22 38 104 81 36 64 128 256), losses := [] }

theorem u11647 : Upper (D 6) (R 6) [10,20,34,96,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11647
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11648 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 22 38 104 81 160 325 389 261), lower := (rows 11 22 38 104 81 160 64 128 256), losses := [] }

theorem u11648 : Upper (D 6) (R 6) [10,20,34,96,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11648
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11649 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 328, targets := 3 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 22 38 104 145 33 324 452 324), lower := (rows 11 22 38 104 145 33 64 128 256), losses := [] }

theorem u11649 : Upper (D 6) (R 6) [10,20,34,96,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11649
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11650 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 104 145 36 321 449 321), lower := (rows 11 22 38 104 145 36 64 128 256), losses := [] }

theorem u11650 : Upper (D 6) (R 6) [10,20,34,96,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11650
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11651 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 38 104 145 96 325 389 261), lower := (rows 11 22 38 104 145 96 64 128 256), losses := [] }

theorem u11651 : Upper (D 6) (R 6) [10,20,34,96,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11651
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11652 : Route 9 := (fun mask => (mask,id))

def c11652 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11652 : Upper (D 6) (R 6) [10,20,34,96,129,256] 13 := by
  apply FastRouting.sound _ _ [10,20,34,96,129,256] 13 (by decide) (choices 1) [1,4] r11652 c11652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1957
  · exact u1958

def r11653 : Route 9 := (fun mask => (mask,id))

def c11653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u11653 : Upper (D 6) (R 6) [10,20,34,96,192,1] 13 := by
  apply FastRouting.sound _ _ [10,20,34,96,192,1] 13 (by decide) (choices 1) [1,4,256] r11653 c11653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1959
  · exact u1960
  · exact u1961

def b11654 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 464, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 22 38 104 208 36 321 385 257), lower := (rows 11 22 38 104 208 36 64 128 256), losses := [] }

theorem u11654 : Upper (D 6) (R 6) [10,20,34,96,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11654
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11655 : Route 9 := (fun mask => (mask,id))

def c11655 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11655 : Upper (D 6) (R 6) [10,20,34,96,192,256] 13 := by
  apply FastRouting.sound _ _ [10,20,34,96,192,256] 13 (by decide) (choices 1) [1,4] r11655 c11655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1962
  · exact u1963

def r11656 : Route 9 := (fun mask => (mask,id))

def c11656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11656 : Upper (D 6) (R 6) [10,20,34,96,384,1] 13 := by
  apply FastRouting.sound _ _ [10,20,34,96,384,1] 13 (by decide) (choices 1) [1,4] r11656 c11656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1964
  · exact u1965

def b11657 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 104 400 36 65 193 321), lower := (rows 11 22 38 104 400 36 64 128 256), losses := [] }

theorem u11657 : Upper (D 6) (R 6) [10,20,34,96,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11657
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11658 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 38 104 400 96 69 133 261), lower := (rows 11 22 38 104 400 96 64 128 256), losses := [] }

theorem u11658 : Upper (D 6) (R 6) [10,20,34,96,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11658
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11659 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 38 137 336 33 100 228 356), lower := (rows 11 22 38 137 336 33 64 128 256), losses := [] }

theorem u11659 : Upper (D 6) (R 6) [10,20,34,129,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11659
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11660 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 137 336 36 97 225 353), lower := (rows 11 22 38 137 336 36 64 128 256), losses := [] }

theorem u11660 : Upper (D 6) (R 6) [10,20,34,129,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11660
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11661 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 137, targets := 64 },{ cop := 4, region := 38, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 22 38 137 336 96 101 165 293), lower := (rows 11 22 38 137 336 96 64 128 256), losses := [] }

theorem u11661 : Upper (D 6) (R 6) [10,20,34,129,320,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11661
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11662 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(4,1),(4,2)], upper := (rows 11 22 38 140 336 33 97 225 353), lower := (rows 11 22 38 140 336 33 64 128 256), losses := [] }

theorem u11662 : Upper (D 6) (R 6) [10,20,34,132,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11662
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11663 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 2, region := 137, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 22 38 140 336 96 97 161 289), lower := (rows 11 22 38 140 336 96 64 128 256), losses := [] }

theorem u11663 : Upper (D 6) (R 6) [10,20,34,132,320,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11663
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11664 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 456, targets := 3 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 22 38 168 81 33 324 452 324), lower := (rows 11 22 38 168 81 33 64 128 256), losses := [] }

theorem u11664 : Upper (D 6) (R 6) [10,20,34,160,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11664
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11665 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 168 81 36 321 449 321), lower := (rows 11 22 38 168 81 36 64 128 256), losses := [] }

theorem u11665 : Upper (D 6) (R 6) [10,20,34,160,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11665
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11666 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 393, targets := 64 },{ cop := 4, region := 38, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 22 38 168 81 96 325 389 261), lower := (rows 11 22 38 168 81 96 64 128 256), losses := [] }

theorem u11666 : Upper (D 6) (R 6) [10,20,34,160,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11666
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11667 : Route 9 := (fun mask => (mask,id))

def c11667 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11667 : Upper (D 6) (R 6) [10,20,34,160,65,256] 13 := by
  apply FastRouting.sound _ _ [10,20,34,160,65,256] 13 (by decide) (choices 1) [1,4] r11667 c11667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1966
  · exact u1967

def b11668 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 200, targets := 3 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 22 38 168 273 33 68 196 324), lower := (rows 11 22 38 168 273 33 64 128 256), losses := [] }

theorem u11668 : Upper (D 6) (R 6) [10,20,34,160,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11668
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11669 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 168 273 36 65 193 321), lower := (rows 11 22 38 168 273 36 64 128 256), losses := [] }

theorem u11669 : Upper (D 6) (R 6) [10,20,34,160,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11669
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11670 : Route 9 := (fun mask => (mask,id))

def c11670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11670 : Upper (D 6) (R 6) [10,20,34,160,257,64] 13 := by
  apply FastRouting.sound _ _ [10,20,34,160,257,64] 13 (by decide) (choices 1) [1,4] r11670 c11670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1968
  · exact u1969

def r11671 : Route 9 := (fun mask => (mask,id))

def c11671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11671 : Upper (D 6) (R 6) [10,20,34,160,320,1] 13 := by
  apply FastRouting.sound _ _ [10,20,34,160,320,1] 13 (by decide) (choices 1) [1,4] r11671 c11671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1970
  · exact u1971

def b11672 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 168 336 36 65 193 321), lower := (rows 11 22 38 168 336 36 64 128 256), losses := [] }

theorem u11672 : Upper (D 6) (R 6) [10,20,34,160,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11672
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11673 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 137, targets := 64 },{ cop := 4, region := 38, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 22 38 168 336 96 69 133 261), lower := (rows 11 22 38 168 336 96 64 128 256), losses := [] }

theorem u11673 : Upper (D 6) (R 6) [10,20,34,160,320,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11673
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11674 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 456, targets := 3 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 22 38 200 81 33 356 420 292), lower := (rows 11 22 38 200 81 33 64 128 256), losses := [] }

theorem u11674 : Upper (D 6) (R 6) [10,20,34,192,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11674
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11675 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 22 38 200 81 36 353 417 289), lower := (rows 11 22 38 200 81 36 64 128 256), losses := [] }

theorem u11675 : Upper (D 6) (R 6) [10,20,34,192,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11675
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11676 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 294, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 22 38 200 81 288 101 165 293), lower := (rows 11 22 38 200 81 288 64 128 256), losses := [] }

theorem u11676 : Upper (D 6) (R 6) [10,20,34,192,65,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11676
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11677 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 200, targets := 3 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 22 38 200 273 33 100 228 356), lower := (rows 11 22 38 200 273 33 64 128 256), losses := [] }

theorem u11677 : Upper (D 6) (R 6) [10,20,34,192,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11677
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11678 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 200 273 36 97 225 353), lower := (rows 11 22 38 200 273 36 64 128 256), losses := [] }

theorem u11678 : Upper (D 6) (R 6) [10,20,34,192,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11678
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11679 : Route 9 := (fun mask => (mask,id))

def c11679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11679 : Upper (D 6) (R 6) [10,20,34,192,257,64] 13 := by
  apply FastRouting.sound _ _ [10,20,34,192,257,64] 13 (by decide) (choices 1) [1,4,32] r11679 c11679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1972
  · exact u1973
  · exact u1974

def r11680 : Route 9 := (fun mask => (mask,id))

def c11680 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11680 : Upper (D 6) (R 6) [10,20,34,192,320,1] 13 := by
  apply FastRouting.sound _ _ [10,20,34,192,320,1] 13 (by decide) (choices 1) [1,4,32] r11680 c11680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1975
  · exact u1976
  · exact u1977

def b11681 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 200 336 36 97 161 289), lower := (rows 11 22 38 200 336 36 64 128 256), losses := [] }

theorem u11681 : Upper (D 6) (R 6) [10,20,34,192,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11681
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11682 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 456, targets := 3 },{ cop := 4, region := 38, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 22 38 392 81 33 100 228 356), lower := (rows 11 22 38 392 81 33 64 128 256), losses := [] }

theorem u11682 : Upper (D 6) (R 6) [10,20,34,384,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11682
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11683 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 392 81 36 97 225 353), lower := (rows 11 22 38 392 81 36 64 128 256), losses := [] }

theorem u11683 : Upper (D 6) (R 6) [10,20,34,384,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11683
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11684 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 393, targets := 64 },{ cop := 4, region := 38, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 22 38 392 81 96 101 165 293), lower := (rows 11 22 38 392 81 96 64 128 256), losses := [] }

theorem u11684 : Upper (D 6) (R 6) [10,20,34,384,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11684
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11685 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 100 41 146 33 324 452 324), lower := (rows 11 22 100 41 146 33 64 128 256), losses := [] }

theorem u11685 : Upper (D 6) (R 6) [10,20,96,33,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11685
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11686 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 464, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 100 41 146 36 321 449 321), lower := (rows 11 22 100 41 146 36 64 128 256), losses := [] }

theorem u11686 : Upper (D 6) (R 6) [10,20,96,33,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11686
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11687 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 22 100 41 146 96 325 389 261), lower := (rows 11 22 100 41 146 96 64 128 256), losses := [] }

theorem u11687 : Upper (D 6) (R 6) [10,20,96,33,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11687
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11688 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 22 100 41 146 288 69 197 325), lower := (rows 11 22 100 41 146 288 64 128 256), losses := [] }

theorem u11688 : Upper (D 6) (R 6) [10,20,96,33,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11688
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11689 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 11 22 100 41 208 33 326 390 262), lower := (rows 11 22 100 41 208 33 64 128 256), losses := [] }

theorem u11689 : Upper (D 6) (R 6) [10,20,96,33,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11689
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11690 : PairBound 9 := { available := 261, camps := [{ cop := 5, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 100 41 208 34 325 389 261), lower := (rows 11 22 100 41 208 34 64 128 256), losses := [] }

theorem u11690 : Upper (D 6) (R 6) [10,20,96,33,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11690
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11691 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 22 100 41 208 36 323 387 259), lower := (rows 11 22 100 41 208 36 64 128 256), losses := [] }

theorem u11691 : Upper (D 6) (R 6) [10,20,96,33,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11691
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11692 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 297, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 22 100 41 208 288 71 135 263), lower := (rows 11 22 100 41 208 288 64 128 256), losses := [] }

theorem u11692 : Upper (D 6) (R 6) [10,20,96,33,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11692
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11693 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 100 41 400 33 70 198 326), lower := (rows 11 22 100 41 400 33 64 128 256), losses := [] }

theorem u11693 : Upper (D 6) (R 6) [10,20,96,33,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11693
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11694 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 100 41 400 34 69 197 325), lower := (rows 11 22 100 41 400 34 64 128 256), losses := [] }

theorem u11694 : Upper (D 6) (R 6) [10,20,96,33,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11694
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11695 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 22 100 41 400 36 67 195 323), lower := (rows 11 22 100 41 400 36 64 128 256), losses := [] }

theorem u11695 : Upper (D 6) (R 6) [10,20,96,33,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11695
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11696 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 22 100 41 400 96 71 135 263), lower := (rows 11 22 100 41 400 96 64 128 256), losses := [] }

theorem u11696 : Upper (D 6) (R 6) [10,20,96,33,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11696
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11697 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 5, region := 68, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 22 100 137 273 34 100 228 356), lower := (rows 11 22 100 137 273 34 64 128 256), losses := [] }

theorem u11697 : Upper (D 6) (R 6) [10,20,96,129,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11697
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11698 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 22 100 137 273 36 98 226 354), lower := (rows 11 22 100 137 273 36 64 128 256), losses := [] }

theorem u11698 : Upper (D 6) (R 6) [10,20,96,129,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11698
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11699 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 22 100 137 273 96 102 166 294), lower := (rows 11 22 100 137 273 96 64 128 256), losses := [] }

theorem u11699 : Upper (D 6) (R 6) [10,20,96,129,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11699
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u11699
end Delivery.IrregularNine14.P06
