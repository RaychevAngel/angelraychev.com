import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0031
import IrregularNine14P06C0032

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11520 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 164 13 112 96 326 390 262), lower := (rows 11 19 164 13 112 96 64 128 256), losses := [] }

theorem u11520 : Upper (D 6) (R 6) [10,17,160,5,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11520
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11521 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 19 164 13 112 288 70 198 326), lower := (rows 11 19 164 13 112 288 64 128 256), losses := [] }

theorem u11521 : Upper (D 6) (R 6) [10,17,160,5,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11521
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11522 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 13 304 34 68 196 324), lower := (rows 11 19 164 13 304 34 64 128 256), losses := [] }

theorem u11522 : Upper (D 6) (R 6) [10,17,160,5,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11522
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11523 : PairBound 9 := { available := 66, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 13 304 36 66 194 322), lower := (rows 11 19 164 13 304 36 64 128 256), losses := [] }

theorem u11523 : Upper (D 6) (R 6) [10,17,160,5,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11523
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11524 : Route 9 := (fun mask => (mask,id))

def c11524 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11524 : Upper (D 6) (R 6) [10,17,160,5,288,64] 13 := by
  apply FastRouting.sound _ _ [10,17,160,5,288,64] 13 (by decide) (choices 1) [2,4] r11524 c11524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1887
  · exact u1888

def b11525 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 13 336 34 100 228 356), lower := (rows 11 19 164 13 336 34 64 128 256), losses := [] }

theorem u11525 : Upper (D 6) (R 6) [10,17,160,5,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11525
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11526 : PairBound 9 := { available := 98, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 13 336 36 98 226 354), lower := (rows 11 19 164 13 336 36 64 128 256), losses := [] }

theorem u11526 : Upper (D 6) (R 6) [10,17,160,5,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11526
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11527 : Route 9 := (fun mask => (mask,id))

def c11527 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11527 : Upper (D 6) (R 6) [10,17,160,5,320,64] 13 := by
  apply FastRouting.sound _ _ [10,17,160,5,320,64] 13 (by decide) (choices 1) [2,4,32] r11527 c11527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1889
  · exact u1890
  · exact u1891

def b11528 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 19 164 41 84 34 324 452 324), lower := (rows 11 19 164 41 84 34 64 128 256), losses := [] }

theorem u11528 : Upper (D 6) (R 6) [10,17,160,33,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11528
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11529 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 164 41 84 36 322 450 322), lower := (rows 11 19 164 41 84 36 64 128 256), losses := [] }

theorem u11529 : Upper (D 6) (R 6) [10,17,160,33,68,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11529
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11530 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 19 164 41 84 96 326 390 262), lower := (rows 11 19 164 41 84 96 64 128 256), losses := [] }

theorem u11530 : Upper (D 6) (R 6) [10,17,160,33,68,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11530
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11531 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 19 164 41 84 288 70 198 326), lower := (rows 11 19 164 41 84 288 64 128 256), losses := [] }

theorem u11531 : Upper (D 6) (R 6) [10,17,160,33,68,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11531
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11532 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 19 164 41 276 34 68 196 324), lower := (rows 11 19 164 41 276 34 64 128 256), losses := [] }

theorem u11532 : Upper (D 6) (R 6) [10,17,160,33,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11532
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11533 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 164 41 276 36 66 194 322), lower := (rows 11 19 164 41 276 36 64 128 256), losses := [] }

theorem u11533 : Upper (D 6) (R 6) [10,17,160,33,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11533
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11534 : Route 9 := (fun mask => (mask,id))

def c11534 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11534 : Upper (D 6) (R 6) [10,17,160,33,260,64] 13 := by
  apply FastRouting.sound _ _ [10,17,160,33,260,64] 13 (by decide) (choices 1) [2,4] r11534 c11534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1892
  · exact u1893

def b11535 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 19 164 41 336 34 68 196 324), lower := (rows 11 19 164 41 336 34 64 128 256), losses := [] }

theorem u11535 : Upper (D 6) (R 6) [10,17,160,33,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11535
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11536 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 41 336 36 70 198 326), lower := (rows 11 19 164 41 336 36 64 128 256), losses := [] }

theorem u11536 : Upper (D 6) (R 6) [10,17,160,33,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11536
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11537 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 19 164 41 336 96 70 134 262), lower := (rows 11 19 164 41 336 96 64 128 256), losses := [] }

theorem u11537 : Upper (D 6) (R 6) [10,17,160,33,320,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11537
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11538 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 73 276 34 100 228 356), lower := (rows 11 19 164 73 276 34 64 128 256), losses := [] }

theorem u11538 : Upper (D 6) (R 6) [10,17,160,65,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11538
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11539 : PairBound 9 := { available := 98, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 73 276 36 98 226 354), lower := (rows 11 19 164 73 276 36 64 128 256), losses := [] }

theorem u11539 : Upper (D 6) (R 6) [10,17,160,65,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11539
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11540 : Route 9 := (fun mask => (mask,id))

def c11540 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11540 : Upper (D 6) (R 6) [10,17,160,65,260,64] 13 := by
  apply FastRouting.sound _ _ [10,17,160,65,260,64] 13 (by decide) (choices 1) [2,4,32] r11540 c11540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1894
  · exact u1895
  · exact u1896

def b11541 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 73 304 34 68 196 324), lower := (rows 11 19 164 73 304 34 64 128 256), losses := [] }

theorem u11541 : Upper (D 6) (R 6) [10,17,160,65,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11541
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11542 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 73 304 36 70 198 326), lower := (rows 11 19 164 73 304 36 64 128 256), losses := [] }

theorem u11542 : Upper (D 6) (R 6) [10,17,160,65,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11542
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11543 : Route 9 := (fun mask => (mask,id))

def c11543 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11543 : Upper (D 6) (R 6) [10,17,160,65,288,64] 13 := by
  apply FastRouting.sound _ _ [10,17,160,65,288,64] 13 (by decide) (choices 1) [2,4] r11543 c11543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1897
  · exact u1898

def b11544 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 19 164 76 112 33 326 390 262), lower := (rows 11 19 164 76 112 33 64 128 256), losses := [] }

theorem u11544 : Upper (D 6) (R 6) [10,17,160,68,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11544
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11545 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 19 164 76 112 34 325 389 261), lower := (rows 11 19 164 76 112 34 64 128 256), losses := [] }

theorem u11545 : Upper (D 6) (R 6) [10,17,160,68,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11545
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11546 : PairBound 9 := { available := 259, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 76 112 36 323 387 259), lower := (rows 11 19 164 76 112 36 64 128 256), losses := [] }

theorem u11546 : Upper (D 6) (R 6) [10,17,160,68,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11546
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11547 : Route 9 := (fun mask => (mask,id))

def c11547 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11547 : Upper (D 6) (R 6) [10,17,160,68,96,256] 13 := by
  apply FastRouting.sound _ _ [10,17,160,68,96,256] 13 (by decide) (choices 1) [1,2,4] r11547 c11547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1899
  · exact u1900
  · exact u1901

def b11548 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 204, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 19 164 76 274 33 100 228 356), lower := (rows 11 19 164 76 274 33 64 128 256), losses := [] }

theorem u11548 : Upper (D 6) (R 6) [10,17,160,68,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11548
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11549 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 76 274 36 97 225 353), lower := (rows 11 19 164 76 274 36 64 128 256), losses := [] }

theorem u11549 : Upper (D 6) (R 6) [10,17,160,68,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11549
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11550 : Route 9 := (fun mask => (mask,id))

def c11550 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11550 : Upper (D 6) (R 6) [10,17,160,68,258,64] 13 := by
  apply FastRouting.sound _ _ [10,17,160,68,258,64] 13 (by decide) (choices 1) [1,4,32] r11550 c11550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1902
  · exact u1903
  · exact u1904

def r11551 : Route 9 := (fun mask => (mask,id))

def c11551 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11551 : Upper (D 6) (R 6) [10,17,160,68,260,1] 13 := by
  apply FastRouting.sound _ _ [10,17,160,68,260,1] 13 (by decide) (choices 1) [2,32] r11551 c11551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1905
  · exact u1906

def r11552 : Route 9 := (fun mask => (mask,id))

def c11552 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11552 : Upper (D 6) (R 6) [10,17,160,68,260,2] 13 := by
  apply FastRouting.sound _ _ [10,17,160,68,260,2] 13 (by decide) (choices 1) [1,32] r11552 c11552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1907
  · exact u1908

def r11553 : Route 9 := (fun mask => (mask,id))

def c11553 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11553 : Upper (D 6) (R 6) [10,17,160,68,260,64] 13 := by
  apply FastRouting.sound _ _ [10,17,160,68,260,64] 13 (by decide) (choices 1) [1,2,32] r11553 c11553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1909
  · exact u1910
  · exact u1911

def r11554 : Route 9 := (fun mask => (mask,id))

def c11554 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11554 : Upper (D 6) (R 6) [10,17,160,68,288,1] 13 := by
  apply FastRouting.sound _ _ [10,17,160,68,288,1] 13 (by decide) (choices 1) [2,4] r11554 c11554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1912
  · exact u1913

def r11555 : Route 9 := (fun mask => (mask,id))

def c11555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11555 : Upper (D 6) (R 6) [10,17,160,68,288,2] 13 := by
  apply FastRouting.sound _ _ [10,17,160,68,288,2] 13 (by decide) (choices 1) [1,4] r11555 c11555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1914
  · exact u1915

def b11556 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 76 304 36 67 195 323), lower := (rows 11 19 164 76 304 36 64 128 256), losses := [] }

theorem u11556 : Upper (D 6) (R 6) [10,17,160,68,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11556
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11557 : Route 9 := (fun mask => (mask,id))

def c11557 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11557 : Upper (D 6) (R 6) [10,17,160,68,288,64] 13 := by
  apply FastRouting.sound _ _ [10,17,160,68,288,64] 13 (by decide) (choices 1) [1,2,4] r11557 c11557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1916
  · exact u1917
  · exact u1918

def r11558 : Route 9 := (fun mask => (mask,id))

def c11558 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11558 : Upper (D 6) (R 6) [10,17,160,68,320,1] 13 := by
  apply FastRouting.sound _ _ [10,17,160,68,320,1] 13 (by decide) (choices 1) [2,4,32] r11558 c11558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1919
  · exact u1920
  · exact u1921

def r11559 : Route 9 := (fun mask => (mask,id))

def c11559 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11559 : Upper (D 6) (R 6) [10,17,160,68,320,2] 13 := by
  apply FastRouting.sound _ _ [10,17,160,68,320,2] 13 (by decide) (choices 1) [1,4,32] r11559 c11559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1922
  · exact u1923
  · exact u1924

def b11560 : PairBound 9 := { available := 35, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 76 336 36 99 163 291), lower := (rows 11 19 164 76 336 36 64 128 256), losses := [] }

theorem u11560 : Upper (D 6) (R 6) [10,17,160,68,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11560
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11561 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 204, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 19 164 104 274 33 68 196 324), lower := (rows 11 19 164 104 274 33 64 128 256), losses := [] }

theorem u11561 : Upper (D 6) (R 6) [10,17,160,96,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11561
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11562 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 104 274 36 69 197 325), lower := (rows 11 19 164 104 274 36 64 128 256), losses := [] }

theorem u11562 : Upper (D 6) (R 6) [10,17,160,96,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11562
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11563 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 164 104 274 96 69 133 261), lower := (rows 11 19 164 104 274 96 64 128 256), losses := [] }

theorem u11563 : Upper (D 6) (R 6) [10,17,160,96,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11563
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11564 : Route 9 := (fun mask => (mask,id))

def c11564 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11564 : Upper (D 6) (R 6) [10,17,160,96,260,1] 13 := by
  apply FastRouting.sound _ _ [10,17,160,96,260,1] 13 (by decide) (choices 1) [2,4] r11564 c11564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1925
  · exact u1926

def r11565 : Route 9 := (fun mask => (mask,id))

def c11565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11565 : Upper (D 6) (R 6) [10,17,160,96,260,2] 13 := by
  apply FastRouting.sound _ _ [10,17,160,96,260,2] 13 (by decide) (choices 1) [1,4] r11565 c11565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1927
  · exact u1928

def b11566 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 104 276 36 67 195 323), lower := (rows 11 19 164 104 276 36 64 128 256), losses := [] }

theorem u11566 : Upper (D 6) (R 6) [10,17,160,96,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11566
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11567 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 164 104 276 96 71 135 263), lower := (rows 11 19 164 104 276 96 64 128 256), losses := [] }

theorem u11567 : Upper (D 6) (R 6) [10,17,160,96,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11567
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11568 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 19 164 104 336 33 70 134 262), lower := (rows 11 19 164 104 336 33 64 128 256), losses := [] }

theorem u11568 : Upper (D 6) (R 6) [10,17,160,96,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11568
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11569 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 19 164 104 336 34 69 133 261), lower := (rows 11 19 164 104 336 34 64 128 256), losses := [] }

theorem u11569 : Upper (D 6) (R 6) [10,17,160,96,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11569
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11570 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 104 336 36 71 135 263), lower := (rows 11 19 164 104 336 36 64 128 256), losses := [] }

theorem u11570 : Upper (D 6) (R 6) [10,17,160,96,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11570
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11571 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 388 13 112 34 100 228 356), lower := (rows 11 19 388 13 112 34 64 128 256), losses := [] }

theorem u11571 : Upper (D 6) (R 6) [10,17,384,5,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11571
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m11572_2 : Upper (D 6) (R 6) [10,17,384,5,96,4,2] 13 :=
  permutation_upper _ _ _ [10,17,384,5,96,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1929

def r11572 : Route 9 := (fun mask => (mask,id))

def c11572 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11572 : Upper (D 6) (R 6) [10,17,384,5,96,4] 13 := by
  apply FastRouting.sound _ _ [10,17,384,5,96,4] 13 (by decide) (choices 1) [2,32] r11572 c11572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m11572_2
  · exact u1930

def b11573 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 19 388 13 112 96 102 166 294), lower := (rows 11 19 388 13 112 96 64 128 256), losses := [] }

theorem u11573 : Upper (D 6) (R 6) [10,17,384,5,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11573
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11574 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 19 388 41 84 34 100 228 356), lower := (rows 11 19 388 41 84 34 64 128 256), losses := [] }

theorem u11574 : Upper (D 6) (R 6) [10,17,384,33,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11574
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11575 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 388 41 84 36 98 226 354), lower := (rows 11 19 388 41 84 36 64 128 256), losses := [] }

theorem u11575 : Upper (D 6) (R 6) [10,17,384,33,68,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11575
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11576 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 19 388 41 84 96 102 166 294), lower := (rows 11 19 388 41 84 96 64 128 256), losses := [] }

theorem u11576 : Upper (D 6) (R 6) [10,17,384,33,68,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11576
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11577 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 388 44 84 33 98 226 354), lower := (rows 11 19 388 44 84 33 64 128 256), losses := [] }

theorem u11577 : Upper (D 6) (R 6) [10,17,384,36,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11577
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11578 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 388 44 84 34 97 225 353), lower := (rows 11 19 388 44 84 34 64 128 256), losses := [] }

theorem u11578 : Upper (D 6) (R 6) [10,17,384,36,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b11578
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m11579_1 : Upper (D 6) (R 6) [10,17,384,36,68,64,1] 13 :=
  permutation_upper _ _ _ [10,17,384,36,68,2,32] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1932

theorem m11579_2 : Upper (D 6) (R 6) [10,17,384,36,68,64,2] 13 :=
  permutation_upper _ _ _ [10,17,384,36,68,1,32] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1931

def r11579 : Route 9 := (fun mask => (mask,id))

def c11579 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11579 : Upper (D 6) (R 6) [10,17,384,36,68,64] 13 := by
  apply FastRouting.sound _ _ [10,17,384,36,68,64] 13 (by decide) (choices 1) [1,2,32] r11579 c11579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m11579_1
  · exact m11579_2
  · exact u1933

#print axioms u11579
end Delivery.IrregularNine14.P06
