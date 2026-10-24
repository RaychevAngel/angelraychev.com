import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0023

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10680 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 388 88 52 34 65 193 321), lower := (rows 7 42 388 88 52 34 64 128 256), losses := [] }

theorem u10680 : Upper (D 6) (R 6) [6,40,384,80,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10680
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10681 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 388 88 52 96 67 131 259), lower := (rows 7 42 388 88 52 96 64 128 256), losses := [] }

theorem u10681 : Upper (D 6) (R 6) [6,40,384,80,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10681
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10682 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 56, targets := 64 },{ cop := 3, region := 354, targets := 1 }], pairs := [(1,0),(3,6),(4,6)], upper := (rows 7 98 133 25 52 34 328 456 328), lower := (rows 7 98 133 25 52 34 64 128 256), losses := [] }

theorem u10682 : Upper (D 6) (R 6) [6,96,129,17,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10682
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10683 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 56, targets := 66 }], pairs := [(3,1),(3,6)], upper := (rows 7 98 133 25 52 40 322 450 322), lower := (rows 7 98 133 25 52 40 64 128 256), losses := [] }

theorem u10683 : Upper (D 6) (R 6) [6,96,129,17,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10683
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10684 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 25 52 96 330 394 266), lower := (rows 7 98 133 25 52 96 64 128 256), losses := [] }

theorem u10684 : Upper (D 6) (R 6) [6,96,129,17,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10684
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10685 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 354, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 133 25 52 288 74 202 330), lower := (rows 7 98 133 25 52 288 64 128 256), losses := [] }

theorem u10685 : Upper (D 6) (R 6) [6,96,129,17,36,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10685
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10686 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 98 133 25 274 36 104 232 360), lower := (rows 7 98 133 25 274 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 24 37 72 136 264), good := (rows 38 98 164 506 274 36 64 128 256) }] }

theorem u10686 : Upper (D 6) (R 6) [6,96,129,17,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10686
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m10687_4 : Upper (D 6) (R 6) [6,96,129,17,258,8,4] 13 :=
  permutation_upper _ _ _ [6,96,129,17,258,4,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1414

def r10687 : Route 9 := (fun mask => (mask,id))

def c10687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10687 : Upper (D 6) (R 6) [6,96,129,17,258,8] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17,258,8] 13 (by decide) (choices 1) [4,32] r10687 c10687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m10687_4
  · exact u1415

def b10688 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 25 274 96 108 172 300), lower := (rows 7 98 133 25 274 96 64 128 256), losses := [] }

theorem u10688 : Upper (D 6) (R 6) [6,96,129,17,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10688
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10689 : Route 9 := (fun mask => (mask,id))

def c10689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10689 : Upper (D 6) (R 6) [6,96,129,17,260,2] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17,260,2] 13 (by decide) (choices 1) [8,32] r10689 c10689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1416
  · exact u1417

def b10690 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 98, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 133 25 276 40 98 226 354), lower := (rows 7 98 133 25 276 40 64 128 256), losses := [] }

theorem u10690 : Upper (D 6) (R 6) [6,96,129,17,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10690
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10691 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 25 276 96 106 170 298), lower := (rows 7 98 133 25 276 96 64 128 256), losses := [] }

theorem u10691 : Upper (D 6) (R 6) [6,96,129,17,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10691
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10692 : PairBound 9 := { available := 100, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 133 25 280 34 100 228 356), lower := (rows 7 98 133 25 280 34 64 128 256), losses := [{ target := 0, region := (rows 0 79 4 8 24 127 69 133 261), good := (rows 486 98 486 506 314 34 98 128 256) }] }

theorem u10692 : Upper (D 6) (R 6) [6,96,129,17,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10692
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10693 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 66, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 98 133 25 280 36 98 226 354), lower := (rows 7 98 133 25 280 36 64 128 256), losses := [{ target := 0, region := (rows 0 47 4 8 24 37 111 175 303), good := (rows 486 482 486 506 474 486 64 128 256) }] }

theorem u10693 : Upper (D 6) (R 6) [6,96,129,17,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10693
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10694 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 25 280 96 102 166 294), lower := (rows 7 98 133 25 280 96 64 128 256), losses := [] }

theorem u10694 : Upper (D 6) (R 6) [6,96,129,17,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10694
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10695 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 7 98 133 25 304 34 76 204 332), lower := (rows 7 98 133 25 304 34 64 128 256), losses := [] }

theorem u10695 : Upper (D 6) (R 6) [6,96,129,17,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10695
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10696 : Route 9 := (fun mask => (mask,id))

def c10696 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10696 : Upper (D 6) (R 6) [6,96,129,17,288,4] 13 := by
  apply FastRouting.sound _ _ [6,96,129,17,288,4] 13 (by decide) (choices 1) [2,8] r10696 c10696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1418
  · exact u1419

def b10697 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 25 304 40 70 198 326), lower := (rows 7 98 133 25 304 40 64 128 256), losses := [] }

theorem u10697 : Upper (D 6) (R 6) [6,96,129,17,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10697
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10698 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 25 304 96 78 142 270), lower := (rows 7 98 133 25 304 96 64 128 256), losses := [] }

theorem u10698 : Upper (D 6) (R 6) [6,96,129,17,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10698
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10699 : PairBound 9 := { available := 328, camps := [{ cop := 4, region := 330, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 133 26 49 36 328 456 328), lower := (rows 7 98 133 26 49 36 64 128 256), losses := [] }

theorem u10699 : Upper (D 6) (R 6) [6,96,129,18,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10699
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10700 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 56, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 7 98 133 26 49 40 324 452 324), lower := (rows 7 98 133 26 49 40 64 128 256), losses := [] }

theorem u10700 : Upper (D 6) (R 6) [6,96,129,18,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10700
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10701 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 26 49 96 332 396 268), lower := (rows 7 98 133 26 49 96 64 128 256), losses := [] }

theorem u10701 : Upper (D 6) (R 6) [6,96,129,18,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10701
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10702 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 26 49 288 76 204 332), lower := (rows 7 98 133 26 49 288 64 128 256), losses := [] }

theorem u10702 : Upper (D 6) (R 6) [6,96,129,18,33,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10702
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10703 : PairBound 9 := { available := 328, camps := [{ cop := 4, region := 330, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 133 26 52 33 328 456 328), lower := (rows 7 98 133 26 52 33 64 128 256), losses := [] }

theorem u10703 : Upper (D 6) (R 6) [6,96,129,18,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10703
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10704 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 98 133 26 52 40 321 449 321), lower := (rows 7 98 133 26 52 40 64 128 256), losses := [] }

theorem u10704 : Upper (D 6) (R 6) [6,96,129,18,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10704
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10705 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 26 52 96 329 393 265), lower := (rows 7 98 133 26 52 96 64 128 256), losses := [] }

theorem u10705 : Upper (D 6) (R 6) [6,96,129,18,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10705
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10706 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 26 52 288 73 201 329), lower := (rows 7 98 133 26 52 288 64 128 256), losses := [] }

theorem u10706 : Upper (D 6) (R 6) [6,96,129,18,36,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10706
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10707 : Route 9 := (fun mask => (mask,id))

def c10707 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10707 : Upper (D 6) (R 6) [6,96,129,18,257,4] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,257,4] 13 (by decide) (choices 1) [8,32] r10707 c10707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1420
  · exact u1421

theorem m10708_4 : Upper (D 6) (R 6) [6,96,129,18,257,8,4] 13 :=
  permutation_upper _ _ _ [6,96,129,18,257,4,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1420

def r10708 : Route 9 := (fun mask => (mask,id))

def c10708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10708 : Upper (D 6) (R 6) [6,96,129,18,257,8] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,257,8] 13 (by decide) (choices 1) [4,32] r10708 c10708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m10708_4
  · exact u1422

def b10709 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 26 273 96 108 172 300), lower := (rows 7 98 133 26 273 96 64 128 256), losses := [] }

theorem u10709 : Upper (D 6) (R 6) [6,96,129,18,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10709
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10710 : PairBound 9 := { available := 104, camps := [], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 133 26 276 33 104 232 360), lower := (rows 7 98 133 26 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 41 17 32 98 162 290), good := (rows 478 490 156 474 276 506 64 128 256) }] }

theorem u10710 : Upper (D 6) (R 6) [6,96,129,18,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10710
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m10711_1 : Upper (D 6) (R 6) [6,96,129,18,260,8,1] 13 :=
  permutation_upper _ _ _ [6,96,129,18,260,1,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1423

def r10711 : Route 9 := (fun mask => (mask,id))

def c10711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10711 : Upper (D 6) (R 6) [6,96,129,18,260,8] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,260,8] 13 (by decide) (choices 1) [1,32] r10711 c10711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m10711_1
  · exact u1424

def b10712 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 26 276 96 105 169 297), lower := (rows 7 98 133 26 276 96 64 128 256), losses := [] }

theorem u10712 : Upper (D 6) (R 6) [6,96,129,18,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10712
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10713 : Route 9 := (fun mask => (mask,id))

def c10713 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10713 : Upper (D 6) (R 6) [6,96,129,18,264,1] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,264,1] 13 (by decide) (choices 1) [4,32] r10713 c10713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1425
  · exact u1426

theorem m10714_1 : Upper (D 6) (R 6) [6,96,129,18,264,4,1] 13 :=
  permutation_upper _ _ _ [6,96,129,18,264,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1425

def r10714 : Route 9 := (fun mask => (mask,id))

def c10714 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10714 : Upper (D 6) (R 6) [6,96,129,18,264,4] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,264,4] 13 (by decide) (choices 1) [1,32] r10714 c10714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m10714_1
  · exact u1427

def b10715 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 26 280 96 101 165 293), lower := (rows 7 98 133 26 280 96 64 128 256), losses := [] }

theorem u10715 : Upper (D 6) (R 6) [6,96,129,18,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10715
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10716 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 197, targets := 32 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 98 133 26 304 33 76 204 332), lower := (rows 7 98 133 26 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 58 48 32 65 129 257), good := (rows 462 122 452 26 314 506 64 128 256) }] }

theorem u10716 : Upper (D 6) (R 6) [6,96,129,18,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10716
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10717 : Route 9 := (fun mask => (mask,id))

def c10717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10717 : Upper (D 6) (R 6) [6,96,129,18,288,4] 13 := by
  apply FastRouting.sound _ _ [6,96,129,18,288,4] 13 (by decide) (choices 1) [1,8] r10717 c10717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1428
  · exact u1429

def b10718 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 98 133 26 304 40 69 197 325), lower := (rows 7 98 133 26 304 40 64 128 256), losses := [] }

theorem u10718 : Upper (D 6) (R 6) [6,96,129,18,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10718
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10719 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 26 304 96 77 141 269), lower := (rows 7 98 133 26 304 96 64 128 256), losses := [] }

theorem u10719 : Upper (D 6) (R 6) [6,96,129,18,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10719
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10720 : PairBound 9 := { available := 328, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 7 98 133 28 49 34 328 456 328), lower := (rows 7 98 133 28 49 34 64 128 256), losses := [] }

theorem u10720 : Upper (D 6) (R 6) [6,96,129,20,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10720
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10721 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 56, targets := 66 }], pairs := [(3,1),(3,6)], upper := (rows 7 98 133 28 49 40 322 450 322), lower := (rows 7 98 133 28 49 40 64 128 256), losses := [] }

theorem u10721 : Upper (D 6) (R 6) [6,96,129,20,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10721
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10722 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 28 49 96 330 394 266), lower := (rows 7 98 133 28 49 96 64 128 256), losses := [] }

theorem u10722 : Upper (D 6) (R 6) [6,96,129,20,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10722
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10723 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 354, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 133 28 49 288 74 202 330), lower := (rows 7 98 133 28 49 288 64 128 256), losses := [] }

theorem u10723 : Upper (D 6) (R 6) [6,96,129,20,33,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10723
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10724 : Route 9 := (fun mask => (mask,id))

def c10724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10724 : Upper (D 6) (R 6) [6,96,129,20,257,2] 13 := by
  apply FastRouting.sound _ _ [6,96,129,20,257,2] 13 (by decide) (choices 1) [8,32] r10724 c10724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1430
  · exact u1431

def b10725 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 98, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 133 28 273 40 98 226 354), lower := (rows 7 98 133 28 273 40 64 128 256), losses := [] }

theorem u10725 : Upper (D 6) (R 6) [6,96,129,20,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10725
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10726 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 28 273 96 106 170 298), lower := (rows 7 98 133 28 273 96 64 128 256), losses := [] }

theorem u10726 : Upper (D 6) (R 6) [6,96,129,20,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10726
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10727 : PairBound 9 := { available := 104, camps := [], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 133 28 274 33 104 232 360), lower := (rows 7 98 133 28 274 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 9 50 32 96 160 288), good := (rows 30 498 140 28 274 506 64 128 256) }] }

theorem u10727 : Upper (D 6) (R 6) [6,96,129,20,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10727
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m10728_1 : Upper (D 6) (R 6) [6,96,129,20,258,8,1] 13 :=
  permutation_upper _ _ _ [6,96,129,20,258,1,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1432

def r10728 : Route 9 := (fun mask => (mask,id))

def c10728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10728 : Upper (D 6) (R 6) [6,96,129,20,258,8] 13 := by
  apply FastRouting.sound _ _ [6,96,129,20,258,8] 13 (by decide) (choices 1) [1,32] r10728 c10728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m10728_1
  · exact u1433

def b10729 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 28 274 96 105 169 297), lower := (rows 7 98 133 28 274 96 64 128 256), losses := [] }

theorem u10729 : Upper (D 6) (R 6) [6,96,129,20,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10729
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10730 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 66, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 98 133 28 280 33 98 226 354), lower := (rows 7 98 133 28 280 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 13 49 32 98 162 290), good := (rows 478 498 156 28 280 506 64 128 256) }] }

theorem u10730 : Upper (D 6) (R 6) [6,96,129,20,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10730
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10731 : PairBound 9 := { available := 97, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 7 98 133 28 280 34 97 225 353), lower := (rows 7 98 133 28 280 34 64 128 256), losses := [{ target := 2, region := (rows 1 79 0 8 24 127 69 133 261), good := (rows 483 98 483 506 314 34 98 128 256) }] }

theorem u10731 : Upper (D 6) (R 6) [6,96,129,20,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10731
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10732 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 28 280 96 99 163 291), lower := (rows 7 98 133 28 280 96 64 128 256), losses := [] }

theorem u10732 : Upper (D 6) (R 6) [6,96,129,20,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10732
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10733 : PairBound 9 := { available := 74, camps := [], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 133 28 304 33 74 202 330), lower := (rows 7 98 133 28 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 50 4 9 50 32 105 169 297), good := (rows 478 498 460 478 498 506 64 128 256) }] }

theorem u10733 : Upper (D 6) (R 6) [6,96,129,20,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10733
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10734 : Route 9 := (fun mask => (mask,id))

def c10734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10734 : Upper (D 6) (R 6) [6,96,129,20,288,2] 13 := by
  apply FastRouting.sound _ _ [6,96,129,20,288,2] 13 (by decide) (choices 1) [1,8] r10734 c10734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1434
  · exact u1435

def b10735 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 133 28 304 40 67 195 323), lower := (rows 7 98 133 28 304 40 64 128 256), losses := [] }

theorem u10735 : Upper (D 6) (R 6) [6,96,129,20,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10735
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10736 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 28 304 96 75 139 267), lower := (rows 7 98 133 28 304 96 64 128 256), losses := [] }

theorem u10736 : Upper (D 6) (R 6) [6,96,129,20,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10736
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10737 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 98 133 41 84 34 344 408 280), lower := (rows 7 98 133 41 84 34 64 128 256), losses := [] }

theorem u10737 : Upper (D 6) (R 6) [6,96,129,33,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10737
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10738 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 98 133 41 84 40 338 402 274), lower := (rows 7 98 133 41 84 40 64 128 256), losses := [] }

theorem u10738 : Upper (D 6) (R 6) [6,96,129,33,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10738
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10739 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 133 41 84 48 330 394 266), lower := (rows 7 98 133 41 84 48 64 128 256), losses := [] }

theorem u10739 : Upper (D 6) (R 6) [6,96,129,33,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10739
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u10739
end Delivery.IrregularNine14.P06
