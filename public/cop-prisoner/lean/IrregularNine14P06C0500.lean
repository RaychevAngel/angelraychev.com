import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0192
import IrregularNine14P06C0193

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30000 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 19, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 19 388 44 52 99 67 195 323), lower := (rows 11 19 388 44 52 32 64 128 256), losses := [] }

theorem u30000 : Upper (D 6) (R 6) [10,17,384,36,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30000
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30001 : Route 9 := (fun mask => (mask,id))

def c30001 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30001 : Upper (D 6) (R 6) [10,17,384,36,68] 13 := by
  apply FastRouting.sound _ _ [10,17,384,36,68] 13 (by decide) (choices 1) [1,2,64] r30001 c30001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11577
  · exact u11578
  · exact u11579

def r30002 : Route 9 := (fun mask => (mask,id))

def c30002 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30002 : Upper (D 6) (R 6) [10,17,384,36,96] 13 := by
  apply FastRouting.sound _ _ [10,17,384,36,96] 13 (by decide) (choices 1) [1,2,4,64] r30002 c30002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11580
  · exact u11581
  · exact u11582
  · exact u11583

def b30003 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 19, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 19 388 104 112 39 71 135 263), lower := (rows 11 19 388 104 112 32 64 128 256), losses := [] }

theorem u30003 : Upper (D 6) (R 6) [10,17,384,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30003
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30004 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 22 37 73 22 480 480 480 480), lower := (rows 11 22 37 73 22 32 64 128 256), losses := [] }

theorem u30004 : Upper (D 6) (R 6) [10,20,33,65,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30004
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30005 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 1, region := 457, targets := 32 }], pairs := [(0,5),(2,1),(3,1)], upper := (rows 11 22 37 73 50 484 452 452 452), lower := (rows 11 22 37 73 50 32 64 128 256), losses := [] }

theorem u30005 : Upper (D 6) (R 6) [10,20,33,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30005
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30006 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 22 37 73 52 482 450 450 450), lower := (rows 11 22 37 73 52 32 64 128 256), losses := [] }

theorem u30006 : Upper (D 6) (R 6) [10,20,33,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30006
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30007 : PairBound 9 := { available := 420, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 22 37 73 82 420 484 420 420), lower := (rows 11 22 37 73 82 32 64 128 256), losses := [] }

theorem u30007 : Upper (D 6) (R 6) [10,20,33,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30007
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30008 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 11, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 22 37 73 84 418 482 418 418), lower := (rows 11 22 37 73 84 32 64 128 256), losses := [] }

theorem u30008 : Upper (D 6) (R 6) [10,20,33,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30008
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30009 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 2, region := 466, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 22 37 73 112 422 454 390 390), lower := (rows 11 22 37 73 112 32 64 128 256), losses := [] }

theorem u30009 : Upper (D 6) (R 6) [10,20,33,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30009
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30010 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 22 37 73 146 356 356 484 356), lower := (rows 11 22 37 73 146 32 64 128 256), losses := [] }

theorem u30010 : Upper (D 6) (R 6) [10,20,33,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30010
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30011 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 361, targets := 4 },{ cop := 2, region := 466, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 22 37 73 148 354 354 482 354), lower := (rows 11 22 37 73 148 32 64 128 256), losses := [] }

theorem u30011 : Upper (D 6) (R 6) [10,20,33,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30011
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30012 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 2, region := 466, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 22 37 73 176 358 326 454 326), lower := (rows 11 22 37 73 176 32 64 128 256), losses := [] }

theorem u30012 : Upper (D 6) (R 6) [10,20,33,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30012
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30013 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 0, region := 292, targets := 64 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 11 22 37 73 208 294 358 422 294), lower := (rows 11 22 37 73 208 32 64 128 256), losses := [] }

theorem u30013 : Upper (D 6) (R 6) [10,20,33,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30013
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30014 : Route 9 := (fun mask => (mask,id))

def c30014 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30014 : Upper (D 6) (R 6) [10,20,33,65,384] 13 := by
  apply FastRouting.sound _ _ [10,20,33,65,384] 13 (by decide) (choices 1) [2,4,64] r30014 c30014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11584
  · exact u11585
  · exact u11586

def b30015 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 19, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 22 37 76 19 480 480 480 480), lower := (rows 11 22 37 76 19 32 64 128 256), losses := [] }

theorem u30015 : Upper (D 6) (R 6) [10,20,33,68,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30015
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30016 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 2, region := 18, targets := 64 }], pairs := [(0,5),(1,6),(3,5)], upper := (rows 11 22 37 76 49 482 450 450 450), lower := (rows 11 22 37 76 49 32 64 128 256), losses := [] }

theorem u30016 : Upper (D 6) (R 6) [10,20,33,68,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30016
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30017 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 37 76 50 481 449 449 449), lower := (rows 11 22 37 76 50 32 64 128 256), losses := [] }

theorem u30017 : Upper (D 6) (R 6) [10,20,33,68,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30017
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30018 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 22 37 76 81 418 482 418 418), lower := (rows 11 22 37 76 81 32 64 128 256), losses := [] }

theorem u30018 : Upper (D 6) (R 6) [10,20,33,68,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30018
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30019 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 22 37 76 82 417 481 417 417), lower := (rows 11 22 37 76 82 32 64 128 256), losses := [] }

theorem u30019 : Upper (D 6) (R 6) [10,20,33,68,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30019
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30020 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 0, region := 496, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 37 76 112 419 451 387 387), lower := (rows 11 22 37 76 112 32 64 128 256), losses := [] }

theorem u30020 : Upper (D 6) (R 6) [10,20,33,68,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30020
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30021 : Route 9 := (fun mask => (mask,id))

def c30021 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30021 : Upper (D 6) (R 6) [10,20,33,68,129] 13 := by
  apply FastRouting.sound _ _ [10,20,33,68,129] 13 (by decide) (choices 1) [2,64,256] r30021 c30021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11587
  · exact u11588
  · exact u11589

def b30022 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 496, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 37 76 146 353 353 481 353), lower := (rows 11 22 37 76 146 32 64 128 256), losses := [] }

theorem u30022 : Upper (D 6) (R 6) [10,20,33,68,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30022
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30023 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 0, region := 496, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 37 76 176 355 323 451 323), lower := (rows 11 22 37 76 176 32 64 128 256), losses := [] }

theorem u30023 : Upper (D 6) (R 6) [10,20,33,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30023
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30024 : Route 9 := (fun mask => (mask,id))

def c30024 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30024 : Upper (D 6) (R 6) [10,20,33,68,192] 13 := by
  apply FastRouting.sound _ _ [10,20,33,68,192] 13 (by decide) (choices 1) [1,2,256] r30024 c30024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11590
  · exact u11591
  · exact u11592

def r30025 : Route 9 := (fun mask => (mask,id))

def c30025 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30025 : Upper (D 6) (R 6) [10,20,33,68,384] 13 := by
  apply FastRouting.sound _ _ [10,20,33,68,384] 13 (by decide) (choices 1) [1,2,64] r30025 c30025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11593
  · exact u11594
  · exact u11595

def b30026 : PairBound 9 := { available := 452, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 37 104 19 484 452 452 452), lower := (rows 11 22 37 104 19 32 64 128 256), losses := [] }

theorem u30026 : Upper (D 6) (R 6) [10,20,33,96,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30026
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30027 : PairBound 9 := { available := 450, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 37 104 21 482 450 450 450), lower := (rows 11 22 37 104 21 32 64 128 256), losses := [] }

theorem u30027 : Upper (D 6) (R 6) [10,20,33,96,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30027
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30028 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 37 104 22 481 449 449 449), lower := (rows 11 22 37 104 22 32 64 128 256), losses := [] }

theorem u30028 : Upper (D 6) (R 6) [10,20,33,96,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30028
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30029 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 22 37 104 81 422 454 390 390), lower := (rows 11 22 37 104 81 32 64 128 256), losses := [] }

theorem u30029 : Upper (D 6) (R 6) [10,20,33,96,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30029
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30030 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 11 22 37 104 82 421 453 389 389), lower := (rows 11 22 37 104 82 32 64 128 256), losses := [] }

theorem u30030 : Upper (D 6) (R 6) [10,20,33,96,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30030
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30031 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 37 104 84 419 451 387 387), lower := (rows 11 22 37 104 84 32 64 128 256), losses := [] }

theorem u30031 : Upper (D 6) (R 6) [10,20,33,96,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30031
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30032 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 1, region := 360, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 11 22 37 104 145 358 326 454 326), lower := (rows 11 22 37 104 145 32 64 128 256), losses := [] }

theorem u30032 : Upper (D 6) (R 6) [10,20,33,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30032
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30033 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 11 22 37 104 146 357 325 453 325), lower := (rows 11 22 37 104 146 32 64 128 256), losses := [] }

theorem u30033 : Upper (D 6) (R 6) [10,20,33,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30033
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30034 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 37 104 148 355 323 451 323), lower := (rows 11 22 37 104 148 32 64 128 256), losses := [] }

theorem u30034 : Upper (D 6) (R 6) [10,20,33,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30034
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30035 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 0, region := 292, targets := 64 }], pairs := [(1,5),(2,6),(4,5)], upper := (rows 11 22 37 104 208 295 327 391 263), lower := (rows 11 22 37 104 208 32 64 128 256), losses := [] }

theorem u30035 : Upper (D 6) (R 6) [10,20,33,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30035
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30036 : Route 9 := (fun mask => (mask,id))

def c30036 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30036 : Upper (D 6) (R 6) [10,20,33,96,384] 13 := by
  apply FastRouting.sound _ _ [10,20,33,96,384] 13 (by decide) (choices 1) [1,2,4,64] r30036 c30036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11596
  · exact u11597
  · exact u11598
  · exact u11599

def b30037 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 22 37 137 22 352 352 480 352), lower := (rows 11 22 37 137 22 32 64 128 256), losses := [] }

theorem u30037 : Upper (D 6) (R 6) [10,20,33,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30037
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30038 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 1, region := 457, targets := 32 }], pairs := [(0,5),(2,1),(3,1)], upper := (rows 11 22 37 137 50 356 324 452 324), lower := (rows 11 22 37 137 50 32 64 128 256), losses := [] }

theorem u30038 : Upper (D 6) (R 6) [10,20,33,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30038
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30039 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 22 37 137 52 354 322 450 322), lower := (rows 11 22 37 137 52 32 64 128 256), losses := [] }

theorem u30039 : Upper (D 6) (R 6) [10,20,33,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30039
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30040 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 22 37 137 82 356 356 484 356), lower := (rows 11 22 37 137 82 32 64 128 256), losses := [] }

theorem u30040 : Upper (D 6) (R 6) [10,20,33,129,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30040
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30041 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 489, targets := 4 },{ cop := 2, region := 338, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 22 37 137 84 354 354 482 354), lower := (rows 11 22 37 137 84 32 64 128 256), losses := [] }

theorem u30041 : Upper (D 6) (R 6) [10,20,33,129,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30041
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30042 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 2, region := 338, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 22 37 137 112 358 326 454 326), lower := (rows 11 22 37 137 112 32 64 128 256), losses := [] }

theorem u30042 : Upper (D 6) (R 6) [10,20,33,129,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30042
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30043 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 338, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 22 37 137 274 100 100 228 356), lower := (rows 11 22 37 137 274 32 64 128 256), losses := [] }

theorem u30043 : Upper (D 6) (R 6) [10,20,33,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30043
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30044 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 233, targets := 4 },{ cop := 2, region := 338, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 22 37 137 276 98 98 226 354), lower := (rows 11 22 37 137 276 32 64 128 256), losses := [] }

theorem u30044 : Upper (D 6) (R 6) [10,20,33,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30044
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30045 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 201, targets := 32 },{ cop := 2, region := 338, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 22 37 137 304 102 70 198 326), lower := (rows 11 22 37 137 304 32 64 128 256), losses := [] }

theorem u30045 : Upper (D 6) (R 6) [10,20,33,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30045
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30046 : Route 9 := (fun mask => (mask,id))

def c30046 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30046 : Upper (D 6) (R 6) [10,20,33,129,320] 13 := by
  apply FastRouting.sound _ _ [10,20,33,129,320] 13 (by decide) (choices 1) [2,4,64] r30046 c30046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11600
  · exact u11601
  · exact u11602

def b30047 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 19, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 22 37 140 19 352 352 480 352), lower := (rows 11 22 37 140 19 32 64 128 256), losses := [] }

theorem u30047 : Upper (D 6) (R 6) [10,20,33,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30047
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30048 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 2, region := 18, targets := 64 }], pairs := [(0,5),(1,6),(3,5)], upper := (rows 11 22 37 140 49 354 322 450 322), lower := (rows 11 22 37 140 49 32 64 128 256), losses := [] }

theorem u30048 : Upper (D 6) (R 6) [10,20,33,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30048
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30049 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 37 140 50 353 321 449 321), lower := (rows 11 22 37 140 50 32 64 128 256), losses := [] }

theorem u30049 : Upper (D 6) (R 6) [10,20,33,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30049
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30050 : Route 9 := (fun mask => (mask,id))

def c30050 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30050 : Upper (D 6) (R 6) [10,20,33,132,65] 13 := by
  apply FastRouting.sound _ _ [10,20,33,132,65] 13 (by decide) (choices 1) [2,64,256] r30050 c30050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11603
  · exact u11604
  · exact u11605

def b30051 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 37 140 82 353 353 481 353), lower := (rows 11 22 37 140 82 32 64 128 256), losses := [] }

theorem u30051 : Upper (D 6) (R 6) [10,20,33,132,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30051
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30052 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 37 140 112 355 323 451 323), lower := (rows 11 22 37 140 112 32 64 128 256), losses := [] }

theorem u30052 : Upper (D 6) (R 6) [10,20,33,132,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30052
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30053 : Route 9 := (fun mask => (mask,id))

def c30053 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30053 : Upper (D 6) (R 6) [10,20,33,132,257] 13 := by
  apply FastRouting.sound _ _ [10,20,33,132,257] 13 (by decide) (choices 1) [2,64] r30053 c30053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11606
  · exact u11607

def b30054 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 37 140 274 97 97 225 353), lower := (rows 11 22 37 140 274 32 64 128 256), losses := [] }

theorem u30054 : Upper (D 6) (R 6) [10,20,33,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30054
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30055 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 201, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 37 140 304 99 67 195 323), lower := (rows 11 22 37 140 304 32 64 128 256), losses := [] }

theorem u30055 : Upper (D 6) (R 6) [10,20,33,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30055
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30056 : Route 9 := (fun mask => (mask,id))

def c30056 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30056 : Upper (D 6) (R 6) [10,20,33,132,320] 13 := by
  apply FastRouting.sound _ _ [10,20,33,132,320] 13 (by decide) (choices 1) [1,2,64] r30056 c30056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11608
  · exact u11609
  · exact u11610

def b30057 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 37 168 19 356 324 452 324), lower := (rows 11 22 37 168 19 32 64 128 256), losses := [] }

theorem u30057 : Upper (D 6) (R 6) [10,20,33,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30057
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30058 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 37 168 21 354 322 450 322), lower := (rows 11 22 37 168 21 32 64 128 256), losses := [] }

theorem u30058 : Upper (D 6) (R 6) [10,20,33,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30058
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30059 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 37 168 22 353 321 449 321), lower := (rows 11 22 37 168 22 32 64 128 256), losses := [] }

theorem u30059 : Upper (D 6) (R 6) [10,20,33,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b30059
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u30059
end Delivery.IrregularNine14.P06
