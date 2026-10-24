import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0310
import IrregularNine14P06C0311

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34980 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 497, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 70 14 49 481 449 449 449), lower := (rows 25 38 70 14 49 32 64 128 256), losses := [] }

theorem u34980 : Upper (D 6) (R 6) [24,36,66,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34981 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 497, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 70 14 112 417 449 385 385), lower := (rows 25 38 70 14 112 32 64 128 256), losses := [] }

theorem u34981 : Upper (D 6) (R 6) [24,36,66,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34982 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 497, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 70 14 145 353 353 481 353), lower := (rows 25 38 70 14 145 32 64 128 256), losses := [] }

theorem u34982 : Upper (D 6) (R 6) [24,36,66,6,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34983 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 497, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 70 14 176 353 321 449 321), lower := (rows 25 38 70 14 176 32 64 128 256), losses := [] }

theorem u34983 : Upper (D 6) (R 6) [24,36,66,6,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34984 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 497, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 70 14 400 97 97 225 353), lower := (rows 25 38 70 14 400 32 64 128 256), losses := [] }

theorem u34984 : Upper (D 6) (R 6) [24,36,66,6,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34985 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 1, region := 452, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 25 38 70 41 81 422 454 390 390), lower := (rows 25 38 70 41 81 32 64 128 256), losses := [] }

theorem u34985 : Upper (D 6) (R 6) [24,36,66,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34986 : PairBound 9 := { available := 389, camps := [{ cop := 2, region := 16, targets := 33 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 25 38 70 41 82 421 453 389 389), lower := (rows 25 38 70 41 82 32 64 128 256), losses := [] }

theorem u34986 : Upper (D 6) (R 6) [24,36,66,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34987 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 25 38 70 41 84 419 451 387 387), lower := (rows 25 38 70 41 84 32 64 128 256), losses := [] }

theorem u34987 : Upper (D 6) (R 6) [24,36,66,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34988 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 358, targets := 1 },{ cop := 1, region := 324, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 25 38 70 41 145 358 326 454 326), lower := (rows 25 38 70 41 145 32 64 128 256), losses := [] }

theorem u34988 : Upper (D 6) (R 6) [24,36,66,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34989 : Route 9 := (fun mask => (mask,id))

def c34989 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34989 : Upper (D 6) (R 6) [24,36,66,33,130] 13 := by
  apply FastRouting.sound _ _ [24,36,66,33,130] 13 (by decide) (choices 1) [1,4,64,256] r34989 c34989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18630
  · exact u18631
  · exact u18632
  · exact u18633

def r34990 : Route 9 := (fun mask => (mask,id))

def c34990 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34990 : Upper (D 6) (R 6) [24,36,66,33,132] 13 := by
  apply FastRouting.sound _ _ [24,36,66,33,132] 13 (by decide) (choices 1) [1,2,64,256] r34990 c34990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18634
  · exact u18635
  · exact u18636
  · exact u18637

def r34991 : Route 9 := (fun mask => (mask,id))

def c34991 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34991 : Upper (D 6) (R 6) [24,36,66,33,192] 13 := by
  apply FastRouting.sound _ _ [24,36,66,33,192] 13 (by decide) (choices 1) [1,2,4,256] r34991 c34991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18638
  · exact u18639
  · exact u18640
  · exact u18641

def r34992 : Route 9 := (fun mask => (mask,id))

def c34992 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34992 : Upper (D 6) (R 6) [24,36,66,33,384] 13 := by
  apply FastRouting.sound _ _ [24,36,66,33,384] 13 (by decide) (choices 1) [1,2,4,64] r34992 c34992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18642
  · exact u18643
  · exact u18644
  · exact u18645

def b34993 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 70 42 145 357 325 453 325), lower := (rows 25 38 70 42 145 32 64 128 256), losses := [] }

theorem u34993 : Upper (D 6) (R 6) [24,36,66,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34994 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 70 42 148 353 321 449 321), lower := (rows 25 38 70 42 148 32 64 128 256), losses := [] }

theorem u34994 : Upper (D 6) (R 6) [24,36,66,34,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34995 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 70 42 208 293 325 389 261), lower := (rows 25 38 70 42 208 32 64 128 256), losses := [] }

theorem u34995 : Upper (D 6) (R 6) [24,36,66,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34996 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 70 42 400 101 69 197 325), lower := (rows 25 38 70 42 400 32 64 128 256), losses := [] }

theorem u34996 : Upper (D 6) (R 6) [24,36,66,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34997 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 70 44 145 355 323 451 323), lower := (rows 25 38 70 44 145 32 64 128 256), losses := [] }

theorem u34997 : Upper (D 6) (R 6) [24,36,66,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34998 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 70 44 146 353 321 449 321), lower := (rows 25 38 70 44 146 32 64 128 256), losses := [] }

theorem u34998 : Upper (D 6) (R 6) [24,36,66,36,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34999 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 70 44 208 291 323 387 259), lower := (rows 25 38 70 44 208 32 64 128 256), losses := [] }

theorem u34999 : Upper (D 6) (R 6) [24,36,66,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34999 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35000 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 70 44 400 99 67 195 323), lower := (rows 25 38 70 44 400 32 64 128 256), losses := [] }

theorem u35000 : Upper (D 6) (R 6) [24,36,66,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35001 : Route 9 := (fun mask => (mask,id))

def c35001 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35001 : Upper (D 6) (R 6) [24,36,66,96,129] 13 := by
  apply FastRouting.sound _ _ [24,36,66,96,129] 13 (by decide) (choices 1) [1,2,4,256] r35001 c35001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18646
  · exact u18647
  · exact u18648
  · exact u18649

def r35002 : Route 9 := (fun mask => (mask,id))

def c35002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35002 : Upper (D 6) (R 6) [24,36,66,96,130] 13 := by
  apply FastRouting.sound _ _ [24,36,66,96,130] 13 (by decide) (choices 1) [1,4,256] r35002 c35002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18650
  · exact u18651
  · exact u18652

def r35003 : Route 9 := (fun mask => (mask,id))

def c35003 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35003 : Upper (D 6) (R 6) [24,36,66,96,384] 13 := by
  apply FastRouting.sound _ _ [24,36,66,96,384] 13 (by decide) (choices 1) [1,2,4] r35003 c35003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18653
  · exact u18654
  · exact u18655

def r35004 : Route 9 := (fun mask => (mask,id))

def c35004 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35004 : Upper (D 6) (R 6) [24,36,66,129,257] 13 := by
  apply FastRouting.sound _ _ [24,36,66,129,257] 13 (by decide) (choices 1) [2,4,64] r35004 c35004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18656
  · exact u18657
  · exact u18658

def r35005 : Route 9 := (fun mask => (mask,id))

def c35005 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35005 : Upper (D 6) (R 6) [24,36,66,129,258] 13 := by
  apply FastRouting.sound _ _ [24,36,66,129,258] 13 (by decide) (choices 1) [1,4,64] r35005 c35005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18659
  · exact u18660
  · exact u18661

def r35006 : Route 9 := (fun mask => (mask,id))

def c35006 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35006 : Upper (D 6) (R 6) [24,36,66,129,288] 13 := by
  apply FastRouting.sound _ _ [24,36,66,129,288] 13 (by decide) (choices 1) [1,2,4,64] r35006 c35006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18662
  · exact u18663
  · exact u18664
  · exact u18665

def r35007 : Route 9 := (fun mask => (mask,id))

def c35007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35007 : Upper (D 6) (R 6) [24,36,66,130,260] 13 := by
  apply FastRouting.sound _ _ [24,36,66,130,260] 13 (by decide) (choices 1) [1,64] r35007 c35007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18666
  · exact u18667

def r35008 : Route 9 := (fun mask => (mask,id))

def c35008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35008 : Upper (D 6) (R 6) [24,36,66,130,288] 13 := by
  apply FastRouting.sound _ _ [24,36,66,130,288] 13 (by decide) (choices 1) [1,4,64] r35008 c35008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18668
  · exact u18669
  · exact u18670

def r35009 : Route 9 := (fun mask => (mask,id))

def c35009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35009 : Upper (D 6) (R 6) [24,36,66,130,320] 13 := by
  apply FastRouting.sound _ _ [24,36,66,130,320] 13 (by decide) (choices 1) [1,4] r35009 c35009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18671
  · exact u18672

def r35010 : Route 9 := (fun mask => (mask,id))

def c35010 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35010 : Upper (D 6) (R 6) [24,36,66,160,320] 13 := by
  apply FastRouting.sound _ _ [24,36,66,160,320] 13 (by decide) (choices 1) [1,2,4] r35010 c35010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18673
  · exact u18674
  · exact u18675

def b35011 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 38 133 11 22 352 352 480 352), lower := (rows 25 38 133 11 22 32 64 128 256), losses := [] }

theorem u35011 : Upper (D 6) (R 6) [24,36,129,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35012 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 38 133 11 50 356 324 452 324), lower := (rows 25 38 133 11 50 32 64 128 256), losses := [] }

theorem u35012 : Upper (D 6) (R 6) [24,36,129,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35013 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 133 11 52 354 322 450 322), lower := (rows 25 38 133 11 52 32 64 128 256), losses := [] }

theorem u35013 : Upper (D 6) (R 6) [24,36,129,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35014 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 38 133 11 82 356 356 484 356), lower := (rows 25 38 133 11 82 32 64 128 256), losses := [] }

theorem u35014 : Upper (D 6) (R 6) [24,36,129,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35015 : Route 9 := (fun mask => (mask,id))

def c35015 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35015 : Upper (D 6) (R 6) [24,36,129,3,68] 13 := by
  apply FastRouting.sound _ _ [24,36,129,3,68] 13 (by decide) (choices 1) [2,64,256] r35015 c35015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18676
  · exact u18677
  · exact u18678

def b35016 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 3, region := 452, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 25 38 133 11 112 358 326 454 326), lower := (rows 25 38 133 11 112 32 64 128 256), losses := [] }

theorem u35016 : Upper (D 6) (R 6) [24,36,129,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35017 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 38 133 11 274 100 100 228 356), lower := (rows 25 38 133 11 274 32 64 128 256), losses := [] }

theorem u35017 : Upper (D 6) (R 6) [24,36,129,3,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35018 : Route 9 := (fun mask => (mask,id))

def c35018 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35018 : Upper (D 6) (R 6) [24,36,129,3,260] 13 := by
  apply FastRouting.sound _ _ [24,36,129,3,260] 13 (by decide) (choices 1) [2,64] r35018 c35018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18679
  · exact u18680

def b35019 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 3, region := 196, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 25 38 133 11 304 102 70 198 326), lower := (rows 25 38 133 11 304 32 64 128 256), losses := [] }

theorem u35019 : Upper (D 6) (R 6) [24,36,129,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35020 : Route 9 := (fun mask => (mask,id))

def c35020 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35020 : Upper (D 6) (R 6) [24,36,129,3,320] 13 := by
  apply FastRouting.sound _ _ [24,36,129,3,320] 13 (by decide) (choices 1) [2,4,64] r35020 c35020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18681
  · exact u18682
  · exact u18683

def b35021 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 25 38 133 13 82 354 354 482 354), lower := (rows 25 38 133 13 82 32 64 128 256), losses := [] }

theorem u35021 : Upper (D 6) (R 6) [24,36,129,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35022 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 25 38 133 13 112 354 322 450 322), lower := (rows 25 38 133 13 112 32 64 128 256), losses := [] }

theorem u35022 : Upper (D 6) (R 6) [24,36,129,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35023 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 25 38 133 13 274 98 98 226 354), lower := (rows 25 38 133 13 274 32 64 128 256), losses := [] }

theorem u35023 : Upper (D 6) (R 6) [24,36,129,5,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35024 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 25 38 133 13 304 98 66 194 322), lower := (rows 25 38 133 13 304 32 64 128 256), losses := [] }

theorem u35024 : Upper (D 6) (R 6) [24,36,129,5,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35025 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 25 38 133 13 336 98 98 226 354), lower := (rows 25 38 133 13 336 32 64 128 256), losses := [] }

theorem u35025 : Upper (D 6) (R 6) [24,36,129,5,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35026 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 8, targets := 96 },{ cop := 2, region := 354, targets := 1 }], pairs := [(1,0),(3,5),(3,6)], upper := (rows 25 38 133 14 81 354 354 482 354), lower := (rows 25 38 133 14 81 32 64 128 256), losses := [] }

theorem u35026 : Upper (D 6) (R 6) [24,36,129,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35027 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 38 133 14 82 353 353 481 353), lower := (rows 25 38 133 14 82 32 64 128 256), losses := [] }

theorem u35027 : Upper (D 6) (R 6) [24,36,129,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35028 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 38 133 14 112 355 323 451 323), lower := (rows 25 38 133 14 112 32 64 128 256), losses := [] }

theorem u35028 : Upper (D 6) (R 6) [24,36,129,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35029 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 8, targets := 96 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(3,5),(3,6)], upper := (rows 25 38 133 14 273 98 98 226 354), lower := (rows 25 38 133 14 273 32 64 128 256), losses := [] }

theorem u35029 : Upper (D 6) (R 6) [24,36,129,6,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35030 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 38 133 14 274 97 97 225 353), lower := (rows 25 38 133 14 274 32 64 128 256), losses := [] }

theorem u35030 : Upper (D 6) (R 6) [24,36,129,6,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35031 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 38 133 14 304 99 67 195 323), lower := (rows 25 38 133 14 304 32 64 128 256), losses := [] }

theorem u35031 : Upper (D 6) (R 6) [24,36,129,6,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35032 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 38 133 14 336 99 99 227 355), lower := (rows 25 38 133 14 336 32 64 128 256), losses := [] }

theorem u35032 : Upper (D 6) (R 6) [24,36,129,6,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35033 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 336, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 25 38 133 41 82 358 326 454 326), lower := (rows 25 38 133 41 82 32 64 128 256), losses := [] }

theorem u35033 : Upper (D 6) (R 6) [24,36,129,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35034 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 336, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 25 38 133 41 84 354 322 450 322), lower := (rows 25 38 133 41 84 32 64 128 256), losses := [] }

theorem u35034 : Upper (D 6) (R 6) [24,36,129,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35035 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 336, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 25 38 133 41 274 102 70 198 326), lower := (rows 25 38 133 41 274 32 64 128 256), losses := [] }

theorem u35035 : Upper (D 6) (R 6) [24,36,129,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35036 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 336, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 25 38 133 41 276 98 66 194 322), lower := (rows 25 38 133 41 276 32 64 128 256), losses := [] }

theorem u35036 : Upper (D 6) (R 6) [24,36,129,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35037 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 1, region := 336, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 25 38 133 41 336 102 70 198 326), lower := (rows 25 38 133 41 336 32 64 128 256), losses := [] }

theorem u35037 : Upper (D 6) (R 6) [24,36,129,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35038 : PairBound 9 := { available := 326, camps := [{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 38 133 42 81 358 326 454 326), lower := (rows 25 38 133 42 81 32 64 128 256), losses := [] }

theorem u35038 : Upper (D 6) (R 6) [24,36,129,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35039 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 133 42 82 357 325 453 325), lower := (rows 25 38 133 42 82 32 64 128 256), losses := [] }

theorem u35039 : Upper (D 6) (R 6) [24,36,129,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u35039
end Delivery.IrregularNine14.P06
