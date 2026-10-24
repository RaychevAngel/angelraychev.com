import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0073
import IrregularNine14P06C0074

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16980 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 73 112 33 70 134 262), lower := (rows 11 146 292 73 112 33 64 128 256), losses := [] }

theorem u16980 : Upper (D 6) (R 6) [10,144,288,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16981 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 292, targets := 64 }], pairs := [(2,6),(4,0),(4,2)], upper := (rows 11 146 292 73 112 34 69 133 261), lower := (rows 11 146 292 73 112 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 35 64 128 256), good := (rows 58 178 292 120 112 34 64 128 256) },{ target := 2, region := (rows 1 2 0 8 24 35 64 128 256), good := (rows 59 178 288 121 112 34 64 128 256) }] }

theorem u16981 : Upper (D 6) (R 6) [10,144,288,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16982 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 73 112 36 71 135 263), lower := (rows 11 146 292 73 112 36 64 128 256), losses := [] }

theorem u16982 : Upper (D 6) (R 6) [10,144,288,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16983 : Route 9 := (fun mask => (mask,id))

def c16983 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16983 : Upper (D 6) (R 6) [10,144,288,68,5,1] 13 := by
  apply FastRouting.sound _ _ [10,144,288,68,5,1] 13 (by decide) (choices 1) [2,32] r16983 c16983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4426
  · exact u4427

def r16984 : Route 9 := (fun mask => (mask,id))

def c16984 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16984 : Upper (D 6) (R 6) [10,144,288,68,5,2] 13 := by
  apply FastRouting.sound _ _ [10,144,288,68,5,2] 13 (by decide) (choices 1) [1,32] r16984 c16984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4428
  · exact u4429

def r16985 : Route 9 := (fun mask => (mask,id))

def c16985 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16985 : Upper (D 6) (R 6) [10,144,288,68,5,64] 13 := by
  apply FastRouting.sound _ _ [10,144,288,68,5,64] 13 (by decide) (choices 1) [1,2,32] r16985 c16985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4430
  · exact u4431
  · exact u4432

def r16986 : Route 9 := (fun mask => (mask,id))

def c16986 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16986 : Upper (D 6) (R 6) [10,144,288,68,6,1] 13 := by
  apply FastRouting.sound _ _ [10,144,288,68,6,1] 13 (by decide) (choices 1) [1,32] r16986 c16986
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4433
  · exact u4434

def r16987 : Route 9 := (fun mask => (mask,id))

def c16987 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16987 : Upper (D 6) (R 6) [10,144,288,68,6,64] 13 := by
  apply FastRouting.sound _ _ [10,144,288,68,6,64] 13 (by decide) (choices 1) [1,32] r16987 c16987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4435
  · exact u4436

def b16988 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 146 292 76 49 33 70 198 326), lower := (rows 11 146 292 76 49 33 64 128 256), losses := [] }

theorem u16988 : Upper (D 6) (R 6) [10,144,288,68,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16989 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 4, region := 324, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 11 146 292 76 49 34 69 197 325), lower := (rows 11 146 292 76 49 34 64 128 256), losses := [] }

theorem u16989 : Upper (D 6) (R 6) [10,144,288,68,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16990 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 76 49 36 67 195 323), lower := (rows 11 146 292 76 49 36 64 128 256), losses := [] }

theorem u16990 : Upper (D 6) (R 6) [10,144,288,68,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16991 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 390, targets := 64 }], pairs := [(1,6),(2,6),(4,1)], upper := (rows 11 146 292 76 49 96 71 135 263), lower := (rows 11 146 292 76 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 104 64 128 256), good := (rows 57 144 292 108 49 96 96 128 256) }] }

theorem u16991 : Upper (D 6) (R 6) [10,144,288,68,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16992 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 48, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 146 292 76 50 33 69 197 325), lower := (rows 11 146 292 76 50 33 64 128 256), losses := [] }

theorem u16992 : Upper (D 6) (R 6) [10,144,288,68,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16993 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 76 50 36 65 193 321), lower := (rows 11 146 292 76 50 36 64 128 256), losses := [] }

theorem u16993 : Upper (D 6) (R 6) [10,144,288,68,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16994 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1),(4,0)], upper := (rows 11 146 292 76 50 96 69 133 261), lower := (rows 11 146 292 76 50 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 104 64 128 256), good := (rows 58 146 292 108 50 96 96 128 256) }] }

theorem u16994 : Upper (D 6) (R 6) [10,144,288,68,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16995 : Route 9 := (fun mask => (mask,id))

def c16995 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16995 : Upper (D 6) (R 6) [10,144,288,68,65,1] 13 := by
  apply FastRouting.sound _ _ [10,144,288,68,65,1] 13 (by decide) (choices 1) [2,4,32] r16995 c16995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4437
  · exact u4438
  · exact u4439

def r16996 : Route 9 := (fun mask => (mask,id))

def c16996 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16996 : Upper (D 6) (R 6) [10,144,288,68,65,2] 13 := by
  apply FastRouting.sound _ _ [10,144,288,68,65,2] 13 (by decide) (choices 1) [1,4,32] r16996 c16996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4440
  · exact u4441
  · exact u4442

def b16997 : PairBound 9 := { available := 35, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 76 81 36 99 163 291), lower := (rows 11 146 292 76 81 36 64 128 256), losses := [] }

theorem u16997 : Upper (D 6) (R 6) [10,144,288,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16998 : Route 9 := (fun mask => (mask,id))

def c16998 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16998 : Upper (D 6) (R 6) [10,144,288,68,96,1] 13 := by
  apply FastRouting.sound _ _ [10,144,288,68,96,1] 13 (by decide) (choices 1) [1,2,4] r16998 c16998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4443
  · exact u4444
  · exact u4445

def r16999 : Route 9 := (fun mask => (mask,id))

def c16999 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16999 : Upper (D 6) (R 6) [10,144,288,68,96,2] 13 := by
  apply FastRouting.sound _ _ [10,144,288,68,96,2] 13 (by decide) (choices 1) [1,4] r16999 c16999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4446
  · exact u4447

def b17000 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 76 112 36 67 131 259), lower := (rows 11 146 292 76 112 36 64 128 256), losses := [] }

theorem u17000 : Upper (D 6) (R 6) [10,144,288,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17001 : Route 9 := (fun mask => (mask,id))

def c17001 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17001 : Upper (D 6) (R 6) [10,144,288,96,5,1] 13 := by
  apply FastRouting.sound _ _ [10,144,288,96,5,1] 13 (by decide) (choices 1) [2,4] r17001 c17001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4448
  · exact u4449

def r17002 : Route 9 := (fun mask => (mask,id))

def c17002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17002 : Upper (D 6) (R 6) [10,144,288,96,5,2] 13 := by
  apply FastRouting.sound _ _ [10,144,288,96,5,2] 13 (by decide) (choices 1) [1,4] r17002 c17002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4450
  · exact u4451

def b17003 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 104 21 36 67 195 323), lower := (rows 11 146 292 104 21 36 64 128 256), losses := [] }

theorem u17003 : Upper (D 6) (R 6) [10,144,288,96,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17004 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 292 104 21 96 71 135 263), lower := (rows 11 146 292 104 21 96 64 128 256), losses := [] }

theorem u17004 : Upper (D 6) (R 6) [10,144,288,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17005 : Route 9 := (fun mask => (mask,id))

def c17005 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17005 : Upper (D 6) (R 6) [10,144,288,96,6,1] 13 := by
  apply FastRouting.sound _ _ [10,144,288,96,6,1] 13 (by decide) (choices 1) [1,4] r17005 c17005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4452
  · exact u4453

def b17006 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 104 22 36 65 193 321), lower := (rows 11 146 292 104 22 36 64 128 256), losses := [] }

theorem u17006 : Upper (D 6) (R 6) [10,144,288,96,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17007 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 292 104 22 96 69 133 261), lower := (rows 11 146 292 104 22 96 64 128 256), losses := [] }

theorem u17007 : Upper (D 6) (R 6) [10,144,288,96,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17008 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 40, targets := 6 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(3,1),(3,2)], upper := (rows 11 146 292 104 81 33 70 134 262), lower := (rows 11 146 292 104 81 33 64 128 256), losses := [] }

theorem u17008 : Upper (D 6) (R 6) [10,144,288,96,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17009 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 11 146 292 104 81 34 69 133 261), lower := (rows 11 146 292 104 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 35 64 128 256), good := (rows 42 186 292 104 120 34 64 128 256) }] }

theorem u17009 : Upper (D 6) (R 6) [10,144,288,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17010 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 104 81 36 71 135 263), lower := (rows 11 146 292 104 81 36 64 128 256), losses := [] }

theorem u17010 : Upper (D 6) (R 6) [10,144,288,96,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17011 : Route 9 := (fun mask => (mask,id))

def c17011 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17011 : Upper (D 6) (R 6) [10,144,288,96,68,1] 13 := by
  apply FastRouting.sound _ _ [10,144,288,96,68,1] 13 (by decide) (choices 1) [1,2,4] r17011 c17011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4454
  · exact u4455
  · exact u4456

def r17012 : Route 9 := (fun mask => (mask,id))

def c17012 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17012 : Upper (D 6) (R 6) [10,144,288,96,68,2] 13 := by
  apply FastRouting.sound _ _ [10,144,288,96,68,2] 13 (by decide) (choices 1) [1,4] r17012 c17012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4457
  · exact u4458

def b17013 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 146 292 104 84 36 67 131 259), lower := (rows 11 146 292 104 84 36 64 128 256), losses := [] }

theorem u17013 : Upper (D 6) (R 6) [10,144,288,96,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17014 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 162 22 44 81 33 324 452 324), lower := (rows 11 162 22 44 81 33 64 128 256), losses := [] }

theorem u17014 : Upper (D 6) (R 6) [10,160,18,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17015 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 22 44 81 36 321 449 321), lower := (rows 11 162 22 44 81 36 64 128 256), losses := [] }

theorem u17015 : Upper (D 6) (R 6) [10,160,18,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17016 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 387, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 162 22 44 81 96 325 389 261), lower := (rows 11 162 22 44 81 96 64 128 256), losses := [] }

theorem u17016 : Upper (D 6) (R 6) [10,160,18,36,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17017 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 22 44 81 288 69 197 325), lower := (rows 11 162 22 44 81 288 64 128 256), losses := [] }

theorem u17017 : Upper (D 6) (R 6) [10,160,18,36,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17017 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17018 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 162 22 44 273 33 68 196 324), lower := (rows 11 162 22 44 273 33 64 128 256), losses := [] }

theorem u17018 : Upper (D 6) (R 6) [10,160,18,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17019 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 22 44 273 36 65 193 321), lower := (rows 11 162 22 44 273 36 64 128 256), losses := [] }

theorem u17019 : Upper (D 6) (R 6) [10,160,18,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17020 : Route 9 := (fun mask => (mask,id))

def c17020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17020 : Upper (D 6) (R 6) [10,160,18,36,257,64] 13 := by
  apply FastRouting.sound _ _ [10,160,18,36,257,64] 13 (by decide) (choices 1) [1,4] r17020 c17020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4459
  · exact u4460

def b17021 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 162 22 44 336 33 69 197 325), lower := (rows 11 162 22 44 336 33 64 128 256), losses := [] }

theorem u17021 : Upper (D 6) (R 6) [10,160,18,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17022 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 22 44 336 36 65 193 321), lower := (rows 11 162 22 44 336 36 64 128 256), losses := [] }

theorem u17022 : Upper (D 6) (R 6) [10,160,18,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17023 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 131, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 162 22 44 336 96 69 133 261), lower := (rows 11 162 22 44 336 96 64 128 256), losses := [] }

theorem u17023 : Upper (D 6) (R 6) [10,160,18,36,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17024 : PairBound 9 := { available := 260, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 22 73 112 33 324 388 260), lower := (rows 11 162 22 73 112 33 64 128 256), losses := [] }

theorem u17024 : Upper (D 6) (R 6) [10,160,18,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17025 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 329, targets := 32 }], pairs := [(0,5),(2,0),(3,5)], upper := (rows 11 162 22 73 112 36 325 389 261), lower := (rows 11 162 22 73 112 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 24 45 64 128 256), good := (rows 62 162 54 124 112 36 64 128 256) }] }

theorem u17025 : Upper (D 6) (R 6) [10,160,18,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17026 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 22 73 112 288 69 133 261), lower := (rows 11 162 22 73 112 288 64 128 256), losses := [] }

theorem u17026 : Upper (D 6) (R 6) [10,160,18,65,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17026 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17027 : Route 9 := (fun mask => (mask,id))

def c17027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17027 : Upper (D 6) (R 6) [10,160,18,65,257,4] 13 := by
  apply FastRouting.sound _ _ [10,160,18,65,257,4] 13 (by decide) (choices 1) [4,32] r17027 c17027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4461
  · exact u4462

def r17028 : Route 9 := (fun mask => (mask,id))

def c17028 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17028 : Upper (D 6) (R 6) [10,160,18,65,257,64] 13 := by
  apply FastRouting.sound _ _ [10,160,18,65,257,64] 13 (by decide) (choices 1) [4,32] r17028 c17028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4463
  · exact u4464

def b17029 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 22 73 276 33 100 228 356), lower := (rows 11 162 22 73 276 33 64 128 256), losses := [] }

theorem u17029 : Upper (D 6) (R 6) [10,160,18,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17030 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 22 73 276 36 97 225 353), lower := (rows 11 162 22 73 276 36 64 128 256), losses := [] }

theorem u17030 : Upper (D 6) (R 6) [10,160,18,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17031 : Route 9 := (fun mask => (mask,id))

def c17031 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17031 : Upper (D 6) (R 6) [10,160,18,65,260,64] 13 := by
  apply FastRouting.sound _ _ [10,160,18,65,260,64] 13 (by decide) (choices 1) [1,4,32] r17031 c17031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4465
  · exact u4466
  · exact u4467

def b17032 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 22 73 304 33 68 196 324), lower := (rows 11 162 22 73 304 33 64 128 256), losses := [] }

theorem u17032 : Upper (D 6) (R 6) [10,160,18,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17033 : Route 9 := (fun mask => (mask,id))

def c17033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17033 : Upper (D 6) (R 6) [10,160,18,65,288,4] 13 := by
  apply FastRouting.sound _ _ [10,160,18,65,288,4] 13 (by decide) (choices 1) [1,4] r17033 c17033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4468
  · exact u4469

def r17034 : Route 9 := (fun mask => (mask,id))

def c17034 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17034 : Upper (D 6) (R 6) [10,160,18,65,288,64] 13 := by
  apply FastRouting.sound _ _ [10,160,18,65,288,64] 13 (by decide) (choices 1) [1,4] r17034 c17034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4470
  · exact u4471

def b17035 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 22 73 336 33 100 164 292), lower := (rows 11 162 22 73 336 33 64 128 256), losses := [] }

theorem u17035 : Upper (D 6) (R 6) [10,160,18,65,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17036 : Route 9 := (fun mask => (mask,id))

def c17036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17036 : Upper (D 6) (R 6) [10,160,18,65,320,4] 13 := by
  apply FastRouting.sound _ _ [10,160,18,65,320,4] 13 (by decide) (choices 1) [1,4,32] r17036 c17036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4472
  · exact u4473
  · exact u4474

def r17037 : Route 9 := (fun mask => (mask,id))

def c17037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17037 : Upper (D 6) (R 6) [10,160,18,68,257,1] 13 := by
  apply FastRouting.sound _ _ [10,160,18,68,257,1] 13 (by decide) (choices 1) [4,32] r17037 c17037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4475
  · exact u4476

def r17038 : Route 9 := (fun mask => (mask,id))

def c17038 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17038 : Upper (D 6) (R 6) [10,160,18,68,257,4] 13 := by
  apply FastRouting.sound _ _ [10,160,18,68,257,4] 13 (by decide) (choices 1) [1,32] r17038 c17038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4477
  · exact u4478

def r17039 : Route 9 := (fun mask => (mask,id))

def c17039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17039 : Upper (D 6) (R 6) [10,160,18,68,257,64] 13 := by
  apply FastRouting.sound _ _ [10,160,18,68,257,64] 13 (by decide) (choices 1) [1,4,32] r17039 c17039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4479
  · exact u4480
  · exact u4481

#print axioms u17039
end Delivery.IrregularNine14.P06
