import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0012
import IrregularNine14P06C0013

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m9000_2 : Upper (D 6) (R 6) [6,9,129,272,96,4,2] 13 :=
  permutation_upper _ _ _ [6,9,129,272,96,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u758

def r9000 : Route 9 := (fun mask => (mask,id))

def c9000 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9000 : Upper (D 6) (R 6) [6,9,129,272,96,4] 13 := by
  apply FastRouting.sound _ _ [6,9,129,272,96,4] 13 (by decide) (choices 1) [2,32] r9000 c9000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m9000_2
  · exact u760

def b9001 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 133 280 112 96 102 166 294), lower := (rows 7 11 133 280 112 96 64 128 256), losses := [] }

theorem u9001 : Upper (D 6) (R 6) [6,9,129,272,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9002 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 328, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 133 296 52 34 80 208 336), lower := (rows 7 11 133 296 52 34 64 128 256), losses := [] }

theorem u9002 : Upper (D 6) (R 6) [6,9,129,288,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9003 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 11 133 296 52 48 66 194 322), lower := (rows 7 11 133 296 52 48 64 128 256), losses := [] }

theorem u9003 : Upper (D 6) (R 6) [6,9,129,288,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9003 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9004 : Route 9 := (fun mask => (mask,id))

def c9004 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9004 : Upper (D 6) (R 6) [6,9,129,288,36,64] 13 := by
  apply FastRouting.sound _ _ [6,9,129,288,36,64] 13 (by decide) (choices 1) [2,16] r9004 c9004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u761
  · exact u762

def r9005 : Route 9 := (fun mask => (mask,id))

def c9005 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9005 : Upper (D 6) (R 6) [6,9,129,288,66,4] 13 := by
  apply FastRouting.sound _ _ [6,9,129,288,66,4] 13 (by decide) (choices 1) [16,32] r9005 c9005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u763
  · exact u764

def b9006 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 133 296 82 48 100 228 356), lower := (rows 7 11 133 296 82 48 64 128 256), losses := [] }

theorem u9006 : Upper (D 6) (R 6) [6,9,129,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9006 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9007 : Route 9 := (fun mask => (mask,id))

def c9007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9007 : Upper (D 6) (R 6) [6,9,129,288,66,64] 13 := by
  apply FastRouting.sound _ _ [6,9,129,288,66,64] 13 (by decide) (choices 1) [4,16,32] r9007 c9007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u765
  · exact u766
  · exact u767

def b9008 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 133 296 84 34 112 240 368), lower := (rows 7 11 133 296 84 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 6 40 50 32 104 168 296), good := (rows 21 477 133 504 84 508 64 128 256) }] }

theorem u9008 : Upper (D 6) (R 6) [6,9,129,288,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9009 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 133 296 84 48 98 226 354), lower := (rows 7 11 133 296 84 48 64 128 256), losses := [] }

theorem u9009 : Upper (D 6) (R 6) [6,9,129,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9009 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9010 : Route 9 := (fun mask => (mask,id))

def c9010 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9010 : Upper (D 6) (R 6) [6,9,129,288,68,64] 13 := by
  apply FastRouting.sound _ _ [6,9,129,288,68,64] 13 (by decide) (choices 1) [2,16,32] r9010 c9010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u768
  · exact u769
  · exact u770

def b9011 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 133 296 112 34 84 212 340), lower := (rows 7 11 133 296 112 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 56 56 32 98 162 290), good := (rows 453 477 133 504 504 508 64 128 256) }] }

theorem u9011 : Upper (D 6) (R 6) [6,9,129,288,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9012 : Route 9 := (fun mask => (mask,id))

def c9012 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9012 : Upper (D 6) (R 6) [6,9,129,288,96,4] 13 := by
  apply FastRouting.sound _ _ [6,9,129,288,96,4] 13 (by decide) (choices 1) [2,16] r9012 c9012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u771
  · exact u772

def b9013 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 199, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 133 296 112 48 70 198 326), lower := (rows 7 11 133 296 112 48 64 128 256), losses := [] }

theorem u9013 : Upper (D 6) (R 6) [6,9,129,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9013 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9014 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 133 296 112 96 86 150 278), lower := (rows 7 11 133 296 112 96 64 128 256), losses := [] }

theorem u9014 : Upper (D 6) (R 6) [6,9,129,288,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9015 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 42, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 11 148 42 112 33 324 452 324), lower := (rows 7 11 148 42 112 33 64 128 256), losses := [] }

theorem u9015 : Upper (D 6) (R 6) [6,9,144,34,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9016 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 148 42 112 36 321 449 321), lower := (rows 7 11 148 42 112 36 64 128 256), losses := [] }

theorem u9016 : Upper (D 6) (R 6) [6,9,144,34,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9017 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 148 42 112 96 325 389 261), lower := (rows 7 11 148 42 112 96 64 128 256), losses := [] }

theorem u9017 : Upper (D 6) (R 6) [6,9,144,34,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9018 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 11 148 42 112 288 69 197 325), lower := (rows 7 11 148 42 112 288 64 128 256), losses := [] }

theorem u9018 : Upper (D 6) (R 6) [6,9,144,34,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9018 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9019 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 42, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 11 148 42 304 33 68 196 324), lower := (rows 7 11 148 42 304 33 64 128 256), losses := [] }

theorem u9019 : Upper (D 6) (R 6) [6,9,144,34,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9020 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 148 42 304 36 65 193 321), lower := (rows 7 11 148 42 304 36 64 128 256), losses := [] }

theorem u9020 : Upper (D 6) (R 6) [6,9,144,34,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9021 : Route 9 := (fun mask => (mask,id))

def c9021 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9021 : Upper (D 6) (R 6) [6,9,144,34,288,64] 13 := by
  apply FastRouting.sound _ _ [6,9,144,34,288,64] 13 (by decide) (choices 1) [1,4] r9021 c9021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u773
  · exact u774

def b9022 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 42, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 11 148 42 336 33 100 228 356), lower := (rows 7 11 148 42 336 33 64 128 256), losses := [] }

theorem u9022 : Upper (D 6) (R 6) [6,9,144,34,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9023 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 148 42 336 36 97 225 353), lower := (rows 7 11 148 42 336 36 64 128 256), losses := [] }

theorem u9023 : Upper (D 6) (R 6) [6,9,144,34,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9024 : Route 9 := (fun mask => (mask,id))

def c9024 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9024 : Upper (D 6) (R 6) [6,9,144,34,320,64] 13 := by
  apply FastRouting.sound _ _ [6,9,144,34,320,64] 13 (by decide) (choices 1) [1,4,32] r9024 c9024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u775
  · exact u776
  · exact u777

def b9025 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 48, targets := 66 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 11 148 104 52 33 322 450 322), lower := (rows 7 11 148 104 52 33 64 128 256), losses := [] }

theorem u9025 : Upper (D 6) (R 6) [6,9,144,96,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9026 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 48, targets := 1 }], pairs := [(1,2),(3,2),(4,0)], upper := (rows 7 11 148 104 52 34 321 449 321), lower := (rows 7 11 148 104 52 34 64 128 256), losses := [] }

theorem u9026 : Upper (D 6) (R 6) [6,9,144,96,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9027 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 148 104 52 96 323 387 259), lower := (rows 7 11 148 104 52 96 64 128 256), losses := [] }

theorem u9027 : Upper (D 6) (R 6) [6,9,144,96,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9028 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 148 104 52 288 67 195 323), lower := (rows 7 11 148 104 52 288 64 128 256), losses := [] }

theorem u9028 : Upper (D 6) (R 6) [6,9,144,96,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9028 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9029 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 104, targets := 1 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 148 104 273 34 100 228 356), lower := (rows 7 11 148 104 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 35 81 145 273), good := (rows 494 490 476 104 508 42 64 128 256) },{ target := 1, region := (rows 1 0 38 40 18 32 104 168 296), good := (rows 21 477 148 492 273 508 64 128 256) }] }

theorem u9029 : Upper (D 6) (R 6) [6,9,144,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m9030_2 : Upper (D 6) (R 6) [6,9,144,96,257,4,2] 13 :=
  permutation_upper _ _ _ [6,9,144,96,257,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u778

def r9030 : Route 9 := (fun mask => (mask,id))

def c9030 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9030 : Upper (D 6) (R 6) [6,9,144,96,257,4] 13 := by
  apply FastRouting.sound _ _ [6,9,144,96,257,4] 13 (by decide) (choices 1) [2,32] r9030 c9030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m9030_2
  · exact u779

def b9031 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 148 104 273 96 102 166 294), lower := (rows 7 11 148 104 273 96 64 128 256), losses := [] }

theorem u9031 : Upper (D 6) (R 6) [6,9,144,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9032 : Route 9 := (fun mask => (mask,id))

def c9032 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9032 : Upper (D 6) (R 6) [6,9,144,96,258,1] 13 := by
  apply FastRouting.sound _ _ [6,9,144,96,258,1] 13 (by decide) (choices 1) [4,32] r9032 c9032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u780
  · exact u781

theorem m9033_1 : Upper (D 6) (R 6) [6,9,144,96,258,4,1] 13 :=
  permutation_upper _ _ _ [6,9,144,96,258,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u780

def r9033 : Route 9 := (fun mask => (mask,id))

def c9033 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9033 : Upper (D 6) (R 6) [6,9,144,96,258,4] 13 := by
  apply FastRouting.sound _ _ [6,9,144,96,258,4] 13 (by decide) (choices 1) [1,32] r9033 c9033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m9033_1
  · exact u782

def b9034 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 148 104 274 96 101 165 293), lower := (rows 7 11 148 104 274 96 64 128 256), losses := [] }

theorem u9034 : Upper (D 6) (R 6) [6,9,144,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9035 : Route 9 := (fun mask => (mask,id))

def c9035 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9035 : Upper (D 6) (R 6) [6,9,144,96,260,1] 13 := by
  apply FastRouting.sound _ _ [6,9,144,96,260,1] 13 (by decide) (choices 1) [2,32] r9035 c9035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u783
  · exact u784

theorem m9036_1 : Upper (D 6) (R 6) [6,9,144,96,260,2,1] 13 :=
  permutation_upper _ _ _ [6,9,144,96,260,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u783

def r9036 : Route 9 := (fun mask => (mask,id))

def c9036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9036 : Upper (D 6) (R 6) [6,9,144,96,260,2] 13 := by
  apply FastRouting.sound _ _ [6,9,144,96,260,2] 13 (by decide) (choices 1) [1,32] r9036 c9036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m9036_1
  · exact u785

def b9037 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 148 104 276 96 99 163 291), lower := (rows 7 11 148 104 276 96 64 128 256), losses := [] }

theorem u9037 : Upper (D 6) (R 6) [6,9,144,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9038 : PairBound 9 := { available := 70, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 11 148 104 304 33 70 198 326), lower := (rows 7 11 148 104 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 48 32 65 129 257), good := (rows 454 458 148 124 316 508 64 128 256) }] }

theorem u9038 : Upper (D 6) (R 6) [6,9,144,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9039 : Route 9 := (fun mask => (mask,id))

def c9039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9039 : Upper (D 6) (R 6) [6,9,144,96,288,2] 13 := by
  apply FastRouting.sound _ _ [6,9,144,96,288,2] 13 (by decide) (choices 1) [1,4] r9039 c9039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u786
  · exact u787

def r9040 : Route 9 := (fun mask => (mask,id))

def c9040 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9040 : Upper (D 6) (R 6) [6,9,144,96,288,4] 13 := by
  apply FastRouting.sound _ _ [6,9,144,96,288,4] 13 (by decide) (choices 1) [1,2] r9040 c9040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u788
  · exact u789

def b9041 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 148 104 304 96 71 135 263), lower := (rows 7 11 148 104 304 96 64 128 256), losses := [] }

theorem u9041 : Upper (D 6) (R 6) [6,9,144,96,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9042 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 212, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 148 266 112 33 100 228 356), lower := (rows 7 11 148 266 112 33 64 128 256), losses := [] }

theorem u9042 : Upper (D 6) (R 6) [6,9,144,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m9043_1 : Upper (D 6) (R 6) [6,9,144,258,96,4,1] 13 :=
  permutation_upper _ _ _ [6,9,144,258,96,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u790

def r9043 : Route 9 := (fun mask => (mask,id))

def c9043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9043 : Upper (D 6) (R 6) [6,9,144,258,96,4] 13 := by
  apply FastRouting.sound _ _ [6,9,144,258,96,4] 13 (by decide) (choices 1) [1,32] r9043 c9043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m9043_1
  · exact u791

def b9044 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 148 266 112 96 101 165 293), lower := (rows 7 11 148 266 112 96 64 128 256), losses := [] }

theorem u9044 : Upper (D 6) (R 6) [6,9,144,258,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9045 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 48, targets := 66 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 11 148 296 52 33 66 194 322), lower := (rows 7 11 148 296 52 33 64 128 256), losses := [] }

theorem u9045 : Upper (D 6) (R 6) [6,9,144,288,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9046 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 48, targets := 1 }], pairs := [(1,2),(3,2),(4,0)], upper := (rows 7 11 148 296 52 34 65 193 321), lower := (rows 7 11 148 296 52 34 64 128 256), losses := [] }

theorem u9046 : Upper (D 6) (R 6) [6,9,144,288,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9047 : Route 9 := (fun mask => (mask,id))

def c9047 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9047 : Upper (D 6) (R 6) [6,9,144,288,36,64] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,36,64] 13 (by decide) (choices 1) [1,2] r9047 c9047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u792
  · exact u793

def b9048 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 360, targets := 1 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 148 296 81 34 100 228 356), lower := (rows 7 11 148 296 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 27 16 35 81 145 273), good := (rows 494 490 476 296 508 42 64 128 256) },{ target := 1, region := (rows 1 0 38 40 18 32 104 168 296), good := (rows 21 477 148 492 81 508 64 128 256) }] }

theorem u9048 : Upper (D 6) (R 6) [6,9,144,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9049 : Route 9 := (fun mask => (mask,id))

def c9049 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9049 : Upper (D 6) (R 6) [6,9,144,288,65,4] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,65,4] 13 (by decide) (choices 1) [2,32] r9049 c9049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u794
  · exact u795

def r9050 : Route 9 := (fun mask => (mask,id))

def c9050 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9050 : Upper (D 6) (R 6) [6,9,144,288,65,64] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,65,64] 13 (by decide) (choices 1) [2,4,32] r9050 c9050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u796
  · exact u797
  · exact u798

def r9051 : Route 9 := (fun mask => (mask,id))

def c9051 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9051 : Upper (D 6) (R 6) [6,9,144,288,66,1] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,66,1] 13 (by decide) (choices 1) [4,32] r9051 c9051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u799
  · exact u800

def r9052 : Route 9 := (fun mask => (mask,id))

def c9052 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9052 : Upper (D 6) (R 6) [6,9,144,288,66,4] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,66,4] 13 (by decide) (choices 1) [1,32] r9052 c9052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u801
  · exact u802

def r9053 : Route 9 := (fun mask => (mask,id))

def c9053 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9053 : Upper (D 6) (R 6) [6,9,144,288,66,64] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,66,64] 13 (by decide) (choices 1) [1,4,32] r9053 c9053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u803
  · exact u804
  · exact u805

def r9054 : Route 9 := (fun mask => (mask,id))

def c9054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9054 : Upper (D 6) (R 6) [6,9,144,288,68,1] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,68,1] 13 (by decide) (choices 1) [2,32] r9054 c9054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u806
  · exact u807

def r9055 : Route 9 := (fun mask => (mask,id))

def c9055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9055 : Upper (D 6) (R 6) [6,9,144,288,68,2] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,68,2] 13 (by decide) (choices 1) [1,32] r9055 c9055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u808
  · exact u809

def r9056 : Route 9 := (fun mask => (mask,id))

def c9056 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9056 : Upper (D 6) (R 6) [6,9,144,288,68,64] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,68,64] 13 (by decide) (choices 1) [1,2,32] r9056 c9056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u810
  · exact u811
  · exact u812

def b9057 : PairBound 9 := { available := 70, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 11 148 296 112 33 70 198 326), lower := (rows 7 11 148 296 112 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 48 32 65 129 257), good := (rows 454 458 148 316 124 508 64 128 256) }] }

theorem u9057 : Upper (D 6) (R 6) [6,9,144,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9058 : Route 9 := (fun mask => (mask,id))

def c9058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9058 : Upper (D 6) (R 6) [6,9,144,288,96,2] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,96,2] 13 (by decide) (choices 1) [1,4] r9058 c9058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u813
  · exact u814

def r9059 : Route 9 := (fun mask => (mask,id))

def c9059 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9059 : Upper (D 6) (R 6) [6,9,144,288,96,4] 13 := by
  apply FastRouting.sound _ _ [6,9,144,288,96,4] 13 (by decide) (choices 1) [1,2] r9059 c9059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u815
  · exact u816

#print axioms u9059
end Delivery.IrregularNine14.P06
