import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0041

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6000 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 400, targets := 1 },{ cop := 1, region := 353, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,0),(2,0),(4,0)], upper := (rows 97 14 22 137 400 33 352 480 352), lower := (rows 97 14 22 137 400 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 14 8 57 32 97 161 289), good := (rows 496 30 22 478 400 496 64 128 256) }] }

theorem u6000 : Upper (D 9) (R 9) [96,12,18,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6000 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6001 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 22 137 400 96 353 417 289), lower := (rows 97 14 22 137 400 96 64 128 256), losses := [] }

theorem u6001 : Upper (D 9) (R 9) [96,12,18,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6001 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6002_1 : Upper (D 9) (R 9) [96,12,18,129,384,256,1] 13 :=
  permutation_upper _ _ _ [96,12,18,129,384,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2461

theorem m6002_32 : Upper (D 9) (R 9) [96,12,18,129,384,256,32] 13 :=
  permutation_upper _ _ _ [96,12,18,129,384,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2462

def r6002 : Route 9 := (fun mask => (mask,id))

def c6002 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6002 : Upper (D 9) (R 9) [96,12,18,129,384,256] 13 := by
  apply FastRouting.sound _ _ [96,12,18,129,384,256] 13 (by decide) (choices 1) [1,32] r6002 c6002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m6002_1
  · exact m6002_32

def b6003 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,5)], upper := (rows 97 14 22 168 208 33 321 385 257), lower := (rows 97 14 22 168 208 33 64 128 256), losses := [] }

theorem u6003 : Upper (D 9) (R 9) [96,12,18,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6003 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6004_1 : Upper (D 9) (R 9) [96,12,18,160,192,256,1] 13 :=
  permutation_upper _ _ _ [96,12,18,160,192,1,256] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2463

def r6004 : Route 9 := (fun mask => (mask,id))

def c6004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6004 : Upper (D 9) (R 9) [96,12,18,160,192,256] 13 := by
  apply FastRouting.sound _ _ [96,12,18,160,192,256] 13 (by decide) (choices 1) [1,256] r6004 c6004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m6004_1
  · exact u2464

def b6005 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 392, targets := 64 }], pairs := [(0,7),(0,8),(1,5),(3,6),(4,5)], upper := (rows 97 14 22 168 336 33 449 385 385), lower := (rows 97 14 22 168 336 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 14 8 57 0 97 161 289), good := (rows 465 30 22 478 336 465 64 128 256) }] }

theorem u6005 : Upper (D 9) (R 9) [96,12,18,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6005 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6006 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 97 14 22 168 336 160 321 385 257), lower := (rows 97 14 22 168 336 160 64 128 256), losses := [] }

theorem u6006 : Upper (D 9) (R 9) [96,12,18,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6006 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6007 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 201, targets := 256 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 136, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(3,6),(3,8),(4,5)], upper := (rows 97 14 22 168 336 288 193 129 385), lower := (rows 97 14 22 168 336 288 64 128 256), losses := [] }

theorem u6007 : Upper (D 9) (R 9) [96,12,18,160,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6007 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6008 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 400, targets := 32 },{ cop := 1, region := 353, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,5),(2,5),(4,5)], upper := (rows 97 14 22 168 400 33 321 449 321), lower := (rows 97 14 22 168 400 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 14 8 57 0 97 161 289), good := (rows 465 30 22 478 400 465 64 128 256) }] }

theorem u6008 : Upper (D 9) (R 9) [96,12,18,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6008 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6009 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 0, region := 400, targets := 32 }], pairs := [(1,6),(2,6),(3,6),(4,5),(4,6)], upper := (rows 97 14 22 168 400 96 321 385 257), lower := (rows 97 14 22 168 400 96 64 128 256), losses := [] }

theorem u6009 : Upper (D 9) (R 9) [96,12,18,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6009 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6010 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 46, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6),(3,0)], upper := (rows 97 14 22 168 400 288 65 193 321), lower := (rows 97 14 22 168 400 288 64 128 256), losses := [] }

theorem u6010 : Upper (D 9) (R 9) [96,12,18,160,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6010 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6011 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 97 14 38 88 400 33 449 385 385), lower := (rows 97 14 38 88 400 33 64 128 256), losses := [] }

theorem u6011 : Upper (D 9) (R 9) [96,12,34,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6011 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6012 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 400, targets := 64 },{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7),(1,0),(3,5),(4,5),(4,6)], upper := (rows 97 14 38 88 400 160 321 385 257), lower := (rows 97 14 38 88 400 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 176 64 128 256), good := (rows 96 14 38 126 432 160 64 160 256) }] }

theorem u6012 : Upper (D 9) (R 9) [96,12,34,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6012 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6013 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 38, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 14 38 137 208 33 336 400 272), lower := (rows 97 14 38 137 208 33 64 128 256), losses := [] }

theorem u6013 : Upper (D 9) (R 9) [96,12,34,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6013 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6014 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 14 38 137 208 48 321 385 257), lower := (rows 97 14 38 137 208 48 64 128 256), losses := [] }

theorem u6014 : Upper (D 9) (R 9) [96,12,34,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6014 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6015 : Route 9 := (fun mask => (mask,id))

def c6015 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6015 : Upper (D 9) (R 9) [96,12,34,129,192,256] 13 := by
  apply FastRouting.sound _ _ [96,12,34,129,192,256] 13 (by decide) (choices 1) [1,16,256] r6015 c6015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2465
  · exact u2466
  · exact u2467

def r6016 : Route 9 := (fun mask => (mask,id))

def c6016 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u6016 : Upper (D 9) (R 9) [96,12,34,129,257,16] 13 := by
  apply FastRouting.sound _ _ [96,12,34,129,257,16] 13 (by decide) (choices 1) [128,256] r6016 c6016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2468
  · exact u2469

def b6017 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 14 38 137 273 96 464 400 400), lower := (rows 97 14 38 137 273 96 64 128 256), losses := [] }

theorem u6017 : Upper (D 9) (R 9) [96,12,34,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6017 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6018 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 38, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(2,0),(2,6)], upper := (rows 97 14 38 137 273 160 336 464 336), lower := (rows 97 14 38 137 273 160 64 128 256), losses := [] }

theorem u6018 : Upper (D 9) (R 9) [96,12,34,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6018 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6019 : Route 9 := (fun mask => (mask,id))

def c6019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6019 : Upper (D 9) (R 9) [96,12,34,129,257,256] 13 := by
  apply FastRouting.sound _ _ [96,12,34,129,257,256] 13 (by decide) (choices 1) [16,128] r6019 c6019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2470
  · exact u2471

def b6020 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 38, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 14 38 137 336 33 464 400 400), lower := (rows 97 14 38 137 336 33 64 128 256), losses := [] }

theorem u6020 : Upper (D 9) (R 9) [96,12,34,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6020 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6021 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 0, region := 392, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6)], upper := (rows 97 14 38 137 336 48 449 385 385), lower := (rows 97 14 38 137 336 48 64 128 256), losses := [] }

theorem u6021 : Upper (D 9) (R 9) [96,12,34,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6021 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6022 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 38, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(2,0),(2,6)], upper := (rows 97 14 38 137 336 160 337 401 273), lower := (rows 97 14 38 137 336 160 64 128 256), losses := [] }

theorem u6022 : Upper (D 9) (R 9) [96,12,34,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6022 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6023 : Route 9 := (fun mask => (mask,id))

def c6023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6023 : Upper (D 9) (R 9) [96,12,34,129,320,256] 13 := by
  apply FastRouting.sound _ _ [96,12,34,129,320,256] 13 (by decide) (choices 1) [1,16,128] r6023 c6023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2472
  · exact u2473
  · exact u2474

def b6024 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 38, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 14 38 137 400 33 336 464 336), lower := (rows 97 14 38 137 400 33 64 128 256), losses := [] }

theorem u6024 : Upper (D 9) (R 9) [96,12,34,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6024 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6025 : Route 9 := (fun mask => (mask,id))

def c6025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6025 : Upper (D 9) (R 9) [96,12,34,129,384,16] 13 := by
  apply FastRouting.sound _ _ [96,12,34,129,384,16] 13 (by decide) (choices 1) [1,256] r6025 c6025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2475
  · exact u2476

def b6026 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 14 38 137 400 96 337 401 273), lower := (rows 97 14 38 137 400 96 64 128 256), losses := [] }

theorem u6026 : Upper (D 9) (R 9) [96,12,34,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6026 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6027 : Route 9 := (fun mask => (mask,id))

def c6027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6027 : Upper (D 9) (R 9) [96,12,34,129,384,256] 13 := by
  apply FastRouting.sound _ _ [96,12,34,129,384,256] 13 (by decide) (choices 1) [1,16] r6027 c6027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2477
  · exact u2478

def b6028 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 6, region := 33, targets := 384 },{ cop := 4, region := 200, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,5),(4,5)], upper := (rows 97 14 38 152 273 33 448 448 448), lower := (rows 97 14 38 152 273 33 64 128 256), losses := [] }

theorem u6028 : Upper (D 9) (R 9) [96,12,34,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6028 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6029 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 14 38 152 273 96 449 385 385), lower := (rows 97 14 38 152 273 96 64 128 256), losses := [] }

theorem u6029 : Upper (D 9) (R 9) [96,12,34,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6029 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6030 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 38, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(2,0),(2,6)], upper := (rows 97 14 38 152 273 160 321 449 321), lower := (rows 97 14 38 152 273 160 64 128 256), losses := [] }

theorem u6030 : Upper (D 9) (R 9) [96,12,34,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6030 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6031 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 2, region := 193, targets := 256 },{ cop := 4, region := 200, targets := 256 }], pairs := [(0,8),(1,0),(3,5),(3,8),(4,5)], upper := (rows 97 14 38 152 273 288 193 193 449), lower := (rows 97 14 38 152 273 288 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 304 64 128 256), good := (rows 96 14 38 190 304 288 64 128 288) }] }

theorem u6031 : Upper (D 9) (R 9) [96,12,34,144,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6031 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6032 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 4, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(1,5),(3,5),(4,5)], upper := (rows 97 14 38 152 336 33 449 385 385), lower := (rows 97 14 38 152 336 33 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 45 53 0 97 161 289), good := (rows 473 30 478 152 336 473 64 128 256) }] }

theorem u6032 : Upper (D 9) (R 9) [96,12,34,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6032 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6033 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 38, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(2,0),(2,6)], upper := (rows 97 14 38 152 336 160 321 385 257), lower := (rows 97 14 38 152 336 160 64 128 256), losses := [] }

theorem u6033 : Upper (D 9) (R 9) [96,12,34,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6033 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6034 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 2, region := 193, targets := 256 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(1,0),(3,5),(4,5)], upper := (rows 97 14 38 152 336 288 193 129 385), lower := (rows 97 14 38 152 336 288 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 304 64 128 256), good := (rows 96 14 38 190 368 288 64 128 288) }] }

theorem u6034 : Upper (D 9) (R 9) [96,12,34,144,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6034 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6035 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 55, targets := 256 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 14 38 200 145 33 336 400 272), lower := (rows 97 14 38 200 145 33 64 128 256), losses := [] }

theorem u6035 : Upper (D 9) (R 9) [96,12,34,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6035 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6036 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 97 14 38 200 145 48 321 385 257), lower := (rows 97 14 38 200 145 48 64 128 256), losses := [] }

theorem u6036 : Upper (D 9) (R 9) [96,12,34,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6036 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6037 : Route 9 := (fun mask => (mask,id))

def c6037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6037 : Upper (D 9) (R 9) [96,12,34,192,129,256] 13 := by
  apply FastRouting.sound _ _ [96,12,34,192,129,256] 13 (by decide) (choices 1) [1,16,256] r6037 c6037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2479
  · exact u2480
  · exact u2481

def b6038 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 97 14 38 200 273 33 464 400 400), lower := (rows 97 14 38 200 273 33 64 128 256), losses := [] }

theorem u6038 : Upper (D 9) (R 9) [96,12,34,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6038 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6039 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,5),(3,5),(4,5),(4,6)], upper := (rows 97 14 38 200 273 48 449 385 385), lower := (rows 97 14 38 200 273 48 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 57 17 0 81 145 273), good := (rows 473 14 14 200 473 472 64 128 256) }] }

theorem u6039 : Upper (D 9) (R 9) [96,12,34,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6039 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6040 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 38, targets := 65 },{ cop := 3, region := 33, targets := 256 }], pairs := [(0,8),(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 14 38 200 273 160 337 401 273), lower := (rows 97 14 38 200 273 160 64 128 256), losses := [] }

theorem u6040 : Upper (D 9) (R 9) [96,12,34,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6040 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6041 : Route 9 := (fun mask => (mask,id))

def c6041 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6041 : Upper (D 9) (R 9) [96,12,34,192,257,256] 13 := by
  apply FastRouting.sound _ _ [96,12,34,192,257,256] 13 (by decide) (choices 1) [1,16,128] r6041 c6041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2482
  · exact u2483
  · exact u2484

def b6042 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 97 14 38 200 400 33 337 401 273), lower := (rows 97 14 38 200 400 33 64 128 256), losses := [] }

theorem u6042 : Upper (D 9) (R 9) [96,12,34,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6042 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6043 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 400, targets := 64 },{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7),(3,5),(4,5),(4,6)], upper := (rows 97 14 38 200 400 48 321 385 257), lower := (rows 97 14 38 200 400 48 64 128 256), losses := [] }

theorem u6043 : Upper (D 9) (R 9) [96,12,34,192,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6043 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6044 : Route 9 := (fun mask => (mask,id))

def c6044 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6044 : Upper (D 9) (R 9) [96,12,34,192,384,256] 13 := by
  apply FastRouting.sound _ _ [96,12,34,192,384,256] 13 (by decide) (choices 1) [1,16] r6044 c6044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2485
  · exact u2486

def b6045 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 6, region := 33, targets := 384 },{ cop := 4, region := 328, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,5),(4,5)], upper := (rows 97 14 38 392 145 33 336 464 336), lower := (rows 97 14 38 392 145 33 64 128 256), losses := [] }

theorem u6045 : Upper (D 9) (R 9) [96,12,34,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6045 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6046 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7),(1,5),(3,5),(4,5)], upper := (rows 97 14 38 392 145 48 321 449 321), lower := (rows 97 14 38 392 145 48 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 57 17 0 81 145 273), good := (rows 473 14 14 392 473 472 64 128 256) }] }

theorem u6046 : Upper (D 9) (R 9) [96,12,34,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6046 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6047 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 14 38 392 145 96 337 401 273), lower := (rows 97 14 38 392 145 96 64 128 256), losses := [] }

theorem u6047 : Upper (D 9) (R 9) [96,12,34,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6047 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6048 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 38, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(2,0),(2,6)], upper := (rows 97 14 38 392 145 288 81 209 337), lower := (rows 97 14 38 392 145 288 64 128 256), losses := [] }

theorem u6048 : Upper (D 9) (R 9) [96,12,34,384,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6048 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6049 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 6, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(1,5),(3,5),(4,5)], upper := (rows 97 14 38 392 208 33 337 401 273), lower := (rows 97 14 38 392 208 33 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 45 53 0 97 161 289), good := (rows 473 30 478 392 208 473 64 128 256) }] }

theorem u6049 : Upper (D 9) (R 9) [96,12,34,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6049 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6050 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 0, region := 392, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6)], upper := (rows 97 14 38 392 208 48 321 385 257), lower := (rows 97 14 38 392 208 48 64 128 256), losses := [] }

theorem u6050 : Upper (D 9) (R 9) [96,12,34,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6050 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6051 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 38, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(2,0),(2,6)], upper := (rows 97 14 38 392 208 288 81 145 273), lower := (rows 97 14 38 392 208 288 64 128 256), losses := [] }

theorem u6051 : Upper (D 9) (R 9) [96,12,34,384,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6051 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6052 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 37, targets := 384 },{ cop := 1, region := 464, targets := 1 }], pairs := [(0,7),(0,8),(2,7),(2,8),(4,0)], upper := (rows 97 14 52 137 82 33 448 384 384), lower := (rows 97 14 52 137 82 33 64 128 256), losses := [] }

theorem u6052 : Upper (D 9) (R 9) [96,12,48,129,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6052 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6053 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 392, targets := 32 },{ cop := 0, region := 392, targets := 64 },{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7),(2,6),(3,5),(3,6),(4,5)], upper := (rows 97 14 52 137 82 160 321 385 257), lower := (rows 97 14 52 137 82 160 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 18 0 73 137 265), good := (rows 457 478 20 457 82 128 64 128 256) },{ target := 6, region := (rows 1 2 20 9 16 171 0 137 265), good := (rows 425 430 52 425 54 160 0 160 256) }] }

theorem u6053 : Upper (D 9) (R 9) [96,12,48,129,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6053 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6054 : Route 9 := (fun mask => (mask,id))

def c6054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u6054 : Upper (D 9) (R 9) [96,12,48,129,66,256] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,66,256] 13 (by decide) (choices 1) [1,128,256] r6054 c6054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2487
  · exact u2488
  · exact u2489

def b6055 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 54, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8),(4,6)], upper := (rows 97 14 52 137 146 33 320 448 320), lower := (rows 97 14 52 137 146 33 64 128 256), losses := [] }

theorem u6055 : Upper (D 9) (R 9) [96,12,48,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6055 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6056 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 52 137 146 96 321 385 257), lower := (rows 97 14 52 137 146 96 64 128 256), losses := [] }

theorem u6056 : Upper (D 9) (R 9) [96,12,48,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6056 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6057 : Route 9 := (fun mask => (mask,id))

def c6057 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6057 : Upper (D 9) (R 9) [96,12,48,129,130,256] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,130,256] 13 (by decide) (choices 1) [1,256] r6057 c6057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2490
  · exact u2491

def b6058 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 1, region := 464, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 14 52 137 208 33 322 386 258), lower := (rows 97 14 52 137 208 33 64 128 256), losses := [] }

theorem u6058 : Upper (D 9) (R 9) [96,12,48,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6058 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6059 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 14 52 137 208 34 321 385 257), lower := (rows 97 14 52 137 208 34 64 128 256), losses := [] }

theorem u6059 : Upper (D 9) (R 9) [96,12,48,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6059 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u6059
end Delivery.IrregularNine14.P09
