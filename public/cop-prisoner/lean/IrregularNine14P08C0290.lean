import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0107

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r17400 : Route 9 := (fun mask => (mask,id))

def c17400 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17400 : Upper (D 8) (R 8) [288,5,192,65,160] 13 := by
  apply FastRouting.sound _ _ [288,5,192,65,160] 13 (by decide) (choices 1) [2,8,16] r17400 c17400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6423
  · exact u6424
  · exact u6425

def b17401 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 74 152 49 113 177 305), lower := (rows 289 7 196 74 152 32 64 128 256), losses := [] }

theorem u17401 : Upper (D 8) (R 8) [288,5,192,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17401 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17402 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 74 176 57 121 185 313), lower := (rows 289 7 196 74 176 32 64 128 256), losses := [] }

theorem u17402 : Upper (D 8) (R 8) [288,5,192,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17402 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17403 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 196 88 152 35 99 163 291), lower := (rows 289 7 196 88 152 32 64 128 256), losses := [] }

theorem u17403 : Upper (D 8) (R 8) [288,5,192,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17403 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17404 : Route 9 := (fun mask => (mask,id))

def c17404 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17404 : Upper (D 8) (R 8) [288,5,192,80,160] 13 := by
  apply FastRouting.sound _ _ [288,5,192,80,160] 13 (by decide) (choices 1) [1,2,8] r17404 c17404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6426
  · exact u6427
  · exact u6428

theorem m17405_16 : Upper (D 8) (R 8) [288,5,192,96,160,16] 13 :=
  permutation_upper _ _ _ [288,5,192,96,160,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6431

def r17405 : Route 9 := (fun mask => (mask,id))

def c17405 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17405 : Upper (D 8) (R 8) [288,5,192,96,160] 13 := by
  apply FastRouting.sound _ _ [288,5,192,96,160] 13 (by decide) (choices 1) [1,2,8,16] r17405 c17405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6429
  · exact u6430
  · exact u6431
  · exact m17405_16

def b17406 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 14 22 41 81 224 224 224 480), lower := (rows 289 14 22 41 81 32 64 128 256), losses := [] }

theorem u17406 : Upper (D 8) (R 8) [288,12,18,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17406 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17407 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 14 22 41 112 225 193 193 449), lower := (rows 289 14 22 41 112 32 64 128 256), losses := [] }

theorem u17407 : Upper (D 8) (R 8) [288,12,18,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17407 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17408 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 289 14 22 41 208 225 225 225 481), lower := (rows 289 14 22 41 208 32 64 128 256), losses := [] }

theorem u17408 : Upper (D 8) (R 8) [288,12,18,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17408 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17409 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 22 73 81 160 224 160 416), lower := (rows 289 14 22 73 81 32 64 128 256), losses := [] }

theorem u17409 : Upper (D 8) (R 8) [288,12,18,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17409 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17410 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 22 73 112 161 225 161 417), lower := (rows 289 14 22 73 112 32 64 128 256), losses := [] }

theorem u17410 : Upper (D 8) (R 8) [288,12,18,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17410 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m17411_128 : Upper (D 8) (R 8) [288,12,18,65,129,128] 13 :=
  permutation_upper _ _ _ [288,12,18,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6432

def r17411 : Route 9 := (fun mask => (mask,id))

def c17411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17411 : Upper (D 8) (R 8) [288,12,18,65,129] 13 := by
  apply FastRouting.sound _ _ [288,12,18,65,129] 13 (by decide) (choices 1) [64,128] r17411 c17411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6432
  · exact m17411_128

def r17412 : Route 9 := (fun mask => (mask,id))

def c17412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17412 : Upper (D 8) (R 8) [288,12,18,65,160] 13 := by
  apply FastRouting.sound _ _ [288,12,18,65,160] 13 (by decide) (choices 1) [1,64,128] r17412 c17412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6433
  · exact u6434
  · exact u6435

def b17413 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 22 73 208 161 225 161 417), lower := (rows 289 14 22 73 208 32 64 128 256), losses := [] }

theorem u17413 : Upper (D 8) (R 8) [288,12,18,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17413 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17414 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 22 104 112 161 193 129 385), lower := (rows 289 14 22 104 112 32 64 128 256), losses := [] }

theorem u17414 : Upper (D 8) (R 8) [288,12,18,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17414 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m17415_128 : Upper (D 8) (R 8) [288,12,18,96,160,128] 13 :=
  permutation_upper _ _ _ [288,12,18,96,160,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6437

def r17415 : Route 9 := (fun mask => (mask,id))

def c17415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17415 : Upper (D 8) (R 8) [288,12,18,96,160] 13 := by
  apply FastRouting.sound _ _ [288,12,18,96,160] 13 (by decide) (choices 1) [1,64,128] r17415 c17415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6436
  · exact u6437
  · exact m17415_128

def b17416 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 22 104 208 161 225 161 417), lower := (rows 289 14 22 104 208 32 64 128 256), losses := [] }

theorem u17416 : Upper (D 8) (R 8) [288,12,18,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17416 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17417 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 22 200 208 33 97 161 289), lower := (rows 289 14 22 200 208 32 64 128 256), losses := [] }

theorem u17417 : Upper (D 8) (R 8) [288,12,18,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17417 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17418 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 14 37 42 81 240 208 208 464), lower := (rows 289 14 37 42 81 32 64 128 256), losses := [] }

theorem u17418 : Upper (D 8) (R 8) [288,12,33,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17418 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17419 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 14 37 42 208 241 209 209 465), lower := (rows 289 14 37 42 208 32 64 128 256), losses := [] }

theorem u17419 : Upper (D 8) (R 8) [288,12,33,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17419 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17420 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 56 81 226 194 194 450), lower := (rows 289 14 37 56 81 32 64 128 256), losses := [] }

theorem u17420 : Upper (D 8) (R 8) [288,12,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17420 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17421 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 56 82 225 193 193 449), lower := (rows 289 14 37 56 82 32 64 128 256), losses := [] }

theorem u17421 : Upper (D 8) (R 8) [288,12,33,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17421 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17422 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 56 208 227 195 195 451), lower := (rows 289 14 37 56 208 32 64 128 256), losses := [] }

theorem u17422 : Upper (D 8) (R 8) [288,12,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17423 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 73 50 240 208 208 464), lower := (rows 289 14 37 73 50 32 64 128 256), losses := [] }

theorem u17423 : Upper (D 8) (R 8) [288,12,33,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17423 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17424 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 73 112 178 210 146 402), lower := (rows 289 14 37 73 112 32 64 128 256), losses := [] }

theorem u17424 : Upper (D 8) (R 8) [288,12,33,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17425 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 73 146 240 240 240 496), lower := (rows 289 14 37 73 146 32 64 128 256), losses := [] }

theorem u17425 : Upper (D 8) (R 8) [288,12,33,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17425 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17426 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 73 176 242 210 210 466), lower := (rows 289 14 37 73 176 32 64 128 256), losses := [] }

theorem u17426 : Upper (D 8) (R 8) [288,12,33,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17426 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17427 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 73 208 178 242 178 434), lower := (rows 289 14 37 73 208 32 64 128 256), losses := [] }

theorem u17427 : Upper (D 8) (R 8) [288,12,33,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17427 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17428 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 74 145 240 240 240 496), lower := (rows 289 14 37 74 145 32 64 128 256), losses := [] }

theorem u17428 : Upper (D 8) (R 8) [288,12,33,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17428 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17429 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 74 176 241 209 209 465), lower := (rows 289 14 37 74 176 32 64 128 256), losses := [] }

theorem u17429 : Upper (D 8) (R 8) [288,12,33,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17429 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17430 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 88 50 225 193 193 449), lower := (rows 289 14 37 88 50 32 64 128 256), losses := [] }

theorem u17430 : Upper (D 8) (R 8) [288,12,33,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17431 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 88 145 226 226 226 482), lower := (rows 289 14 37 88 145 32 64 128 256), losses := [] }

theorem u17431 : Upper (D 8) (R 8) [288,12,33,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17431 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17432 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 88 146 225 225 225 481), lower := (rows 289 14 37 88 146 32 64 128 256), losses := [] }

theorem u17432 : Upper (D 8) (R 8) [288,12,33,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17433 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 88 176 227 195 195 451), lower := (rows 289 14 37 88 176 32 64 128 256), losses := [] }

theorem u17433 : Upper (D 8) (R 8) [288,12,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17433 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17434 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 104 81 178 210 146 402), lower := (rows 289 14 37 104 81 32 64 128 256), losses := [] }

theorem u17434 : Upper (D 8) (R 8) [288,12,33,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17435 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 104 145 242 210 210 466), lower := (rows 289 14 37 104 145 32 64 128 256), losses := [] }

theorem u17435 : Upper (D 8) (R 8) [288,12,33,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17435 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17436 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 104 146 241 209 209 465), lower := (rows 289 14 37 104 146 32 64 128 256), losses := [] }

theorem u17436 : Upper (D 8) (R 8) [288,12,33,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17436 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17437 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 104 208 179 211 147 403), lower := (rows 289 14 37 104 208 32 64 128 256), losses := [] }

theorem u17437 : Upper (D 8) (R 8) [288,12,33,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17437 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17438 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 200 50 241 209 209 465), lower := (rows 289 14 37 200 50 32 64 128 256), losses := [] }

theorem u17438 : Upper (D 8) (R 8) [288,12,33,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17438 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17439 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 200 81 178 242 178 434), lower := (rows 289 14 37 200 81 32 64 128 256), losses := [] }

theorem u17439 : Upper (D 8) (R 8) [288,12,33,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17439 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17440 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 37 200 112 179 211 147 403), lower := (rows 289 14 37 200 112 32 64 128 256), losses := [] }

theorem u17440 : Upper (D 8) (R 8) [288,12,33,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17441 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 38 56 81 225 193 193 449), lower := (rows 289 14 38 56 81 32 64 128 256), losses := [] }

theorem u17441 : Upper (D 8) (R 8) [288,12,34,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17441 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17442 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 38 56 208 225 193 193 449), lower := (rows 289 14 38 56 208 32 64 128 256), losses := [] }

theorem u17442 : Upper (D 8) (R 8) [288,12,34,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17442 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17443 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 14 38 73 49 240 208 208 464), lower := (rows 289 14 38 73 49 32 64 128 256), losses := [] }

theorem u17443 : Upper (D 8) (R 8) [288,12,34,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17444 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 14 38 73 81 176 240 176 432), lower := (rows 289 14 38 73 81 32 64 128 256), losses := [] }

theorem u17444 : Upper (D 8) (R 8) [288,12,34,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17445 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 38 73 112 177 209 145 401), lower := (rows 289 14 38 73 112 32 64 128 256), losses := [] }

theorem u17445 : Upper (D 8) (R 8) [288,12,34,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17445 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17446 : Route 9 := (fun mask => (mask,id))

def c17446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17446 : Upper (D 8) (R 8) [288,12,34,65,129] 13 := by
  apply FastRouting.sound _ _ [288,12,34,65,129] 13 (by decide) (choices 1) [16,64,128] r17446 c17446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6438
  · exact u6439
  · exact u6440

def r17447 : Route 9 := (fun mask => (mask,id))

def c17447 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17447 : Upper (D 8) (R 8) [288,12,34,65,160] 13 := by
  apply FastRouting.sound _ _ [288,12,34,65,160] 13 (by decide) (choices 1) [1,16,64,128] r17447 c17447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6441
  · exact u6442
  · exact u6443
  · exact u6444

def b17448 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 38 73 208 177 241 177 433), lower := (rows 289 14 38 73 208 32 64 128 256), losses := [] }

theorem u17448 : Upper (D 8) (R 8) [288,12,34,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17448 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17449 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 14 38 88 49 225 193 193 449), lower := (rows 289 14 38 88 49 32 64 128 256), losses := [] }

theorem u17449 : Upper (D 8) (R 8) [288,12,34,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17450 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 38 88 81 161 225 161 417), lower := (rows 289 14 38 88 81 32 64 128 256), losses := [] }

theorem u17450 : Upper (D 8) (R 8) [288,12,34,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17451 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 38 88 112 161 193 129 385), lower := (rows 289 14 38 88 112 32 64 128 256), losses := [] }

theorem u17451 : Upper (D 8) (R 8) [288,12,34,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17451 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17452 : Route 9 := (fun mask => (mask,id))

def c17452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17452 : Upper (D 8) (R 8) [288,12,34,80,129] 13 := by
  apply FastRouting.sound _ _ [288,12,34,80,129] 13 (by decide) (choices 1) [1,64,128] r17452 c17452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6445
  · exact u6446
  · exact u6447

def r17453 : Route 9 := (fun mask => (mask,id))

def c17453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17453 : Upper (D 8) (R 8) [288,12,34,80,160] 13 := by
  apply FastRouting.sound _ _ [288,12,34,80,160] 13 (by decide) (choices 1) [1,64,128] r17453 c17453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6448
  · exact u6449
  · exact u6450

def b17454 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 38 88 208 161 225 161 417), lower := (rows 289 14 38 88 208 32 64 128 256), losses := [] }

theorem u17454 : Upper (D 8) (R 8) [288,12,34,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17455 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 38 104 81 177 209 145 401), lower := (rows 289 14 38 104 81 32 64 128 256), losses := [] }

theorem u17455 : Upper (D 8) (R 8) [288,12,34,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17455 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17456 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 38 104 145 241 209 209 465), lower := (rows 289 14 38 104 145 32 64 128 256), losses := [] }

theorem u17456 : Upper (D 8) (R 8) [288,12,34,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17456 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17457 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 38 104 208 177 209 145 401), lower := (rows 289 14 38 104 208 32 64 128 256), losses := [] }

theorem u17457 : Upper (D 8) (R 8) [288,12,34,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17457 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17458 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 14 38 200 49 241 209 209 465), lower := (rows 289 14 38 200 49 32 64 128 256), losses := [] }

theorem u17458 : Upper (D 8) (R 8) [288,12,34,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17459 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 38 200 81 177 241 177 433), lower := (rows 289 14 38 200 81 32 64 128 256), losses := [] }

theorem u17459 : Upper (D 8) (R 8) [288,12,34,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17459 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u17459
end Delivery.IrregularNine14.P08
