import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0010

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4500 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 56 146 160 97 225 353), lower := (rows 97 7 268 56 146 160 64 128 256), losses := [] }

theorem u4500 : Upper (D 8) (R 8) [96,5,264,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4501 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 56 208 33 226 162 418), lower := (rows 97 7 268 56 208 33 64 128 256), losses := [] }

theorem u4501 : Upper (D 8) (R 8) [96,5,264,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4501 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4502 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 268 56 208 34 225 161 417), lower := (rows 97 7 268 56 208 34 64 128 256), losses := [] }

theorem u4502 : Upper (D 8) (R 8) [96,5,264,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4502 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4503 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 56 208 160 99 163 291), lower := (rows 97 7 268 56 208 160 64 128 256), losses := [] }

theorem u4503 : Upper (D 8) (R 8) [96,5,264,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4504 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 152 50 33 224 224 480), lower := (rows 97 7 268 152 50 33 64 128 256), losses := [] }

theorem u4504 : Upper (D 8) (R 8) [96,5,264,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4505 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 152 50 96 225 161 417), lower := (rows 97 7 268 152 50 96 64 128 256), losses := [] }

theorem u4505 : Upper (D 8) (R 8) [96,5,264,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4506 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 152 50 160 97 225 353), lower := (rows 97 7 268 152 50 160 64 128 256), losses := [] }

theorem u4506 : Upper (D 8) (R 8) [96,5,264,144,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4507 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 168 50 33 208 208 464), lower := (rows 97 7 268 168 50 33 64 128 256), losses := [] }

theorem u4507 : Upper (D 8) (R 8) [96,5,264,160,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4508 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 268 168 50 48 193 193 449), lower := (rows 97 7 268 168 50 48 64 128 256), losses := [] }

theorem u4508 : Upper (D 8) (R 8) [96,5,264,160,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4508 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4509 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 168 50 96 209 145 401), lower := (rows 97 7 268 168 50 96 64 128 256), losses := [] }

theorem u4509 : Upper (D 8) (R 8) [96,5,264,160,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4510 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 168 50 160 81 209 337), lower := (rows 97 7 268 168 50 160 64 128 256), losses := [] }

theorem u4510 : Upper (D 8) (R 8) [96,5,264,160,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4511 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 168 82 33 240 176 432), lower := (rows 97 7 268 168 82 33 64 128 256), losses := [] }

theorem u4511 : Upper (D 8) (R 8) [96,5,264,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4512 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 268 168 82 48 225 161 417), lower := (rows 97 7 268 168 82 48 64 128 256), losses := [] }

theorem u4512 : Upper (D 8) (R 8) [96,5,264,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4512 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4513 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 168 82 160 113 177 305), lower := (rows 97 7 268 168 82 160 64 128 256), losses := [] }

theorem u4513 : Upper (D 8) (R 8) [96,5,264,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4514 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 97 7 268 168 145 34 112 240 368), lower := (rows 97 7 268 168 145 34 64 128 256), losses := [] }

theorem u4514 : Upper (D 8) (R 8) [96,5,264,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4514 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4515 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 97 7 268 168 145 48 98 226 354), lower := (rows 97 7 268 168 145 48 64 128 256), losses := [] }

theorem u4515 : Upper (D 8) (R 8) [96,5,264,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4515 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4516 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 168 145 96 114 178 306), lower := (rows 97 7 268 168 145 96 64 128 256), losses := [] }

theorem u4516 : Upper (D 8) (R 8) [96,5,264,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4517 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 168 208 33 114 178 306), lower := (rows 97 7 268 168 208 33 64 128 256), losses := [] }

theorem u4517 : Upper (D 8) (R 8) [96,5,264,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4518 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 7 268 168 208 34 113 177 305), lower := (rows 97 7 268 168 208 34 64 128 256), losses := [] }

theorem u4518 : Upper (D 8) (R 8) [96,5,264,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4518 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4519 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 7 268 168 208 48 99 163 291), lower := (rows 97 7 268 168 208 48 64 128 256), losses := [] }

theorem u4519 : Upper (D 8) (R 8) [96,5,264,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4519 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4520 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 292 26 56 33 192 192 448), lower := (rows 97 7 292 26 56 33 64 128 256), losses := [] }

theorem u4520 : Upper (D 8) (R 8) [96,5,288,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4521 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 26 56 96 193 129 385), lower := (rows 97 7 292 26 56 96 64 128 256), losses := [] }

theorem u4521 : Upper (D 8) (R 8) [96,5,288,18,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4521 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4522 : Route 9 := (fun mask => (mask,id))

def c4522 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4522 : Upper (D 8) (R 8) [96,5,288,18,40,128] 13 := by
  apply FastRouting.sound _ _ [96,5,288,18,40,128] 13 (by decide) (choices 1) [1,128] r4522 c4522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u609
  · exact u610

def b4523 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 388, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 292 26 152 33 224 224 480), lower := (rows 97 7 292 26 152 33 64 128 256), losses := [] }

theorem u4523 : Upper (D 8) (R 8) [96,5,288,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4524 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 26 152 96 225 161 417), lower := (rows 97 7 292 26 152 96 64 128 256), losses := [] }

theorem u4524 : Upper (D 8) (R 8) [96,5,288,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4524 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4525 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 26 152 160 97 225 353), lower := (rows 97 7 292 26 152 160 64 128 256), losses := [] }

theorem u4525 : Upper (D 8) (R 8) [96,5,288,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4525 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4526 : PairBound 9 := { available := 200, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 26 176 33 200 200 456), lower := (rows 97 7 292 26 176 33 64 128 256), losses := [] }

theorem u4526 : Upper (D 8) (R 8) [96,5,288,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4527 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 292 26 176 40 193 193 449), lower := (rows 97 7 292 26 176 40 64 128 256), losses := [] }

theorem u4527 : Upper (D 8) (R 8) [96,5,288,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4527 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4528 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 26 176 96 201 137 393), lower := (rows 97 7 292 26 176 96 64 128 256), losses := [] }

theorem u4528 : Upper (D 8) (R 8) [96,5,288,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4529 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 26 176 160 73 201 329), lower := (rows 97 7 292 26 176 160 64 128 256), losses := [] }

theorem u4529 : Upper (D 8) (R 8) [96,5,288,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4530 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 26 208 33 232 168 424), lower := (rows 97 7 292 26 208 33 64 128 256), losses := [] }

theorem u4530 : Upper (D 8) (R 8) [96,5,288,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4531 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 292 26 208 40 225 161 417), lower := (rows 97 7 292 26 208 40 64 128 256), losses := [] }

theorem u4531 : Upper (D 8) (R 8) [96,5,288,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4531 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4532 : Route 9 := (fun mask => (mask,id))

def c4532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4532 : Upper (D 8) (R 8) [96,5,288,18,192,128] 13 := by
  apply FastRouting.sound _ _ [96,5,288,18,192,128] 13 (by decide) (choices 1) [1,8,32] r4532 c4532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u611
  · exact u612
  · exact u613

def b4533 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 292 42 88 33 208 144 400), lower := (rows 97 7 292 42 88 33 64 128 256), losses := [] }

theorem u4533 : Upper (D 8) (R 8) [96,5,288,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4534 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 7 292 42 88 48 193 129 385), lower := (rows 97 7 292 42 88 48 64 128 256), losses := [] }

theorem u4534 : Upper (D 8) (R 8) [96,5,288,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4534 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4535 : Route 9 := (fun mask => (mask,id))

def c4535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4535 : Upper (D 8) (R 8) [96,5,288,34,72,128] 13 := by
  apply FastRouting.sound _ _ [96,5,288,34,72,128] 13 (by decide) (choices 1) [1,16,128] r4535 c4535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u614
  · exact u615
  · exact u616

def b4536 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 97 7 292 42 145 40 208 208 464), lower := (rows 97 7 292 42 145 40 64 128 256), losses := [] }

theorem u4536 : Upper (D 8) (R 8) [96,5,288,34,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4536 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4537 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 97 7 292 42 145 48 200 200 456), lower := (rows 97 7 292 42 145 48 64 128 256), losses := [] }

theorem u4537 : Upper (D 8) (R 8) [96,5,288,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4537 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4538 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 42 145 96 216 152 408), lower := (rows 97 7 292 42 145 96 64 128 256), losses := [] }

theorem u4538 : Upper (D 8) (R 8) [96,5,288,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4539 : Route 9 := (fun mask => (mask,id))

def c4539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4539 : Upper (D 8) (R 8) [96,5,288,34,129,128] 13 := by
  apply FastRouting.sound _ _ [96,5,288,34,129,128] 13 (by decide) (choices 1) [8,16] r4539 c4539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u617
  · exact u618

def b4540 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 292 42 152 33 208 208 464), lower := (rows 97 7 292 42 152 33 64 128 256), losses := [] }

theorem u4540 : Upper (D 8) (R 8) [96,5,288,34,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4541 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 292 42 152 48 193 193 449), lower := (rows 97 7 292 42 152 48 64 128 256), losses := [] }

theorem u4541 : Upper (D 8) (R 8) [96,5,288,34,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4541 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4542 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 42 152 96 209 145 401), lower := (rows 97 7 292 42 152 96 64 128 256), losses := [] }

theorem u4542 : Upper (D 8) (R 8) [96,5,288,34,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4543 : Route 9 := (fun mask => (mask,id))

def c4543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4543 : Upper (D 8) (R 8) [96,5,288,34,136,128] 13 := by
  apply FastRouting.sound _ _ [96,5,288,34,136,128] 13 (by decide) (choices 1) [1,16] r4543 c4543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u619
  · exact u620

def b4544 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 292 42 208 33 216 152 408), lower := (rows 97 7 292 42 208 33 64 128 256), losses := [] }

theorem u4544 : Upper (D 8) (R 8) [96,5,288,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4544 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4545 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 97 7 292 42 208 40 209 145 401), lower := (rows 97 7 292 42 208 40 64 128 256), losses := [] }

theorem u4545 : Upper (D 8) (R 8) [96,5,288,34,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4545 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4546 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 97 7 292 42 208 48 201 137 393), lower := (rows 97 7 292 42 208 48 64 128 256), losses := [] }

theorem u4546 : Upper (D 8) (R 8) [96,5,288,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4546 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4547 : Route 9 := (fun mask => (mask,id))

def c4547 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4547 : Upper (D 8) (R 8) [96,5,288,34,192,128] 13 := by
  apply FastRouting.sound _ _ [96,5,288,34,192,128] 13 (by decide) (choices 1) [1,8,16] r4547 c4547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u621
  · exact u622
  · exact u623

def b4548 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 56 82 33 200 136 392), lower := (rows 97 7 292 56 82 33 64 128 256), losses := [] }

theorem u4548 : Upper (D 8) (R 8) [96,5,288,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4549 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 7 292 56 82 40 193 129 385), lower := (rows 97 7 292 56 82 40 64 128 256), losses := [] }

theorem u4549 : Upper (D 8) (R 8) [96,5,288,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4549 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4550 : Route 9 := (fun mask => (mask,id))

def c4550 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4550 : Upper (D 8) (R 8) [96,5,288,48,66,128] 13 := by
  apply FastRouting.sound _ _ [96,5,288,48,66,128] 13 (by decide) (choices 1) [1,8,128] r4550 c4550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u624
  · exact u625
  · exact u626

def b4551 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 97 7 292 56 145 34 200 200 456), lower := (rows 97 7 292 56 145 34 64 128 256), losses := [] }

theorem u4551 : Upper (D 8) (R 8) [96,5,288,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4551 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4552 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 97 7 292 56 145 40 194 194 450), lower := (rows 97 7 292 56 145 40 64 128 256), losses := [] }

theorem u4552 : Upper (D 8) (R 8) [96,5,288,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4552 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4553 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 56 145 96 202 138 394), lower := (rows 97 7 292 56 145 96 64 128 256), losses := [] }

theorem u4553 : Upper (D 8) (R 8) [96,5,288,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4554 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 56 145 160 74 202 330), lower := (rows 97 7 292 56 145 160 64 128 256), losses := [] }

theorem u4554 : Upper (D 8) (R 8) [96,5,288,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4555 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 292 56 146 33 200 200 456), lower := (rows 97 7 292 56 146 33 64 128 256), losses := [] }

theorem u4555 : Upper (D 8) (R 8) [96,5,288,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4556 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 292 56 146 40 193 193 449), lower := (rows 97 7 292 56 146 40 64 128 256), losses := [] }

theorem u4556 : Upper (D 8) (R 8) [96,5,288,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4556 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4557 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 292 56 146 96 201 137 393), lower := (rows 97 7 292 56 146 96 64 128 256), losses := [] }

theorem u4557 : Upper (D 8) (R 8) [96,5,288,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4558 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 56 146 160 73 201 329), lower := (rows 97 7 292 56 146 160 64 128 256), losses := [] }

theorem u4558 : Upper (D 8) (R 8) [96,5,288,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4559 : PairBound 9 := { available := 194, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 292 56 152 33 194 194 450), lower := (rows 97 7 292 56 152 33 64 128 256), losses := [] }

theorem u4559 : Upper (D 8) (R 8) [96,5,288,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4559 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4559
end Delivery.IrregularNine14.P08
