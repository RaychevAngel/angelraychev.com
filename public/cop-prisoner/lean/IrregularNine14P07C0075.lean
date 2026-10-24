import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0005

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4500 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 290 37 74 208 48 66 129 385), lower := (rows 13 290 37 74 208 48 66 128 256), losses := [] }

theorem u4500 : Upper (D 7) (R 7) [12,288,33,66,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4500 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4501 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 37 74 208 48 192 131 259), lower := (rows 13 290 37 74 208 48 192 128 256), losses := [] }

theorem u4501 : Upper (D 7) (R 7) [12,288,33,66,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4501 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4502 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 290 37 74 208 160 65 146 274), lower := (rows 13 290 37 74 208 160 65 128 256), losses := [] }

theorem u4502 : Upper (D 7) (R 7) [12,288,33,66,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4503 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 3, region := 181, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 13 290 37 74 208 160 66 145 273), lower := (rows 13 290 37 74 208 160 66 128 256), losses := [] }

theorem u4503 : Upper (D 7) (R 7) [12,288,33,66,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4504 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 13 290 37 74 208 160 80 131 259), lower := (rows 13 290 37 74 208 160 80 128 256), losses := [] }

theorem u4504 : Upper (D 7) (R 7) [12,288,33,66,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4504 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4505 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 37 88 19 160 66 192 448), lower := (rows 13 290 37 88 19 160 66 128 256), losses := [] }

theorem u4505 : Upper (D 7) (R 7) [12,288,33,80,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4506 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 200, targets := 32 }], pairs := [(0,1),(1,0),(3,0),(3,5)], upper := (rows 13 290 37 88 19 160 192 194 322), lower := (rows 13 290 37 88 19 160 192 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 224 224 128 256), good := (rows 13 352 101 125 17 224 224 224 256) }] }

theorem u4506 : Upper (D 7) (R 7) [12,288,33,80,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4507 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 136, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 13 290 37 200 82 34 65 144 400), lower := (rows 13 290 37 200 82 34 65 128 256), losses := [] }

theorem u4507 : Upper (D 7) (R 7) [12,288,33,192,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4508 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 290 37 200 82 34 80 129 385), lower := (rows 13 290 37 200 82 34 80 128 256), losses := [] }

theorem u4508 : Upper (D 7) (R 7) [12,288,33,192,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4508 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4509 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 290 37 200 82 34 192 145 273), lower := (rows 13 290 37 200 82 34 192 128 256), losses := [] }

theorem u4509 : Upper (D 7) (R 7) [12,288,33,192,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4510 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 290 37 200 82 48 65 130 386), lower := (rows 13 290 37 200 82 48 65 128 256), losses := [] }

theorem u4510 : Upper (D 7) (R 7) [12,288,33,192,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4510 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4511 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 290 37 200 82 48 66 129 385), lower := (rows 13 290 37 200 82 48 66 128 256), losses := [] }

theorem u4511 : Upper (D 7) (R 7) [12,288,33,192,66,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4511 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4512 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 37 200 82 48 192 131 259), lower := (rows 13 290 37 200 82 48 192 128 256), losses := [] }

theorem u4512 : Upper (D 7) (R 7) [12,288,33,192,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4512 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4513 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 73, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(3,1)], upper := (rows 13 290 52 73 82 160 65 130 386), lower := (rows 13 290 52 73 82 160 65 128 256), losses := [] }

theorem u4513 : Upper (D 7) (R 7) [12,288,48,65,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4514 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 52 73 82 160 66 129 385), lower := (rows 13 290 52 73 82 160 66 128 256), losses := [] }

theorem u4514 : Upper (D 7) (R 7) [12,288,48,65,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4515 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(0,1),(1,6),(2,0),(4,0)], upper := (rows 13 290 52 73 82 160 192 131 259), lower := (rows 13 290 52 73 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 22 8 18 224 224 128 256), good := (rows 12 374 116 104 118 224 224 224 256) },{ target := 1, region := (rows 21 0 20 28 16 224 224 128 256), good := (rows 13 352 125 105 125 224 224 224 256) }] }

theorem u4515 : Upper (D 7) (R 7) [12,288,48,65,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4516 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 109, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 290 52 73 146 96 65 130 386), lower := (rows 13 290 52 73 146 96 65 128 256), losses := [] }

theorem u4516 : Upper (D 7) (R 7) [12,288,48,65,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4517 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 8, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 290 52 73 146 96 66 129 385), lower := (rows 13 290 52 73 146 96 66 128 256), losses := [] }

theorem u4517 : Upper (D 7) (R 7) [12,288,48,65,130,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4518 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 109, targets := 2 },{ cop := 3, region := 290, targets := 128 }], pairs := [(0,1),(1,7),(2,1),(3,1)], upper := (rows 13 290 52 73 146 96 192 131 259), lower := (rows 13 290 52 73 146 96 192 128 256), losses := [] }

theorem u4518 : Upper (D 7) (R 7) [12,288,48,65,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4519 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 73, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(3,1)], upper := (rows 13 290 52 73 208 34 65 130 386), lower := (rows 13 290 52 73 208 34 65 128 256), losses := [] }

theorem u4519 : Upper (D 7) (R 7) [12,288,48,65,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4520 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 144, targets := 34 },{ cop := 8, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 13 290 52 73 208 34 66 129 385), lower := (rows 13 290 52 73 208 34 66 128 256), losses := [] }

theorem u4520 : Upper (D 7) (R 7) [12,288,48,65,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4521 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 52 73 208 34 192 131 259), lower := (rows 13 290 52 73 208 34 192 128 256), losses := [] }

theorem u4521 : Upper (D 7) (R 7) [12,288,48,65,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4522 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 52 74 19 160 65 192 448), lower := (rows 13 290 52 74 19 160 65 128 256), losses := [] }

theorem u4522 : Upper (D 7) (R 7) [12,288,48,66,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4523 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 228, targets := 2 },{ cop := 4, region := 200, targets := 32 }], pairs := [(0,5),(2,1),(3,0),(3,5)], upper := (rows 13 290 52 74 19 160 192 193 321), lower := (rows 13 290 52 74 19 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 224 224 128 256), good := (rows 12 362 116 106 26 224 224 224 256) },{ target := 5, region := (rows 5 2 4 26 16 0 245 149 277), good := (rows 461 330 477 74 475 192 192 192 256) }] }

theorem u4523 : Upper (D 7) (R 7) [12,288,48,66,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4524 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 52 74 81 160 65 130 386), lower := (rows 13 290 52 74 81 160 65 128 256), losses := [] }

theorem u4524 : Upper (D 7) (R 7) [12,288,48,66,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4525 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 52 74 81 160 66 129 385), lower := (rows 13 290 52 74 81 160 66 128 256), losses := [] }

theorem u4525 : Upper (D 7) (R 7) [12,288,48,66,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4526 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,0),(2,6),(3,0)], upper := (rows 13 290 52 74 81 160 192 131 259), lower := (rows 13 290 52 74 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 20 10 16 224 224 128 256), good := (rows 12 362 116 106 116 224 224 224 256) }] }

theorem u4526 : Upper (D 7) (R 7) [12,288,48,66,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4527 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 386, targets := 65 },{ cop := 4, region := 100, targets := 130 }], pairs := [(1,0),(1,6),(2,1),(2,7)], upper := (rows 13 290 52 74 145 96 65 130 386), lower := (rows 13 290 52 74 145 96 65 128 256), losses := [] }

theorem u4527 : Upper (D 7) (R 7) [12,288,48,66,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4528 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 13 290 52 74 145 96 66 129 385), lower := (rows 13 290 52 74 145 96 66 128 256), losses := [] }

theorem u4528 : Upper (D 7) (R 7) [12,288,48,66,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4529 : Route 9 := (fun mask => (mask,id))

def c4529 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4529 : Upper (D 7) (R 7) [12,288,48,66,129,64,128] 13 := by
  apply FastRouting.sound _ _ [12,288,48,66,129,64,128] 13 (by decide) (choices 1) [1,2] r4529 c4529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u347
  · exact u348

def b4530 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 3, region := 144, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 13 290 52 74 146 33 65 192 448), lower := (rows 13 290 52 74 146 33 65 128 256), losses := [] }

theorem u4530 : Upper (D 7) (R 7) [12,288,48,66,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4531 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 72, targets := 33 }], pairs := [(0,5),(3,0),(3,5),(4,5)], upper := (rows 13 290 52 74 146 33 192 193 321), lower := (rows 13 290 52 74 146 33 192 128 256), losses := [{ target := 5, region := (rows 5 2 4 26 18 0 247 165 293), good := (rows 461 474 477 90 218 449 192 192 256) }] }

theorem u4531 : Upper (D 7) (R 7) [12,288,48,66,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4532 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,5)], upper := (rows 13 290 52 74 146 96 65 129 385), lower := (rows 13 290 52 74 146 96 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 24 0 65 193 321), good := (rows 477 258 20 474 146 448 449 128 256) }] }

theorem u4532 : Upper (D 7) (R 7) [12,288,48,66,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4533 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 108, targets := 1 },{ cop := 4, region := 100, targets := 2 },{ cop := 4, region := 72, targets := 32 }], pairs := [(2,0),(2,1),(3,0),(3,5)], upper := (rows 13 290 52 74 146 96 192 129 257), lower := (rows 13 290 52 74 146 96 192 128 256), losses := [] }

theorem u4533 : Upper (D 7) (R 7) [12,288,48,66,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4534 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 386, targets := 65 },{ cop := 3, region := 144, targets := 33 }], pairs := [(1,0),(1,6),(4,0),(4,5)], upper := (rows 13 290 52 74 208 33 65 130 386), lower := (rows 13 290 52 74 208 33 65 128 256), losses := [] }

theorem u4534 : Upper (D 7) (R 7) [12,288,48,66,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4535 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 72, targets := 161 },{ cop := 3, region := 181, targets := 2 }], pairs := [(0,1),(3,0),(3,5),(3,7)], upper := (rows 13 290 52 74 208 33 66 129 385), lower := (rows 13 290 52 74 208 33 66 128 256), losses := [] }

theorem u4535 : Upper (D 7) (R 7) [12,288,48,66,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4536 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 52 74 208 33 192 131 259), lower := (rows 13 290 52 74 208 33 192 128 256), losses := [] }

theorem u4536 : Upper (D 7) (R 7) [12,288,48,66,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4537 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 386, targets := 65 },{ cop := 4, region := 136, targets := 33 }], pairs := [(1,0),(1,6),(3,0),(3,5)], upper := (rows 13 290 52 200 82 33 65 130 386), lower := (rows 13 290 52 200 82 33 65 128 256), losses := [] }

theorem u4537 : Upper (D 7) (R 7) [12,288,48,192,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4538 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 84, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 290 52 200 82 33 66 129 385), lower := (rows 13 290 52 200 82 33 66 128 256), losses := [] }

theorem u4538 : Upper (D 7) (R 7) [12,288,48,192,66,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4539 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 290 52 200 82 33 192 131 259), lower := (rows 13 290 52 200 82 33 192 128 256), losses := [] }

theorem u4539 : Upper (D 7) (R 7) [12,288,48,192,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4540 : Route 9 := (fun mask => (mask,id))

def c4540 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4540 : Upper (D 7) (R 7) [12,288,48,192,66,128,1] 13 := by
  apply FastRouting.sound _ _ [12,288,48,192,66,128,1] 13 (by decide) (choices 1) [1,2] r4540 c4540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u349
  · exact u350

def b4541 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 84, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 290 52 200 82 160 66 129 257), lower := (rows 13 290 52 200 82 160 66 128 256), losses := [] }

theorem u4541 : Upper (D 7) (R 7) [12,288,48,192,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4542 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 394, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 13 290 69 138 19 96 80 160 416), lower := (rows 13 290 69 138 19 96 80 128 256), losses := [] }

theorem u4542 : Upper (D 7) (R 7) [12,288,65,130,3,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4542 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4543 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 117, targets := 128 },{ cop := 3, region := 101, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 13 290 69 138 19 96 96 144 400), lower := (rows 13 290 69 138 19 96 96 128 256), losses := [] }

theorem u4543 : Upper (D 7) (R 7) [12,288,65,130,3,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4544 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 85, targets := 32 },{ cop := 2, region := 306, targets := 128 }], pairs := [(0,5),(1,7),(2,5),(4,5)], upper := (rows 13 290 69 138 19 96 192 176 304), lower := (rows 13 290 69 138 19 96 192 128 256), losses := [] }

theorem u4544 : Upper (D 7) (R 7) [12,288,65,130,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4545 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 85, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 13 290 69 138 19 160 80 224 352), lower := (rows 13 290 69 138 19 160 80 128 256), losses := [] }

theorem u4545 : Upper (D 7) (R 7) [12,288,65,130,3,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4545 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4546 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 101, targets := 2 },{ cop := 4, region := 490, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 13 290 69 138 19 160 96 208 336), lower := (rows 13 290 69 138 19 160 96 128 256), losses := [] }

theorem u4546 : Upper (D 7) (R 7) [12,288,65,130,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4547 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 290 69 138 82 33 80 160 416), lower := (rows 13 290 69 138 82 33 80 128 256), losses := [] }

theorem u4547 : Upper (D 7) (R 7) [12,288,65,130,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4547 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4548 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 117, targets := 128 },{ cop := 4, region := 141, targets := 32 }], pairs := [(0,5),(0,7),(2,7),(4,7)], upper := (rows 13 290 69 138 82 33 96 144 400), lower := (rows 13 290 69 138 82 33 96 128 256), losses := [] }

theorem u4548 : Upper (D 7) (R 7) [12,288,65,130,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4549 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 85, targets := 32 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 13 290 69 138 82 33 192 176 304), lower := (rows 13 290 69 138 82 33 192 128 256), losses := [] }

theorem u4549 : Upper (D 7) (R 7) [12,288,65,130,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4550 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 426, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 13 290 69 138 82 48 65 160 416), lower := (rows 13 290 69 138 82 48 65 128 256), losses := [] }

theorem u4550 : Upper (D 7) (R 7) [12,288,65,130,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4550 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4551 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 290 69 138 82 48 96 129 385), lower := (rows 13 290 69 138 82 48 96 128 256), losses := [] }

theorem u4551 : Upper (D 7) (R 7) [12,288,65,130,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4551 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4552 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 85, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 13 290 69 138 82 48 192 161 289), lower := (rows 13 290 69 138 82 48 192 128 256), losses := [] }

theorem u4552 : Upper (D 7) (R 7) [12,288,65,130,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4552 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4553 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 69 138 82 160 65 176 304), lower := (rows 13 290 69 138 82 160 65 128 256), losses := [] }

theorem u4553 : Upper (D 7) (R 7) [12,288,65,130,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4554 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 85, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 13 290 69 138 82 160 80 161 289), lower := (rows 13 290 69 138 82 160 80 128 256), losses := [] }

theorem u4554 : Upper (D 7) (R 7) [12,288,65,130,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4554 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4555 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 141, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 13 290 69 138 82 160 96 145 273), lower := (rows 13 290 69 138 82 160 96 128 256), losses := [] }

theorem u4555 : Upper (D 7) (R 7) [12,288,65,130,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4556 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 69 138 112 34 65 144 400), lower := (rows 13 290 69 138 112 34 65 128 256), losses := [] }

theorem u4556 : Upper (D 7) (R 7) [12,288,65,130,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4557 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 290 69 138 112 34 80 129 385), lower := (rows 13 290 69 138 112 34 80 128 256), losses := [] }

theorem u4557 : Upper (D 7) (R 7) [12,288,65,130,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4557 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4558 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 69 138 112 34 192 145 273), lower := (rows 13 290 69 138 112 34 192 128 256), losses := [] }

theorem u4558 : Upper (D 7) (R 7) [12,288,65,130,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4559 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 69 138 112 160 65 146 274), lower := (rows 13 290 69 138 112 160 65 128 256), losses := [] }

theorem u4559 : Upper (D 7) (R 7) [12,288,65,130,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4559
end Delivery.IrregularNine14.P07
