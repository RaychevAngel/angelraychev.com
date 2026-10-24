import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0007

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6420 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 8, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 35 322 13 140 112 160 66 145 273), lower := (rows 35 322 13 140 112 160 66 128 256), losses := [] }

theorem u6420 : Upper (D 7) (R 7) [34,320,9,132,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6421 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 322 13 140 112 160 80 131 259), lower := (rows 35 322 13 140 112 160 80 128 256), losses := [] }

theorem u6421 : Upper (D 7) (R 7) [34,320,9,132,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6421 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6422 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 172, targets := 66 }], pairs := [(2,1),(2,6),(3,1),(3,6)], upper := (rows 35 322 13 152 81 160 66 164 292), lower := (rows 35 322 13 152 81 160 66 128 256), losses := [] }

theorem u6422 : Upper (D 7) (R 7) [34,320,9,144,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6423 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 35 322 13 152 81 160 68 162 290), lower := (rows 35 322 13 152 81 160 68 128 256), losses := [] }

theorem u6423 : Upper (D 7) (R 7) [34,320,9,144,65,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6423 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6424 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 35 322 13 152 81 160 96 134 262), lower := (rows 35 322 13 152 81 160 96 128 256), losses := [] }

theorem u6424 : Upper (D 7) (R 7) [34,320,9,144,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6425 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 322 13 152 112 36 65 130 386), lower := (rows 35 322 13 152 112 36 65 128 256), losses := [] }

theorem u6425 : Upper (D 7) (R 7) [34,320,9,144,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6425 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6426 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 322 13 152 112 36 66 129 385), lower := (rows 35 322 13 152 112 36 66 128 256), losses := [] }

theorem u6426 : Upper (D 7) (R 7) [34,320,9,144,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6426 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6427 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 259, targets := 128 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,7),(1,5),(1,7)], upper := (rows 35 322 13 152 112 36 192 131 259), lower := (rows 35 322 13 152 112 36 192 128 256), losses := [] }

theorem u6427 : Upper (D 7) (R 7) [34,320,9,144,96,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6427 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6428 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 80, targets := 130 },{ cop := 2, region := 322, targets := 32 },{ cop := 2, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(4,1),(4,7)], upper := (rows 35 322 13 152 112 160 65 134 262), lower := (rows 35 322 13 152 112 160 65 128 256), losses := [] }

theorem u6428 : Upper (D 7) (R 7) [34,320,9,144,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6429 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 0, region := 80, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 35 322 13 152 112 160 66 133 261), lower := (rows 35 322 13 152 112 160 66 128 256), losses := [] }

theorem u6429 : Upper (D 7) (R 7) [34,320,9,144,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6430 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 259, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(0,7),(1,7)], upper := (rows 35 322 13 152 112 160 68 131 259), lower := (rows 35 322 13 152 112 160 68 128 256), losses := [] }

theorem u6430 : Upper (D 7) (R 7) [34,320,9,144,96,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6430 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6431 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 322 13 168 208 36 65 146 274), lower := (rows 35 322 13 168 208 36 65 128 256), losses := [] }

theorem u6431 : Upper (D 7) (R 7) [34,320,9,160,192,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6431 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6432 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 322 13 168 208 36 66 145 273), lower := (rows 35 322 13 168 208 36 66 128 256), losses := [] }

theorem u6432 : Upper (D 7) (R 7) [34,320,9,160,192,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6432 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6433 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 322 13 168 208 36 80 131 259), lower := (rows 35 322 13 168 208 36 80 128 256), losses := [] }

theorem u6433 : Upper (D 7) (R 7) [34,320,9,160,192,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6433 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6434 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0)], upper := (rows 35 322 13 200 22 33 80 160 416), lower := (rows 35 322 13 200 22 33 80 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 20 32 84 161 289), good := (rows 418 322 478 200 94 416 80 128 256) }] }

theorem u6434 : Upper (D 7) (R 7) [34,320,9,192,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6434 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6435 : PairBound 9 := { available := 144, camps := [{ cop := 8, region := 99, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7)], upper := (rows 35 322 13 200 22 33 96 144 400), lower := (rows 35 322 13 200 22 33 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 20 32 97 148 276), good := (rows 98 322 478 200 414 96 96 128 256) }] }

theorem u6435 : Upper (D 7) (R 7) [34,320,9,192,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6436 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 322 13 200 22 33 192 176 304), lower := (rows 35 322 13 200 22 33 192 128 256), losses := [] }

theorem u6436 : Upper (D 7) (R 7) [34,320,9,192,6,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6437 : Route 9 := (fun mask => (mask,id))

def c6437 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6437 : Upper (D 7) (R 7) [34,320,9,192,6,128,1] 13 := by
  apply FastRouting.sound _ _ [34,320,9,192,6,128,1] 13 (by decide) (choices 1) [16,32] r6437 c6437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u474
  · exact u475

def b6438 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(1,7),(3,1)], upper := (rows 35 322 13 200 22 160 80 161 289), lower := (rows 35 322 13 200 22 160 80 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 189 80 133 261), good := (rows 417 320 429 232 508 160 120 160 256) },{ target := 7, region := (rows 1 6 4 8 20 32 84 0 257), good := (rows 291 322 351 72 86 32 80 0 256) }] }

theorem u6438 : Upper (D 7) (R 7) [34,320,9,192,6,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6438 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6439 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 72, targets := 3 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(2,1),(3,0),(3,1)], upper := (rows 35 322 13 200 22 160 96 145 273), lower := (rows 35 322 13 200 22 160 96 128 256), losses := [{ target := 1, region := (rows 1 0 5 168 16 168 237 128 256), good := (rows 109 320 109 232 84 232 104 232 256) }] }

theorem u6439 : Upper (D 7) (R 7) [34,320,9,192,6,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6440 : PairBound 9 := { available := 48, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 322 13 200 145 36 66 176 304), lower := (rows 35 322 13 200 145 36 66 128 256), losses := [] }

theorem u6440 : Upper (D 7) (R 7) [34,320,9,192,129,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6440 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6441 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 322 13 200 145 36 80 162 290), lower := (rows 35 322 13 200 145 36 80 128 256), losses := [] }

theorem u6441 : Upper (D 7) (R 7) [34,320,9,192,129,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6441 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6442 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 144, targets := 96 },{ cop := 4, region := 108, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 35 322 13 200 145 36 96 146 274), lower := (rows 35 322 13 200 145 36 96 128 256), losses := [] }

theorem u6442 : Upper (D 7) (R 7) [34,320,9,192,129,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6442 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6443 : PairBound 9 := { available := 36, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 322 13 200 145 48 66 164 292), lower := (rows 35 322 13 200 145 48 66 128 256), losses := [] }

theorem u6443 : Upper (D 7) (R 7) [34,320,9,192,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6443 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6444 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 322 13 200 145 48 68 162 290), lower := (rows 35 322 13 200 145 48 68 128 256), losses := [] }

theorem u6444 : Upper (D 7) (R 7) [34,320,9,192,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6444 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6445 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 108, targets := 2 },{ cop := 4, region := 104, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 35 322 13 200 145 48 96 134 262), lower := (rows 35 322 13 200 145 48 96 128 256), losses := [] }

theorem u6445 : Upper (D 7) (R 7) [34,320,9,192,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6445 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6446 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 144, targets := 1 }], pairs := [(0,6),(4,0),(4,6)], upper := (rows 35 322 13 200 146 33 68 176 304), lower := (rows 35 322 13 200 146 33 68 128 256), losses := [] }

theorem u6446 : Upper (D 7) (R 7) [34,320,9,192,130,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6446 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6447 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 13 200 146 33 80 164 292), lower := (rows 35 322 13 200 146 33 80 128 256), losses := [] }

theorem u6447 : Upper (D 7) (R 7) [34,320,9,192,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6447 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6448 : PairBound 9 := { available := 20, camps := [{ cop := 8, region := 99, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7)], upper := (rows 35 322 13 200 146 33 96 148 276), lower := (rows 35 322 13 200 146 33 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 20 32 97 132 260), good := (rows 98 322 478 200 146 96 96 128 256) }] }

theorem u6448 : Upper (D 7) (R 7) [34,320,9,192,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6449 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 1 },{ cop := 0, region := 144, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 35 322 13 200 146 36 65 176 304), lower := (rows 35 322 13 200 146 36 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 72 89 36 64 133 261), good := (rows 434 346 444 218 146 420 474 128 256) }] }

theorem u6449 : Upper (D 7) (R 7) [34,320,9,192,130,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6449 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6450 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 322 13 200 146 36 80 161 289), lower := (rows 35 322 13 200 146 36 80 128 256), losses := [] }

theorem u6450 : Upper (D 7) (R 7) [34,320,9,192,130,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6450 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6451 : Route 9 := (fun mask => (mask,id))

def c6451 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6451 : Upper (D 7) (R 7) [34,320,9,192,130,4,32] 13 := by
  apply FastRouting.sound _ _ [34,320,9,192,130,4,32] 13 (by decide) (choices 1) [1,16] r6451 c6451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u476
  · exact u477

def b6452 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 176, targets := 66 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,6)], upper := (rows 35 322 13 200 148 33 66 176 304), lower := (rows 35 322 13 200 148 33 66 128 256), losses := [] }

theorem u6452 : Upper (D 7) (R 7) [34,320,9,192,132,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6453 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 13 200 148 33 80 162 290), lower := (rows 35 322 13 200 148 33 80 128 256), losses := [] }

theorem u6453 : Upper (D 7) (R 7) [34,320,9,192,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6453 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6454 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7)], upper := (rows 35 322 13 200 148 33 96 146 274), lower := (rows 35 322 13 200 148 33 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 20 32 97 148 276), good := (rows 98 322 478 200 414 96 96 128 256) }] }

theorem u6454 : Upper (D 7) (R 7) [34,320,9,192,132,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6455 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 176, targets := 66 },{ cop := 8, region := 66, targets := 33 }], pairs := [(1,0),(1,5),(4,1),(4,6)], upper := (rows 35 322 13 200 176 33 66 148 276), lower := (rows 35 322 13 200 176 33 66 128 256), losses := [] }

theorem u6455 : Upper (D 7) (R 7) [34,320,9,192,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6456 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 144, targets := 1 }], pairs := [(0,6),(4,0),(4,6)], upper := (rows 35 322 13 200 176 33 68 146 274), lower := (rows 35 322 13 200 176 33 68 128 256), losses := [] }

theorem u6456 : Upper (D 7) (R 7) [34,320,9,192,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6456 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6457 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 13 200 176 33 80 134 262), lower := (rows 35 322 13 200 176 33 80 128 256), losses := [] }

theorem u6457 : Upper (D 7) (R 7) [34,320,9,192,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6457 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6458 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 92, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 322 14 28 81 160 65 160 416), lower := (rows 35 322 14 28 81 160 65 128 256), losses := [] }

theorem u6458 : Upper (D 7) (R 7) [34,320,10,20,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6459 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 4, region := 386, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 322 14 28 81 160 96 129 385), lower := (rows 35 322 14 28 81 160 96 128 256), losses := [] }

theorem u6459 : Upper (D 7) (R 7) [34,320,10,20,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6460 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(2,5),(3,5),(4,1)], upper := (rows 35 322 14 28 81 160 192 161 289), lower := (rows 35 322 14 28 81 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 5 25 17 0 224 128 256), good := (rows 95 322 14 28 93 192 192 192 256) }] }

theorem u6460 : Upper (D 7) (R 7) [34,320,10,20,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6461 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 0, region := 80, targets := 2 }], pairs := [(2,7),(3,7),(4,1),(4,7)], upper := (rows 35 322 14 28 112 160 65 129 385), lower := (rows 35 322 14 28 112 160 65 128 256), losses := [] }

theorem u6461 : Upper (D 7) (R 7) [34,320,10,20,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6462 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 322 14 28 112 160 192 129 257), lower := (rows 35 322 14 28 112 160 192 128 256), losses := [] }

theorem u6462 : Upper (D 7) (R 7) [34,320,10,20,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6463 : PairBound 9 := { available := 160, camps := [{ cop := 8, region := 99, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 35 322 14 28 208 33 65 160 416), lower := (rows 35 322 14 28 208 33 65 128 256), losses := [] }

theorem u6463 : Upper (D 7) (R 7) [34,320,10,20,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6464 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 99, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 35 322 14 28 208 33 96 129 385), lower := (rows 35 322 14 28 208 33 96 128 256), losses := [] }

theorem u6464 : Upper (D 7) (R 7) [34,320,10,20,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6464 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6465 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 322 14 28 208 33 192 161 289), lower := (rows 35 322 14 28 208 33 192 128 256), losses := [] }

theorem u6465 : Upper (D 7) (R 7) [34,320,10,20,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6466 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 322 14 56 81 160 65 132 388), lower := (rows 35 322 14 56 81 160 65 128 256), losses := [] }

theorem u6466 : Upper (D 7) (R 7) [34,320,10,48,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6467 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 322 14 56 81 160 68 129 385), lower := (rows 35 322 14 56 81 160 68 128 256), losses := [] }

theorem u6467 : Upper (D 7) (R 7) [34,320,10,48,65,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6467 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6468 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(3,0),(3,1),(4,1)], upper := (rows 35 322 14 56 81 160 192 133 261), lower := (rows 35 322 14 56 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 224 224 128 256), good := (rows 98 354 14 120 120 224 224 224 256) },{ target := 1, region := (rows 1 0 4 25 17 224 224 128 256), good := (rows 121 352 12 120 121 224 224 224 256) }] }

theorem u6468 : Upper (D 7) (R 7) [34,320,10,48,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6469 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 322 14 56 84 160 65 129 385), lower := (rows 35 322 14 56 84 160 65 128 256), losses := [] }

theorem u6469 : Upper (D 7) (R 7) [34,320,10,48,68,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6470 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(1,5),(2,0),(3,0)], upper := (rows 35 322 14 56 84 160 192 129 257), lower := (rows 35 322 14 56 84 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 7 27 19 224 224 128 256), good := (rows 126 382 30 120 124 224 224 224 256) }] }

theorem u6470 : Upper (D 7) (R 7) [34,320,10,48,68,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6471 : PairBound 9 := { available := 132, camps := [{ cop := 8, region := 99, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7)], upper := (rows 35 322 14 56 208 33 65 132 388), lower := (rows 35 322 14 56 208 33 65 128 256), losses := [{ target := 0, region := (rows 0 82 77 9 82 32 64 255 383), good := (rows 446 470 414 446 470 428 478 128 256) }] }

theorem u6471 : Upper (D 7) (R 7) [34,320,10,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6472 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,5)], upper := (rows 35 322 14 56 208 33 68 129 385), lower := (rows 35 322 14 56 208 33 68 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 24 0 76 161 289), good := (rows 387 322 94 478 208 385 68 128 256) }] }

theorem u6472 : Upper (D 7) (R 7) [34,320,10,48,192,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6472 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6473 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 322 14 56 208 33 192 133 261), lower := (rows 35 322 14 56 208 33 192 128 256), losses := [] }

theorem u6473 : Upper (D 7) (R 7) [34,320,10,48,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6474 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 322 14 73 52 160 65 144 400), lower := (rows 35 322 14 73 52 160 65 128 256), losses := [] }

theorem u6474 : Upper (D 7) (R 7) [34,320,10,65,36,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6475 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 322 14 73 52 160 80 129 385), lower := (rows 35 322 14 73 52 160 80 128 256), losses := [] }

theorem u6475 : Upper (D 7) (R 7) [34,320,10,65,36,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6475 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6476 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(2,5),(3,1),(4,6)], upper := (rows 35 322 14 73 52 160 192 145 273), lower := (rows 35 322 14 73 52 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 224 224 128 256), good := (rows 105 352 12 105 116 224 224 224 256) },{ target := 5, region := (rows 1 2 5 9 16 0 224 128 256), good := (rows 79 322 14 77 84 192 192 192 256) }] }

theorem u6476 : Upper (D 7) (R 7) [34,320,10,65,36,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6477 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7)], upper := (rows 35 322 14 73 145 48 68 160 416), lower := (rows 35 322 14 73 145 48 68 128 256), losses := [] }

theorem u6477 : Upper (D 7) (R 7) [34,320,10,65,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6477 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6478 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 322 14 73 145 48 96 132 388), lower := (rows 35 322 14 73 145 48 96 128 256), losses := [] }

theorem u6478 : Upper (D 7) (R 7) [34,320,10,65,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6478 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6479 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 72, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 35 322 14 73 145 48 192 164 292), lower := (rows 35 322 14 73 145 48 192 128 256), losses := [] }

theorem u6479 : Upper (D 7) (R 7) [34,320,10,65,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6479 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u6479
end Delivery.IrregularNine14.P07
