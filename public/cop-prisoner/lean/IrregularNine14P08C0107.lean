import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0013

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6420 : Route 9 := (fun mask => (mask,id))

def c6420 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6420 : Upper (D 8) (R 8) [288,5,192,48,65,128] 13 := by
  apply FastRouting.sound _ _ [288,5,192,48,65,128] 13 (by decide) (choices 1) [2,8,32] r6420 c6420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u816
  · exact u817
  · exact u818

def b6421 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 289 7 196 73 152 34 112 176 304), lower := (rows 289 7 196 73 152 34 64 128 256), losses := [] }

theorem u6421 : Upper (D 8) (R 8) [288,5,192,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6421 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6422 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 289 7 196 73 152 48 98 162 290), lower := (rows 289 7 196 73 152 48 64 128 256), losses := [] }

theorem u6422 : Upper (D 8) (R 8) [288,5,192,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6422 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6423 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 289 7 196 73 176 34 120 184 312), lower := (rows 289 7 196 73 176 34 64 128 256), losses := [] }

theorem u6423 : Upper (D 8) (R 8) [288,5,192,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6423 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6424 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 289 7 196 73 176 40 114 178 306), lower := (rows 289 7 196 73 176 40 64 128 256), losses := [] }

theorem u6424 : Upper (D 8) (R 8) [288,5,192,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6424 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6425 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 289 7 196 73 176 48 106 170 298), lower := (rows 289 7 196 73 176 48 64 128 256), losses := [] }

theorem u6425 : Upper (D 8) (R 8) [288,5,192,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6425 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6426 : PairBound 9 := { available := 42, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 88 176 33 106 170 298), lower := (rows 289 7 196 88 176 33 64 128 256), losses := [] }

theorem u6426 : Upper (D 8) (R 8) [288,5,192,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6426 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6427 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 289 7 196 88 176 34 105 169 297), lower := (rows 289 7 196 88 176 34 64 128 256), losses := [] }

theorem u6427 : Upper (D 8) (R 8) [288,5,192,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6427 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6428 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 289 7 196 88 176 40 99 163 291), lower := (rows 289 7 196 88 176 40 64 128 256), losses := [] }

theorem u6428 : Upper (D 8) (R 8) [288,5,192,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6428 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6429 : PairBound 9 := { available := 26, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 104 176 33 90 154 282), lower := (rows 289 7 196 104 176 33 64 128 256), losses := [] }

theorem u6429 : Upper (D 8) (R 8) [288,5,192,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6429 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6430 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 289 7 196 104 176 34 89 153 281), lower := (rows 289 7 196 104 176 34 64 128 256), losses := [] }

theorem u6430 : Upper (D 8) (R 8) [288,5,192,96,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6430 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6431 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 289 7 196 104 176 40 83 147 275), lower := (rows 289 7 196 104 176 40 64 128 256), losses := [] }

theorem u6431 : Upper (D 8) (R 8) [288,5,192,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6431 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6432 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 22 73 145 96 224 160 416), lower := (rows 289 14 22 73 145 96 64 128 256), losses := [] }

theorem u6432 : Upper (D 8) (R 8) [288,12,18,65,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6433 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 22 73 176 33 224 224 480), lower := (rows 289 14 22 73 176 33 64 128 256), losses := [] }

theorem u6433 : Upper (D 8) (R 8) [288,12,18,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6433 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6434 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 22 73 176 96 225 161 417), lower := (rows 289 14 22 73 176 96 64 128 256), losses := [] }

theorem u6434 : Upper (D 8) (R 8) [288,12,18,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6435 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 22 73 176 160 97 225 353), lower := (rows 289 14 22 73 176 160 64 128 256), losses := [] }

theorem u6435 : Upper (D 8) (R 8) [288,12,18,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6435 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6436 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 22 104 176 33 193 193 449), lower := (rows 289 14 22 104 176 33 64 128 256), losses := [] }

theorem u6436 : Upper (D 8) (R 8) [288,12,18,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6436 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6437 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 22 104 176 96 193 129 385), lower := (rows 289 14 22 104 176 96 64 128 256), losses := [] }

theorem u6437 : Upper (D 8) (R 8) [288,12,18,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6437 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6438 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 289 14 38 73 145 48 224 224 480), lower := (rows 289 14 38 73 145 48 64 128 256), losses := [] }

theorem u6438 : Upper (D 8) (R 8) [288,12,34,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6438 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6439 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 38, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 38 73 145 96 240 176 432), lower := (rows 289 14 38 73 145 96 64 128 256), losses := [] }

theorem u6439 : Upper (D 8) (R 8) [288,12,34,65,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6439 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6440 : Route 9 := (fun mask => (mask,id))

def c6440 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6440 : Upper (D 8) (R 8) [288,12,34,65,129,128] 13 := by
  apply FastRouting.sound _ _ [288,12,34,65,129,128] 13 (by decide) (choices 1) [16,32] r6440 c6440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u819
  · exact u820

def b6441 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 289 14 38 73 176 33 208 208 464), lower := (rows 289 14 38 73 176 33 64 128 256), losses := [] }

theorem u6441 : Upper (D 8) (R 8) [288,12,34,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6441 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6442 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 14 38 73 176 48 193 193 449), lower := (rows 289 14 38 73 176 48 64 128 256), losses := [] }

theorem u6442 : Upper (D 8) (R 8) [288,12,34,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6442 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6443 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 38, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 38 73 176 96 209 145 401), lower := (rows 289 14 38 73 176 96 64 128 256), losses := [] }

theorem u6443 : Upper (D 8) (R 8) [288,12,34,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6444 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 38 73 176 160 81 209 337), lower := (rows 289 14 38 73 176 160 64 128 256), losses := [] }

theorem u6444 : Upper (D 8) (R 8) [288,12,34,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6445 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 38 88 145 33 224 224 480), lower := (rows 289 14 38 88 145 33 64 128 256), losses := [] }

theorem u6445 : Upper (D 8) (R 8) [288,12,34,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6445 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6446 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 38, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 38 88 145 96 225 161 417), lower := (rows 289 14 38 88 145 96 64 128 256), losses := [] }

theorem u6446 : Upper (D 8) (R 8) [288,12,34,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6446 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6447 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 38 88 145 160 97 225 353), lower := (rows 289 14 38 88 145 160 64 128 256), losses := [] }

theorem u6447 : Upper (D 8) (R 8) [288,12,34,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6447 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6448 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 38 88 176 33 193 193 449), lower := (rows 289 14 38 88 176 33 64 128 256), losses := [] }

theorem u6448 : Upper (D 8) (R 8) [288,12,34,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6448 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6449 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 38, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 38 88 176 96 193 129 385), lower := (rows 289 14 38 88 176 96 64 128 256), losses := [] }

theorem u6449 : Upper (D 8) (R 8) [288,12,34,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6450 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 38 88 176 160 65 193 321), lower := (rows 289 14 38 88 176 160 64 128 256), losses := [] }

theorem u6450 : Upper (D 8) (R 8) [288,12,34,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6451 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 289 14 52 73 145 34 224 224 480), lower := (rows 289 14 52 73 145 34 64 128 256), losses := [] }

theorem u6451 : Upper (D 8) (R 8) [288,12,48,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6451 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6452 : Route 9 := (fun mask => (mask,id))

def c6452 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u6452 : Upper (D 8) (R 8) [288,12,48,65,129,64] 13 := by
  apply FastRouting.sound _ _ [288,12,48,65,129,64] 13 (by decide) (choices 1) [2,32,128] r6452 c6452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u821
  · exact u822
  · exact u823

def b6453 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 52 73 145 160 98 226 354), lower := (rows 289 14 52 73 145 160 64 128 256), losses := [] }

theorem u6453 : Upper (D 8) (R 8) [288,12,48,65,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6453 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6454 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 73 146 33 224 224 480), lower := (rows 289 14 52 73 146 33 64 128 256), losses := [] }

theorem u6454 : Upper (D 8) (R 8) [288,12,48,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6455 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 73 146 96 225 161 417), lower := (rows 289 14 52 73 146 96 64 128 256), losses := [] }

theorem u6455 : Upper (D 8) (R 8) [288,12,48,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6455 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6456 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 52 73 146 160 97 225 353), lower := (rows 289 14 52 73 146 160 64 128 256), losses := [] }

theorem u6456 : Upper (D 8) (R 8) [288,12,48,65,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6456 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6457 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 52 74 145 33 224 224 480), lower := (rows 289 14 52 74 145 33 64 128 256), losses := [] }

theorem u6457 : Upper (D 8) (R 8) [288,12,48,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6457 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6458 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 74 145 96 225 161 417), lower := (rows 289 14 52 74 145 96 64 128 256), losses := [] }

theorem u6458 : Upper (D 8) (R 8) [288,12,48,66,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6459 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 52 74 145 160 97 225 353), lower := (rows 289 14 52 74 145 160 64 128 256), losses := [] }

theorem u6459 : Upper (D 8) (R 8) [288,12,48,66,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6459 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6460 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 52 104 145 33 194 194 450), lower := (rows 289 14 52 104 145 33 64 128 256), losses := [] }

theorem u6460 : Upper (D 8) (R 8) [288,12,48,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6461 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 14 52 104 145 34 193 193 449), lower := (rows 289 14 52 104 145 34 64 128 256), losses := [] }

theorem u6461 : Upper (D 8) (R 8) [288,12,48,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6461 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6462 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 104 145 96 195 131 387), lower := (rows 289 14 52 104 145 96 64 128 256), losses := [] }

theorem u6462 : Upper (D 8) (R 8) [288,12,48,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6463 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 52 104 145 160 67 195 323), lower := (rows 289 14 52 104 145 160 64 128 256), losses := [] }

theorem u6463 : Upper (D 8) (R 8) [288,12,48,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6464 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 104 146 33 193 193 449), lower := (rows 289 14 52 104 146 33 64 128 256), losses := [] }

theorem u6464 : Upper (D 8) (R 8) [288,12,48,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6465 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 104 146 96 193 129 385), lower := (rows 289 14 52 104 146 96 64 128 256), losses := [] }

theorem u6465 : Upper (D 8) (R 8) [288,12,48,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6466 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 52 104 146 160 65 193 321), lower := (rows 289 14 52 104 146 160 64 128 256), losses := [] }

theorem u6466 : Upper (D 8) (R 8) [288,12,48,96,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6467 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 152 50 33 224 224 480), lower := (rows 289 14 69 152 50 33 64 128 256), losses := [] }

theorem u6467 : Upper (D 8) (R 8) [288,12,65,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6467 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6468 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 152 50 96 225 161 417), lower := (rows 289 14 69 152 50 96 64 128 256), losses := [] }

theorem u6468 : Upper (D 8) (R 8) [288,12,65,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6469 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 152 50 160 97 225 353), lower := (rows 289 14 69 152 50 160 64 128 256), losses := [] }

theorem u6469 : Upper (D 8) (R 8) [288,12,65,144,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6470 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 168 50 33 208 208 464), lower := (rows 289 14 69 168 50 33 64 128 256), losses := [] }

theorem u6470 : Upper (D 8) (R 8) [288,12,65,160,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6471 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 14 69 168 50 48 193 193 449), lower := (rows 289 14 69 168 50 48 64 128 256), losses := [] }

theorem u6471 : Upper (D 8) (R 8) [288,12,65,160,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6471 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6472 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 168 50 96 209 145 401), lower := (rows 289 14 69 168 50 96 64 128 256), losses := [] }

theorem u6472 : Upper (D 8) (R 8) [288,12,65,160,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6473 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 168 50 160 81 209 337), lower := (rows 289 14 69 168 50 160 64 128 256), losses := [] }

theorem u6473 : Upper (D 8) (R 8) [288,12,65,160,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6474 : PairBound 9 := { available := 146, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 168 112 33 210 146 402), lower := (rows 289 14 69 168 112 33 64 128 256), losses := [] }

theorem u6474 : Upper (D 8) (R 8) [288,12,65,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6474 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6475 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 289 14 69 168 112 34 209 145 401), lower := (rows 289 14 69 168 112 34 64 128 256), losses := [] }

theorem u6475 : Upper (D 8) (R 8) [288,12,65,160,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6475 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6476 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 289 14 69 168 112 48 195 131 387), lower := (rows 289 14 69 168 112 48 64 128 256), losses := [] }

theorem u6476 : Upper (D 8) (R 8) [288,12,65,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6476 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6477 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 168 112 160 83 147 275), lower := (rows 289 14 69 168 112 160 64 128 256), losses := [] }

theorem u6477 : Upper (D 8) (R 8) [288,12,65,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6478 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 289 14 69 168 145 34 112 240 368), lower := (rows 289 14 69 168 145 34 64 128 256), losses := [] }

theorem u6478 : Upper (D 8) (R 8) [288,12,65,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6478 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6479 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 289 14 69 168 145 48 98 226 354), lower := (rows 289 14 69 168 145 48 64 128 256), losses := [] }

theorem u6479 : Upper (D 8) (R 8) [288,12,65,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6479 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u6479
end Delivery.IrregularNine14.P08
