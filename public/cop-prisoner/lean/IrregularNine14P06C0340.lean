import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0101

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20400 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 134 73 273 40 116 180 308), lower := (rows 35 70 134 73 273 40 64 128 256), losses := [] }

theorem u20400 : Upper (D 6) (R 6) [34,68,130,65,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20400 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20401 : Route 9 := (fun mask => (mask,id))

def c20401 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20401 : Upper (D 6) (R 6) [34,68,130,65,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,130,65,257,16] 13 (by decide) (choices 1) [4,8,32] r20401 c20401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6060
  · exact u6061
  · exact u6062

def b20402 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 134 73 276 33 120 184 312), lower := (rows 35 70 134 73 276 33 64 128 256), losses := [] }

theorem u20402 : Upper (D 6) (R 6) [34,68,130,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20403 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 134 73 276 40 113 177 305), lower := (rows 35 70 134 73 276 40 64 128 256), losses := [] }

theorem u20403 : Upper (D 6) (R 6) [34,68,130,65,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20403 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20404 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 72, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 70 134 73 276 48 105 169 297), lower := (rows 35 70 134 73 276 48 64 128 256), losses := [] }

theorem u20404 : Upper (D 6) (R 6) [34,68,130,65,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20404 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20405 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 134 73 280 33 116 180 308), lower := (rows 35 70 134 73 280 33 64 128 256), losses := [] }

theorem u20405 : Upper (D 6) (R 6) [34,68,130,65,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20406 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 73 280 36 113 177 305), lower := (rows 35 70 134 73 280 36 64 128 256), losses := [] }

theorem u20406 : Upper (D 6) (R 6) [34,68,130,65,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20407 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 134 73 280 48 101 165 293), lower := (rows 35 70 134 73 280 48 64 128 256), losses := [{ target := 6, region := (rows 1 2 5 8 24 56 0 137 265), good := (rows 423 6 134 445 440 48 0 128 256) }] }

theorem u20407 : Upper (D 6) (R 6) [34,68,130,65,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20407 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20408 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 134 73 304 33 92 156 284), lower := (rows 35 70 134 73 304 33 64 128 256), losses := [] }

theorem u20408 : Upper (D 6) (R 6) [34,68,130,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20409 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 73 304 36 89 153 281), lower := (rows 35 70 134 73 304 36 64 128 256), losses := [] }

theorem u20409 : Upper (D 6) (R 6) [34,68,130,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20410 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 134 73 304 40 85 149 277), lower := (rows 35 70 134 73 304 40 64 128 256), losses := [] }

theorem u20410 : Upper (D 6) (R 6) [34,68,130,65,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20410 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20411 : PairBound 9 := { available := 13, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 134 73 304 48 77 141 269), lower := (rows 35 70 134 73 304 48 64 128 256), losses := [] }

theorem u20411 : Upper (D 6) (R 6) [34,68,130,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20411 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20412 : Route 9 := (fun mask => (mask,id))

def c20412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20412 : Upper (D 6) (R 6) [34,68,130,80,257,1] 13 := by
  apply FastRouting.sound _ _ [34,68,130,80,257,1] 13 (by decide) (choices 1) [4,8,32] r20412 c20412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6063
  · exact u6064
  · exact u6065

def b20413 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 88 273 36 105 169 297), lower := (rows 35 70 134 88 273 36 64 128 256), losses := [] }

theorem u20413 : Upper (D 6) (R 6) [34,68,130,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20414 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 134 88 273 40 101 165 293), lower := (rows 35 70 134 88 273 40 64 128 256), losses := [] }

theorem u20414 : Upper (D 6) (R 6) [34,68,130,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20414 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20415 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 134 88 276 33 105 169 297), lower := (rows 35 70 134 88 276 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 24 16 55 80 144 272), good := (rows 35 99 163 504 505 33 64 128 256) }] }

theorem u20415 : Upper (D 6) (R 6) [34,68,130,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20416 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 134 88 276 40 97 161 289), lower := (rows 35 70 134 88 276 40 64 128 256), losses := [] }

theorem u20416 : Upper (D 6) (R 6) [34,68,130,80,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20416 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20417 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 70 134 88 280 33 101 165 293), lower := (rows 35 70 134 88 280 33 64 128 256), losses := [] }

theorem u20417 : Upper (D 6) (R 6) [34,68,130,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20418 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 88 280 36 97 161 289), lower := (rows 35 70 134 88 280 36 64 128 256), losses := [] }

theorem u20418 : Upper (D 6) (R 6) [34,68,130,80,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20419 : Route 9 := (fun mask => (mask,id))

def c20419 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20419 : Upper (D 6) (R 6) [34,68,130,80,288,1] 13 := by
  apply FastRouting.sound _ _ [34,68,130,80,288,1] 13 (by decide) (choices 1) [1,4,8] r20419 c20419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6066
  · exact u6067
  · exact u6068

def b20420 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 88 304 36 73 137 265), lower := (rows 35 70 134 88 304 36 64 128 256), losses := [] }

theorem u20420 : Upper (D 6) (R 6) [34,68,130,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20421 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 88 304 40 69 133 261), lower := (rows 35 70 134 88 304 40 64 128 256), losses := [] }

theorem u20421 : Upper (D 6) (R 6) [34,68,130,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20421 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20422 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 134 104 273 33 92 156 284), lower := (rows 35 70 134 104 273 33 64 128 256), losses := [] }

theorem u20422 : Upper (D 6) (R 6) [34,68,130,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20423 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 104 273 36 89 153 281), lower := (rows 35 70 134 104 273 36 64 128 256), losses := [] }

theorem u20423 : Upper (D 6) (R 6) [34,68,130,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20424 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 104 273 40 85 149 277), lower := (rows 35 70 134 104 273 40 64 128 256), losses := [] }

theorem u20424 : Upper (D 6) (R 6) [34,68,130,96,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20424 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20425 : Route 9 := (fun mask => (mask,id))

def c20425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20425 : Upper (D 6) (R 6) [34,68,130,96,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,130,96,257,16] 13 (by decide) (choices 1) [1,4,8] r20425 c20425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6069
  · exact u6070
  · exact u6071

def b20426 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 134 104 276 33 89 153 281), lower := (rows 35 70 134 104 276 33 64 128 256), losses := [] }

theorem u20426 : Upper (D 6) (R 6) [34,68,130,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20427 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 104 276 40 81 145 273), lower := (rows 35 70 134 104 276 40 64 128 256), losses := [] }

theorem u20427 : Upper (D 6) (R 6) [34,68,130,96,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20427 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20428 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 72, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 70 134 104 276 48 73 137 265), lower := (rows 35 70 134 104 276 48 64 128 256), losses := [] }

theorem u20428 : Upper (D 6) (R 6) [34,68,130,96,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20428 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20429 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 134 104 280 33 85 149 277), lower := (rows 35 70 134 104 280 33 64 128 256), losses := [] }

theorem u20429 : Upper (D 6) (R 6) [34,68,130,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20430 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 104 280 36 81 145 273), lower := (rows 35 70 134 104 280 36 64 128 256), losses := [] }

theorem u20430 : Upper (D 6) (R 6) [34,68,130,96,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20431 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 104 280 48 69 133 261), lower := (rows 35 70 134 104 280 48 64 128 256), losses := [] }

theorem u20431 : Upper (D 6) (R 6) [34,68,130,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20431 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20432 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 13 81 34 368 432 304), lower := (rows 35 70 140 13 81 34 64 128 256), losses := [] }

theorem u20432 : Upper (D 6) (R 6) [34,68,136,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20433 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 140 13 81 48 354 418 290), lower := (rows 35 70 140 13 81 48 64 128 256), losses := [] }

theorem u20433 : Upper (D 6) (R 6) [34,68,136,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20433 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20434 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 305, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 70 140 13 81 288 114 178 306), lower := (rows 35 70 140 13 81 288 64 128 256), losses := [] }

theorem u20434 : Upper (D 6) (R 6) [34,68,136,5,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20434 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20435 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 13 112 33 338 402 274), lower := (rows 35 70 140 13 112 33 64 128 256), losses := [] }

theorem u20435 : Upper (D 6) (R 6) [34,68,136,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20436 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 13 112 34 337 401 273), lower := (rows 35 70 140 13 112 34 64 128 256), losses := [] }

theorem u20436 : Upper (D 6) (R 6) [34,68,136,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20437 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 140 13 112 48 323 387 259), lower := (rows 35 70 140 13 112 48 64 128 256), losses := [] }

theorem u20437 : Upper (D 6) (R 6) [34,68,136,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20437 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20438 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 305, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 70 140 13 112 288 83 147 275), lower := (rows 35 70 140 13 112 288 64 128 256), losses := [] }

theorem u20438 : Upper (D 6) (R 6) [34,68,136,5,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20438 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20439 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 13 273 34 112 240 368), lower := (rows 35 70 140 13 273 34 64 128 256), losses := [] }

theorem u20439 : Upper (D 6) (R 6) [34,68,136,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20440 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 305, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 70 140 13 273 48 98 226 354), lower := (rows 35 70 140 13 273 48 64 128 256), losses := [] }

theorem u20440 : Upper (D 6) (R 6) [34,68,136,5,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20440 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20441 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 13 273 96 114 178 306), lower := (rows 35 70 140 13 273 96 64 128 256), losses := [] }

theorem u20441 : Upper (D 6) (R 6) [34,68,136,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20442 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 305, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 13 274 33 112 240 368), lower := (rows 35 70 140 13 274 33 64 128 256), losses := [] }

theorem u20442 : Upper (D 6) (R 6) [34,68,136,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20443 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 140 13 274 48 97 225 353), lower := (rows 35 70 140 13 274 48 64 128 256), losses := [] }

theorem u20443 : Upper (D 6) (R 6) [34,68,136,5,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20443 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20444 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 13 274 96 113 177 305), lower := (rows 35 70 140 13 274 96 64 128 256), losses := [] }

theorem u20444 : Upper (D 6) (R 6) [34,68,136,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20445 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 305, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 13 304 33 82 210 338), lower := (rows 35 70 140 13 304 33 64 128 256), losses := [] }

theorem u20445 : Upper (D 6) (R 6) [34,68,136,5,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20446 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 13 304 34 81 209 337), lower := (rows 35 70 140 13 304 34 64 128 256), losses := [] }

theorem u20446 : Upper (D 6) (R 6) [34,68,136,5,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20447 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 140 13 304 48 67 195 323), lower := (rows 35 70 140 13 304 48 64 128 256), losses := [] }

theorem u20447 : Upper (D 6) (R 6) [34,68,136,5,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20447 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20448 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 13 304 96 83 147 275), lower := (rows 35 70 140 13 304 96 64 128 256), losses := [] }

theorem u20448 : Upper (D 6) (R 6) [34,68,136,5,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20449 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 305, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 13 336 33 114 178 306), lower := (rows 35 70 140 13 336 33 64 128 256), losses := [] }

theorem u20449 : Upper (D 6) (R 6) [34,68,136,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20450 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 13 336 34 113 177 305), lower := (rows 35 70 140 13 336 34 64 128 256), losses := [] }

theorem u20450 : Upper (D 6) (R 6) [34,68,136,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20451 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 140 13 336 48 99 163 291), lower := (rows 35 70 140 13 336 48 64 128 256), losses := [] }

theorem u20451 : Upper (D 6) (R 6) [34,68,136,5,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20451 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20452 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 140 25 274 33 100 228 356), lower := (rows 35 70 140 25 274 33 64 128 256), losses := [] }

theorem u20452 : Upper (D 6) (R 6) [34,68,136,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20453 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 140 25 274 36 97 225 353), lower := (rows 35 70 140 25 274 36 64 128 256), losses := [] }

theorem u20453 : Upper (D 6) (R 6) [34,68,136,17,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20454 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 25 274 96 101 165 293), lower := (rows 35 70 140 25 274 96 64 128 256), losses := [] }

theorem u20454 : Upper (D 6) (R 6) [34,68,136,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20455 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 140 25 276 33 98 226 354), lower := (rows 35 70 140 25 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 24 32 65 129 257), good := (rows 482 70 158 478 276 480 64 128 256) }] }

theorem u20455 : Upper (D 6) (R 6) [34,68,136,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20456 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 25 276 34 97 225 353), lower := (rows 35 70 140 25 276 34 64 128 256), losses := [] }

theorem u20456 : Upper (D 6) (R 6) [34,68,136,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20457 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 140 25 276 96 99 163 291), lower := (rows 35 70 140 25 276 96 64 128 256), losses := [] }

theorem u20457 : Upper (D 6) (R 6) [34,68,136,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20458 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 140 25 304 33 70 198 326), lower := (rows 35 70 140 25 304 33 64 128 256), losses := [] }

theorem u20458 : Upper (D 6) (R 6) [34,68,136,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20459 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 140 25 304 34 69 197 325), lower := (rows 35 70 140 25 304 34 64 128 256), losses := [] }

theorem u20459 : Upper (D 6) (R 6) [34,68,136,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20459
end Delivery.IrregularNine14.P06
