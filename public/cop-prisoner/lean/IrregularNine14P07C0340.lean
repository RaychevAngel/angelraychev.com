import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0094

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20400 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 44, targets := 1 }], pairs := [(2,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 104 273 160 85 149 277), lower := (rows 35 194 14 104 273 160 64 128 256), losses := [] }

theorem u20400 : Upper (D 7) (R 7) [34,192,10,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20401 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 14 104 276 33 209 145 401), lower := (rows 35 194 14 104 276 33 64 128 256), losses := [] }

theorem u20401 : Upper (D 7) (R 7) [34,192,10,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20402 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 35 194 14 104 276 48 193 129 385), lower := (rows 35 194 14 104 276 48 64 128 256), losses := [] }

theorem u20402 : Upper (D 7) (R 7) [34,192,10,96,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20402 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20403 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 44, targets := 1 }], pairs := [(2,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 104 276 160 81 145 273), lower := (rows 35 194 14 104 276 160 64 128 256), losses := [] }

theorem u20403 : Upper (D 7) (R 7) [34,192,10,96,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20404 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 14 104 400 33 85 149 277), lower := (rows 35 194 14 104 400 33 64 128 256), losses := [] }

theorem u20404 : Upper (D 7) (R 7) [34,192,10,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20405 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 104 400 36 81 145 273), lower := (rows 35 194 14 104 400 36 64 128 256), losses := [] }

theorem u20405 : Upper (D 7) (R 7) [34,192,10,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20405 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20406 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(2,7),(3,7)], upper := (rows 35 194 14 104 400 48 69 133 261), lower := (rows 35 194 14 104 400 48 64 128 256), losses := [] }

theorem u20406 : Upper (D 7) (R 7) [34,192,10,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20406 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20407 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 194 14 265 52 33 208 208 464), lower := (rows 35 194 14 265 52 33 64 128 256), losses := [] }

theorem u20407 : Upper (D 7) (R 7) [34,192,10,257,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20408 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 35 194 14 265 52 48 193 193 449), lower := (rows 35 194 14 265 52 48 64 128 256), losses := [] }

theorem u20408 : Upper (D 7) (R 7) [34,192,10,257,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20408 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20409 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 194 14 265 52 96 209 145 401), lower := (rows 35 194 14 265 52 96 64 128 256), losses := [] }

theorem u20409 : Upper (D 7) (R 7) [34,192,10,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20410 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 194 14 265 81 36 240 176 432), lower := (rows 35 194 14 265 81 36 64 128 256), losses := [] }

theorem u20410 : Upper (D 7) (R 7) [34,192,10,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20410 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20411 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 194 14 265 81 48 228 164 420), lower := (rows 35 194 14 265 81 48 64 128 256), losses := [] }

theorem u20411 : Upper (D 7) (R 7) [34,192,10,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20411 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20412 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 265 81 160 116 180 308), lower := (rows 35 194 14 265 81 160 64 128 256), losses := [] }

theorem u20412 : Upper (D 7) (R 7) [34,192,10,257,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20413 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(4,1)], upper := (rows 35 194 14 265 84 33 240 176 432), lower := (rows 35 194 14 265 84 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 41 68 132 260), good := (rows 33 192 508 297 468 33 64 128 256) },{ target := 6, region := (rows 7 2 4 24 16 63 0 144 272), good := (rows 35 163 47 297 445 33 0 128 256) }] }

theorem u20413 : Upper (D 7) (R 7) [34,192,10,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20414 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 0, region := 392, targets := 2 }], pairs := [(2,6),(3,1),(3,6)], upper := (rows 35 194 14 265 84 48 225 161 417), lower := (rows 35 194 14 265 84 48 64 128 256), losses := [] }

theorem u20414 : Upper (D 7) (R 7) [34,192,10,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20414 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20415 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 265 84 160 113 177 305), lower := (rows 35 194 14 265 84 160 64 128 256), losses := [] }

theorem u20415 : Upper (D 7) (R 7) [34,192,10,257,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20416 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,7)], upper := (rows 35 194 14 265 112 33 212 148 404), lower := (rows 35 194 14 265 112 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 41 68 132 260), good := (rows 33 192 508 297 112 33 64 128 256) }] }

theorem u20416 : Upper (D 7) (R 7) [34,192,10,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20416 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20417 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 194 14 265 112 36 209 145 401), lower := (rows 35 194 14 265 112 36 64 128 256), losses := [] }

theorem u20417 : Upper (D 7) (R 7) [34,192,10,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20417 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20418 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 14 265 112 48 197 133 389), lower := (rows 35 194 14 265 112 48 64 128 256), losses := [] }

theorem u20418 : Upper (D 7) (R 7) [34,192,10,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20418 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20419 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(2,7),(3,7),(4,0),(4,7)], upper := (rows 35 194 14 265 112 160 85 149 277), lower := (rows 35 194 14 265 112 160 64 128 256), losses := [] }

theorem u20419 : Upper (D 7) (R 7) [34,192,10,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20420 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,7)], upper := (rows 35 194 14 268 81 33 240 176 432), lower := (rows 35 194 14 268 81 33 64 128 256), losses := [] }

theorem u20420 : Upper (D 7) (R 7) [34,192,10,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20421 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 194 14 268 81 48 225 161 417), lower := (rows 35 194 14 268 81 48 64 128 256), losses := [] }

theorem u20421 : Upper (D 7) (R 7) [34,192,10,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20421 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20422 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 0, region := 80, targets := 2 }], pairs := [(2,7),(3,7),(4,1),(4,7)], upper := (rows 35 194 14 268 81 160 113 177 305), lower := (rows 35 194 14 268 81 160 64 128 256), losses := [] }

theorem u20422 : Upper (D 7) (R 7) [34,192,10,260,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20423 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,7)], upper := (rows 35 194 14 268 112 33 209 145 401), lower := (rows 35 194 14 268 112 33 64 128 256), losses := [] }

theorem u20423 : Upper (D 7) (R 7) [34,192,10,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20424 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 14 268 112 48 193 129 385), lower := (rows 35 194 14 268 112 48 64 128 256), losses := [] }

theorem u20424 : Upper (D 7) (R 7) [34,192,10,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20424 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20425 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 0, region := 80, targets := 2 }], pairs := [(2,7),(3,7),(4,1),(4,7)], upper := (rows 35 194 14 268 112 160 81 145 273), lower := (rows 35 194 14 268 112 160 64 128 256), losses := [] }

theorem u20425 : Upper (D 7) (R 7) [34,192,10,260,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20426 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 194 14 280 52 33 193 193 449), lower := (rows 35 194 14 280 52 33 64 128 256), losses := [] }

theorem u20426 : Upper (D 7) (R 7) [34,192,10,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20427 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 194 14 280 52 96 193 129 385), lower := (rows 35 194 14 280 52 96 64 128 256), losses := [] }

theorem u20427 : Upper (D 7) (R 7) [34,192,10,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20428 : Route 9 := (fun mask => (mask,id))

def c20428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20428 : Upper (D 7) (R 7) [34,192,10,272,65,1] 13 := by
  apply FastRouting.sound _ _ [34,192,10,272,65,1] 13 (by decide) (choices 1) [4,32,128] r20428 c20428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5679
  · exact u5680
  · exact u5681

def b20429 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 194 14 280 81 36 225 161 417), lower := (rows 35 194 14 280 81 36 64 128 256), losses := [] }

theorem u20429 : Upper (D 7) (R 7) [34,192,10,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20429 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20430 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 280 81 160 101 165 293), lower := (rows 35 194 14 280 81 160 64 128 256), losses := [] }

theorem u20430 : Upper (D 7) (R 7) [34,192,10,272,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20431 : Route 9 := (fun mask => (mask,id))

def c20431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20431 : Upper (D 7) (R 7) [34,192,10,272,68,1] 13 := by
  apply FastRouting.sound _ _ [34,192,10,272,68,1] 13 (by decide) (choices 1) [1,32,128] r20431 c20431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5682
  · exact u5683
  · exact u5684

def b20432 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 280 84 160 97 161 289), lower := (rows 35 194 14 280 84 160 64 128 256), losses := [] }

theorem u20432 : Upper (D 7) (R 7) [34,192,10,272,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20433 : Route 9 := (fun mask => (mask,id))

def c20433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20433 : Upper (D 7) (R 7) [34,192,10,272,96,1] 13 := by
  apply FastRouting.sound _ _ [34,192,10,272,96,1] 13 (by decide) (choices 1) [1,4,128] r20433 c20433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5685
  · exact u5686
  · exact u5687

def b20434 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 194 14 280 112 36 193 129 385), lower := (rows 35 194 14 280 112 36 64 128 256), losses := [] }

theorem u20434 : Upper (D 7) (R 7) [34,192,10,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20434 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20435 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(2,7),(3,7),(4,0),(4,7)], upper := (rows 35 194 14 280 112 160 69 133 261), lower := (rows 35 194 14 280 112 160 64 128 256), losses := [] }

theorem u20435 : Upper (D 7) (R 7) [34,192,10,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20436 : Route 9 := (fun mask => (mask,id))

def c20436 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20436 : Upper (D 7) (R 7) [34,192,10,288,65,1] 13 := by
  apply FastRouting.sound _ _ [34,192,10,288,65,1] 13 (by decide) (choices 1) [4,16,128] r20436 c20436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5688
  · exact u5689
  · exact u5690

def b20437 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 194 14 296 81 36 209 145 401), lower := (rows 35 194 14 296 81 36 64 128 256), losses := [] }

theorem u20437 : Upper (D 7) (R 7) [34,192,10,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20437 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20438 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 194 14 296 81 48 197 133 389), lower := (rows 35 194 14 296 81 48 64 128 256), losses := [] }

theorem u20438 : Upper (D 7) (R 7) [34,192,10,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20438 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20439 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 296 81 160 85 149 277), lower := (rows 35 194 14 296 81 160 64 128 256), losses := [] }

theorem u20439 : Upper (D 7) (R 7) [34,192,10,288,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20440 : Route 9 := (fun mask => (mask,id))

def c20440 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20440 : Upper (D 7) (R 7) [34,192,10,288,68,1] 13 := by
  apply FastRouting.sound _ _ [34,192,10,288,68,1] 13 (by decide) (choices 1) [1,16,128] r20440 c20440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5691
  · exact u5692
  · exact u5693

def b20441 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 0, region := 392, targets := 2 }], pairs := [(2,6),(3,1),(3,6)], upper := (rows 35 194 14 296 84 48 193 129 385), lower := (rows 35 194 14 296 84 48 64 128 256), losses := [] }

theorem u20441 : Upper (D 7) (R 7) [34,192,10,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20441 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20442 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 296 84 160 81 145 273), lower := (rows 35 194 14 296 84 160 64 128 256), losses := [] }

theorem u20442 : Upper (D 7) (R 7) [34,192,10,288,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20443 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 2, region := 49, targets := 64 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 194 14 328 52 33 209 145 401), lower := (rows 35 194 14 328 52 33 64 128 256), losses := [] }

theorem u20443 : Upper (D 7) (R 7) [34,192,10,320,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20444 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 14 328 52 48 193 129 385), lower := (rows 35 194 14 328 52 48 64 128 256), losses := [] }

theorem u20444 : Upper (D 7) (R 7) [34,192,10,320,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20444 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20445 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 328 52 160 81 145 273), lower := (rows 35 194 14 328 52 160 64 128 256), losses := [] }

theorem u20445 : Upper (D 7) (R 7) [34,192,10,320,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20446 : Route 9 := (fun mask => (mask,id))

def c20446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20446 : Upper (D 7) (R 7) [34,192,10,320,129,1] 13 := by
  apply FastRouting.sound _ _ [34,192,10,320,129,1] 13 (by decide) (choices 1) [4,16,32] r20446 c20446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5694
  · exact u5695
  · exact u5696

def b20447 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 194 14 328 145 36 113 177 305), lower := (rows 35 194 14 328 145 36 64 128 256), losses := [] }

theorem u20447 : Upper (D 7) (R 7) [34,192,10,320,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20447 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20448 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(2,7),(3,7)], upper := (rows 35 194 14 328 145 48 101 165 293), lower := (rows 35 194 14 328 145 48 64 128 256), losses := [] }

theorem u20448 : Upper (D 7) (R 7) [34,192,10,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20448 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20449 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 194 14 328 148 33 113 177 305), lower := (rows 35 194 14 328 148 33 64 128 256), losses := [{ target := 7, region := (rows 7 2 4 24 16 55 80 0 272), good := (rows 35 99 47 328 381 33 64 0 256) }] }

theorem u20449 : Upper (D 7) (R 7) [34,192,10,320,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20450 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6),(2,7),(3,7)], upper := (rows 35 194 14 328 148 48 97 161 289), lower := (rows 35 194 14 328 148 48 64 128 256), losses := [] }

theorem u20450 : Upper (D 7) (R 7) [34,192,10,320,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20450 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20451 : Route 9 := (fun mask => (mask,id))

def c20451 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20451 : Upper (D 7) (R 7) [34,192,10,320,160,1] 13 := by
  apply FastRouting.sound _ _ [34,192,10,320,160,1] 13 (by decide) (choices 1) [1,4,16] r20451 c20451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5697
  · exact u5698
  · exact u5699

def b20452 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 194 14 328 176 36 81 145 273), lower := (rows 35 194 14 328 176 36 64 128 256), losses := [] }

theorem u20452 : Upper (D 7) (R 7) [34,192,10,320,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20452 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20453 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 14 328 176 48 69 133 261), lower := (rows 35 194 14 328 176 48 64 128 256), losses := [] }

theorem u20453 : Upper (D 7) (R 7) [34,192,10,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20453 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20454 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 44, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 194 28 44 273 33 194 194 450), lower := (rows 35 194 28 44 273 33 64 128 256), losses := [] }

theorem u20454 : Upper (D 7) (R 7) [34,192,24,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20455 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 194 28 44 273 34 193 193 449), lower := (rows 35 194 28 44 273 34 64 128 256), losses := [] }

theorem u20455 : Upper (D 7) (R 7) [34,192,24,36,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20456 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 194 28 44 273 96 195 131 387), lower := (rows 35 194 28 44 273 96 64 128 256), losses := [] }

theorem u20456 : Upper (D 7) (R 7) [34,192,24,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20457 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 28 44 274 33 193 193 449), lower := (rows 35 194 28 44 274 33 64 128 256), losses := [] }

theorem u20457 : Upper (D 7) (R 7) [34,192,24,36,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20458 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 194 28 44 274 96 193 129 385), lower := (rows 35 194 28 44 274 96 64 128 256), losses := [] }

theorem u20458 : Upper (D 7) (R 7) [34,192,24,36,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20459 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(4,5)], upper := (rows 35 194 28 44 336 33 195 131 387), lower := (rows 35 194 28 44 336 33 64 128 256), losses := [] }

theorem u20459 : Upper (D 7) (R 7) [34,192,24,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u20459
end Delivery.IrregularNine14.P07
