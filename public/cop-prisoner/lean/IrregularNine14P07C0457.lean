import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0167
import IrregularNine14P07C0168

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27420 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 28 11 208 33 226 162 418), lower := (rows 37 322 28 11 208 33 64 128 256), losses := [] }

theorem u27420 : Upper (D 7) (R 7) [36,320,24,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27421 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(0,7),(2,1),(4,1)], upper := (rows 37 322 28 11 208 34 225 161 417), lower := (rows 37 322 28 11 208 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 25 32 65 129 257), good := (rows 501 320 28 477 208 32 64 128 256) },{ target := 6, region := (rows 5 2 4 8 16 42 0 141 269), good := (rows 421 290 445 427 144 34 0 128 256) },{ target := 7, region := (rows 5 2 4 8 16 42 64 0 256), good := (rows 37 354 61 43 80 34 64 0 256) }] }

theorem u27421 : Upper (D 7) (R 7) [36,320,24,3,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27422 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 322 28 11 208 160 99 163 291), lower := (rows 37 322 28 11 208 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 320 61 9 240 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 188 0 136 264), good := (rows 37 258 445 427 176 160 0 160 256) }] }

theorem u27422 : Upper (D 7) (R 7) [36,320,24,3,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27423 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 28 42 81 33 194 130 386), lower := (rows 37 322 28 42 81 33 64 128 256), losses := [] }

theorem u27423 : Upper (D 7) (R 7) [36,320,24,34,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27424 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 28 42 81 34 193 129 385), lower := (rows 37 322 28 42 81 34 64 128 256), losses := [] }

theorem u27424 : Upper (D 7) (R 7) [36,320,24,34,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27425 : Route 9 := (fun mask => (mask,id))

def c27425 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27425 : Upper (D 7) (R 7) [36,320,24,34,65,128] 13 := by
  apply FastRouting.sound _ _ [36,320,24,34,65,128] 13 (by decide) (choices 1) [1,2,128] r27425 c27425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10066
  · exact u10067
  · exact u10068

def b27426 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 28 42 145 33 194 194 450), lower := (rows 37 322 28 42 145 33 64 128 256), losses := [] }

theorem u27426 : Upper (D 7) (R 7) [36,320,24,34,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27427 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 322 28 42 145 34 193 193 449), lower := (rows 37 322 28 42 145 34 64 128 256), losses := [] }

theorem u27427 : Upper (D 7) (R 7) [36,320,24,34,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27428 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 149, targets := 64 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(4,6)], upper := (rows 37 322 28 42 145 96 195 131 387), lower := (rows 37 322 28 42 145 96 64 128 256), losses := [] }

theorem u27428 : Upper (D 7) (R 7) [36,320,24,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27429 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 330, targets := 128 }], pairs := [(1,5),(1,7),(3,7),(4,5)], upper := (rows 37 322 28 42 145 160 67 195 323), lower := (rows 37 322 28 42 145 160 64 128 256), losses := [] }

theorem u27429 : Upper (D 7) (R 7) [36,320,24,34,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27430 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 322 28 42 146 33 193 193 449), lower := (rows 37 322 28 42 146 33 64 128 256), losses := [] }

theorem u27430 : Upper (D 7) (R 7) [36,320,24,34,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27431 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 149, targets := 64 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(4,6)], upper := (rows 37 322 28 42 146 96 193 129 385), lower := (rows 37 322 28 42 146 96 64 128 256), losses := [] }

theorem u27431 : Upper (D 7) (R 7) [36,320,24,34,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27432 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 0, region := 322, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(3,6)], upper := (rows 37 322 28 42 146 160 65 193 321), lower := (rows 37 322 28 42 146 160 64 128 256), losses := [] }

theorem u27432 : Upper (D 7) (R 7) [36,320,24,34,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27433 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 28 42 208 33 195 131 387), lower := (rows 37 322 28 42 208 33 64 128 256), losses := [] }

theorem u27433 : Upper (D 7) (R 7) [36,320,24,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27434 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 322 28 42 208 34 193 129 385), lower := (rows 37 322 28 42 208 34 64 128 256), losses := [] }

theorem u27434 : Upper (D 7) (R 7) [36,320,24,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27434 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27435 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 330, targets := 128 }], pairs := [(1,5),(1,7),(3,7),(4,5)], upper := (rows 37 322 28 42 208 160 67 131 259), lower := (rows 37 322 28 42 208 160 64 128 256), losses := [] }

theorem u27435 : Upper (D 7) (R 7) [36,320,24,34,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27436 : Route 9 := (fun mask => (mask,id))

def c27436 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27436 : Upper (D 7) (R 7) [36,320,24,65,129,2] 13 := by
  apply FastRouting.sound _ _ [36,320,24,65,129,2] 13 (by decide) (choices 1) [2,32,128] r27436 c27436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10069
  · exact u10070
  · exact u10071

def b27437 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 0, region := 322, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(3,7)], upper := (rows 37 322 28 73 145 160 98 162 290), lower := (rows 37 322 28 73 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 320 61 73 177 160 64 160 256) }] }

theorem u27437 : Upper (D 7) (R 7) [36,320,24,65,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27438 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 28 73 146 33 226 162 418), lower := (rows 37 322 28 73 146 33 64 128 256), losses := [] }

theorem u27438 : Upper (D 7) (R 7) [36,320,24,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27439 : Route 9 := (fun mask => (mask,id))

def c27439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27439 : Upper (D 7) (R 7) [36,320,24,65,130,2] 13 := by
  apply FastRouting.sound _ _ [36,320,24,65,130,2] 13 (by decide) (choices 1) [1,32,128] r27439 c27439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10072
  · exact u10073
  · exact u10074

def b27440 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 322 28 73 146 160 99 163 291), lower := (rows 37 322 28 73 146 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 320 61 73 176 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 258 61 9 178 160 0 160 256) }] }

theorem u27440 : Upper (D 7) (R 7) [36,320,24,65,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27441 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 28 73 176 33 194 130 386), lower := (rows 37 322 28 73 176 33 64 128 256), losses := [] }

theorem u27441 : Upper (D 7) (R 7) [36,320,24,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27442 : Route 9 := (fun mask => (mask,id))

def c27442 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27442 : Upper (D 7) (R 7) [36,320,24,65,160,2] 13 := by
  apply FastRouting.sound _ _ [36,320,24,65,160,2] 13 (by decide) (choices 1) [1,2,128] r27442 c27442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10075
  · exact u10076
  · exact u10077

def b27443 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 28 73 176 160 67 131 259), lower := (rows 37 322 28 73 176 160 64 128 256), losses := [] }

theorem u27443 : Upper (D 7) (R 7) [36,320,24,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27444 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 28 104 145 33 194 130 386), lower := (rows 37 322 28 104 145 33 64 128 256), losses := [] }

theorem u27444 : Upper (D 7) (R 7) [36,320,24,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27445 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 40, targets := 129 }], pairs := [(1,5),(3,0),(3,7),(4,5)], upper := (rows 37 322 28 104 145 34 195 131 387), lower := (rows 37 322 28 104 145 34 64 128 256), losses := [] }

theorem u27445 : Upper (D 7) (R 7) [36,320,24,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27446 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 330, targets := 128 }], pairs := [(1,5),(1,7),(3,7),(4,5)], upper := (rows 37 322 28 104 145 160 67 131 259), lower := (rows 37 322 28 104 145 160 64 128 256), losses := [] }

theorem u27446 : Upper (D 7) (R 7) [36,320,24,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27447 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 28 104 146 33 195 131 387), lower := (rows 37 322 28 104 146 33 64 128 256), losses := [] }

theorem u27447 : Upper (D 7) (R 7) [36,320,24,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27448 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 40, targets := 129 }], pairs := [(1,5),(3,0),(3,7),(4,5)], upper := (rows 37 322 28 104 146 34 193 129 385), lower := (rows 37 322 28 104 146 34 64 128 256), losses := [] }

theorem u27448 : Upper (D 7) (R 7) [36,320,24,96,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27449 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 330, targets := 128 }], pairs := [(1,5),(1,7),(3,7),(4,5)], upper := (rows 37 322 28 104 146 160 67 131 259), lower := (rows 37 322 28 104 146 160 64 128 256), losses := [] }

theorem u27449 : Upper (D 7) (R 7) [36,320,24,96,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27450 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 28 137 146 33 98 226 354), lower := (rows 37 322 28 137 146 33 64 128 256), losses := [] }

theorem u27450 : Upper (D 7) (R 7) [36,320,24,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27451 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,6)], upper := (rows 37 322 28 137 146 34 97 225 353), lower := (rows 37 322 28 137 146 34 64 128 256), losses := [] }

theorem u27451 : Upper (D 7) (R 7) [36,320,24,129,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27452 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(2,1)], upper := (rows 37 322 28 137 146 96 99 163 291), lower := (rows 37 322 28 137 146 96 64 128 256), losses := [{ target := 1, region := (rows 17 0 20 24 16 98 64 128 256), good := (rows 37 352 29 137 189 96 96 128 256) }] }

theorem u27452 : Upper (D 7) (R 7) [36,320,24,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27453 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 28 137 208 33 98 162 290), lower := (rows 37 322 28 137 208 33 64 128 256), losses := [] }

theorem u27453 : Upper (D 7) (R 7) [36,320,24,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27454 : Route 9 := (fun mask => (mask,id))

def c27454 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27454 : Upper (D 7) (R 7) [36,320,24,129,192,2] 13 := by
  apply FastRouting.sound _ _ [36,320,24,129,192,2] 13 (by decide) (choices 1) [1,2,32] r27454 c27454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10078
  · exact u10079
  · exact u10080

def b27455 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 322 28 138 208 33 99 163 291), lower := (rows 37 322 28 138 208 33 64 128 256), losses := [] }

theorem u27455 : Upper (D 7) (R 7) [36,320,24,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27456 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 37 322 28 138 208 34 97 161 289), lower := (rows 37 322 28 138 208 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 42 0 133 261), good := (rows 421 290 445 170 144 34 0 128 256) }] }

theorem u27456 : Upper (D 7) (R 7) [36,320,24,130,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27457 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 69 11 50 40 208 144 400), lower := (rows 37 322 69 11 50 40 64 128 256), losses := [] }

theorem u27457 : Upper (D 7) (R 7) [36,320,65,3,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27457 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27458 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 69 11 50 48 200 136 392), lower := (rows 37 322 69 11 50 48 64 128 256), losses := [] }

theorem u27458 : Upper (D 7) (R 7) [36,320,65,3,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27458 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27459 : Route 9 := (fun mask => (mask,id))

def c27459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27459 : Upper (D 7) (R 7) [36,320,65,3,34,128] 13 := by
  apply FastRouting.sound _ _ [36,320,65,3,34,128] 13 (by decide) (choices 1) [8,16,128] r27459 c27459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10081
  · exact u10082
  · exact u10083

def b27460 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 69 11 146 40 240 176 432), lower := (rows 37 322 69 11 146 40 64 128 256), losses := [] }

theorem u27460 : Upper (D 7) (R 7) [36,320,65,3,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27460 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27461 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 176, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 322 69 11 146 48 232 168 424), lower := (rows 37 322 69 11 146 48 64 128 256), losses := [] }

theorem u27461 : Upper (D 7) (R 7) [36,320,65,3,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27461 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27462 : Route 9 := (fun mask => (mask,id))

def c27462 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27462 : Upper (D 7) (R 7) [36,320,65,3,130,128] 13 := by
  apply FastRouting.sound _ _ [36,320,65,3,130,128] 13 (by decide) (choices 1) [8,16,32] r27462 c27462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10084
  · exact u10085
  · exact u10086

def b27463 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 322 69 11 152 34 240 176 432), lower := (rows 37 322 69 11 152 34 64 128 256), losses := [] }

theorem u27463 : Upper (D 7) (R 7) [36,320,65,3,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27464 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 176, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 322 69 11 152 48 226 162 418), lower := (rows 37 322 69 11 152 48 64 128 256), losses := [] }

theorem u27464 : Upper (D 7) (R 7) [36,320,65,3,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27464 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27465 : Route 9 := (fun mask => (mask,id))

def c27465 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27465 : Upper (D 7) (R 7) [36,320,65,3,136,128] 13 := by
  apply FastRouting.sound _ _ [36,320,65,3,136,128] 13 (by decide) (choices 1) [2,16,32] r27465 c27465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10087
  · exact u10088
  · exact u10089

def b27466 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 322 69 11 176 34 216 152 408), lower := (rows 37 322 69 11 176 34 64 128 256), losses := [] }

theorem u27466 : Upper (D 7) (R 7) [36,320,65,3,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27467 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 69 11 176 40 210 146 402), lower := (rows 37 322 69 11 176 40 64 128 256), losses := [] }

theorem u27467 : Upper (D 7) (R 7) [36,320,65,3,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27467 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27468 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 69 11 176 48 202 138 394), lower := (rows 37 322 69 11 176 48 64 128 256), losses := [] }

theorem u27468 : Upper (D 7) (R 7) [36,320,65,3,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27468 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27469 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 69 11 176 160 90 154 282), lower := (rows 37 322 69 11 176 160 64 128 256), losses := [] }

theorem u27469 : Upper (D 7) (R 7) [36,320,65,3,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27470 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 69 25 26 34 224 160 416), lower := (rows 37 322 69 25 26 34 64 128 256), losses := [] }

theorem u27470 : Upper (D 7) (R 7) [36,320,65,17,10,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27471 : Route 9 := (fun mask => (mask,id))

def c27471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27471 : Upper (D 7) (R 7) [36,320,65,17,10,128] 13 := by
  apply FastRouting.sound _ _ [36,320,65,17,10,128] 13 (by decide) (choices 1) [2,32,128] r27471 c27471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10090
  · exact u10091
  · exact u10092

def b27472 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 322 69 25 146 34 232 168 424), lower := (rows 37 322 69 25 146 34 64 128 256), losses := [] }

theorem u27472 : Upper (D 7) (R 7) [36,320,65,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27473 : Route 9 := (fun mask => (mask,id))

def c27473 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27473 : Upper (D 7) (R 7) [36,320,65,17,130,8] 13 := by
  apply FastRouting.sound _ _ [36,320,65,17,130,8] 13 (by decide) (choices 1) [2,32,128] r27473 c27473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10093
  · exact u10094
  · exact u10095

def r27474 : Route 9 := (fun mask => (mask,id))

def c27474 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27474 : Upper (D 7) (R 7) [36,320,65,17,130,128] 13 := by
  apply FastRouting.sound _ _ [36,320,65,17,130,128] 13 (by decide) (choices 1) [2,8,32] r27474 c27474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10096
  · exact u10097
  · exact u10098

def b27475 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 322 69 25 152 34 226 162 418), lower := (rows 37 322 69 25 152 34 64 128 256), losses := [] }

theorem u27475 : Upper (D 7) (R 7) [36,320,65,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27476 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 3, region := 482, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 322 69 25 152 160 98 162 290), lower := (rows 37 322 69 25 152 160 64 128 256), losses := [] }

theorem u27476 : Upper (D 7) (R 7) [36,320,65,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27477 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 322 69 26 56 33 194 130 386), lower := (rows 37 322 69 26 56 33 64 128 256), losses := [] }

theorem u27477 : Upper (D 7) (R 7) [36,320,65,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27478 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 24, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 37 322 69 26 56 34 193 129 385), lower := (rows 37 322 69 26 56 34 64 128 256), losses := [] }

theorem u27478 : Upper (D 7) (R 7) [36,320,65,18,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27479 : Route 9 := (fun mask => (mask,id))

def c27479 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27479 : Upper (D 7) (R 7) [36,320,65,18,40,128] 13 := by
  apply FastRouting.sound _ _ [36,320,65,18,40,128] 13 (by decide) (choices 1) [1,2,128] r27479 c27479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10099
  · exact u10100
  · exact u10101

#print axioms u27479
end Delivery.IrregularNine14.P07
