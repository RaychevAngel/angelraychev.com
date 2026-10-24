import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0055

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15600 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 1, region := 200, targets := 1 }], pairs := [(1,7),(2,6),(3,0),(4,6)], upper := (rows 13 35 22 200 273 96 226 162 418), lower := (rows 13 35 22 200 273 96 64 128 256), losses := [{ target := 7, region := (rows 1 3 20 8 16 104 64 0 256), good := (rows 47 35 22 104 279 96 96 0 256) }] }

theorem u15600 : Upper (D 7) (R 7) [12,33,18,192,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15601 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 22 200 304 33 194 194 450), lower := (rows 13 35 22 200 304 33 64 128 256), losses := [] }

theorem u15601 : Upper (D 7) (R 7) [12,33,18,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15602 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 35 22 200 304 34 193 193 449), lower := (rows 13 35 22 200 304 34 64 128 256), losses := [] }

theorem u15602 : Upper (D 7) (R 7) [12,33,18,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15603 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 2, region := 201, targets := 32 }], pairs := [(0,5),(2,6),(3,5),(4,6)], upper := (rows 13 35 22 200 304 96 195 131 387), lower := (rows 13 35 22 200 304 96 64 128 256), losses := [] }

theorem u15603 : Upper (D 7) (R 7) [12,33,18,192,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15604 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 22 200 336 33 226 162 418), lower := (rows 13 35 22 200 336 33 64 128 256), losses := [] }

theorem u15604 : Upper (D 7) (R 7) [12,33,18,192,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15605 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 472, targets := 2 },{ cop := 0, region := 34, targets := 64 },{ cop := 0, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(3,1),(4,1)], upper := (rows 13 35 22 200 336 34 225 161 417), lower := (rows 13 35 22 200 336 34 64 128 256), losses := [] }

theorem u15605 : Upper (D 7) (R 7) [12,33,18,192,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15606 : Route 9 := (fun mask => (mask,id))

def c15606 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15606 : Upper (D 7) (R 7) [12,33,18,192,320,128] 13 := by
  apply FastRouting.sound _ _ [12,33,18,192,320,128] 13 (by decide) (choices 1) [1,2,32] r15606 c15606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3324
  · exact u3325
  · exact u3326

def b15607 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 212, targets := 1 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 13 35 22 265 208 34 224 224 480), lower := (rows 13 35 22 265 208 34 64 128 256), losses := [] }

theorem u15607 : Upper (D 7) (R 7) [12,33,18,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15608 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 1, region := 392, targets := 64 }], pairs := [(0,6),(2,0),(3,6),(4,0)], upper := (rows 13 35 22 265 208 96 226 162 418), lower := (rows 13 35 22 265 208 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 14 16 32 0 130 258), good := (rows 13 427 415 265 144 32 0 128 256) }] }

theorem u15608 : Upper (D 7) (R 7) [12,33,18,257,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15609 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 38, targets := 128 },{ cop := 0, region := 240, targets := 2 },{ cop := 1, region := 392, targets := 1 }], pairs := [(1,7),(2,7),(3,0),(4,1)], upper := (rows 13 35 22 266 81 96 224 160 416), lower := (rows 13 35 22 266 81 96 64 128 256), losses := [] }

theorem u15609 : Upper (D 7) (R 7) [12,33,18,258,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15610 : Route 9 := (fun mask => (mask,id))

def c15610 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15610 : Upper (D 7) (R 7) [12,33,18,258,65,128] 13 := by
  apply FastRouting.sound _ _ [12,33,18,258,65,128] 13 (by decide) (choices 1) [32,128] r15610 c15610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3327
  · exact u3328

def b15611 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 22 266 112 33 192 192 448), lower := (rows 13 35 22 266 112 33 64 128 256), losses := [] }

theorem u15611 : Upper (D 7) (R 7) [12,33,18,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15612 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 13 35 22 266 112 96 193 129 385), lower := (rows 13 35 22 266 112 96 64 128 256), losses := [] }

theorem u15612 : Upper (D 7) (R 7) [12,33,18,258,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15613 : Route 9 := (fun mask => (mask,id))

def c15613 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15613 : Upper (D 7) (R 7) [12,33,18,258,96,128] 13 := by
  apply FastRouting.sound _ _ [12,33,18,258,96,128] 13 (by decide) (choices 1) [1,128] r15613 c15613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3329
  · exact u3330

def b15614 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 22 266 208 33 224 224 480), lower := (rows 13 35 22 266 208 33 64 128 256), losses := [] }

theorem u15614 : Upper (D 7) (R 7) [12,33,18,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15615 : Route 9 := (fun mask => (mask,id))

def c15615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15615 : Upper (D 7) (R 7) [12,33,18,258,192,64] 13 := by
  apply FastRouting.sound _ _ [12,33,18,258,192,64] 13 (by decide) (choices 1) [1,32,128] r15615 c15615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3331
  · exact u3332
  · exact u3333

def b15616 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 35 22 296 81 34 192 192 448), lower := (rows 13 35 22 296 81 34 64 128 256), losses := [] }

theorem u15616 : Upper (D 7) (R 7) [12,33,18,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15617 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 4, region := 38, targets := 128 }], pairs := [(1,7),(2,5),(2,7),(4,5)], upper := (rows 13 35 22 296 81 96 194 130 386), lower := (rows 13 35 22 296 81 96 64 128 256), losses := [] }

theorem u15617 : Upper (D 7) (R 7) [12,33,18,288,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15618 : Route 9 := (fun mask => (mask,id))

def c15618 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15618 : Upper (D 7) (R 7) [12,33,18,288,65,128] 13 := by
  apply FastRouting.sound _ _ [12,33,18,288,65,128] 13 (by decide) (choices 1) [2,128] r15618 c15618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3334
  · exact u3335

def b15619 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 22 296 208 33 194 194 450), lower := (rows 13 35 22 296 208 33 64 128 256), losses := [] }

theorem u15619 : Upper (D 7) (R 7) [12,33,18,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15620 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(4,1),(4,5)], upper := (rows 13 35 22 296 208 34 193 193 449), lower := (rows 13 35 22 296 208 34 64 128 256), losses := [] }

theorem u15620 : Upper (D 7) (R 7) [12,33,18,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15621 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 1, region := 392, targets := 64 }], pairs := [(0,6),(2,5),(3,6),(4,5)], upper := (rows 13 35 22 296 208 96 195 131 387), lower := (rows 13 35 22 296 208 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 10 16 32 0 134 262), good := (rows 397 427 415 296 144 32 0 128 256) }] }

theorem u15621 : Upper (D 7) (R 7) [12,33,18,288,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15622 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 35 22 328 81 34 224 160 416), lower := (rows 13 35 22 328 81 34 64 128 256), losses := [] }

theorem u15622 : Upper (D 7) (R 7) [12,33,18,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15623 : Route 9 := (fun mask => (mask,id))

def c15623 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15623 : Upper (D 7) (R 7) [12,33,18,320,65,128] 13 := by
  apply FastRouting.sound _ _ [12,33,18,320,65,128] 13 (by decide) (choices 1) [2,32,128] r15623 c15623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3336
  · exact u3337
  · exact u3338

def b15624 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 35 22 328 112 33 194 130 386), lower := (rows 13 35 22 328 112 33 64 128 256), losses := [] }

theorem u15624 : Upper (D 7) (R 7) [12,33,18,320,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15625 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 35 22 328 112 34 193 129 385), lower := (rows 13 35 22 328 112 34 64 128 256), losses := [] }

theorem u15625 : Upper (D 7) (R 7) [12,33,18,320,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15626 : Route 9 := (fun mask => (mask,id))

def c15626 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15626 : Upper (D 7) (R 7) [12,33,18,320,96,128] 13 := by
  apply FastRouting.sound _ _ [12,33,18,320,96,128] 13 (by decide) (choices 1) [1,2,128] r15626 c15626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3339
  · exact u3340
  · exact u3341

def b15627 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 35 22 328 145 34 224 224 480), lower := (rows 13 35 22 328 145 34 64 128 256), losses := [] }

theorem u15627 : Upper (D 7) (R 7) [12,33,18,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15628 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 148, targets := 64 },{ cop := 1, region := 456, targets := 1 }], pairs := [(1,7),(2,6),(3,0),(4,6)], upper := (rows 13 35 22 328 145 96 226 162 418), lower := (rows 13 35 22 328 145 96 64 128 256), losses := [{ target := 7, region := (rows 1 3 20 8 16 104 64 0 256), good := (rows 47 35 22 360 23 96 96 0 256) }] }

theorem u15628 : Upper (D 7) (R 7) [12,33,18,320,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15629 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 38, targets := 64 },{ cop := 1, region := 328, targets := 1 },{ cop := 1, region := 328, targets := 128 }], pairs := [(1,6),(2,6),(3,0),(3,7)], upper := (rows 13 35 22 328 145 160 98 226 354), lower := (rows 13 35 22 328 145 160 64 128 256), losses := [] }

theorem u15629 : Upper (D 7) (R 7) [12,33,18,320,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15629 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15630 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 22 328 176 33 194 194 450), lower := (rows 13 35 22 328 176 33 64 128 256), losses := [] }

theorem u15630 : Upper (D 7) (R 7) [12,33,18,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15631 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 35 22 328 176 34 193 193 449), lower := (rows 13 35 22 328 176 34 64 128 256), losses := [] }

theorem u15631 : Upper (D 7) (R 7) [12,33,18,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15632 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 148, targets := 64 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(2,6),(3,5),(4,6)], upper := (rows 13 35 22 328 176 96 195 131 387), lower := (rows 13 35 22 328 176 96 64 128 256), losses := [] }

theorem u15632 : Upper (D 7) (R 7) [12,33,18,320,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15633 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 22 328 176 160 67 195 323), lower := (rows 13 35 22 328 176 160 64 128 256), losses := [] }

theorem u15633 : Upper (D 7) (R 7) [12,33,18,320,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15634 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 22 328 208 33 226 162 418), lower := (rows 13 35 22 328 208 33 64 128 256), losses := [] }

theorem u15634 : Upper (D 7) (R 7) [12,33,18,320,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15635 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 472, targets := 2 },{ cop := 0, region := 34, targets := 64 },{ cop := 0, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(3,1),(4,1)], upper := (rows 13 35 22 328 208 34 225 161 417), lower := (rows 13 35 22 328 208 34 64 128 256), losses := [] }

theorem u15635 : Upper (D 7) (R 7) [12,33,18,320,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15636 : Route 9 := (fun mask => (mask,id))

def c15636 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15636 : Upper (D 7) (R 7) [12,33,18,320,192,128] 13 := by
  apply FastRouting.sound _ _ [12,33,18,320,192,128] 13 (by decide) (choices 1) [1,2,32] r15636 c15636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3342
  · exact u3343
  · exact u3344

def b15637 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 35 52 74 145 34 448 448 448), lower := (rows 13 35 52 74 145 34 64 128 256), losses := [] }

theorem u15637 : Upper (D 7) (R 7) [12,33,48,66,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15638 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 13 35 52 74 145 96 450 386 386), lower := (rows 13 35 52 74 145 96 64 128 256), losses := [] }

theorem u15638 : Upper (D 7) (R 7) [12,33,48,66,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15639 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 1, region := 328, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(3,7)], upper := (rows 13 35 52 74 145 160 322 450 322), lower := (rows 13 35 52 74 145 160 64 128 256), losses := [] }

theorem u15639 : Upper (D 7) (R 7) [12,33,48,66,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15640 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 216, targets := 32 },{ cop := 1, region := 200, targets := 1 }], pairs := [(3,0),(3,5),(4,5)], upper := (rows 13 35 52 74 145 288 194 194 450), lower := (rows 13 35 52 74 145 288 64 128 256), losses := [] }

theorem u15640 : Upper (D 7) (R 7) [12,33,48,66,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15640 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15641 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 52 74 208 33 450 386 386), lower := (rows 13 35 52 74 208 33 64 128 256), losses := [] }

theorem u15641 : Upper (D 7) (R 7) [12,33,48,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15642 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 52 74 208 34 449 385 385), lower := (rows 13 35 52 74 208 34 64 128 256), losses := [] }

theorem u15642 : Upper (D 7) (R 7) [12,33,48,66,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15643 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 13 35 52 74 208 160 323 387 259), lower := (rows 13 35 52 74 208 160 64 128 256), losses := [] }

theorem u15643 : Upper (D 7) (R 7) [12,33,48,66,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15644 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 216, targets := 32 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6),(3,5),(4,5)], upper := (rows 13 35 52 74 208 288 195 131 387), lower := (rows 13 35 52 74 208 288 64 128 256), losses := [] }

theorem u15644 : Upper (D 7) (R 7) [12,33,48,66,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15644 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15645 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 35 52 74 273 34 192 192 448), lower := (rows 13 35 52 74 273 34 64 128 256), losses := [] }

theorem u15645 : Upper (D 7) (R 7) [12,33,48,66,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15646 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 13 35 52 74 273 96 194 130 386), lower := (rows 13 35 52 74 273 96 64 128 256), losses := [] }

theorem u15646 : Upper (D 7) (R 7) [12,33,48,66,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15647 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 200, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(4,5)], upper := (rows 13 35 52 74 273 160 194 194 450), lower := (rows 13 35 52 74 273 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 10 16 171 74 138 266), good := (rows 492 490 52 490 308 160 64 160 256) }] }

theorem u15647 : Upper (D 7) (R 7) [12,33,48,66,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15648 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 52 74 336 33 194 130 386), lower := (rows 13 35 52 74 336 33 64 128 256), losses := [] }

theorem u15648 : Upper (D 7) (R 7) [12,33,48,66,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15649 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 52 74 336 34 193 129 385), lower := (rows 13 35 52 74 336 34 64 128 256), losses := [] }

theorem u15649 : Upper (D 7) (R 7) [12,33,48,66,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15650 : Route 9 := (fun mask => (mask,id))

def c15650 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15650 : Upper (D 7) (R 7) [12,33,48,66,320,128] 13 := by
  apply FastRouting.sound _ _ [12,33,48,66,320,128] 13 (by decide) (choices 1) [1,2,128] r15650 c15650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3345
  · exact u3346
  · exact u3347

def b15651 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 52 74 400 33 194 194 450), lower := (rows 13 35 52 74 400 33 64 128 256), losses := [] }

theorem u15651 : Upper (D 7) (R 7) [12,33,48,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15652 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(4,1),(4,5)], upper := (rows 13 35 52 74 400 34 193 193 449), lower := (rows 13 35 52 74 400 34 64 128 256), losses := [] }

theorem u15652 : Upper (D 7) (R 7) [12,33,48,66,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15652 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15653 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 13 35 52 74 400 96 195 131 387), lower := (rows 13 35 52 74 400 96 64 128 256), losses := [] }

theorem u15653 : Upper (D 7) (R 7) [12,33,48,66,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15654 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 13 35 52 74 400 160 67 195 323), lower := (rows 13 35 52 74 400 160 64 128 256), losses := [] }

theorem u15654 : Upper (D 7) (R 7) [12,33,48,66,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15655 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 35 52 200 273 34 194 194 450), lower := (rows 13 35 52 200 273 34 64 128 256), losses := [] }

theorem u15655 : Upper (D 7) (R 7) [12,33,48,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15656 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 13 35 52 200 273 96 194 130 386), lower := (rows 13 35 52 200 273 96 64 128 256), losses := [] }

theorem u15656 : Upper (D 7) (R 7) [12,33,48,192,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15657 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 52 200 274 33 194 194 450), lower := (rows 13 35 52 200 274 33 64 128 256), losses := [] }

theorem u15657 : Upper (D 7) (R 7) [12,33,48,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15658 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 35 52 200 274 34 193 193 449), lower := (rows 13 35 52 200 274 34 64 128 256), losses := [] }

theorem u15658 : Upper (D 7) (R 7) [12,33,48,192,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15659 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 13 35 52 200 274 96 195 131 387), lower := (rows 13 35 52 200 274 96 64 128 256), losses := [] }

theorem u15659 : Upper (D 7) (R 7) [12,33,48,192,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u15659
end Delivery.IrregularNine14.P07
