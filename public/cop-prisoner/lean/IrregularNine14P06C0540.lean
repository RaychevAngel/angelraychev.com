import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0247
import IrregularNine14P06C0248
import IrregularNine14P06C0249

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32400 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 452, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 98 133 56 22 357 325 453 325), lower := (rows 11 98 133 56 22 32 64 128 256), losses := [] }

theorem u32400 : Upper (D 6) (R 6) [10,96,129,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32401 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 133 56 81 294 326 390 262), lower := (rows 11 98 133 56 81 32 64 128 256), losses := [] }

theorem u32401 : Upper (D 6) (R 6) [10,96,129,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32402 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 133 56 82 293 325 389 261), lower := (rows 11 98 133 56 82 32 64 128 256), losses := [] }

theorem u32402 : Upper (D 6) (R 6) [10,96,129,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32403 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 98 133 56 84 295 327 391 263), lower := (rows 11 98 133 56 84 32 64 128 256), losses := [] }

theorem u32403 : Upper (D 6) (R 6) [10,96,129,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32404 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 98 133 56 273 102 70 198 326), lower := (rows 11 98 133 56 273 32 64 128 256), losses := [] }

theorem u32404 : Upper (D 6) (R 6) [10,96,129,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32405 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 98 133 56 274 101 69 197 325), lower := (rows 11 98 133 56 274 32 64 128 256), losses := [] }

theorem u32405 : Upper (D 6) (R 6) [10,96,129,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32406 : Route 9 := (fun mask => (mask,id))

def c32406 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32406 : Upper (D 6) (R 6) [10,96,129,48,260] 13 := by
  apply FastRouting.sound _ _ [10,96,129,48,260] 13 (by decide) (choices 1) [1,2,4,64] r32406 c32406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14869
  · exact u14870
  · exact u14871
  · exact u14872

def b32407 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 98 133 56 336 39 71 135 263), lower := (rows 11 98 133 56 336 32 64 128 256), losses := [] }

theorem u32407 : Upper (D 6) (R 6) [10,96,129,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32408 : Route 9 := (fun mask => (mask,id))

def c32408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32408 : Upper (D 6) (R 6) [10,96,129,257,6] 13 := by
  apply FastRouting.sound _ _ [10,96,129,257,6] 13 (by decide) (choices 1) [4,16,64] r32408 c32408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14873
  · exact u14874
  · exact u14875

def b32409 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 98 133 265 50 116 84 212 340), lower := (rows 11 98 133 265 50 32 64 128 256), losses := [] }

theorem u32409 : Upper (D 6) (R 6) [10,96,129,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32410 : Route 9 := (fun mask => (mask,id))

def c32410 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32410 : Upper (D 6) (R 6) [10,96,129,257,36] 13 := by
  apply FastRouting.sound _ _ [10,96,129,257,36] 13 (by decide) (choices 1) [2,4,16,64] r32410 c32410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14876
  · exact u14877
  · exact u14878
  · exact u14879

def b32411 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 11 98 133 265 112 54 86 150 278), lower := (rows 11 98 133 265 112 32 64 128 256), losses := [] }

theorem u32411 : Upper (D 6) (R 6) [10,96,129,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32412 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 133 268 19 116 116 244 372), lower := (rows 11 98 133 268 19 32 64 128 256), losses := [] }

theorem u32412 : Upper (D 6) (R 6) [10,96,129,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32413 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 98 133 268 21 114 114 242 370), lower := (rows 11 98 133 268 21 32 64 128 256), losses := [] }

theorem u32413 : Upper (D 6) (R 6) [10,96,129,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32414 : Route 9 := (fun mask => (mask,id))

def c32414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32414 : Upper (D 6) (R 6) [10,96,129,260,6] 13 := by
  apply FastRouting.sound _ _ [10,96,129,260,6] 13 (by decide) (choices 1) [1,16,64] r32414 c32414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14880
  · exact u14881
  · exact u14882

def r32415 : Route 9 := (fun mask => (mask,id))

def c32415 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32415 : Upper (D 6) (R 6) [10,96,129,260,33] 13 := by
  apply FastRouting.sound _ _ [10,96,129,260,33] 13 (by decide) (choices 1) [2,4,16,64] r32415 c32415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14883
  · exact u14884
  · exact u14885
  · exact u14886

def b32416 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 98 133 268 50 117 85 213 341), lower := (rows 11 98 133 268 50 32 64 128 256), losses := [] }

theorem u32416 : Upper (D 6) (R 6) [10,96,129,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32417 : Route 9 := (fun mask => (mask,id))

def c32417 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32417 : Upper (D 6) (R 6) [10,96,129,260,36] 13 := by
  apply FastRouting.sound _ _ [10,96,129,260,36] 13 (by decide) (choices 1) [1,2,16,64] r32417 c32417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14887
  · exact u14888
  · exact u14889
  · exact u14890

def b32418 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 11 98 133 268 112 55 87 151 279), lower := (rows 11 98 133 268 112 32 64 128 256), losses := [] }

theorem u32418 : Upper (D 6) (R 6) [10,96,129,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32419 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 98 133 280 19 100 100 228 356), lower := (rows 11 98 133 280 19 32 64 128 256), losses := [] }

theorem u32419 : Upper (D 6) (R 6) [10,96,129,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32420 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 98 133 280 21 102 102 230 358), lower := (rows 11 98 133 280 21 32 64 128 256), losses := [] }

theorem u32420 : Upper (D 6) (R 6) [10,96,129,272,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32421 : Route 9 := (fun mask => (mask,id))

def c32421 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32421 : Upper (D 6) (R 6) [10,96,129,272,6] 13 := by
  apply FastRouting.sound _ _ [10,96,129,272,6] 13 (by decide) (choices 1) [1,4,64] r32421 c32421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14891
  · exact u14892
  · exact u14893

def b32422 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 196, targets := 32 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 11 98 133 280 49 102 70 198 326), lower := (rows 11 98 133 280 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 21 24 16 0 65 129 257), good := (rows 463 66 453 284 477 0 64 128 256) }] }

theorem u32422 : Upper (D 6) (R 6) [10,96,129,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32423 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 98 133 280 50 101 69 197 325), lower := (rows 11 98 133 280 50 32 64 128 256), losses := [] }

theorem u32423 : Upper (D 6) (R 6) [10,96,129,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32424 : Route 9 := (fun mask => (mask,id))

def c32424 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32424 : Upper (D 6) (R 6) [10,96,129,272,36] 13 := by
  apply FastRouting.sound _ _ [10,96,129,272,36] 13 (by decide) (choices 1) [1,2,4,64] r32424 c32424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14894
  · exact u14895
  · exact u14896
  · exact u14897

def b32425 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 11 98 133 280 112 39 71 135 263), lower := (rows 11 98 133 280 112 32 64 128 256), losses := [] }

theorem u32425 : Upper (D 6) (R 6) [10,96,129,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32426 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 98 133 296 19 116 84 212 340), lower := (rows 11 98 133 296 19 32 64 128 256), losses := [] }

theorem u32426 : Upper (D 6) (R 6) [10,96,129,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32427 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 98 133 296 21 118 86 214 342), lower := (rows 11 98 133 296 21 32 64 128 256), losses := [] }

theorem u32427 : Upper (D 6) (R 6) [10,96,129,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32428 : Route 9 := (fun mask => (mask,id))

def c32428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32428 : Upper (D 6) (R 6) [10,96,129,288,6] 13 := by
  apply FastRouting.sound _ _ [10,96,129,288,6] 13 (by decide) (choices 1) [1,4,16,64] r32428 c32428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14898
  · exact u14899
  · exact u14900
  · exact u14901

def r32429 : Route 9 := (fun mask => (mask,id))

def c32429 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32429 : Upper (D 6) (R 6) [10,96,129,288,65] 13 := by
  apply FastRouting.sound _ _ [10,96,129,288,65] 13 (by decide) (choices 1) [2,4,16] r32429 c32429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14902
  · exact u14903
  · exact u14904

def b32430 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 11 98 133 296 82 53 85 149 277), lower := (rows 11 98 133 296 82 32 64 128 256), losses := [] }

theorem u32430 : Upper (D 6) (R 6) [10,96,129,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32431 : Route 9 := (fun mask => (mask,id))

def c32431 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32431 : Upper (D 6) (R 6) [10,96,129,288,68] 13 := by
  apply FastRouting.sound _ _ [10,96,129,288,68] 13 (by decide) (choices 1) [1,2,4,16] r32431 c32431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14905
  · exact u14906
  · exact u14907
  · exact u14908

def b32432 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 98 134 25 21 356 356 484 356), lower := (rows 11 98 134 25 21 32 64 128 256), losses := [] }

theorem u32432 : Upper (D 6) (R 6) [10,96,130,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32433 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 134 25 49 356 324 452 324), lower := (rows 11 98 134 25 49 32 64 128 256), losses := [] }

theorem u32433 : Upper (D 6) (R 6) [10,96,130,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32434 : Route 9 := (fun mask => (mask,id))

def c32434 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32434 : Upper (D 6) (R 6) [10,96,130,17,36] 13 := by
  apply FastRouting.sound _ _ [10,96,130,17,36] 13 (by decide) (choices 1) [1,4,64,256] r32434 c32434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14909
  · exact u14910
  · exact u14911
  · exact u14912

def b32435 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 134 25 112 293 325 389 261), lower := (rows 11 98 134 25 112 32 64 128 256), losses := [] }

theorem u32435 : Upper (D 6) (R 6) [10,96,130,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32436 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 98 134 25 273 100 100 228 356), lower := (rows 11 98 134 25 273 32 64 128 256), losses := [] }

theorem u32436 : Upper (D 6) (R 6) [10,96,130,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32437 : Route 9 := (fun mask => (mask,id))

def c32437 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32437 : Upper (D 6) (R 6) [10,96,130,17,260] 13 := by
  apply FastRouting.sound _ _ [10,96,130,17,260] 13 (by decide) (choices 1) [1,4,64] r32437 c32437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14913
  · exact u14914
  · exact u14915

def r32438 : Route 9 := (fun mask => (mask,id))

def c32438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32438 : Upper (D 6) (R 6) [10,96,130,17,288] 13 := by
  apply FastRouting.sound _ _ [10,96,130,17,288] 13 (by decide) (choices 1) [1,4,64] r32438 c32438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14916
  · exact u14917
  · exact u14918

def b32439 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 98 134 28 21 353 353 481 353), lower := (rows 11 98 134 28 21 32 64 128 256), losses := [] }

theorem u32439 : Upper (D 6) (R 6) [10,96,130,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32440 : Route 9 := (fun mask => (mask,id))

def c32440 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32440 : Upper (D 6) (R 6) [10,96,130,20,33] 13 := by
  apply FastRouting.sound _ _ [10,96,130,20,33] 13 (by decide) (choices 1) [1,4,64,256] r32440 c32440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14919
  · exact u14920
  · exact u14921
  · exact u14922

def b32441 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 98 134 28 52 353 321 449 321), lower := (rows 11 98 134 28 52 32 64 128 256), losses := [] }

theorem u32441 : Upper (D 6) (R 6) [10,96,130,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32442 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 11 98 134 28 112 293 325 389 261), lower := (rows 11 98 134 28 112 32 64 128 256), losses := [] }

theorem u32442 : Upper (D 6) (R 6) [10,96,130,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32443 : Route 9 := (fun mask => (mask,id))

def c32443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32443 : Upper (D 6) (R 6) [10,96,130,20,257] 13 := by
  apply FastRouting.sound _ _ [10,96,130,20,257] 13 (by decide) (choices 1) [1,4,64] r32443 c32443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14923
  · exact u14924
  · exact u14925

def b32444 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 98 134 28 276 97 97 225 353), lower := (rows 11 98 134 28 276 32 64 128 256), losses := [] }

theorem u32444 : Upper (D 6) (R 6) [10,96,130,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32445 : Route 9 := (fun mask => (mask,id))

def c32445 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32445 : Upper (D 6) (R 6) [10,96,130,20,288] 13 := by
  apply FastRouting.sound _ _ [10,96,130,20,288] 13 (by decide) (choices 1) [1,4,64] r32445 c32445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14926
  · exact u14927
  · exact u14928

def b32446 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 98 134 44 21 369 337 465 337), lower := (rows 11 98 134 44 21 32 64 128 256), losses := [] }

theorem u32446 : Upper (D 6) (R 6) [10,96,130,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32447 : Route 9 := (fun mask => (mask,id))

def c32447 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32447 : Upper (D 6) (R 6) [10,96,130,36,65] 13 := by
  apply FastRouting.sound _ _ [10,96,130,36,65] 13 (by decide) (choices 1) [1,4,16,256] r32447 c32447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14929
  · exact u14930
  · exact u14931
  · exact u14932

def r32448 : Route 9 := (fun mask => (mask,id))

def c32448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32448 : Upper (D 6) (R 6) [10,96,130,36,68] 13 := by
  apply FastRouting.sound _ _ [10,96,130,36,68] 13 (by decide) (choices 1) [1,16,256] r32448 c32448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14933
  · exact u14934
  · exact u14935

def r32449 : Route 9 := (fun mask => (mask,id))

def c32449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32449 : Upper (D 6) (R 6) [10,96,130,36,257] 13 := by
  apply FastRouting.sound _ _ [10,96,130,36,257] 13 (by decide) (choices 1) [1,4,16,64] r32449 c32449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14936
  · exact u14937
  · exact u14938
  · exact u14939

def r32450 : Route 9 := (fun mask => (mask,id))

def c32450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32450 : Upper (D 6) (R 6) [10,96,130,36,260] 13 := by
  apply FastRouting.sound _ _ [10,96,130,36,260] 13 (by decide) (choices 1) [1,16,64] r32450 c32450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14940
  · exact u14941
  · exact u14942

def r32451 : Route 9 := (fun mask => (mask,id))

def c32451 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32451 : Upper (D 6) (R 6) [10,96,130,36,320] 13 := by
  apply FastRouting.sound _ _ [10,96,130,36,320] 13 (by decide) (choices 1) [1,4,16] r32451 c32451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14943
  · exact u14944
  · exact u14945

def b32452 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 98 134 56 21 357 325 453 325), lower := (rows 11 98 134 56 21 32 64 128 256), losses := [] }

theorem u32452 : Upper (D 6) (R 6) [10,96,130,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32453 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 134 56 81 293 325 389 261), lower := (rows 11 98 134 56 81 32 64 128 256), losses := [] }

theorem u32453 : Upper (D 6) (R 6) [10,96,130,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32454 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 98 134 56 84 293 325 389 261), lower := (rows 11 98 134 56 84 32 64 128 256), losses := [] }

theorem u32454 : Upper (D 6) (R 6) [10,96,130,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32455 : Route 9 := (fun mask => (mask,id))

def c32455 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32455 : Upper (D 6) (R 6) [10,96,130,48,257] 13 := by
  apply FastRouting.sound _ _ [10,96,130,48,257] 13 (by decide) (choices 1) [1,4,64] r32455 c32455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14946
  · exact u14947
  · exact u14948

def r32456 : Route 9 := (fun mask => (mask,id))

def c32456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32456 : Upper (D 6) (R 6) [10,96,130,48,260] 13 := by
  apply FastRouting.sound _ _ [10,96,130,48,260] 13 (by decide) (choices 1) [1,4,64] r32456 c32456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14949
  · exact u14950
  · exact u14951

def b32457 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 98 134 56 336 37 69 133 261), lower := (rows 11 98 134 56 336 32 64 128 256), losses := [] }

theorem u32457 : Upper (D 6) (R 6) [10,96,130,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32458 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 98 134 265 21 116 116 244 372), lower := (rows 11 98 134 265 21 32 64 128 256), losses := [] }

theorem u32458 : Upper (D 6) (R 6) [10,96,130,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32459 : Route 9 := (fun mask => (mask,id))

def c32459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32459 : Upper (D 6) (R 6) [10,96,130,257,33] 13 := by
  apply FastRouting.sound _ _ [10,96,130,257,33] 13 (by decide) (choices 1) [4,16,64] r32459 c32459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14952
  · exact u14953
  · exact u14954

#print axioms u32459
end Delivery.IrregularNine14.P06
