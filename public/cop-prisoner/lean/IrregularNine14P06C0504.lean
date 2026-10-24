import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0196
import IrregularNine14P06C0197

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30240 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 22 133 296 19 100 100 228 356), lower := (rows 11 22 133 296 19 32 64 128 256), losses := [] }

theorem u30240 : Upper (D 6) (R 6) [10,20,129,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30241 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 22 133 296 21 98 98 226 354), lower := (rows 11 22 133 296 21 32 64 128 256), losses := [] }

theorem u30241 : Upper (D 6) (R 6) [10,20,129,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30242 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 18, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 133 296 22 97 97 225 353), lower := (rows 11 22 133 296 22 32 64 128 256), losses := [] }

theorem u30242 : Upper (D 6) (R 6) [10,20,129,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30243 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 198, targets := 32 },{ cop := 1, region := 360, targets := 1 }], pairs := [(1,5),(2,5),(3,0)], upper := (rows 11 22 133 296 49 102 70 198 326), lower := (rows 11 22 133 296 49 32 64 128 256), losses := [] }

theorem u30243 : Upper (D 6) (R 6) [10,20,129,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30244 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 22 133 296 50 101 69 197 325), lower := (rows 11 22 133 296 50 32 64 128 256), losses := [] }

theorem u30244 : Upper (D 6) (R 6) [10,20,129,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30245 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 133 296 52 99 67 195 323), lower := (rows 11 22 133 296 52 32 64 128 256), losses := [] }

theorem u30245 : Upper (D 6) (R 6) [10,20,129,288,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30246 : Route 9 := (fun mask => (mask,id))

def c30246 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30246 : Upper (D 6) (R 6) [10,20,129,288,65] 13 := by
  apply FastRouting.sound _ _ [10,20,129,288,65] 13 (by decide) (choices 1) [2,4,64] r30246 c30246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11764
  · exact u11765
  · exact u11766

def r30247 : Route 9 := (fun mask => (mask,id))

def c30247 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30247 : Upper (D 6) (R 6) [10,20,129,288,66] 13 := by
  apply FastRouting.sound _ _ [10,20,129,288,66] 13 (by decide) (choices 1) [1,4,64] r30247 c30247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11767
  · exact u11768
  · exact u11769

def b30248 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 133 296 84 99 99 227 355), lower := (rows 11 22 133 296 84 32 64 128 256), losses := [] }

theorem u30248 : Upper (D 6) (R 6) [10,20,129,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30249 : Route 9 := (fun mask => (mask,id))

def c30249 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30249 : Upper (D 6) (R 6) [10,20,129,288,96] 13 := by
  apply FastRouting.sound _ _ [10,20,129,288,96] 13 (by decide) (choices 1) [1,2,4,64] r30249 c30249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11770
  · exact u11771
  · exact u11772
  · exact u11773

def b30250 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 360, targets := 6 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 22 134 41 21 352 352 480 352), lower := (rows 11 22 134 41 21 32 64 128 256), losses := [] }

theorem u30250 : Upper (D 6) (R 6) [10,20,130,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30251 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 22 134 41 49 356 324 452 324), lower := (rows 11 22 134 41 49 32 64 128 256), losses := [] }

theorem u30251 : Upper (D 6) (R 6) [10,20,130,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30252 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 22 134 41 52 353 321 449 321), lower := (rows 11 22 134 41 52 32 64 128 256), losses := [] }

theorem u30252 : Upper (D 6) (R 6) [10,20,130,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30253 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 22 134 41 81 356 356 484 356), lower := (rows 11 22 134 41 81 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 38 70 134 262), good := (rows 505 500 484 57 89 32 64 128 256) }] }

theorem u30253 : Upper (D 6) (R 6) [10,20,130,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30254 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 134 41 84 353 353 481 353), lower := (rows 11 22 134 41 84 32 64 128 256), losses := [] }

theorem u30254 : Upper (D 6) (R 6) [10,20,130,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30255 : Route 9 := (fun mask => (mask,id))

def c30255 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30255 : Upper (D 6) (R 6) [10,20,130,33,96] 13 := by
  apply FastRouting.sound _ _ [10,20,130,33,96] 13 (by decide) (choices 1) [1,4,64,256] r30255 c30255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11774
  · exact u11775
  · exact u11776
  · exact u11777

def b30256 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 22 134 41 273 100 100 228 356), lower := (rows 11 22 134 41 273 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 38 70 134 262), good := (rows 505 500 484 57 281 32 64 128 256) }] }

theorem u30256 : Upper (D 6) (R 6) [10,20,130,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30257 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 134 41 276 97 97 225 353), lower := (rows 11 22 134 41 276 32 64 128 256), losses := [] }

theorem u30257 : Upper (D 6) (R 6) [10,20,130,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30258 : Route 9 := (fun mask => (mask,id))

def c30258 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30258 : Upper (D 6) (R 6) [10,20,130,33,288] 13 := by
  apply FastRouting.sound _ _ [10,20,130,33,288] 13 (by decide) (choices 1) [1,4,64] r30258 c30258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11778
  · exact u11779
  · exact u11780

def r30259 : Route 9 := (fun mask => (mask,id))

def c30259 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30259 : Upper (D 6) (R 6) [10,20,130,33,320] 13 := by
  apply FastRouting.sound _ _ [10,20,130,33,320] 13 (by decide) (choices 1) [1,4,64] r30259 c30259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11781
  · exact u11782
  · exact u11783

def b30260 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 19, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 22 134 44 49 353 321 449 321), lower := (rows 11 22 134 44 49 32 64 128 256), losses := [] }

theorem u30260 : Upper (D 6) (R 6) [10,20,130,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30261 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 22 134 44 81 353 353 481 353), lower := (rows 11 22 134 44 81 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 17 49 81 145 273), good := (rows 505 508 140 44 497 32 64 128 256) }] }

theorem u30261 : Upper (D 6) (R 6) [10,20,130,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30262 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 0, region := 452, targets := 32 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 11 22 134 44 112 353 321 449 321), lower := (rows 11 22 134 44 112 32 64 128 256), losses := [] }

theorem u30262 : Upper (D 6) (R 6) [10,20,130,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30263 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 22 134 44 273 97 97 225 353), lower := (rows 11 22 134 44 273 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 17 49 81 145 273), good := (rows 505 508 140 44 497 32 64 128 256) }] }

theorem u30263 : Upper (D 6) (R 6) [10,20,130,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30264 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 11 22 134 44 304 97 65 193 321), lower := (rows 11 22 134 44 304 32 64 128 256), losses := [] }

theorem u30264 : Upper (D 6) (R 6) [10,20,130,36,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30265 : Route 9 := (fun mask => (mask,id))

def c30265 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30265 : Upper (D 6) (R 6) [10,20,130,36,320] 13 := by
  apply FastRouting.sound _ _ [10,20,130,36,320] 13 (by decide) (choices 1) [1,64] r30265 c30265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11784
  · exact u11785

def b30266 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 134 104 21 353 353 481 353), lower := (rows 11 22 134 104 21 32 64 128 256), losses := [] }

theorem u30266 : Upper (D 6) (R 6) [10,20,130,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30267 : Route 9 := (fun mask => (mask,id))

def c30267 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30267 : Upper (D 6) (R 6) [10,20,130,96,33] 13 := by
  apply FastRouting.sound _ _ [10,20,130,96,33] 13 (by decide) (choices 1) [1,4,64,256] r30267 c30267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11786
  · exact u11787
  · exact u11788
  · exact u11789

def b30268 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 134 104 52 353 321 449 321), lower := (rows 11 22 134 104 52 32 64 128 256), losses := [] }

theorem u30268 : Upper (D 6) (R 6) [10,20,130,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30269 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 22 134 104 112 293 325 389 261), lower := (rows 11 22 134 104 112 32 64 128 256), losses := [] }

theorem u30269 : Upper (D 6) (R 6) [10,20,130,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30270 : Route 9 := (fun mask => (mask,id))

def c30270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30270 : Upper (D 6) (R 6) [10,20,130,96,257] 13 := by
  apply FastRouting.sound _ _ [10,20,130,96,257] 13 (by decide) (choices 1) [1,4,64] r30270 c30270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11790
  · exact u11791
  · exact u11792

def b30271 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 134 104 276 97 97 225 353), lower := (rows 11 22 134 104 276 32 64 128 256), losses := [] }

theorem u30271 : Upper (D 6) (R 6) [10,20,130,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30272 : Route 9 := (fun mask => (mask,id))

def c30272 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30272 : Upper (D 6) (R 6) [10,20,130,96,288] 13 := by
  apply FastRouting.sound _ _ [10,20,130,96,288] 13 (by decide) (choices 1) [1,4,64] r30272 c30272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11793
  · exact u11794
  · exact u11795

def b30273 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 360, targets := 6 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 22 134 265 21 96 96 224 352), lower := (rows 11 22 134 265 21 32 64 128 256), losses := [] }

theorem u30273 : Upper (D 6) (R 6) [10,20,130,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30274 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 22 134 265 49 100 100 228 356), lower := (rows 11 22 134 265 49 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 38 70 134 262), good := (rows 505 500 484 281 57 32 64 128 256) }] }

theorem u30274 : Upper (D 6) (R 6) [10,20,130,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30275 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 134 265 52 97 97 225 353), lower := (rows 11 22 134 265 52 32 64 128 256), losses := [] }

theorem u30275 : Upper (D 6) (R 6) [10,20,130,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30276 : Route 9 := (fun mask => (mask,id))

def c30276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30276 : Upper (D 6) (R 6) [10,20,130,257,96] 13 := by
  apply FastRouting.sound _ _ [10,20,130,257,96] 13 (by decide) (choices 1) [1,4,64] r30276 c30276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11796
  · exact u11797
  · exact u11798

def b30277 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 22 134 268 49 97 97 225 353), lower := (rows 11 22 134 268 49 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 17 49 81 145 273), good := (rows 505 508 140 268 497 32 64 128 256) }] }

theorem u30277 : Upper (D 6) (R 6) [10,20,130,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30278 : Route 9 := (fun mask => (mask,id))

def c30278 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30278 : Upper (D 6) (R 6) [10,20,130,260,96] 13 := by
  apply FastRouting.sound _ _ [10,20,130,260,96] 13 (by decide) (choices 1) [1,64] r30278 c30278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11799
  · exact u11800

def b30279 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 134 296 21 97 97 225 353), lower := (rows 11 22 134 296 21 32 64 128 256), losses := [] }

theorem u30279 : Upper (D 6) (R 6) [10,20,130,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30280 : Route 9 := (fun mask => (mask,id))

def c30280 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30280 : Upper (D 6) (R 6) [10,20,130,288,33] 13 := by
  apply FastRouting.sound _ _ [10,20,130,288,33] 13 (by decide) (choices 1) [1,4,64] r30280 c30280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11801
  · exact u11802
  · exact u11803

def b30281 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 134 296 52 97 65 193 321), lower := (rows 11 22 134 296 52 32 64 128 256), losses := [] }

theorem u30281 : Upper (D 6) (R 6) [10,20,130,288,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30282 : Route 9 := (fun mask => (mask,id))

def c30282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30282 : Upper (D 6) (R 6) [10,20,130,288,65] 13 := by
  apply FastRouting.sound _ _ [10,20,130,288,65] 13 (by decide) (choices 1) [1,4,64] r30282 c30282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11804
  · exact u11805
  · exact u11806

def b30283 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 134 296 84 97 97 225 353), lower := (rows 11 22 134 296 84 32 64 128 256), losses := [] }

theorem u30283 : Upper (D 6) (R 6) [10,20,130,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30284 : Route 9 := (fun mask => (mask,id))

def c30284 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30284 : Upper (D 6) (R 6) [10,20,130,288,96] 13 := by
  apply FastRouting.sound _ _ [10,20,130,288,96] 13 (by decide) (choices 1) [1,4,64] r30284 c30284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11807
  · exact u11808
  · exact u11809

def b30285 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 22 164 41 19 356 324 452 324), lower := (rows 11 22 164 41 19 32 64 128 256), losses := [] }

theorem u30285 : Upper (D 6) (R 6) [10,20,160,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30286 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 22 164 41 21 354 322 450 322), lower := (rows 11 22 164 41 21 32 64 128 256), losses := [] }

theorem u30286 : Upper (D 6) (R 6) [10,20,160,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30287 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 18, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 11 22 164 41 22 353 321 449 321), lower := (rows 11 22 164 41 22 32 64 128 256), losses := [] }

theorem u30287 : Upper (D 6) (R 6) [10,20,160,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30288 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0),(4,5)], upper := (rows 11 22 164 41 81 358 326 454 326), lower := (rows 11 22 164 41 81 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 66 130 258), good := (rows 475 470 132 25 81 0 64 128 256) }] }

theorem u30288 : Upper (D 6) (R 6) [10,20,160,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30289 : Route 9 := (fun mask => (mask,id))

def c30289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30289 : Upper (D 6) (R 6) [10,20,160,33,66] 13 := by
  apply FastRouting.sound _ _ [10,20,160,33,66] 13 (by decide) (choices 1) [1,4,64,256] r30289 c30289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11810
  · exact u11811
  · exact u11812
  · exact u11813

def b30290 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 164 41 84 355 323 451 323), lower := (rows 11 22 164 41 84 32 64 128 256), losses := [] }

theorem u30290 : Upper (D 6) (R 6) [10,20,160,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30291 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(2,0),(4,5)], upper := (rows 11 22 164 41 273 102 70 198 326), lower := (rows 11 22 164 41 273 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 66 130 258), good := (rows 475 470 132 25 273 0 64 128 256) }] }

theorem u30291 : Upper (D 6) (R 6) [10,20,160,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30292 : Route 9 := (fun mask => (mask,id))

def c30292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30292 : Upper (D 6) (R 6) [10,20,160,33,258] 13 := by
  apply FastRouting.sound _ _ [10,20,160,33,258] 13 (by decide) (choices 1) [1,4,64] r30292 c30292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11814
  · exact u11815
  · exact u11816

def b30293 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 164 41 276 99 67 195 323), lower := (rows 11 22 164 41 276 32 64 128 256), losses := [] }

theorem u30293 : Upper (D 6) (R 6) [10,20,160,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30294 : Route 9 := (fun mask => (mask,id))

def c30294 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30294 : Upper (D 6) (R 6) [10,20,160,33,320] 13 := by
  apply FastRouting.sound _ _ [10,20,160,33,320] 13 (by decide) (choices 1) [1,2,4,64] r30294 c30294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11817
  · exact u11818
  · exact u11819
  · exact u11820

def b30295 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 22 164 73 19 356 356 484 356), lower := (rows 11 22 164 73 19 32 64 128 256), losses := [] }

theorem u30295 : Upper (D 6) (R 6) [10,20,160,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30296 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 361, targets := 4 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 22 164 73 21 354 354 482 354), lower := (rows 11 22 164 73 21 32 64 128 256), losses := [] }

theorem u30296 : Upper (D 6) (R 6) [10,20,160,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30297 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 18, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 164 73 22 353 353 481 353), lower := (rows 11 22 164 73 22 32 64 128 256), losses := [] }

theorem u30297 : Upper (D 6) (R 6) [10,20,160,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30298 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 4, region := 454, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 22 164 73 49 358 326 454 326), lower := (rows 11 22 164 73 49 32 64 128 256), losses := [] }

theorem u30298 : Upper (D 6) (R 6) [10,20,160,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30299 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 164 73 50 357 325 453 325), lower := (rows 11 22 164 73 50 32 64 128 256), losses := [] }

theorem u30299 : Upper (D 6) (R 6) [10,20,160,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u30299
end Delivery.IrregularNine14.P06
