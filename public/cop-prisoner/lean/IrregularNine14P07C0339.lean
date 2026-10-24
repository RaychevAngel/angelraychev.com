import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0093
import IrregularNine14P07C0094

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20340 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 194 14 56 276 96 193 129 385), lower := (rows 35 194 14 56 276 96 64 128 256), losses := [] }

theorem u20340 : Upper (D 7) (R 7) [34,192,10,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20341 : Route 9 := (fun mask => (mask,id))

def c20341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20341 : Upper (D 7) (R 7) [34,192,10,48,320,1] 13 := by
  apply FastRouting.sound _ _ [34,192,10,48,320,1] 13 (by decide) (choices 1) [1,4,128] r20341 c20341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5635
  · exact u5636
  · exact u5637

def b20342 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 194 14 56 336 36 193 129 385), lower := (rows 35 194 14 56 336 36 64 128 256), losses := [] }

theorem u20342 : Upper (D 7) (R 7) [34,192,10,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20342 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20343 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 56 336 160 69 133 261), lower := (rows 35 194 14 56 336 160 64 128 256), losses := [] }

theorem u20343 : Upper (D 7) (R 7) [34,192,10,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20344 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 73 52 33 464 400 400), lower := (rows 35 194 14 73 52 33 64 128 256), losses := [] }

theorem u20344 : Upper (D 7) (R 7) [34,192,10,65,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20345 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 73 52 48 449 385 385), lower := (rows 35 194 14 73 52 48 64 128 256), losses := [] }

theorem u20345 : Upper (D 7) (R 7) [34,192,10,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20345 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20346 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 73 52 160 337 401 273), lower := (rows 35 194 14 73 52 160 64 128 256), losses := [] }

theorem u20346 : Upper (D 7) (R 7) [34,192,10,65,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20347 : Route 9 := (fun mask => (mask,id))

def c20347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20347 : Upper (D 7) (R 7) [34,192,10,65,36,256] 13 := by
  apply FastRouting.sound _ _ [34,192,10,65,36,256] 13 (by decide) (choices 1) [1,16,128] r20347 c20347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5638
  · exact u5639
  · exact u5640

def b20348 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 73 145 36 368 432 304), lower := (rows 35 194 14 73 145 36 64 128 256), losses := [] }

theorem u20348 : Upper (D 7) (R 7) [34,192,10,65,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20348 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20349 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(2,7),(3,7)], upper := (rows 35 194 14 73 145 48 356 420 292), lower := (rows 35 194 14 73 145 48 64 128 256), losses := [] }

theorem u20349 : Upper (D 7) (R 7) [34,192,10,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20349 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20350 : Route 9 := (fun mask => (mask,id))

def c20350 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20350 : Upper (D 7) (R 7) [34,192,10,65,129,256] 13 := by
  apply FastRouting.sound _ _ [34,192,10,65,129,256] 13 (by decide) (choices 1) [4,16,32] r20350 c20350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5641
  · exact u5642
  · exact u5643

def b20351 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 14 73 148 33 368 432 304), lower := (rows 35 194 14 73 148 33 64 128 256), losses := [] }

theorem u20351 : Upper (D 7) (R 7) [34,192,10,65,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20352 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(2,7),(3,7)], upper := (rows 35 194 14 73 148 48 353 417 289), lower := (rows 35 194 14 73 148 48 64 128 256), losses := [] }

theorem u20352 : Upper (D 7) (R 7) [34,192,10,65,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20352 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20353 : Route 9 := (fun mask => (mask,id))

def c20353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20353 : Upper (D 7) (R 7) [34,192,10,65,132,256] 13 := by
  apply FastRouting.sound _ _ [34,192,10,65,132,256] 13 (by decide) (choices 1) [1,16,32] r20353 c20353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5644
  · exact u5645
  · exact u5646

def b20354 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 14 73 176 33 340 404 276), lower := (rows 35 194 14 73 176 33 64 128 256), losses := [] }

theorem u20354 : Upper (D 7) (R 7) [34,192,10,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20355 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 73 176 36 337 401 273), lower := (rows 35 194 14 73 176 36 64 128 256), losses := [] }

theorem u20355 : Upper (D 7) (R 7) [34,192,10,65,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20355 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20356 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 14 73 176 48 325 389 261), lower := (rows 35 194 14 73 176 48 64 128 256), losses := [] }

theorem u20356 : Upper (D 7) (R 7) [34,192,10,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20356 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20357 : Route 9 := (fun mask => (mask,id))

def c20357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20357 : Upper (D 7) (R 7) [34,192,10,65,160,256] 13 := by
  apply FastRouting.sound _ _ [34,192,10,65,160,256] 13 (by decide) (choices 1) [1,4,16] r20357 c20357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5647
  · exact u5648
  · exact u5649

def b20358 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 73 273 36 240 176 432), lower := (rows 35 194 14 73 273 36 64 128 256), losses := [] }

theorem u20358 : Upper (D 7) (R 7) [34,192,10,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20358 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20359 : Route 9 := (fun mask => (mask,id))

def c20359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20359 : Upper (D 7) (R 7) [34,192,10,65,257,16] 13 := by
  apply FastRouting.sound _ _ [34,192,10,65,257,16] 13 (by decide) (choices 1) [4,32,128] r20359 c20359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5650
  · exact u5651
  · exact u5652

def b20360 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 73 273 160 116 180 308), lower := (rows 35 194 14 73 273 160 64 128 256), losses := [] }

theorem u20360 : Upper (D 7) (R 7) [34,192,10,65,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20361 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 14 73 276 33 240 176 432), lower := (rows 35 194 14 73 276 33 64 128 256), losses := [] }

theorem u20361 : Upper (D 7) (R 7) [34,192,10,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20362 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 35 194 14 73 276 48 225 161 417), lower := (rows 35 194 14 73 276 48 64 128 256), losses := [] }

theorem u20362 : Upper (D 7) (R 7) [34,192,10,65,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20362 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20363 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 73 276 160 113 177 305), lower := (rows 35 194 14 73 276 160 64 128 256), losses := [] }

theorem u20363 : Upper (D 7) (R 7) [34,192,10,65,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20364 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 14 73 304 33 212 148 404), lower := (rows 35 194 14 73 304 33 64 128 256), losses := [] }

theorem u20364 : Upper (D 7) (R 7) [34,192,10,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20365 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 73 304 36 209 145 401), lower := (rows 35 194 14 73 304 36 64 128 256), losses := [] }

theorem u20365 : Upper (D 7) (R 7) [34,192,10,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20365 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20366 : PairBound 9 := { available := 133, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 14 73 304 48 197 133 389), lower := (rows 35 194 14 73 304 48 64 128 256), losses := [] }

theorem u20366 : Upper (D 7) (R 7) [34,192,10,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20366 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20367 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 73 304 160 85 149 277), lower := (rows 35 194 14 73 304 160 64 128 256), losses := [] }

theorem u20367 : Upper (D 7) (R 7) [34,192,10,65,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20368 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 14 73 400 33 116 180 308), lower := (rows 35 194 14 73 400 33 64 128 256), losses := [] }

theorem u20368 : Upper (D 7) (R 7) [34,192,10,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20369 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 73 400 36 113 177 305), lower := (rows 35 194 14 73 400 36 64 128 256), losses := [] }

theorem u20369 : Upper (D 7) (R 7) [34,192,10,65,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20369 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20370 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6),(2,7),(3,7)], upper := (rows 35 194 14 73 400 48 101 165 293), lower := (rows 35 194 14 73 400 48 64 128 256), losses := [] }

theorem u20370 : Upper (D 7) (R 7) [34,192,10,65,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20370 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20371 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 88 52 33 449 385 385), lower := (rows 35 194 14 88 52 33 64 128 256), losses := [] }

theorem u20371 : Upper (D 7) (R 7) [34,192,10,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20372 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 60, targets := 1 }], pairs := [(2,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 88 52 160 321 385 257), lower := (rows 35 194 14 88 52 160 64 128 256), losses := [] }

theorem u20372 : Upper (D 7) (R 7) [34,192,10,80,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20373 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,6),(1,5),(4,6)], upper := (rows 35 194 14 88 52 288 193 129 385), lower := (rows 35 194 14 88 52 288 64 128 256), losses := [] }

theorem u20373 : Upper (D 7) (R 7) [34,192,10,80,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20373 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20374 : Route 9 := (fun mask => (mask,id))

def c20374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u20374 : Upper (D 7) (R 7) [34,192,10,80,129,1] 13 := by
  apply FastRouting.sound _ _ [34,192,10,80,129,1] 13 (by decide) (choices 1) [4,32,256] r20374 c20374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5653
  · exact u5654
  · exact u5655

def b20375 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 194 14 88 145 36 353 417 289), lower := (rows 35 194 14 88 145 36 64 128 256), losses := [] }

theorem u20375 : Upper (D 7) (R 7) [34,192,10,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20375 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20376 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 2, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 35 194 14 88 145 288 101 165 293), lower := (rows 35 194 14 88 145 288 64 128 256), losses := [] }

theorem u20376 : Upper (D 7) (R 7) [34,192,10,80,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20376 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20377 : Route 9 := (fun mask => (mask,id))

def c20377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u20377 : Upper (D 7) (R 7) [34,192,10,80,160,1] 13 := by
  apply FastRouting.sound _ _ [34,192,10,80,160,1] 13 (by decide) (choices 1) [1,4,256] r20377 c20377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5656
  · exact u5657
  · exact u5658

def b20378 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 60, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 194 14 88 176 36 321 385 257), lower := (rows 35 194 14 88 176 36 64 128 256), losses := [] }

theorem u20378 : Upper (D 7) (R 7) [34,192,10,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20378 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20379 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 2, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 35 194 14 88 176 288 69 133 261), lower := (rows 35 194 14 88 176 288 64 128 256), losses := [] }

theorem u20379 : Upper (D 7) (R 7) [34,192,10,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20379 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20380 : Route 9 := (fun mask => (mask,id))

def c20380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20380 : Upper (D 7) (R 7) [34,192,10,80,257,1] 13 := by
  apply FastRouting.sound _ _ [34,192,10,80,257,1] 13 (by decide) (choices 1) [4,32,128] r20380 c20380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5659
  · exact u5660
  · exact u5661

def b20381 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 194 14 88 273 36 225 161 417), lower := (rows 35 194 14 88 273 36 64 128 256), losses := [] }

theorem u20381 : Upper (D 7) (R 7) [34,192,10,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20381 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20382 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 88 273 160 101 165 293), lower := (rows 35 194 14 88 273 160 64 128 256), losses := [] }

theorem u20382 : Upper (D 7) (R 7) [34,192,10,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20383 : Route 9 := (fun mask => (mask,id))

def c20383 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20383 : Upper (D 7) (R 7) [34,192,10,80,260,1] 13 := by
  apply FastRouting.sound _ _ [34,192,10,80,260,1] 13 (by decide) (choices 1) [1,32,128] r20383 c20383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5662
  · exact u5663
  · exact u5664

def b20384 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 88 276 160 97 161 289), lower := (rows 35 194 14 88 276 160 64 128 256), losses := [] }

theorem u20384 : Upper (D 7) (R 7) [34,192,10,80,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20385 : Route 9 := (fun mask => (mask,id))

def c20385 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20385 : Upper (D 7) (R 7) [34,192,10,80,288,1] 13 := by
  apply FastRouting.sound _ _ [34,192,10,80,288,1] 13 (by decide) (choices 1) [1,4,128] r20385 c20385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5665
  · exact u5666
  · exact u5667

def b20386 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 194 14 88 304 36 193 129 385), lower := (rows 35 194 14 88 304 36 64 128 256), losses := [] }

theorem u20386 : Upper (D 7) (R 7) [34,192,10,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20386 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20387 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 88 304 160 69 133 261), lower := (rows 35 194 14 88 304 160 64 128 256), losses := [] }

theorem u20387 : Upper (D 7) (R 7) [34,192,10,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20388 : Route 9 := (fun mask => (mask,id))

def c20388 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20388 : Upper (D 7) (R 7) [34,192,10,80,384,1] 13 := by
  apply FastRouting.sound _ _ [34,192,10,80,384,1] 13 (by decide) (choices 1) [1,4,32] r20388 c20388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5668
  · exact u5669
  · exact u5670

def b20389 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 194 14 88 400 36 97 161 289), lower := (rows 35 194 14 88 400 36 64 128 256), losses := [] }

theorem u20389 : Upper (D 7) (R 7) [34,192,10,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20389 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20390 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 14 104 145 33 340 404 276), lower := (rows 35 194 14 104 145 33 64 128 256), losses := [] }

theorem u20390 : Upper (D 7) (R 7) [34,192,10,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20391 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 104 145 36 337 401 273), lower := (rows 35 194 14 104 145 36 64 128 256), losses := [] }

theorem u20391 : Upper (D 7) (R 7) [34,192,10,96,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20391 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20392 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(2,7),(3,7)], upper := (rows 35 194 14 104 145 48 325 389 261), lower := (rows 35 194 14 104 145 48 64 128 256), losses := [] }

theorem u20392 : Upper (D 7) (R 7) [34,192,10,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20392 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20393 : Route 9 := (fun mask => (mask,id))

def c20393 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20393 : Upper (D 7) (R 7) [34,192,10,96,129,256] 13 := by
  apply FastRouting.sound _ _ [34,192,10,96,129,256] 13 (by decide) (choices 1) [1,4,16] r20393 c20393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5671
  · exact u5672
  · exact u5673

def b20394 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 14 104 148 33 337 401 273), lower := (rows 35 194 14 104 148 33 64 128 256), losses := [] }

theorem u20394 : Upper (D 7) (R 7) [34,192,10,96,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20395 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 60, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 194 14 104 148 48 321 385 257), lower := (rows 35 194 14 104 148 48 64 128 256), losses := [] }

theorem u20395 : Upper (D 7) (R 7) [34,192,10,96,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20395 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20396 : Route 9 := (fun mask => (mask,id))

def c20396 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20396 : Upper (D 7) (R 7) [34,192,10,96,132,256] 13 := by
  apply FastRouting.sound _ _ [34,192,10,96,132,256] 13 (by decide) (choices 1) [1,16] r20396 c20396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5674
  · exact u5675

def b20397 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 14 104 273 33 212 148 404), lower := (rows 35 194 14 104 273 33 64 128 256), losses := [] }

theorem u20397 : Upper (D 7) (R 7) [34,192,10,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20398 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 104 273 36 209 145 401), lower := (rows 35 194 14 104 273 36 64 128 256), losses := [] }

theorem u20398 : Upper (D 7) (R 7) [34,192,10,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20398 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20399 : Route 9 := (fun mask => (mask,id))

def c20399 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20399 : Upper (D 7) (R 7) [34,192,10,96,257,16] 13 := by
  apply FastRouting.sound _ _ [34,192,10,96,257,16] 13 (by decide) (choices 1) [1,4,128] r20399 c20399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5676
  · exact u5677
  · exact u5678

#print axioms u20399
end Delivery.IrregularNine14.P07
