import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0100

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20340 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 25 280 36 97 225 353), lower := (rows 35 70 134 25 280 36 64 128 256), losses := [] }

theorem u20340 : Upper (D 6) (R 6) [34,68,130,17,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20341 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 25 280 96 101 165 293), lower := (rows 35 70 134 25 280 96 64 128 256), losses := [] }

theorem u20341 : Upper (D 6) (R 6) [34,68,130,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20342 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 25 304 33 76 204 332), lower := (rows 35 70 134 25 304 33 64 128 256), losses := [] }

theorem u20342 : Upper (D 6) (R 6) [34,68,130,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20343 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 25 304 36 73 201 329), lower := (rows 35 70 134 25 304 36 64 128 256), losses := [] }

theorem u20343 : Upper (D 6) (R 6) [34,68,130,17,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20344 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 25 304 40 69 197 325), lower := (rows 35 70 134 25 304 40 64 128 256), losses := [] }

theorem u20344 : Upper (D 6) (R 6) [34,68,130,17,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20344 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20345 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 25 304 96 77 141 269), lower := (rows 35 70 134 25 304 96 64 128 256), losses := [] }

theorem u20345 : Upper (D 6) (R 6) [34,68,130,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20346 : Route 9 := (fun mask => (mask,id))

def c20346 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20346 : Upper (D 6) (R 6) [34,68,130,17,320,1] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,320,1] 13 (by decide) (choices 1) [4,8,32] r20346 c20346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6036
  · exact u6037
  · exact u6038

def b20347 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 25 336 36 105 169 297), lower := (rows 35 70 134 25 336 36 64 128 256), losses := [] }

theorem u20347 : Upper (D 6) (R 6) [34,68,130,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20348 : Route 9 := (fun mask => (mask,id))

def c20348 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20348 : Upper (D 6) (R 6) [34,68,130,17,320,8] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,320,8] 13 (by decide) (choices 1) [1,4,32] r20348 c20348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6039
  · exact u6040
  · exact u6041

def b20349 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 134 28 81 33 360 424 296), lower := (rows 35 70 134 28 81 33 64 128 256), losses := [] }

theorem u20349 : Upper (D 6) (R 6) [34,68,130,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20350 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 336, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 28 81 40 353 417 289), lower := (rows 35 70 134 28 81 40 64 128 256), losses := [] }

theorem u20350 : Upper (D 6) (R 6) [34,68,130,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20350 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20351 : Route 9 := (fun mask => (mask,id))

def c20351 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20351 : Upper (D 6) (R 6) [34,68,130,20,65,256] 13 := by
  apply FastRouting.sound _ _ [34,68,130,20,65,256] 13 (by decide) (choices 1) [1,8,32] r20351 c20351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6042
  · exact u6043
  · exact u6044

def b20352 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 134 28 112 33 329 393 265), lower := (rows 35 70 134 28 112 33 64 128 256), losses := [] }

theorem u20352 : Upper (D 6) (R 6) [34,68,130,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20353 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 336, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 28 112 40 321 385 257), lower := (rows 35 70 134 28 112 40 64 128 256), losses := [] }

theorem u20353 : Upper (D 6) (R 6) [34,68,130,20,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20353 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20354 : Route 9 := (fun mask => (mask,id))

def c20354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20354 : Upper (D 6) (R 6) [34,68,130,20,96,256] 13 := by
  apply FastRouting.sound _ _ [34,68,130,20,96,256] 13 (by decide) (choices 1) [1,8] r20354 c20354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6045
  · exact u6046

def b20355 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 134 28 273 33 104 232 360), lower := (rows 35 70 134 28 273 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 8 24 63 72 136 264), good := (rows 35 99 163 505 305 33 64 128 256) }] }

theorem u20355 : Upper (D 6) (R 6) [34,68,130,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20355 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20356 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 336, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 28 273 40 97 225 353), lower := (rows 35 70 134 28 273 40 64 128 256), losses := [] }

theorem u20356 : Upper (D 6) (R 6) [34,68,130,20,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20356 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20357 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 28 273 96 105 169 297), lower := (rows 35 70 134 28 273 96 64 128 256), losses := [] }

theorem u20357 : Upper (D 6) (R 6) [34,68,130,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20358 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 134 28 280 33 97 225 353), lower := (rows 35 70 134 28 280 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 8 24 47 111 175 303), good := (rows 483 483 483 505 504 481 64 128 256) }] }

theorem u20358 : Upper (D 6) (R 6) [34,68,130,20,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20359 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 28 280 96 97 161 289), lower := (rows 35 70 134 28 280 96 64 128 256), losses := [] }

theorem u20359 : Upper (D 6) (R 6) [34,68,130,20,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20360 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 134 28 304 33 73 201 329), lower := (rows 35 70 134 28 304 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 8 24 47 72 136 264), good := (rows 35 99 163 505 304 33 64 128 256) }] }

theorem u20360 : Upper (D 6) (R 6) [34,68,130,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20361 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 28 304 40 65 193 321), lower := (rows 35 70 134 28 304 40 64 128 256), losses := [] }

theorem u20361 : Upper (D 6) (R 6) [34,68,130,20,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20361 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20362 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 28 304 96 73 137 265), lower := (rows 35 70 134 28 304 96 64 128 256), losses := [] }

theorem u20362 : Upper (D 6) (R 6) [34,68,130,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20363 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 134 28 336 33 105 169 297), lower := (rows 35 70 134 28 336 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 8 24 47 72 136 264), good := (rows 35 99 163 505 336 33 64 128 256) }] }

theorem u20363 : Upper (D 6) (R 6) [34,68,130,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20364 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 336, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 28 336 40 97 161 289), lower := (rows 35 70 134 28 336 40 64 128 256), losses := [] }

theorem u20364 : Upper (D 6) (R 6) [34,68,130,20,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20364 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20365 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 134 44 81 33 344 408 280), lower := (rows 35 70 134 44 81 33 64 128 256), losses := [] }

theorem u20365 : Upper (D 6) (R 6) [34,68,130,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20366 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 44 81 40 337 401 273), lower := (rows 35 70 134 44 81 40 64 128 256), losses := [] }

theorem u20366 : Upper (D 6) (R 6) [34,68,130,36,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20366 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20367 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 134 44 81 48 329 393 265), lower := (rows 35 70 134 44 81 48 64 128 256), losses := [] }

theorem u20367 : Upper (D 6) (R 6) [34,68,130,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20367 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20368 : Route 9 := (fun mask => (mask,id))

def c20368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20368 : Upper (D 6) (R 6) [34,68,130,36,65,256] 13 := by
  apply FastRouting.sound _ _ [34,68,130,36,65,256] 13 (by decide) (choices 1) [1,8,16] r20368 c20368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6047
  · exact u6048
  · exact u6049

def b20369 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 70 134 44 88 33 337 401 273), lower := (rows 35 70 134 44 88 33 64 128 256), losses := [] }

theorem u20369 : Upper (D 6) (R 6) [34,68,130,36,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20370 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 44 88 48 321 385 257), lower := (rows 35 70 134 44 88 48 64 128 256), losses := [] }

theorem u20370 : Upper (D 6) (R 6) [34,68,130,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20370 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20371 : Route 9 := (fun mask => (mask,id))

def c20371 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20371 : Upper (D 6) (R 6) [34,68,130,36,72,256] 13 := by
  apply FastRouting.sound _ _ [34,68,130,36,72,256] 13 (by decide) (choices 1) [1,16] r20371 c20371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6050
  · exact u6051

def b20372 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 70 134 44 273 33 88 216 344), lower := (rows 35 70 134 44 273 33 64 128 256), losses := [] }

theorem u20372 : Upper (D 6) (R 6) [34,68,130,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20373 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 44 273 40 81 209 337), lower := (rows 35 70 134 44 273 40 64 128 256), losses := [] }

theorem u20373 : Upper (D 6) (R 6) [34,68,130,36,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20373 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20374 : Route 9 := (fun mask => (mask,id))

def c20374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20374 : Upper (D 6) (R 6) [34,68,130,36,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,130,36,257,16] 13 (by decide) (choices 1) [1,8] r20374 c20374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6052
  · exact u6053

def b20375 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 44 273 96 89 153 281), lower := (rows 35 70 134 44 273 96 64 128 256), losses := [] }

theorem u20375 : Upper (D 6) (R 6) [34,68,130,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20376 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 70 134 44 280 33 81 209 337), lower := (rows 35 70 134 44 280 33 64 128 256), losses := [] }

theorem u20376 : Upper (D 6) (R 6) [34,68,130,36,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20377 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 44 280 48 65 193 321), lower := (rows 35 70 134 44 280 48 64 128 256), losses := [] }

theorem u20377 : Upper (D 6) (R 6) [34,68,130,36,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20377 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20378 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 44 280 96 81 145 273), lower := (rows 35 70 134 44 280 96 64 128 256), losses := [] }

theorem u20378 : Upper (D 6) (R 6) [34,68,130,36,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20379 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 70 134 44 336 33 89 153 281), lower := (rows 35 70 134 44 336 33 64 128 256), losses := [] }

theorem u20379 : Upper (D 6) (R 6) [34,68,130,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20380 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 44 336 40 81 145 273), lower := (rows 35 70 134 44 336 40 64 128 256), losses := [] }

theorem u20380 : Upper (D 6) (R 6) [34,68,130,36,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20380 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20381 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 134 44 336 48 73 137 265), lower := (rows 35 70 134 44 336 48 64 128 256), losses := [] }

theorem u20381 : Upper (D 6) (R 6) [34,68,130,36,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20381 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20382 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 56 81 33 332 396 268), lower := (rows 35 70 134 56 81 33 64 128 256), losses := [] }

theorem u20382 : Upper (D 6) (R 6) [34,68,130,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20383 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 56 81 36 329 393 265), lower := (rows 35 70 134 56 81 36 64 128 256), losses := [] }

theorem u20383 : Upper (D 6) (R 6) [34,68,130,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20384 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 134 56 81 40 325 389 261), lower := (rows 35 70 134 56 81 40 64 128 256), losses := [] }

theorem u20384 : Upper (D 6) (R 6) [34,68,130,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20384 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20385 : Route 9 := (fun mask => (mask,id))

def c20385 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20385 : Upper (D 6) (R 6) [34,68,130,48,65,256] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,65,256] 13 (by decide) (choices 1) [1,4,8] r20385 c20385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6054
  · exact u6055
  · exact u6056

def b20386 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 56 273 33 76 204 332), lower := (rows 35 70 134 56 273 33 64 128 256), losses := [] }

theorem u20386 : Upper (D 6) (R 6) [34,68,130,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20387 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 56 273 36 73 201 329), lower := (rows 35 70 134 56 273 36 64 128 256), losses := [] }

theorem u20387 : Upper (D 6) (R 6) [34,68,130,48,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20388 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 134 56 273 40 69 197 325), lower := (rows 35 70 134 56 273 40 64 128 256), losses := [] }

theorem u20388 : Upper (D 6) (R 6) [34,68,130,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20388 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20389 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 56 273 96 77 141 269), lower := (rows 35 70 134 56 273 96 64 128 256), losses := [] }

theorem u20389 : Upper (D 6) (R 6) [34,68,130,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20390 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 134 56 276 33 73 201 329), lower := (rows 35 70 134 56 276 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 24 16 55 80 144 272), good := (rows 35 99 163 504 505 33 64 128 256) }] }

theorem u20390 : Upper (D 6) (R 6) [34,68,130,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20391 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 134 56 276 40 65 193 321), lower := (rows 35 70 134 56 276 40 64 128 256), losses := [] }

theorem u20391 : Upper (D 6) (R 6) [34,68,130,48,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20391 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20392 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 56 276 96 73 137 265), lower := (rows 35 70 134 56 276 96 64 128 256), losses := [] }

theorem u20392 : Upper (D 6) (R 6) [34,68,130,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20393 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 70 134 56 280 33 69 197 325), lower := (rows 35 70 134 56 280 33 64 128 256), losses := [] }

theorem u20393 : Upper (D 6) (R 6) [34,68,130,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20394 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 56 280 36 65 193 321), lower := (rows 35 70 134 56 280 36 64 128 256), losses := [] }

theorem u20394 : Upper (D 6) (R 6) [34,68,130,48,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20395 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 56 280 96 69 133 261), lower := (rows 35 70 134 56 280 96 64 128 256), losses := [] }

theorem u20395 : Upper (D 6) (R 6) [34,68,130,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20396 : Route 9 := (fun mask => (mask,id))

def c20396 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20396 : Upper (D 6) (R 6) [34,68,130,48,320,1] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,320,1] 13 (by decide) (choices 1) [1,4,8] r20396 c20396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6057
  · exact u6058
  · exact u6059

def b20397 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 56 336 36 73 137 265), lower := (rows 35 70 134 56 336 36 64 128 256), losses := [] }

theorem u20397 : Upper (D 6) (R 6) [34,68,130,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20398 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 134 56 336 40 69 133 261), lower := (rows 35 70 134 56 336 40 64 128 256), losses := [] }

theorem u20398 : Upper (D 6) (R 6) [34,68,130,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20398 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20399 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 73 273 36 120 184 312), lower := (rows 35 70 134 73 273 36 64 128 256), losses := [] }

theorem u20399 : Upper (D 6) (R 6) [34,68,130,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20399
end Delivery.IrregularNine14.P06
