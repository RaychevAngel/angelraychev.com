import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0315
import IrregularNine14P07C0316

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r34320 : Route 9 := (fun mask => (mask,id))

def c34320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34320 : Upper (D 7) (R 7) [34,68,10,384,192] 13 := by
  apply FastRouting.sound _ _ [34,68,10,384,192] 13 (by decide) (choices 1) [1,16] r34320 c34320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18955
  · exact u18956

def b34321 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 14, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 35 70 28 11 81 416 480 416 416), lower := (rows 35 70 28 11 81 32 64 128 256), losses := [] }

theorem u34321 : Upper (D 7) (R 7) [34,68,24,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34322 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 28 11 112 417 449 385 385), lower := (rows 35 70 28 11 112 32 64 128 256), losses := [] }

theorem u34322 : Upper (D 7) (R 7) [34,68,24,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34323 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 28 11 145 480 480 480 480), lower := (rows 35 70 28 11 145 32 64 128 256), losses := [] }

theorem u34323 : Upper (D 7) (R 7) [34,68,24,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34324 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,6),(3,7),(4,1)], upper := (rows 35 70 28 11 176 481 449 449 449), lower := (rows 35 70 28 11 176 32 64 128 256), losses := [] }

theorem u34324 : Upper (D 7) (R 7) [34,68,24,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34325 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 8, targets := 160 },{ cop := 1, region := 425, targets := 64 }], pairs := [(0,6),(3,5),(3,6),(3,7)], upper := (rows 35 70 28 11 208 417 481 417 417), lower := (rows 35 70 28 11 208 32 64 128 256), losses := [] }

theorem u34325 : Upper (D 7) (R 7) [34,68,24,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34326 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 28 11 273 224 224 224 480), lower := (rows 35 70 28 11 273 32 64 128 256), losses := [] }

theorem u34326 : Upper (D 7) (R 7) [34,68,24,3,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34327 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,6),(3,7),(4,1)], upper := (rows 35 70 28 11 304 225 193 193 449), lower := (rows 35 70 28 11 304 32 64 128 256), losses := [] }

theorem u34327 : Upper (D 7) (R 7) [34,68,24,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34328 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 8, targets := 160 },{ cop := 1, region := 169, targets := 64 }], pairs := [(0,6),(3,5),(3,6),(3,7)], upper := (rows 35 70 28 11 336 161 225 161 417), lower := (rows 35 70 28 11 336 32 64 128 256), losses := [] }

theorem u34328 : Upper (D 7) (R 7) [34,68,24,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34329 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 28 11 400 225 225 225 481), lower := (rows 35 70 28 11 400 32 64 128 256), losses := [] }

theorem u34329 : Upper (D 7) (R 7) [34,68,24,3,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34330 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 28 41 81 418 450 386 386), lower := (rows 35 70 28 41 81 32 64 128 256), losses := [] }

theorem u34330 : Upper (D 7) (R 7) [34,68,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34331 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 28 41 145 482 450 450 450), lower := (rows 35 70 28 41 145 32 64 128 256), losses := [] }

theorem u34331 : Upper (D 7) (R 7) [34,68,24,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34332 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 64 }], pairs := [(1,5),(2,5),(3,6),(4,5)], upper := (rows 35 70 28 41 146 481 449 449 449), lower := (rows 35 70 28 41 146 32 64 128 256), losses := [] }

theorem u34332 : Upper (D 7) (R 7) [34,68,24,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34333 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 28 41 208 419 451 387 387), lower := (rows 35 70 28 41 208 32 64 128 256), losses := [] }

theorem u34333 : Upper (D 7) (R 7) [34,68,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34334 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 28 41 273 226 194 194 450), lower := (rows 35 70 28 41 273 32 64 128 256), losses := [] }

theorem u34334 : Upper (D 7) (R 7) [34,68,24,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34335 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 64 }], pairs := [(1,5),(2,5),(3,6),(4,5)], upper := (rows 35 70 28 41 274 225 193 193 449), lower := (rows 35 70 28 41 274 32 64 128 256), losses := [] }

theorem u34335 : Upper (D 7) (R 7) [34,68,24,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34335 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34336 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 28 41 336 163 195 131 387), lower := (rows 35 70 28 41 336 32 64 128 256), losses := [] }

theorem u34336 : Upper (D 7) (R 7) [34,68,24,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34337 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 28 41 400 227 195 195 451), lower := (rows 35 70 28 41 400 32 64 128 256), losses := [] }

theorem u34337 : Upper (D 7) (R 7) [34,68,24,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34338 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 464, targets := 2 }], pairs := [(0,6),(3,0),(3,6),(4,1)], upper := (rows 35 70 28 42 81 417 449 385 385), lower := (rows 35 70 28 42 81 32 64 128 256), losses := [] }

theorem u34338 : Upper (D 7) (R 7) [34,68,24,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34339 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 28 42 145 481 449 449 449), lower := (rows 35 70 28 42 145 32 64 128 256), losses := [] }

theorem u34339 : Upper (D 7) (R 7) [34,68,24,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34340 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 464, targets := 2 }], pairs := [(0,6),(3,0),(3,6),(4,1)], upper := (rows 35 70 28 42 208 417 449 385 385), lower := (rows 35 70 28 42 208 32 64 128 256), losses := [] }

theorem u34340 : Upper (D 7) (R 7) [34,68,24,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34341 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 28 42 273 225 193 193 449), lower := (rows 35 70 28 42 273 32 64 128 256), losses := [] }

theorem u34341 : Upper (D 7) (R 7) [34,68,24,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34342 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 169, targets := 64 },{ cop := 0, region := 8, targets := 1 },{ cop := 0, region := 464, targets := 2 }], pairs := [(0,6),(3,0),(3,6),(4,1)], upper := (rows 35 70 28 42 336 161 193 129 385), lower := (rows 35 70 28 42 336 32 64 128 256), losses := [] }

theorem u34342 : Upper (D 7) (R 7) [34,68,24,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34343 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 28 42 400 225 193 193 449), lower := (rows 35 70 28 42 400 32 64 128 256), losses := [] }

theorem u34343 : Upper (D 7) (R 7) [34,68,24,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34344 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 482, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 35 70 28 73 145 418 482 418 418), lower := (rows 35 70 28 73 145 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 27 35 0 131 259), good := (rows 435 439 28 445 433 32 0 128 256) }] }

theorem u34344 : Upper (D 7) (R 7) [34,68,24,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34345 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 456, targets := 2 }], pairs := [(0,6),(2,6),(3,1),(4,6)], upper := (rows 35 70 28 73 146 417 481 417 417), lower := (rows 35 70 28 73 146 32 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 19 63 0 159 287), good := (rows 435 439 445 445 435 32 0 128 256) }] }

theorem u34345 : Upper (D 7) (R 7) [34,68,24,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34346 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,6)], upper := (rows 35 70 28 73 176 419 451 387 387), lower := (rows 35 70 28 73 176 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 27 35 0 131 259), good := (rows 435 439 28 445 176 32 0 128 256) }] }

theorem u34346 : Upper (D 7) (R 7) [34,68,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34347 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 226, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 35 70 28 73 273 162 226 162 418), lower := (rows 35 70 28 73 273 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 27 35 0 131 259), good := (rows 435 439 28 445 433 32 0 128 256) }] }

theorem u34347 : Upper (D 7) (R 7) [34,68,24,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34348 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(2,6),(3,1),(4,6)], upper := (rows 35 70 28 73 274 161 225 161 417), lower := (rows 35 70 28 73 274 32 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 19 63 0 159 287), good := (rows 435 439 445 445 435 32 0 128 256) }] }

theorem u34348 : Upper (D 7) (R 7) [34,68,24,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34349 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 200, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,6)], upper := (rows 35 70 28 73 304 163 195 131 387), lower := (rows 35 70 28 73 304 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 27 35 0 131 259), good := (rows 435 439 28 445 304 32 0 128 256) }] }

theorem u34349 : Upper (D 7) (R 7) [34,68,24,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34350 : Route 9 := (fun mask => (mask,id))

def c34350 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34350 : Upper (D 7) (R 7) [34,68,24,65,384] 13 := by
  apply FastRouting.sound _ _ [34,68,24,65,384] 13 (by decide) (choices 1) [1,2,128] r34350 c34350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18957
  · exact u18958
  · exact u18959

def b34351 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 28 74 145 417 481 417 417), lower := (rows 35 70 28 74 145 32 64 128 256), losses := [] }

theorem u34351 : Upper (D 7) (R 7) [34,68,24,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34352 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 28 74 176 417 449 385 385), lower := (rows 35 70 28 74 176 32 64 128 256), losses := [] }

theorem u34352 : Upper (D 7) (R 7) [34,68,24,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34353 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 161, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 28 74 273 161 225 161 417), lower := (rows 35 70 28 74 273 32 64 128 256), losses := [] }

theorem u34353 : Upper (D 7) (R 7) [34,68,24,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34353 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34354 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 161, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 28 74 304 161 193 129 385), lower := (rows 35 70 28 74 304 32 64 128 256), losses := [] }

theorem u34354 : Upper (D 7) (R 7) [34,68,24,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34355 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 161, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 28 74 400 161 225 161 417), lower := (rows 35 70 28 74 400 32 64 128 256), losses := [] }

theorem u34355 : Upper (D 7) (R 7) [34,68,24,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34356 : Route 9 := (fun mask => (mask,id))

def c34356 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34356 : Upper (D 7) (R 7) [34,68,24,96,129] 13 := by
  apply FastRouting.sound _ _ [34,68,24,96,129] 13 (by decide) (choices 1) [1,2,128,256] r34356 c34356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18960
  · exact u18961
  · exact u18962
  · exact u18963

def b34357 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 456, targets := 2 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,6),(3,1),(4,5),(4,6)], upper := (rows 35 70 28 104 146 417 449 385 385), lower := (rows 35 70 28 104 146 32 64 128 256), losses := [] }

theorem u34357 : Upper (D 7) (R 7) [34,68,24,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34358 : Route 9 := (fun mask => (mask,id))

def c34358 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34358 : Upper (D 7) (R 7) [34,68,24,96,257] 13 := by
  apply FastRouting.sound _ _ [34,68,24,96,257] 13 (by decide) (choices 1) [1,2,128] r34358 c34358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18964
  · exact u18965
  · exact u18966

def b34359 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 200, targets := 2 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,6),(3,1),(4,5),(4,6)], upper := (rows 35 70 28 104 274 161 193 129 385), lower := (rows 35 70 28 104 274 32 64 128 256), losses := [] }

theorem u34359 : Upper (D 7) (R 7) [34,68,24,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34360 : Route 9 := (fun mask => (mask,id))

def c34360 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34360 : Upper (D 7) (R 7) [34,68,24,96,384] 13 := by
  apply FastRouting.sound _ _ [34,68,24,96,384] 13 (by decide) (choices 1) [1,2,128] r34360 c34360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18967
  · exact u18968
  · exact u18969

def b34361 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 20, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 35 70 28 137 145 354 354 482 354), lower := (rows 35 70 28 137 145 32 64 128 256), losses := [] }

theorem u34361 : Upper (D 7) (R 7) [34,68,24,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34362 : Route 9 := (fun mask => (mask,id))

def c34362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34362 : Upper (D 7) (R 7) [34,68,24,129,130] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,130] 13 (by decide) (choices 1) [1,64,256] r34362 c34362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18970
  · exact u18971
  · exact u18972

def r34363 : Route 9 := (fun mask => (mask,id))

def c34363 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34363 : Upper (D 7) (R 7) [34,68,24,129,160] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,160] 13 (by decide) (choices 1) [1,2,64,256] r34363 c34363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18973
  · exact u18974
  · exact u18975
  · exact u18976

def b34364 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(3,6)], upper := (rows 35 70 28 137 208 291 355 419 291), lower := (rows 35 70 28 137 208 32 64 128 256), losses := [] }

theorem u34364 : Upper (D 7) (R 7) [34,68,24,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34365 : Route 9 := (fun mask => (mask,id))

def c34365 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34365 : Upper (D 7) (R 7) [34,68,24,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,257] 13 (by decide) (choices 1) [2,64,128] r34365 c34365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18977
  · exact u18978
  · exact u18979

def r34366 : Route 9 := (fun mask => (mask,id))

def c34366 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34366 : Upper (D 7) (R 7) [34,68,24,129,258] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,258] 13 (by decide) (choices 1) [1,64,128] r34366 c34366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18980
  · exact u18981
  · exact u18982

def r34367 : Route 9 := (fun mask => (mask,id))

def c34367 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34367 : Upper (D 7) (R 7) [34,68,24,129,288] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,288] 13 (by decide) (choices 1) [1,2,64,128] r34367 c34367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18983
  · exact u18984
  · exact u18985
  · exact u18986

def r34368 : Route 9 := (fun mask => (mask,id))

def c34368 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34368 : Upper (D 7) (R 7) [34,68,24,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,320] 13 (by decide) (choices 1) [1,2,128] r34368 c34368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18987
  · exact u18988
  · exact u18989

def r34369 : Route 9 := (fun mask => (mask,id))

def c34369 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34369 : Upper (D 7) (R 7) [34,68,24,129,384] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,384] 13 (by decide) (choices 1) [1,2,64] r34369 c34369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18990
  · exact u18991
  · exact u18992

def b34370 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 2 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(4,1)], upper := (rows 35 70 28 138 176 353 321 449 321), lower := (rows 35 70 28 138 176 32 64 128 256), losses := [] }

theorem u34370 : Upper (D 7) (R 7) [34,68,24,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34371 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 14, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 28 138 208 289 353 417 289), lower := (rows 35 70 28 138 208 32 64 128 256), losses := [] }

theorem u34371 : Upper (D 7) (R 7) [34,68,24,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34372 : Route 9 := (fun mask => (mask,id))

def c34372 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34372 : Upper (D 7) (R 7) [34,68,24,130,257] 13 := by
  apply FastRouting.sound _ _ [34,68,24,130,257] 13 (by decide) (choices 1) [1,64,128] r34372 c34372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18993
  · exact u18994
  · exact u18995

def r34373 : Route 9 := (fun mask => (mask,id))

def c34373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34373 : Upper (D 7) (R 7) [34,68,24,130,288] 13 := by
  apply FastRouting.sound _ _ [34,68,24,130,288] 13 (by decide) (choices 1) [1,64,128] r34373 c34373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18996
  · exact u18997
  · exact u18998

def r34374 : Route 9 := (fun mask => (mask,id))

def c34374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34374 : Upper (D 7) (R 7) [34,68,24,130,320] 13 := by
  apply FastRouting.sound _ _ [34,68,24,130,320] 13 (by decide) (choices 1) [1,128] r34374 c34374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18999
  · exact u19000

def r34375 : Route 9 := (fun mask => (mask,id))

def c34375 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34375 : Upper (D 7) (R 7) [34,68,24,130,384] 13 := by
  apply FastRouting.sound _ _ [34,68,24,130,384] 13 (by decide) (choices 1) [1,64] r34375 c34375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19001
  · exact u19002

def b34376 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(3,6)], upper := (rows 35 70 28 168 208 291 323 387 259), lower := (rows 35 70 28 168 208 32 64 128 256), losses := [] }

theorem u34376 : Upper (D 7) (R 7) [34,68,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34377 : Route 9 := (fun mask => (mask,id))

def c34377 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34377 : Upper (D 7) (R 7) [34,68,24,160,257] 13 := by
  apply FastRouting.sound _ _ [34,68,24,160,257] 13 (by decide) (choices 1) [1,2,64,128] r34377 c34377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19003
  · exact u19004
  · exact u19005
  · exact u19006

def r34378 : Route 9 := (fun mask => (mask,id))

def c34378 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34378 : Upper (D 7) (R 7) [34,68,24,160,258] 13 := by
  apply FastRouting.sound _ _ [34,68,24,160,258] 13 (by decide) (choices 1) [1,64,128] r34378 c34378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19007
  · exact u19008
  · exact u19009

def r34379 : Route 9 := (fun mask => (mask,id))

def c34379 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34379 : Upper (D 7) (R 7) [34,68,24,160,320] 13 := by
  apply FastRouting.sound _ _ [34,68,24,160,320] 13 (by decide) (choices 1) [1,2,128] r34379 c34379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19010
  · exact u19011
  · exact u19012

#print axioms u34379
end Delivery.IrregularNine14.P07
