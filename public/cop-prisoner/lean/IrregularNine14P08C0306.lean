import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0113

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18360 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 168 49 241 209 209 465), lower := (rows 321 14 38 168 49 32 64 128 256), losses := [] }

theorem u18360 : Upper (D 8) (R 8) [320,12,34,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18360 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18361 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 168 112 177 209 145 401), lower := (rows 321 14 38 168 112 32 64 128 256), losses := [] }

theorem u18361 : Upper (D 8) (R 8) [320,12,34,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18361 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18362 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 168 145 113 113 241 369), lower := (rows 321 14 38 168 145 32 64 128 256), losses := [] }

theorem u18362 : Upper (D 8) (R 8) [320,12,34,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18362 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18363 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 168 176 113 81 209 337), lower := (rows 321 14 38 168 176 32 64 128 256), losses := [] }

theorem u18363 : Upper (D 8) (R 8) [320,12,34,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18363 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18364 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 38 168 208 49 113 177 305), lower := (rows 321 14 38 168 208 32 64 128 256), losses := [] }

theorem u18364 : Upper (D 8) (R 8) [320,12,34,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18364 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18365 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 38 200 49 177 241 177 433), lower := (rows 321 14 38 200 49 32 64 128 256), losses := [] }

theorem u18365 : Upper (D 8) (R 8) [320,12,34,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18365 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18366 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 38 200 145 49 113 177 305), lower := (rows 321 14 38 200 145 32 64 128 256), losses := [] }

theorem u18366 : Upper (D 8) (R 8) [320,12,34,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18367 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 14 38 200 176 49 113 177 305), lower := (rows 321 14 38 200 176 32 64 128 256), losses := [] }

theorem u18367 : Upper (D 8) (R 8) [320,12,34,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18367 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18368 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 52 73 145 162 226 162 418), lower := (rows 321 14 52 73 145 32 64 128 256), losses := [] }

theorem u18368 : Upper (D 8) (R 8) [320,12,48,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18368 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18369 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 52 73 146 161 225 161 417), lower := (rows 321 14 52 73 146 32 64 128 256), losses := [] }

theorem u18369 : Upper (D 8) (R 8) [320,12,48,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18370 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 321 14 52 74 145 161 225 161 417), lower := (rows 321 14 52 74 145 32 64 128 256), losses := [] }

theorem u18370 : Upper (D 8) (R 8) [320,12,48,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18370 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18371 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 14 52 104 49 163 195 131 387), lower := (rows 321 14 52 104 49 32 64 128 256), losses := [] }

theorem u18371 : Upper (D 8) (R 8) [320,12,48,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18371 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18372 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 52 104 50 161 193 129 385), lower := (rows 321 14 52 104 50 32 64 128 256), losses := [] }

theorem u18372 : Upper (D 8) (R 8) [320,12,48,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18373 : Route 9 := (fun mask => (mask,id))

def c18373 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18373 : Upper (D 8) (R 8) [320,12,48,96,129] 13 := by
  apply FastRouting.sound _ _ [320,12,48,96,129] 13 (by decide) (choices 1) [1,2,128] r18373 c18373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6799
  · exact u6800
  · exact u6801

def r18374 : Route 9 := (fun mask => (mask,id))

def c18374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18374 : Upper (D 8) (R 8) [320,12,48,96,130] 13 := by
  apply FastRouting.sound _ _ [320,12,48,96,130] 13 (by decide) (choices 1) [1,128] r18374 c18374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6802
  · exact u6803

def b18375 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 14 52 104 176 163 195 131 387), lower := (rows 321 14 52 104 176 32 64 128 256), losses := [] }

theorem u18375 : Upper (D 8) (R 8) [320,12,48,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18375 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18376 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 14 52 137 49 226 226 226 482), lower := (rows 321 14 52 137 49 32 64 128 256), losses := [] }

theorem u18376 : Upper (D 8) (R 8) [320,12,48,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18376 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18377 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 14 52 137 50 225 225 225 481), lower := (rows 321 14 52 137 50 32 64 128 256), losses := [] }

theorem u18377 : Upper (D 8) (R 8) [320,12,48,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18377 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18378 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 52 137 81 162 226 162 418), lower := (rows 321 14 52 137 81 32 64 128 256), losses := [] }

theorem u18378 : Upper (D 8) (R 8) [320,12,48,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18378 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18379 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 321 14 52 137 82 161 225 161 417), lower := (rows 321 14 52 137 82 32 64 128 256), losses := [] }

theorem u18379 : Upper (D 8) (R 8) [320,12,48,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18379 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18380 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 14 52 137 112 163 227 163 419), lower := (rows 321 14 52 137 112 32 64 128 256), losses := [] }

theorem u18380 : Upper (D 8) (R 8) [320,12,48,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18381 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 321 14 52 137 145 98 98 226 354), lower := (rows 321 14 52 137 145 32 64 128 256), losses := [] }

theorem u18381 : Upper (D 8) (R 8) [320,12,48,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18381 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18382 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 52 137 146 97 97 225 353), lower := (rows 321 14 52 137 146 32 64 128 256), losses := [] }

theorem u18382 : Upper (D 8) (R 8) [320,12,48,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18382 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18383 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 14 52 137 176 99 99 227 355), lower := (rows 321 14 52 137 176 32 64 128 256), losses := [] }

theorem u18383 : Upper (D 8) (R 8) [320,12,48,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18384 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 52 137 208 35 99 163 291), lower := (rows 321 14 52 137 208 32 64 128 256), losses := [] }

theorem u18384 : Upper (D 8) (R 8) [320,12,48,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18384 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18385 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 14 52 138 49 225 225 225 481), lower := (rows 321 14 52 138 49 32 64 128 256), losses := [] }

theorem u18385 : Upper (D 8) (R 8) [320,12,48,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18386 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 52 138 81 161 225 161 417), lower := (rows 321 14 52 138 81 32 64 128 256), losses := [] }

theorem u18386 : Upper (D 8) (R 8) [320,12,48,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18387 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 14 52 138 112 161 225 161 417), lower := (rows 321 14 52 138 112 32 64 128 256), losses := [] }

theorem u18387 : Upper (D 8) (R 8) [320,12,48,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18387 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18388 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 52 138 145 97 97 225 353), lower := (rows 321 14 52 138 145 32 64 128 256), losses := [] }

theorem u18388 : Upper (D 8) (R 8) [320,12,48,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18389 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 52 138 176 97 97 225 353), lower := (rows 321 14 52 138 176 32 64 128 256), losses := [] }

theorem u18389 : Upper (D 8) (R 8) [320,12,48,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18390 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 52 138 208 33 97 161 289), lower := (rows 321 14 52 138 208 32 64 128 256), losses := [] }

theorem u18390 : Upper (D 8) (R 8) [320,12,48,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18390 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18391 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 14 52 168 49 227 195 195 451), lower := (rows 321 14 52 168 49 32 64 128 256), losses := [] }

theorem u18391 : Upper (D 8) (R 8) [320,12,48,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18391 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18392 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 52 168 50 225 193 193 449), lower := (rows 321 14 52 168 50 32 64 128 256), losses := [] }

theorem u18392 : Upper (D 8) (R 8) [320,12,48,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18393 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 52 168 81 163 227 163 419), lower := (rows 321 14 52 168 81 32 64 128 256), losses := [] }

theorem u18393 : Upper (D 8) (R 8) [320,12,48,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18393 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18394 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 321 14 52 168 82 161 225 161 417), lower := (rows 321 14 52 168 82 32 64 128 256), losses := [] }

theorem u18394 : Upper (D 8) (R 8) [320,12,48,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18394 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18395 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 14 52 168 112 163 195 131 387), lower := (rows 321 14 52 168 112 32 64 128 256), losses := [] }

theorem u18395 : Upper (D 8) (R 8) [320,12,48,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18396 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 52 168 145 99 99 227 355), lower := (rows 321 14 52 168 145 32 64 128 256), losses := [] }

theorem u18396 : Upper (D 8) (R 8) [320,12,48,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18397 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 52 168 146 97 97 225 353), lower := (rows 321 14 52 168 146 32 64 128 256), losses := [] }

theorem u18397 : Upper (D 8) (R 8) [320,12,48,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18398 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 321 14 52 168 176 99 67 195 323), lower := (rows 321 14 52 168 176 32 64 128 256), losses := [] }

theorem u18398 : Upper (D 8) (R 8) [320,12,48,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18399 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 52 168 208 35 99 163 291), lower := (rows 321 14 52 168 208 32 64 128 256), losses := [] }

theorem u18399 : Upper (D 8) (R 8) [320,12,48,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18399 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18400 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 14 52 200 49 163 227 163 419), lower := (rows 321 14 52 200 49 32 64 128 256), losses := [] }

theorem u18400 : Upper (D 8) (R 8) [320,12,48,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18400 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18401 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 14 52 200 50 161 225 161 417), lower := (rows 321 14 52 200 50 32 64 128 256), losses := [] }

theorem u18401 : Upper (D 8) (R 8) [320,12,48,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18401 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18402 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 52 200 145 35 99 163 291), lower := (rows 321 14 52 200 145 32 64 128 256), losses := [] }

theorem u18402 : Upper (D 8) (R 8) [320,12,48,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18402 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18403 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 14 52 200 146 33 97 161 289), lower := (rows 321 14 52 200 146 32 64 128 256), losses := [] }

theorem u18403 : Upper (D 8) (R 8) [320,12,48,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18403 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18404 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 321 14 52 200 176 35 99 163 291), lower := (rows 321 14 52 200 176 32 64 128 256), losses := [] }

theorem u18404 : Upper (D 8) (R 8) [320,12,48,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18404 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18405 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 69 137 50 176 240 176 432), lower := (rows 321 14 69 137 50 32 64 128 256), losses := [] }

theorem u18405 : Upper (D 8) (R 8) [320,12,65,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18405 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18406 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 69 137 176 50 114 178 306), lower := (rows 321 14 69 137 176 32 64 128 256), losses := [] }

theorem u18406 : Upper (D 8) (R 8) [320,12,65,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18406 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18407 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 69 138 49 176 240 176 432), lower := (rows 321 14 69 138 49 32 64 128 256), losses := [] }

theorem u18407 : Upper (D 8) (R 8) [320,12,65,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18407 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18408 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 69 152 49 162 226 162 418), lower := (rows 321 14 69 152 49 32 64 128 256), losses := [] }

theorem u18408 : Upper (D 8) (R 8) [320,12,65,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18408 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18409 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 69 152 50 161 225 161 417), lower := (rows 321 14 69 152 50 32 64 128 256), losses := [] }

theorem u18409 : Upper (D 8) (R 8) [320,12,65,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18409 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18410 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 69 168 49 178 242 178 434), lower := (rows 321 14 69 168 49 32 64 128 256), losses := [] }

theorem u18410 : Upper (D 8) (R 8) [320,12,65,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18410 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18411 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 69 168 50 177 241 177 433), lower := (rows 321 14 69 168 50 32 64 128 256), losses := [] }

theorem u18411 : Upper (D 8) (R 8) [320,12,65,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18411 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18412 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 186, targets := 64 }], pairs := [(1,6)], upper := (rows 321 14 69 168 145 50 114 178 306), lower := (rows 321 14 69 168 145 32 64 128 256), losses := [] }

theorem u18412 : Upper (D 8) (R 8) [320,12,65,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18412 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18413 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 14 70 137 49 176 240 176 432), lower := (rows 321 14 70 137 49 32 64 128 256), losses := [] }

theorem u18413 : Upper (D 8) (R 8) [320,12,66,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18413 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18414 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 14 70 137 176 49 113 177 305), lower := (rows 321 14 70 137 176 32 64 128 256), losses := [] }

theorem u18414 : Upper (D 8) (R 8) [320,12,66,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18414 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18415 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 14 70 152 49 161 225 161 417), lower := (rows 321 14 70 152 49 32 64 128 256), losses := [] }

theorem u18415 : Upper (D 8) (R 8) [320,12,66,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18415 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18416 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 14 70 168 49 177 241 177 433), lower := (rows 321 14 70 168 49 32 64 128 256), losses := [] }

theorem u18416 : Upper (D 8) (R 8) [320,12,66,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18416 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18417 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 14 70 168 145 49 113 177 305), lower := (rows 321 14 70 168 145 32 64 128 256), losses := [] }

theorem u18417 : Upper (D 8) (R 8) [320,12,66,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18417 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18418 : Route 9 := (fun mask => (mask,id))

def c18418 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18418 : Upper (D 8) (R 8) [320,12,80,129,33] 13 := by
  apply FastRouting.sound _ _ [320,12,80,129,33] 13 (by decide) (choices 1) [2,128] r18418 c18418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6804
  · exact u6805

def b18419 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 321 14 84 137 50 161 225 161 417), lower := (rows 321 14 84 137 50 32 64 128 256), losses := [] }

theorem u18419 : Upper (D 8) (R 8) [320,12,80,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18419 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u18419
end Delivery.IrregularNine14.P08
