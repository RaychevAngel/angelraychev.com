import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0010

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8340 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 105, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 41 131 324 74 22 48 96 133 261), lower := (rows 41 131 324 74 22 48 96 128 256), losses := [] }

theorem u8340 : Upper (D 6) (R 6) [40,129,320,66,6,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8340 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8341 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 72, targets := 36 },{ cop := 3, region := 308, targets := 1 }], pairs := [(2,0),(3,2),(3,5)], upper := (rows 41 131 324 74 50 36 65 148 276), lower := (rows 41 131 324 74 50 36 65 128 256), losses := [] }

theorem u8341 : Upper (D 6) (R 6) [40,129,320,66,34,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8342 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 146, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 41 131 324 74 50 36 68 145 273), lower := (rows 41 131 324 74 50 36 68 128 256), losses := [] }

theorem u8342 : Upper (D 6) (R 6) [40,129,320,66,34,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8343 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 293, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 41 131 324 74 50 36 80 133 261), lower := (rows 41 131 324 74 50 36 80 128 256), losses := [] }

theorem u8343 : Upper (D 6) (R 6) [40,129,320,66,34,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8343 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8344 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 73, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 131 324 88 52 34 65 134 262), lower := (rows 41 131 324 88 52 34 65 128 256), losses := [] }

theorem u8344 : Upper (D 6) (R 6) [40,129,320,80,36,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8345 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,0)], upper := (rows 41 131 324 88 52 34 66 133 261), lower := (rows 41 131 324 88 52 34 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 28 20 98 98 128 256), good := (rows 104 226 380 120 124 98 98 128 256) }] }

theorem u8345 : Upper (D 6) (R 6) [40,129,320,80,36,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8346 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 41 131 324 88 52 34 68 131 259), lower := (rows 41 131 324 88 52 34 68 128 256), losses := [] }

theorem u8346 : Upper (D 6) (R 6) [40,129,320,80,36,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8347 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 486, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 134 262 11 21 96 80 224 352), lower := (rows 41 134 262 11 21 96 80 128 256), losses := [] }

theorem u8347 : Upper (D 6) (R 6) [40,132,258,3,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8347 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8348 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 134 262 11 21 96 96 208 336), lower := (rows 41 134 262 11 21 96 96 128 256), losses := [] }

theorem u8348 : Upper (D 6) (R 6) [40,132,258,3,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8349 : PairBound 9 := { available := 80, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 134 262 11 52 96 65 208 336), lower := (rows 41 134 262 11 52 96 65 128 256), losses := [] }

theorem u8349 : Upper (D 6) (R 6) [40,132,258,3,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8350 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 41 134 262 11 52 96 80 193 321), lower := (rows 41 134 262 11 52 96 80 128 256), losses := [] }

theorem u8350 : Upper (D 6) (R 6) [40,132,258,3,36,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8350 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8351 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 41 134 262 11 81 96 68 176 304), lower := (rows 41 134 262 11 81 96 68 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 24 126 70 153 281), good := (rows 441 228 356 505 497 96 100 128 256) }] }

theorem u8351 : Upper (D 6) (R 6) [40,132,258,3,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8352 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 113, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 134 262 11 81 96 80 164 292), lower := (rows 41 134 262 11 81 96 80 128 256), losses := [] }

theorem u8352 : Upper (D 6) (R 6) [40,132,258,3,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8352 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8353 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 41 134 262 11 81 96 96 148 276), lower := (rows 41 134 262 11 81 96 96 128 256), losses := [] }

theorem u8353 : Upper (D 6) (R 6) [40,132,258,3,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8354 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 134 262 11 84 48 65 224 352), lower := (rows 41 134 262 11 84 48 65 128 256), losses := [] }

theorem u8354 : Upper (D 6) (R 6) [40,132,258,3,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8354 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8355 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 41 134 262 11 84 48 96 193 321), lower := (rows 41 134 262 11 84 48 96 128 256), losses := [] }

theorem u8355 : Upper (D 6) (R 6) [40,132,258,3,68,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8355 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8356 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 134 262 11 84 96 65 176 304), lower := (rows 41 134 262 11 84 96 65 128 256), losses := [] }

theorem u8356 : Upper (D 6) (R 6) [40,132,258,3,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8357 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 134 262 11 84 96 80 161 289), lower := (rows 41 134 262 11 84 96 80 128 256), losses := [] }

theorem u8357 : Upper (D 6) (R 6) [40,132,258,3,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8357 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8358 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 2, region := 112, targets := 1 }], pairs := [(0,2),(3,2),(4,0)], upper := (rows 41 134 262 11 84 96 96 145 273), lower := (rows 41 134 262 11 84 96 96 128 256), losses := [] }

theorem u8358 : Upper (D 6) (R 6) [40,132,258,3,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8359 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 97, targets := 6 },{ cop := 5, region := 390, targets := 1 }], pairs := [(0,1),(0,2),(1,0)], upper := (rows 41 134 262 26 21 96 65 224 352), lower := (rows 41 134 262 26 21 96 65 128 256), losses := [] }

theorem u8359 : Upper (D 6) (R 6) [40,132,258,18,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8360 : Route 9 := (fun mask => (mask,id))

def c8360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8360 : Upper (D 6) (R 6) [40,132,258,18,5,64,32] 13 := by
  apply FastRouting.sound _ _ [40,132,258,18,5,64,32] 13 (by decide) (choices 1) [1,64] r8360 c8360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u645
  · exact u646

def b8361 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 41 134 262 73 82 36 65 176 304), lower := (rows 41 134 262 73 82 36 65 128 256), losses := [] }

theorem u8361 : Upper (D 6) (R 6) [40,132,258,65,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8362 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 134 262 73 82 36 80 161 289), lower := (rows 41 134 262 73 82 36 80 128 256), losses := [] }

theorem u8362 : Upper (D 6) (R 6) [40,132,258,65,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8362 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8363 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 73, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 262 73 82 36 96 145 273), lower := (rows 41 134 262 73 82 36 96 128 256), losses := [] }

theorem u8363 : Upper (D 6) (R 6) [40,132,258,65,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8364 : Route 9 := (fun mask => (mask,id))

def c8364 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8364 : Upper (D 6) (R 6) [40,132,258,66,5,16,1] 13 := by
  apply FastRouting.sound _ _ [40,132,258,66,5,16,1] 13 (by decide) (choices 1) [32,64] r8364 c8364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u647
  · exact u648

def r8365 : Route 9 := (fun mask => (mask,id))

def c8365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8365 : Upper (D 6) (R 6) [40,132,258,66,5,16,32] 13 := by
  apply FastRouting.sound _ _ [40,132,258,66,5,16,32] 13 (by decide) (choices 1) [1,64] r8365 c8365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u649
  · exact u650

def b8366 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 134 276 11 52 96 65 194 322), lower := (rows 41 134 276 11 52 96 65 128 256), losses := [] }

theorem u8366 : Upper (D 6) (R 6) [40,132,272,3,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8367 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 1, region := 112, targets := 1 }], pairs := [(0,2),(3,2),(4,0)], upper := (rows 41 134 276 11 52 96 66 193 321), lower := (rows 41 134 276 11 52 96 66 128 256), losses := [] }

theorem u8367 : Upper (D 6) (R 6) [40,132,272,3,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8368 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 134 276 11 81 96 66 164 292), lower := (rows 41 134 276 11 81 96 66 128 256), losses := [] }

theorem u8368 : Upper (D 6) (R 6) [40,132,272,3,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8369 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 41 134 276 11 81 96 68 162 290), lower := (rows 41 134 276 11 81 96 68 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 24 126 70 128 256), good := (rows 57 228 372 121 113 96 100 128 256) }] }

theorem u8369 : Upper (D 6) (R 6) [40,132,272,3,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8370 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 41 134 276 11 81 96 96 134 262), lower := (rows 41 134 276 11 81 96 96 128 256), losses := [] }

theorem u8370 : Upper (D 6) (R 6) [40,132,272,3,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8371 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 134 276 11 82 96 65 164 292), lower := (rows 41 134 276 11 82 96 65 128 256), losses := [] }

theorem u8371 : Upper (D 6) (R 6) [40,132,272,3,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8372 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 41, targets := 4 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,2),(3,2),(4,0)], upper := (rows 41 134 276 11 82 96 68 161 289), lower := (rows 41 134 276 11 82 96 68 128 256), losses := [] }

theorem u8372 : Upper (D 6) (R 6) [40,132,272,3,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8373 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 134 276 11 82 96 96 133 261), lower := (rows 41 134 276 11 82 96 96 128 256), losses := [] }

theorem u8373 : Upper (D 6) (R 6) [40,132,272,3,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8374 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 134 276 11 84 96 65 162 290), lower := (rows 41 134 276 11 84 96 65 128 256), losses := [] }

theorem u8374 : Upper (D 6) (R 6) [40,132,272,3,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8375 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,2),(3,2),(4,0)], upper := (rows 41 134 276 11 84 96 66 161 289), lower := (rows 41 134 276 11 84 96 66 128 256), losses := [] }

theorem u8375 : Upper (D 6) (R 6) [40,132,272,3,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8376 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 41 134 276 11 84 96 96 131 259), lower := (rows 41 134 276 11 84 96 96 128 256), losses := [] }

theorem u8376 : Upper (D 6) (R 6) [40,132,272,3,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8377 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 134 276 13 50 96 65 194 322), lower := (rows 41 134 276 13 50 96 65 128 256), losses := [] }

theorem u8377 : Upper (D 6) (R 6) [40,132,272,5,34,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8378 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 112, targets := 5 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,5),(4,0),(4,2)], upper := (rows 41 134 276 13 50 96 66 193 321), lower := (rows 41 134 276 13 50 96 66 128 256), losses := [] }

theorem u8378 : Upper (D 6) (R 6) [40,132,272,5,34,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8379 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 134 276 13 82 34 65 224 352), lower := (rows 41 134 276 13 82 34 65 128 256), losses := [] }

theorem u8379 : Upper (D 6) (R 6) [40,132,272,5,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8380 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 112, targets := 5 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(4,0),(4,2)], upper := (rows 41 134 276 13 82 34 96 193 321), lower := (rows 41 134 276 13 82 34 96 128 256), losses := [] }

theorem u8380 : Upper (D 6) (R 6) [40,132,272,5,66,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8381 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 486, targets := 1 }], pairs := [(0,1),(1,0),(2,0)], upper := (rows 41 134 276 73 19 34 68 224 352), lower := (rows 41 134 276 73 19 34 68 128 256), losses := [{ target := 1, region := (rows 33 0 4 56 16 32 70 160 288), good := (rows 425 196 348 73 89 489 68 128 256) }] }

theorem u8381 : Upper (D 6) (R 6) [40,132,272,65,3,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8382 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 276 73 19 34 96 196 324), lower := (rows 41 134 276 73 19 34 96 128 256), losses := [] }

theorem u8382 : Upper (D 6) (R 6) [40,132,272,65,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8383 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 72, targets := 4 }], pairs := [(1,0),(2,0),(3,2)], upper := (rows 41 134 276 73 19 36 66 224 352), lower := (rows 41 134 276 73 19 36 66 128 256), losses := [] }

theorem u8383 : Upper (D 6) (R 6) [40,132,272,65,3,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8384 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 73, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 276 73 19 36 96 194 322), lower := (rows 41 134 276 73 19 36 96 128 256), losses := [] }

theorem u8384 : Upper (D 6) (R 6) [40,132,272,65,3,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8385 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 41 134 276 73 82 34 65 164 292), lower := (rows 41 134 276 73 82 34 65 128 256), losses := [] }

theorem u8385 : Upper (D 6) (R 6) [40,132,272,65,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8386 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 41, targets := 4 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,2),(3,2),(4,0)], upper := (rows 41 134 276 73 82 34 68 161 289), lower := (rows 41 134 276 73 82 34 68 128 256), losses := [] }

theorem u8386 : Upper (D 6) (R 6) [40,132,272,65,66,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8387 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 276 73 82 34 96 133 261), lower := (rows 41 134 276 73 82 34 96 128 256), losses := [] }

theorem u8387 : Upper (D 6) (R 6) [40,132,272,65,66,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8388 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 41 134 276 73 82 36 65 162 290), lower := (rows 41 134 276 73 82 36 65 128 256), losses := [] }

theorem u8388 : Upper (D 6) (R 6) [40,132,272,65,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8389 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 301, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 134 276 73 82 36 66 161 289), lower := (rows 41 134 276 73 82 36 66 128 256), losses := [] }

theorem u8389 : Upper (D 6) (R 6) [40,132,272,65,66,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8390 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 73, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 276 73 82 36 96 131 259), lower := (rows 41 134 276 73 82 36 96 128 256), losses := [] }

theorem u8390 : Upper (D 6) (R 6) [40,132,272,65,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8391 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 41 134 276 73 84 34 65 162 290), lower := (rows 41 134 276 73 84 34 65 128 256), losses := [] }

theorem u8391 : Upper (D 6) (R 6) [40,132,272,65,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8392 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,2),(3,2),(4,0)], upper := (rows 41 134 276 73 84 34 66 161 289), lower := (rows 41 134 276 73 84 34 66 128 256), losses := [] }

theorem u8392 : Upper (D 6) (R 6) [40,132,272,65,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8393 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 276 73 84 34 96 131 259), lower := (rows 41 134 276 73 84 34 96 128 256), losses := [] }

theorem u8393 : Upper (D 6) (R 6) [40,132,272,65,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8394 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 41 134 276 76 19 34 65 224 352), lower := (rows 41 134 276 76 19 34 65 128 256), losses := [{ target := 1, region := (rows 1 0 20 28 16 32 81 129 257), good := (rows 489 140 348 76 477 32 449 128 256) }] }

theorem u8394 : Upper (D 6) (R 6) [40,132,272,68,3,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8395 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 104, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 41 134 276 76 19 34 96 193 321), lower := (rows 41 134 276 76 19 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 97 145 273), good := (rows 489 132 412 76 477 96 96 128 256) }] }

theorem u8395 : Upper (D 6) (R 6) [40,132,272,68,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8396 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 41 134 276 76 82 34 65 161 289), lower := (rows 41 134 276 76 82 34 65 128 256), losses := [{ target := 6, region := (rows 9 26 20 8 16 63 0 201 329), good := (rows 427 166 310 431 438 34 417 128 256) }] }

theorem u8396 : Upper (D 6) (R 6) [40,132,272,68,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8397 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 120, targets := 1 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 41 134 276 76 82 34 96 129 257), lower := (rows 41 134 276 76 82 34 96 128 256), losses := [] }

theorem u8397 : Upper (D 6) (R 6) [40,132,272,68,66,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8398 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 41 134 276 76 112 34 65 131 259), lower := (rows 41 134 276 76 112 34 65 128 256), losses := [] }

theorem u8398 : Upper (D 6) (R 6) [40,132,272,68,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8399 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 269, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 134 276 76 112 34 66 129 257), lower := (rows 41 134 276 76 112 34 66 128 256), losses := [] }

theorem u8399 : Upper (D 6) (R 6) [40,132,272,68,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u8399
end Delivery.IrregularNine14.P06
