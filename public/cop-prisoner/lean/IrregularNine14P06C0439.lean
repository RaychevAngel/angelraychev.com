import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0136
import IrregularNine14P06C0137

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26340 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 41 131 261 74 50 48 68 196 324), lower := (rows 41 131 261 74 50 48 64 128 256), losses := [] }

theorem u26340 : Upper (D 6) (R 6) [40,129,257,66,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26340 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26341 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 261 74 50 96 84 148 276), lower := (rows 41 131 261 74 50 96 64 128 256), losses := [] }

theorem u26341 : Upper (D 6) (R 6) [40,129,257,66,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26342 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 261 74 52 34 84 212 340), lower := (rows 41 131 261 74 52 34 64 128 256), losses := [] }

theorem u26342 : Upper (D 6) (R 6) [40,129,257,66,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26343 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 41 131 261 74 52 36 82 210 338), lower := (rows 41 131 261 74 52 36 64 128 256), losses := [] }

theorem u26343 : Upper (D 6) (R 6) [40,129,257,66,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26344 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 131 261 74 52 48 70 198 326), lower := (rows 41 131 261 74 52 48 64 128 256), losses := [] }

theorem u26344 : Upper (D 6) (R 6) [40,129,257,66,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26344 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26345 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 261 74 52 96 86 150 278), lower := (rows 41 131 261 74 52 96 64 128 256), losses := [] }

theorem u26345 : Upper (D 6) (R 6) [40,129,257,66,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26346 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 261 74 84 34 116 180 308), lower := (rows 41 131 261 74 84 34 64 128 256), losses := [] }

theorem u26346 : Upper (D 6) (R 6) [40,129,257,66,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26347 : Route 9 := (fun mask => (mask,id))

def c26347 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26347 : Upper (D 6) (R 6) [40,129,257,66,68,4] 13 := by
  apply FastRouting.sound _ _ [40,129,257,66,68,4] 13 (by decide) (choices 1) [2,16,32] r26347 c26347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8203
  · exact u8204
  · exact u8205

def b26348 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 41 131 261 74 84 48 102 166 294), lower := (rows 41 131 261 74 84 48 64 128 256), losses := [] }

theorem u26348 : Upper (D 6) (R 6) [40,129,257,66,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26348 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26349 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 261 74 112 34 84 148 276), lower := (rows 41 131 261 74 112 34 64 128 256), losses := [] }

theorem u26349 : Upper (D 6) (R 6) [40,129,257,66,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26350 : Route 9 := (fun mask => (mask,id))

def c26350 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26350 : Upper (D 6) (R 6) [40,129,257,66,96,4] 13 := by
  apply FastRouting.sound _ _ [40,129,257,66,96,4] 13 (by decide) (choices 1) [2,4,16] r26350 c26350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8206
  · exact u8207
  · exact u8208

def b26351 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 131 261 74 112 48 70 134 262), lower := (rows 41 131 261 74 112 48 64 128 256), losses := [] }

theorem u26351 : Upper (D 6) (R 6) [40,129,257,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26351 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26352 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 324, targets := 2 },{ cop := 4, region := 104, targets := 1 }], pairs := [(0,2),(2,1),(3,0)], upper := (rows 41 131 261 88 22 34 100 228 356), lower := (rows 41 131 261 88 22 34 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 50 64 128 256), good := (rows 41 163 257 121 50 34 64 128 256) }] }

theorem u26352 : Upper (D 6) (R 6) [40,129,257,80,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26353 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 261 88 22 96 102 166 294), lower := (rows 41 131 261 88 22 96 64 128 256), losses := [] }

theorem u26353 : Upper (D 6) (R 6) [40,129,257,80,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26354 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 131 262 13 82 36 112 240 368), lower := (rows 41 131 262 13 82 36 64 128 256), losses := [] }

theorem u26354 : Upper (D 6) (R 6) [40,129,258,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26355 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 41 131 262 13 82 48 100 228 356), lower := (rows 41 131 262 13 82 48 64 128 256), losses := [] }

theorem u26355 : Upper (D 6) (R 6) [40,129,258,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26355 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26356 : Route 9 := (fun mask => (mask,id))

def c26356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26356 : Upper (D 6) (R 6) [40,129,258,5,66,64] 13 := by
  apply FastRouting.sound _ _ [40,129,258,5,66,64] 13 (by decide) (choices 1) [4,16,32] r26356 c26356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8209
  · exact u8210
  · exact u8211

def b26357 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,0),(4,0)], upper := (rows 41 131 262 13 84 34 112 240 368), lower := (rows 41 131 262 13 84 34 64 128 256), losses := [] }

theorem u26357 : Upper (D 6) (R 6) [40,129,258,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26358 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 131 262 13 84 48 98 226 354), lower := (rows 41 131 262 13 84 48 64 128 256), losses := [] }

theorem u26358 : Upper (D 6) (R 6) [40,129,258,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26358 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26359 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 4, region := 41, targets := 2 }], pairs := [(0,1),(2,0),(4,0)], upper := (rows 41 131 262 13 84 96 114 178 306), lower := (rows 41 131 262 13 84 96 64 128 256), losses := [] }

theorem u26359 : Upper (D 6) (R 6) [40,129,258,5,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26360 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,0),(4,0)], upper := (rows 41 131 262 13 112 34 84 212 340), lower := (rows 41 131 262 13 112 34 64 128 256), losses := [] }

theorem u26360 : Upper (D 6) (R 6) [40,129,258,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26361 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 131 262 13 112 36 82 210 338), lower := (rows 41 131 262 13 112 36 64 128 256), losses := [] }

theorem u26361 : Upper (D 6) (R 6) [40,129,258,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26362 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 131 262 13 112 48 70 198 326), lower := (rows 41 131 262 13 112 48 64 128 256), losses := [] }

theorem u26362 : Upper (D 6) (R 6) [40,129,258,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26362 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26363 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 41 131 262 13 112 96 86 150 278), lower := (rows 41 131 262 13 112 96 64 128 256), losses := [] }

theorem u26363 : Upper (D 6) (R 6) [40,129,258,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26364 : Route 9 := (fun mask => (mask,id))

def c26364 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26364 : Upper (D 6) (R 6) [40,129,258,17,66,4] 13 := by
  apply FastRouting.sound _ _ [40,129,258,17,66,4] 13 (by decide) (choices 1) [4,32] r26364 c26364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8212
  · exact u8213

def b26365 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 131 262 25 82 96 100 164 292), lower := (rows 41 131 262 25 82 96 64 128 256), losses := [] }

theorem u26365 : Upper (D 6) (R 6) [40,129,258,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26366 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 372, targets := 1 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 41 131 262 25 84 34 100 228 356), lower := (rows 41 131 262 25 84 34 64 128 256), losses := [{ target := 2, region := (rows 17 2 0 24 16 38 64 128 256), good := (rows 41 163 290 25 121 34 64 128 256) }] }

theorem u26366 : Upper (D 6) (R 6) [40,129,258,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26367 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 131 262 25 84 36 98 226 354), lower := (rows 41 131 262 25 84 36 64 128 256), losses := [] }

theorem u26367 : Upper (D 6) (R 6) [40,129,258,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26368 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 131 262 25 84 96 102 166 294), lower := (rows 41 131 262 25 84 96 64 128 256), losses := [] }

theorem u26368 : Upper (D 6) (R 6) [40,129,258,17,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26369 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 41 131 262 26 21 36 96 224 352), lower := (rows 41 131 262 26 21 36 64 128 256), losses := [] }

theorem u26369 : Upper (D 6) (R 6) [40,129,258,18,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26370 : Route 9 := (fun mask => (mask,id))

def c26370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26370 : Upper (D 6) (R 6) [40,129,258,18,5,64] 13 := by
  apply FastRouting.sound _ _ [40,129,258,18,5,64] 13 (by decide) (choices 1) [4,32] r26370 c26370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8214
  · exact u8215

def b26371 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 41 131 262 26 52 33 68 196 324), lower := (rows 41 131 262 26 52 33 64 128 256), losses := [] }

theorem u26371 : Upper (D 6) (R 6) [40,129,258,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26372 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 41 131 262 26 52 36 65 193 321), lower := (rows 41 131 262 26 52 36 64 128 256), losses := [] }

theorem u26372 : Upper (D 6) (R 6) [40,129,258,18,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26373 : Route 9 := (fun mask => (mask,id))

def c26373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26373 : Upper (D 6) (R 6) [40,129,258,18,36,64] 13 := by
  apply FastRouting.sound _ _ [40,129,258,18,36,64] 13 (by decide) (choices 1) [1,4] r26373 c26373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8216
  · exact u8217

def r26374 : Route 9 := (fun mask => (mask,id))

def c26374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26374 : Upper (D 6) (R 6) [40,129,258,18,65,4] 13 := by
  apply FastRouting.sound _ _ [40,129,258,18,65,4] 13 (by decide) (choices 1) [4,32] r26374 c26374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8218
  · exact u8219

def b26375 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 1, region := 356, targets := 1 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 41 131 262 26 81 96 100 164 292), lower := (rows 41 131 262 26 81 96 64 128 256), losses := [] }

theorem u26375 : Upper (D 6) (R 6) [40,129,258,18,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26376 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 262 26 84 33 100 228 356), lower := (rows 41 131 262 26 84 33 64 128 256), losses := [] }

theorem u26376 : Upper (D 6) (R 6) [40,129,258,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26377 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 194, targets := 4 }], pairs := [(0,1),(0,6),(1,2)], upper := (rows 41 131 262 26 84 36 97 225 353), lower := (rows 41 131 262 26 84 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 52 73 137 265), good := (rows 489 449 292 505 116 36 64 128 256) },{ target := 6, region := (rows 9 2 4 8 16 52 0 128 256), good := (rows 41 131 294 59 52 36 0 128 256) }] }

theorem u26377 : Upper (D 6) (R 6) [40,129,258,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26378 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 41 131 262 26 84 96 101 165 293), lower := (rows 41 131 262 26 84 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 112 64 128 256), good := (rows 41 129 260 57 116 96 96 128 256) }] }

theorem u26378 : Upper (D 6) (R 6) [40,129,258,18,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26379 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 262 26 112 33 68 196 324), lower := (rows 41 131 262 26 112 33 64 128 256), losses := [] }

theorem u26379 : Upper (D 6) (R 6) [40,129,258,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26380 : Route 9 := (fun mask => (mask,id))

def c26380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26380 : Upper (D 6) (R 6) [40,129,258,18,96,4] 13 := by
  apply FastRouting.sound _ _ [40,129,258,18,96,4] 13 (by decide) (choices 1) [1,4] r26380 c26380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8220
  · exact u8221

def b26381 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 41 131 262 26 112 96 69 133 261), lower := (rows 41 131 262 26 112 96 64 128 256), losses := [] }

theorem u26381 : Upper (D 6) (R 6) [40,129,258,18,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26382 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 356, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 41 131 262 28 81 34 100 228 356), lower := (rows 41 131 262 28 81 34 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 38 64 128 256), good := (rows 41 163 290 57 81 34 64 128 256) },{ target := 6, region := (rows 9 2 4 8 16 38 0 128 256), good := (rows 41 163 294 61 17 34 0 128 256) }] }

theorem u26382 : Upper (D 6) (R 6) [40,129,258,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26383 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 131 262 28 81 36 98 226 354), lower := (rows 41 131 262 28 81 36 64 128 256), losses := [] }

theorem u26383 : Upper (D 6) (R 6) [40,129,258,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26384 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 1, region := 356, targets := 1 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 41 131 262 28 81 96 102 166 294), lower := (rows 41 131 262 28 81 96 64 128 256), losses := [] }

theorem u26384 : Upper (D 6) (R 6) [40,129,258,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26385 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 33, targets := 68 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 262 28 82 33 100 228 356), lower := (rows 41 131 262 28 82 33 64 128 256), losses := [] }

theorem u26385 : Upper (D 6) (R 6) [40,129,258,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26386 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 131 262 28 82 36 97 225 353), lower := (rows 41 131 262 28 82 36 64 128 256), losses := [] }

theorem u26386 : Upper (D 6) (R 6) [40,129,258,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26387 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 41 131 262 28 82 96 101 165 293), lower := (rows 41 131 262 28 82 96 64 128 256), losses := [] }

theorem u26387 : Upper (D 6) (R 6) [40,129,258,20,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26388 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 262 28 112 33 70 198 326), lower := (rows 41 131 262 28 112 33 64 128 256), losses := [] }

theorem u26388 : Upper (D 6) (R 6) [40,129,258,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26389 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 41 131 262 28 112 34 69 197 325), lower := (rows 41 131 262 28 112 34 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 38 64 128 256), good := (rows 41 163 290 57 112 34 64 128 256) }] }

theorem u26389 : Upper (D 6) (R 6) [40,129,258,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26390 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 131 262 28 112 36 67 195 323), lower := (rows 41 131 262 28 112 36 64 128 256), losses := [] }

theorem u26390 : Upper (D 6) (R 6) [40,129,258,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26391 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 41 131 262 28 112 96 71 135 263), lower := (rows 41 131 262 28 112 96 64 128 256), losses := [] }

theorem u26391 : Upper (D 6) (R 6) [40,129,258,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26392 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 4, region := 73, targets := 2 }], pairs := [(0,1),(2,0),(4,0)], upper := (rows 41 131 262 73 52 34 84 212 340), lower := (rows 41 131 262 73 52 34 64 128 256), losses := [] }

theorem u26392 : Upper (D 6) (R 6) [40,129,258,65,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26393 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 131 262 73 52 36 82 210 338), lower := (rows 41 131 262 73 52 36 64 128 256), losses := [] }

theorem u26393 : Upper (D 6) (R 6) [40,129,258,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26394 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 131 262 73 52 48 70 198 326), lower := (rows 41 131 262 73 52 48 64 128 256), losses := [] }

theorem u26394 : Upper (D 6) (R 6) [40,129,258,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26394 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26395 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 131 262 73 52 96 86 150 278), lower := (rows 41 131 262 73 52 96 64 128 256), losses := [] }

theorem u26395 : Upper (D 6) (R 6) [40,129,258,65,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26396 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 372, targets := 1 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 41 131 262 73 84 34 116 180 308), lower := (rows 41 131 262 73 84 34 64 128 256), losses := [{ target := 2, region := (rows 17 2 0 24 16 38 64 128 256), good := (rows 41 163 290 73 121 34 64 128 256) }] }

theorem u26396 : Upper (D 6) (R 6) [40,129,258,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26397 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 4, region := 41, targets := 2 }], pairs := [(0,1),(2,0),(4,0)], upper := (rows 41 131 262 73 84 36 114 178 306), lower := (rows 41 131 262 73 84 36 64 128 256), losses := [] }

theorem u26397 : Upper (D 6) (R 6) [40,129,258,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26398 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 131 262 73 84 48 102 166 294), lower := (rows 41 131 262 73 84 48 64 128 256), losses := [] }

theorem u26398 : Upper (D 6) (R 6) [40,129,258,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26398 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26399 : Route 9 := (fun mask => (mask,id))

def c26399 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26399 : Upper (D 6) (R 6) [40,129,258,66,5,4] 13 := by
  apply FastRouting.sound _ _ [40,129,258,66,5,4] 13 (by decide) (choices 1) [16,32] r26399 c26399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8222
  · exact u8223

#print axioms u26399
end Delivery.IrregularNine14.P06
