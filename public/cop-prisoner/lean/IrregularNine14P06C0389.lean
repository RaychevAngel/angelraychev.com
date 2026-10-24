import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0119
import IrregularNine14P06C0120

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23340 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 262 13 56 48 65 193 321), lower := (rows 35 134 262 13 56 48 64 128 256), losses := [] }

theorem u23340 : Upper (D 6) (R 6) [34,132,258,5,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23340 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23341 : Route 9 := (fun mask => (mask,id))

def c23341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23341 : Upper (D 6) (R 6) [34,132,258,5,40,64] 13 := by
  apply FastRouting.sound _ _ [34,132,258,5,40,64] 13 (by decide) (choices 1) [1,16] r23341 c23341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7172
  · exact u7173

def b23342 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 134 262 13 81 40 112 240 368), lower := (rows 35 134 262 13 81 40 64 128 256), losses := [] }

theorem u23342 : Upper (D 6) (R 6) [34,132,258,5,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23342 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23343 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 112, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 134 262 13 81 48 104 232 360), lower := (rows 35 134 262 13 81 48 64 128 256), losses := [] }

theorem u23343 : Upper (D 6) (R 6) [34,132,258,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23343 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23344 : Route 9 := (fun mask => (mask,id))

def c23344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23344 : Upper (D 6) (R 6) [34,132,258,5,65,64] 13 := by
  apply FastRouting.sound _ _ [34,132,258,5,65,64] 13 (by decide) (choices 1) [8,16,32] r23344 c23344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7174
  · exact u7175
  · exact u7176

def b23345 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 112, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 35 134 262 13 88 33 112 240 368), lower := (rows 35 134 262 13 88 33 64 128 256), losses := [] }

theorem u23345 : Upper (D 6) (R 6) [34,132,258,5,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23346 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 112, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 134 262 13 88 48 97 225 353), lower := (rows 35 134 262 13 88 48 64 128 256), losses := [] }

theorem u23346 : Upper (D 6) (R 6) [34,132,258,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23346 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23347 : Route 9 := (fun mask => (mask,id))

def c23347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23347 : Upper (D 6) (R 6) [34,132,258,5,72,64] 13 := by
  apply FastRouting.sound _ _ [34,132,258,5,72,64] 13 (by decide) (choices 1) [1,16,32] r23347 c23347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7177
  · exact u7178
  · exact u7179

def b23348 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 112, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 35 134 262 13 112 33 88 216 344), lower := (rows 35 134 262 13 112 33 64 128 256), losses := [] }

theorem u23348 : Upper (D 6) (R 6) [34,132,258,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23349 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 134 262 13 112 40 81 209 337), lower := (rows 35 134 262 13 112 40 64 128 256), losses := [] }

theorem u23349 : Upper (D 6) (R 6) [34,132,258,5,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23349 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23350 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 262 13 112 48 73 201 329), lower := (rows 35 134 262 13 112 48 64 128 256), losses := [] }

theorem u23350 : Upper (D 6) (R 6) [34,132,258,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23350 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23351 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 262 13 112 96 89 153 281), lower := (rows 35 134 262 13 112 96 64 128 256), losses := [] }

theorem u23351 : Upper (D 6) (R 6) [34,132,258,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23352 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 134 262 25 28 33 96 224 352), lower := (rows 35 134 262 25 28 33 64 128 256), losses := [] }

theorem u23352 : Upper (D 6) (R 6) [34,132,258,17,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23353 : Route 9 := (fun mask => (mask,id))

def c23353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23353 : Upper (D 6) (R 6) [34,132,258,17,12,64] 13 := by
  apply FastRouting.sound _ _ [34,132,258,17,12,64] 13 (by decide) (choices 1) [1,32] r23353 c23353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7180
  · exact u7181

def b23354 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 134 262 25 52 33 72 200 328), lower := (rows 35 134 262 25 52 33 64 128 256), losses := [] }

theorem u23354 : Upper (D 6) (R 6) [34,132,258,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23355 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 134 262 25 52 40 65 193 321), lower := (rows 35 134 262 25 52 40 64 128 256), losses := [] }

theorem u23355 : Upper (D 6) (R 6) [34,132,258,17,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23355 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23356 : Route 9 := (fun mask => (mask,id))

def c23356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23356 : Upper (D 6) (R 6) [34,132,258,17,36,64] 13 := by
  apply FastRouting.sound _ _ [34,132,258,17,36,64] 13 (by decide) (choices 1) [1,8] r23356 c23356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7182
  · exact u7183

def b23357 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 262 25 84 33 104 232 360), lower := (rows 35 134 262 25 84 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 24 16 63 88 152 280), good := (rows 35 163 291 505 505 33 64 128 256) }] }

theorem u23357 : Upper (D 6) (R 6) [34,132,258,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23358 : Route 9 := (fun mask => (mask,id))

def c23358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23358 : Upper (D 6) (R 6) [34,132,258,17,68,8] 13 := by
  apply FastRouting.sound _ _ [34,132,258,17,68,8] 13 (by decide) (choices 1) [1,32] r23358 c23358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7184
  · exact u7185

def r23359 : Route 9 := (fun mask => (mask,id))

def c23359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23359 : Upper (D 6) (R 6) [34,132,258,17,68,64] 13 := by
  apply FastRouting.sound _ _ [34,132,258,17,68,64] 13 (by decide) (choices 1) [1,8,32] r23359 c23359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7186
  · exact u7187
  · exact u7188

def b23360 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 134 262 25 88 33 100 228 356), lower := (rows 35 134 262 25 88 33 64 128 256), losses := [] }

theorem u23360 : Upper (D 6) (R 6) [34,132,258,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23361 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 134 262 25 88 36 97 225 353), lower := (rows 35 134 262 25 88 36 64 128 256), losses := [] }

theorem u23361 : Upper (D 6) (R 6) [34,132,258,17,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23362 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 262 25 88 96 101 165 293), lower := (rows 35 134 262 25 88 96 64 128 256), losses := [] }

theorem u23362 : Upper (D 6) (R 6) [34,132,258,17,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23363 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 134 262 25 112 33 76 204 332), lower := (rows 35 134 262 25 112 33 64 128 256), losses := [] }

theorem u23363 : Upper (D 6) (R 6) [34,132,258,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23364 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 134 262 25 112 36 73 201 329), lower := (rows 35 134 262 25 112 36 64 128 256), losses := [] }

theorem u23364 : Upper (D 6) (R 6) [34,132,258,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23365 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 262 25 112 40 69 197 325), lower := (rows 35 134 262 25 112 40 64 128 256), losses := [] }

theorem u23365 : Upper (D 6) (R 6) [34,132,258,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23365 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23366 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 262 25 112 96 77 141 269), lower := (rows 35 134 262 25 112 96 64 128 256), losses := [] }

theorem u23366 : Upper (D 6) (R 6) [34,132,258,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23367 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 262 28 81 33 104 232 360), lower := (rows 35 134 262 28 81 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 8 24 63 72 136 264), good := (rows 35 163 291 505 113 33 64 128 256) }] }

theorem u23367 : Upper (D 6) (R 6) [34,132,258,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23368 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 134 262 28 81 40 97 225 353), lower := (rows 35 134 262 28 81 40 64 128 256), losses := [] }

theorem u23368 : Upper (D 6) (R 6) [34,132,258,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23368 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23369 : Route 9 := (fun mask => (mask,id))

def c23369 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23369 : Upper (D 6) (R 6) [34,132,258,20,65,64] 13 := by
  apply FastRouting.sound _ _ [34,132,258,20,65,64] 13 (by decide) (choices 1) [1,8,32] r23369 c23369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7189
  · exact u7190
  · exact u7191

def b23370 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 262 28 88 33 97 225 353), lower := (rows 35 134 262 28 88 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 8 24 47 111 175 303), good := (rows 483 483 483 505 504 481 64 128 256) }] }

theorem u23370 : Upper (D 6) (R 6) [34,132,258,20,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23371 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 262 28 88 96 97 161 289), lower := (rows 35 134 262 28 88 96 64 128 256), losses := [] }

theorem u23371 : Upper (D 6) (R 6) [34,132,258,20,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23372 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 262 28 112 33 73 201 329), lower := (rows 35 134 262 28 112 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 8 24 47 72 136 264), good := (rows 35 163 291 505 112 33 64 128 256) }] }

theorem u23372 : Upper (D 6) (R 6) [34,132,258,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23373 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 134 262 28 112 40 65 193 321), lower := (rows 35 134 262 28 112 40 64 128 256), losses := [] }

theorem u23373 : Upper (D 6) (R 6) [34,132,258,20,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23373 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23374 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 262 28 112 96 73 137 265), lower := (rows 35 134 262 28 112 96 64 128 256), losses := [] }

theorem u23374 : Upper (D 6) (R 6) [34,132,258,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23375 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 134 262 44 81 33 88 216 344), lower := (rows 35 134 262 44 81 33 64 128 256), losses := [] }

theorem u23375 : Upper (D 6) (R 6) [34,132,258,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23376 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 262 44 81 40 81 209 337), lower := (rows 35 134 262 44 81 40 64 128 256), losses := [] }

theorem u23376 : Upper (D 6) (R 6) [34,132,258,36,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23376 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23377 : Route 9 := (fun mask => (mask,id))

def c23377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23377 : Upper (D 6) (R 6) [34,132,258,36,65,16] 13 := by
  apply FastRouting.sound _ _ [34,132,258,36,65,16] 13 (by decide) (choices 1) [1,8] r23377 c23377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7192
  · exact u7193

def r23378 : Route 9 := (fun mask => (mask,id))

def c23378 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23378 : Upper (D 6) (R 6) [34,132,258,36,65,64] 13 := by
  apply FastRouting.sound _ _ [34,132,258,36,65,64] 13 (by decide) (choices 1) [1,8,16] r23378 c23378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7194
  · exact u7195
  · exact u7196

def b23379 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 134 262 44 88 33 81 209 337), lower := (rows 35 134 262 44 88 33 64 128 256), losses := [] }

theorem u23379 : Upper (D 6) (R 6) [34,132,258,36,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23380 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 262 44 88 48 65 193 321), lower := (rows 35 134 262 44 88 48 64 128 256), losses := [] }

theorem u23380 : Upper (D 6) (R 6) [34,132,258,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23380 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23381 : Route 9 := (fun mask => (mask,id))

def c23381 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23381 : Upper (D 6) (R 6) [34,132,258,36,72,64] 13 := by
  apply FastRouting.sound _ _ [34,132,258,36,72,64] 13 (by decide) (choices 1) [1,16] r23381 c23381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7197
  · exact u7198

def b23382 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 134 262 56 81 33 76 204 332), lower := (rows 35 134 262 56 81 33 64 128 256), losses := [] }

theorem u23382 : Upper (D 6) (R 6) [34,132,258,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23383 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 134 262 56 81 36 73 201 329), lower := (rows 35 134 262 56 81 36 64 128 256), losses := [] }

theorem u23383 : Upper (D 6) (R 6) [34,132,258,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23384 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 134 262 56 81 40 69 197 325), lower := (rows 35 134 262 56 81 40 64 128 256), losses := [] }

theorem u23384 : Upper (D 6) (R 6) [34,132,258,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23384 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23385 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 262 56 81 96 77 141 269), lower := (rows 35 134 262 56 81 96 64 128 256), losses := [] }

theorem u23385 : Upper (D 6) (R 6) [34,132,258,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23386 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 262 56 84 33 73 201 329), lower := (rows 35 134 262 56 84 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 24 16 55 80 144 272), good := (rows 35 163 291 504 505 33 64 128 256) }] }

theorem u23386 : Upper (D 6) (R 6) [34,132,258,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23387 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 134 262 56 84 40 65 193 321), lower := (rows 35 134 262 56 84 40 64 128 256), losses := [] }

theorem u23387 : Upper (D 6) (R 6) [34,132,258,48,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23387 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23388 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 262 56 84 96 73 137 265), lower := (rows 35 134 262 56 84 96 64 128 256), losses := [] }

theorem u23388 : Upper (D 6) (R 6) [34,132,258,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23389 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 134 262 56 88 33 69 197 325), lower := (rows 35 134 262 56 88 33 64 128 256), losses := [] }

theorem u23389 : Upper (D 6) (R 6) [34,132,258,48,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23390 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 134 262 56 88 36 65 193 321), lower := (rows 35 134 262 56 88 36 64 128 256), losses := [] }

theorem u23390 : Upper (D 6) (R 6) [34,132,258,48,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23391 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 134 262 56 88 96 69 133 261), lower := (rows 35 134 262 56 88 96 64 128 256), losses := [] }

theorem u23391 : Upper (D 6) (R 6) [34,132,258,48,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23392 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 262 73 84 33 120 184 312), lower := (rows 35 134 262 73 84 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 24 16 63 80 144 272), good := (rows 35 163 291 105 505 33 64 128 256) }] }

theorem u23392 : Upper (D 6) (R 6) [34,132,258,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23393 : Route 9 := (fun mask => (mask,id))

def c23393 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23393 : Upper (D 6) (R 6) [34,132,258,65,68,8] 13 := by
  apply FastRouting.sound _ _ [34,132,258,65,68,8] 13 (by decide) (choices 1) [1,16,32] r23393 c23393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7199
  · exact u7200
  · exact u7201

def b23394 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 72, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 134 262 73 84 48 105 169 297), lower := (rows 35 134 262 73 84 48 64 128 256), losses := [] }

theorem u23394 : Upper (D 6) (R 6) [34,132,258,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23394 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23395 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 48, targets := 2 }], pairs := [(0,2),(0,6),(4,1)], upper := (rows 35 134 262 73 112 33 92 156 284), lower := (rows 35 134 262 73 112 33 64 128 256), losses := [] }

theorem u23395 : Upper (D 6) (R 6) [34,132,258,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23396 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 134 262 73 112 36 89 153 281), lower := (rows 35 134 262 73 112 36 64 128 256), losses := [] }

theorem u23396 : Upper (D 6) (R 6) [34,132,258,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23397 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 134 262 73 112 40 85 149 277), lower := (rows 35 134 262 73 112 40 64 128 256), losses := [] }

theorem u23397 : Upper (D 6) (R 6) [34,132,258,65,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23397 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23398 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 262 73 112 48 77 141 269), lower := (rows 35 134 262 73 112 48 64 128 256), losses := [] }

theorem u23398 : Upper (D 6) (R 6) [34,132,258,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23398 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23399 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 262 76 112 33 89 153 281), lower := (rows 35 134 262 76 112 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 8 24 47 72 136 264), good := (rows 35 163 291 505 112 33 64 128 256) }] }

theorem u23399 : Upper (D 6) (R 6) [34,132,258,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u23399
end Delivery.IrregularNine14.P06
