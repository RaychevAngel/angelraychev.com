import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0013

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10320 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 322 140 73 176 34 65 146 274), lower := (rows 37 322 140 73 176 34 65 128 256), losses := [] }

theorem u10320 : Upper (D 7) (R 7) [36,320,136,65,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10321 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 8, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,6)], upper := (rows 37 322 140 73 176 34 66 145 273), lower := (rows 37 322 140 73 176 34 66 128 256), losses := [] }

theorem u10321 : Upper (D 7) (R 7) [36,320,136,65,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10322 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 77, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 322 140 73 176 34 80 131 259), lower := (rows 37 322 140 73 176 34 80 128 256), losses := [] }

theorem u10322 : Upper (D 7) (R 7) [36,320,136,65,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10322 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10323 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 322 140 88 145 34 65 162 290), lower := (rows 37 322 140 88 145 34 65 128 256), losses := [] }

theorem u10323 : Upper (D 7) (R 7) [36,320,136,80,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10324 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,6)], upper := (rows 37 322 140 88 145 34 66 161 289), lower := (rows 37 322 140 88 145 34 66 128 256), losses := [] }

theorem u10324 : Upper (D 7) (R 7) [36,320,136,80,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10325 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 362, targets := 128 },{ cop := 8, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 37 322 140 88 145 34 96 131 259), lower := (rows 37 322 140 88 145 34 96 128 256), losses := [] }

theorem u10325 : Upper (D 7) (R 7) [36,320,136,80,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10326 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 77, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 37 322 140 88 176 34 65 131 259), lower := (rows 37 322 140 88 176 34 65 128 256), losses := [] }

theorem u10326 : Upper (D 7) (R 7) [36,320,136,80,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10327 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,6)], upper := (rows 37 322 140 88 176 34 66 129 257), lower := (rows 37 322 140 88 176 34 66 128 256), losses := [] }

theorem u10327 : Upper (D 7) (R 7) [36,320,136,80,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10328 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 322 140 104 19 48 65 130 386), lower := (rows 37 322 140 104 19 48 65 128 256), losses := [] }

theorem u10328 : Upper (D 7) (R 7) [36,320,136,96,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10328 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10329 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 140 104 19 48 66 129 385), lower := (rows 37 322 140 104 19 48 66 128 256), losses := [] }

theorem u10329 : Upper (D 7) (R 7) [36,320,136,96,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10329 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10330 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 37 322 140 104 19 48 192 131 259), lower := (rows 37 322 140 104 19 48 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 16 48 196 128 256), good := (rows 108 322 204 104 58 48 192 192 256) }] }

theorem u10330 : Upper (D 7) (R 7) [36,320,136,96,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10330 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10331 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(4,1),(4,6)], upper := (rows 37 322 196 11 145 34 72 176 304), lower := (rows 37 322 196 11 145 34 72 128 256), losses := [] }

theorem u10331 : Upper (D 7) (R 7) [36,320,192,3,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10331 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10332 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 322 196 11 145 34 80 168 296), lower := (rows 37 322 196 11 145 34 80 128 256), losses := [] }

theorem u10332 : Upper (D 7) (R 7) [36,320,192,3,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10332 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10333 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 144, targets := 34 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7),(4,1),(4,5)], upper := (rows 37 322 196 11 145 34 96 152 280), lower := (rows 37 322 196 11 145 34 96 128 256), losses := [] }

theorem u10333 : Upper (D 7) (R 7) [36,320,192,3,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10334 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 176, targets := 65 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 322 196 11 146 40 65 176 304), lower := (rows 37 322 196 11 146 40 65 128 256), losses := [{ target := 0, region := (rows 0 66 68 8 92 40 64 169 297), good := (rows 436 342 214 442 146 440 470 128 256) }] }

theorem u10334 : Upper (D 7) (R 7) [36,320,192,3,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10334 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10335 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 322 196 11 146 40 80 161 289), lower := (rows 37 322 196 11 146 40 80 128 256), losses := [] }

theorem u10335 : Upper (D 7) (R 7) [36,320,192,3,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10335 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10336 : Route 9 := (fun mask => (mask,id))

def c10336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10336 : Upper (D 7) (R 7) [36,320,192,3,130,8,32] 13 := by
  apply FastRouting.sound _ _ [36,320,192,3,130,8,32] 13 (by decide) (choices 1) [1,16] r10336 c10336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u783
  · exact u784

def b10337 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 176, targets := 65 }], pairs := [(2,1),(2,5),(4,0),(4,6)], upper := (rows 37 322 196 11 152 34 65 176 304), lower := (rows 37 322 196 11 152 34 65 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 32 73 128 256), good := (rows 101 320 196 73 220 32 65 128 256) },{ target := 5, region := (rows 1 2 20 8 16 0 73 128 256), good := (rows 69 322 196 75 220 2 65 128 256) }] }

theorem u10337 : Upper (D 7) (R 7) [36,320,192,3,136,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10338 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 322 196 11 152 34 80 161 289), lower := (rows 37 322 196 11 152 34 80 128 256), losses := [] }

theorem u10338 : Upper (D 7) (R 7) [36,320,192,3,136,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10338 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10339 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 144, targets := 34 },{ cop := 8, region := 98, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 37 322 196 11 152 34 96 145 273), lower := (rows 37 322 196 11 152 34 96 128 256), losses := [] }

theorem u10339 : Upper (D 7) (R 7) [36,320,192,3,136,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10340 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 176, targets := 65 },{ cop := 4, region := 69, targets := 2 }], pairs := [(0,1),(2,1),(4,0),(4,6)], upper := (rows 37 322 196 11 176 34 65 152 280), lower := (rows 37 322 196 11 176 34 65 128 256), losses := [] }

theorem u10340 : Upper (D 7) (R 7) [36,320,192,3,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10341 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 37 322 196 11 176 34 72 145 273), lower := (rows 37 322 196 11 176 34 72 128 256), losses := [{ target := 1, region := (rows 1 0 76 8 17 32 72 137 265), good := (rows 437 324 196 477 176 32 460 128 256) }] }

theorem u10341 : Upper (D 7) (R 7) [36,320,192,3,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10341 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10342 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 322 196 11 176 34 80 137 265), lower := (rows 37 322 196 11 176 34 80 128 256), losses := [] }

theorem u10342 : Upper (D 7) (R 7) [36,320,192,3,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10342 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10343 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 176, targets := 65 },{ cop := 4, region := 69, targets := 2 }], pairs := [(0,1),(4,0),(4,6)], upper := (rows 37 322 196 11 176 40 65 146 274), lower := (rows 37 322 196 11 176 40 65 128 256), losses := [] }

theorem u10343 : Upper (D 7) (R 7) [36,320,192,3,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10343 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10344 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 196 11 176 40 66 145 273), lower := (rows 37 322 196 11 176 40 66 128 256), losses := [] }

theorem u10344 : Upper (D 7) (R 7) [36,320,192,3,160,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10344 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10345 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 322 196 11 176 40 80 131 259), lower := (rows 37 322 196 11 176 40 80 128 256), losses := [] }

theorem u10345 : Upper (D 7) (R 7) [36,320,192,3,160,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10345 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10346 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 197, targets := 2 },{ cop := 6, region := 422, targets := 1 }], pairs := [(0,1),(1,0),(2,0),(2,1)], upper := (rows 37 322 196 25 26 34 65 160 416), lower := (rows 37 322 196 25 26 34 65 128 256), losses := [] }

theorem u10346 : Upper (D 7) (R 7) [36,320,192,17,10,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10347 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 197, targets := 2 },{ cop := 8, region := 98, targets := 129 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 37 322 196 25 26 34 96 129 385), lower := (rows 37 322 196 25 26 34 96 128 256), losses := [] }

theorem u10347 : Upper (D 7) (R 7) [36,320,192,17,10,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10348 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 322 196 25 26 34 192 161 289), lower := (rows 37 322 196 25 26 34 192 128 256), losses := [] }

theorem u10348 : Upper (D 7) (R 7) [36,320,192,17,10,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10349 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 322 196 25 50 40 65 130 386), lower := (rows 37 322 196 25 50 40 65 128 256), losses := [] }

theorem u10349 : Upper (D 7) (R 7) [36,320,192,17,34,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10349 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10350 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 196 25 50 40 66 129 385), lower := (rows 37 322 196 25 50 40 66 128 256), losses := [] }

theorem u10350 : Upper (D 7) (R 7) [36,320,192,17,34,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10350 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10351 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 322 196 25 50 40 192 131 259), lower := (rows 37 322 196 25 50 40 192 128 256), losses := [] }

theorem u10351 : Upper (D 7) (R 7) [36,320,192,17,34,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10351 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10352 : Route 9 := (fun mask => (mask,id))

def c10352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10352 : Upper (D 7) (R 7) [36,320,192,17,130,2,1] 13 := by
  apply FastRouting.sound _ _ [36,320,192,17,130,2,1] 13 (by decide) (choices 1) [8,32] r10352 c10352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u785
  · exact u786

def b10353 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,7),(2,1)], upper := (rows 37 322 196 25 146 34 72 161 289), lower := (rows 37 322 196 25 146 34 72 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 32 72 129 257), good := (rows 421 320 196 477 144 32 76 128 256) }] }

theorem u10353 : Upper (D 7) (R 7) [36,320,192,17,130,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10353 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10354 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 98, targets := 129 },{ cop := 4, region := 100, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(2,1)], upper := (rows 37 322 196 25 146 34 96 137 265), lower := (rows 37 322 196 25 146 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 32 97 136 264), good := (rows 101 320 196 477 144 96 96 128 256) }] }

theorem u10354 : Upper (D 7) (R 7) [36,320,192,17,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10355 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 322 196 25 146 40 65 162 290), lower := (rows 37 322 196 25 146 40 65 128 256), losses := [] }

theorem u10355 : Upper (D 7) (R 7) [36,320,192,17,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10355 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10356 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 196 25 146 40 66 161 289), lower := (rows 37 322 196 25 146 40 66 128 256), losses := [] }

theorem u10356 : Upper (D 7) (R 7) [36,320,192,17,130,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10356 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10357 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 322 196 25 146 40 96 131 259), lower := (rows 37 322 196 25 146 40 96 128 256), losses := [] }

theorem u10357 : Upper (D 7) (R 7) [36,320,192,17,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10357 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10358 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 6, region := 422, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 37 322 196 25 152 34 65 162 290), lower := (rows 37 322 196 25 152 34 65 128 256), losses := [] }

theorem u10358 : Upper (D 7) (R 7) [36,320,192,17,136,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10359 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 152, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 322 196 25 152 34 66 161 289), lower := (rows 37 322 196 25 152 34 66 128 256), losses := [] }

theorem u10359 : Upper (D 7) (R 7) [36,320,192,17,136,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10360 : Route 9 := (fun mask => (mask,id))

def c10360 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10360 : Upper (D 7) (R 7) [36,320,192,17,136,2,32] 13 := by
  apply FastRouting.sound _ _ [36,320,192,17,136,2,32] 13 (by decide) (choices 1) [1,2] r10360 c10360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u787
  · exact u788

def b10361 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 77, targets := 2 },{ cop := 3, region := 322, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(3,1)], upper := (rows 37 322 196 25 176 34 65 138 266), lower := (rows 37 322 196 25 176 34 65 128 256), losses := [] }

theorem u10361 : Upper (D 7) (R 7) [36,320,192,17,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10362 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 152, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 322 196 25 176 34 66 137 265), lower := (rows 37 322 196 25 176 34 66 128 256), losses := [] }

theorem u10362 : Upper (D 7) (R 7) [36,320,192,17,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10362 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10363 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 77, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 322 196 25 176 34 72 131 259), lower := (rows 37 322 196 25 176 34 72 128 256), losses := [] }

theorem u10363 : Upper (D 7) (R 7) [36,320,192,17,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10363 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10364 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 68, targets := 34 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,1),(2,5),(3,7)], upper := (rows 37 322 196 26 145 34 65 168 296), lower := (rows 37 322 196 26 145 34 65 128 256), losses := [] }

theorem u10364 : Upper (D 7) (R 7) [36,320,192,18,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10365 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(4,1),(4,6)], upper := (rows 37 322 196 26 145 34 72 161 289), lower := (rows 37 322 196 26 145 34 72 128 256), losses := [] }

theorem u10365 : Upper (D 7) (R 7) [36,320,192,18,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10365 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10366 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 8, region := 98, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(3,7)], upper := (rows 37 322 196 26 145 34 96 137 265), lower := (rows 37 322 196 26 145 34 96 128 256), losses := [{ target := 0, region := (rows 0 258 20 8 16 298 363 128 256), good := (rows 100 354 196 126 212 98 96 128 354) }] }

theorem u10366 : Upper (D 7) (R 7) [36,320,192,18,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10367 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 68, targets := 34 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,1),(2,5)], upper := (rows 37 322 196 26 145 40 65 162 290), lower := (rows 37 322 196 26 145 40 65 128 256), losses := [] }

theorem u10367 : Upper (D 7) (R 7) [36,320,192,18,129,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10367 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10368 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 196 26 145 40 66 161 289), lower := (rows 37 322 196 26 145 40 66 128 256), losses := [] }

theorem u10368 : Upper (D 7) (R 7) [36,320,192,18,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10368 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10369 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,0),(3,7)], upper := (rows 37 322 196 26 145 40 96 131 259), lower := (rows 37 322 196 26 145 40 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 40 105 128 256), good := (rows 100 322 196 126 212 104 96 128 256) }] }

theorem u10369 : Upper (D 7) (R 7) [36,320,192,18,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10369 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10370 : Route 9 := (fun mask => (mask,id))

def c10370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10370 : Upper (D 7) (R 7) [36,320,192,18,160,2,1] 13 := by
  apply FastRouting.sound _ _ [36,320,192,18,160,2,1] 13 (by decide) (choices 1) [1,8] r10370 c10370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u789
  · exact u790

def b10371 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(4,1),(4,6)], upper := (rows 37 322 196 26 176 34 72 129 257), lower := (rows 37 322 196 26 176 34 72 128 256), losses := [] }

theorem u10371 : Upper (D 7) (R 7) [36,320,192,18,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10371 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10372 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 144, targets := 97 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,6)], upper := (rows 37 322 196 42 146 33 65 152 280), lower := (rows 37 322 196 42 146 33 65 128 256), losses := [] }

theorem u10372 : Upper (D 7) (R 7) [36,320,192,34,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10373 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7)], upper := (rows 37 322 196 42 146 33 72 145 273), lower := (rows 37 322 196 42 146 33 72 128 256), losses := [] }

theorem u10373 : Upper (D 7) (R 7) [36,320,192,34,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10373 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10374 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 322 196 42 146 33 80 137 265), lower := (rows 37 322 196 42 146 33 80 128 256), losses := [] }

theorem u10374 : Upper (D 7) (R 7) [36,320,192,34,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10374 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10375 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 144, targets := 97 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,6)], upper := (rows 37 322 196 42 152 33 65 146 274), lower := (rows 37 322 196 42 152 33 65 128 256), losses := [] }

theorem u10375 : Upper (D 7) (R 7) [36,320,192,34,136,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10376 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 8, region := 66, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 196 42 152 33 66 145 273), lower := (rows 37 322 196 42 152 33 66 128 256), losses := [] }

theorem u10376 : Upper (D 7) (R 7) [36,320,192,34,136,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10377 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 322 196 42 152 33 80 131 259), lower := (rows 37 322 196 42 152 33 80 128 256), losses := [] }

theorem u10377 : Upper (D 7) (R 7) [36,320,192,34,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10377 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10378 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 68, targets := 34 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,1),(2,5),(3,7)], upper := (rows 37 322 196 56 145 34 65 138 266), lower := (rows 37 322 196 56 145 34 65 128 256), losses := [] }

theorem u10378 : Upper (D 7) (R 7) [36,320,192,48,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10379 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 152, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 322 196 56 145 34 66 137 265), lower := (rows 37 322 196 56 145 34 66 128 256), losses := [] }

theorem u10379 : Upper (D 7) (R 7) [36,320,192,48,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10379
end Delivery.IrregularNine14.P07
