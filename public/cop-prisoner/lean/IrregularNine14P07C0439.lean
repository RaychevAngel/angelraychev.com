import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0157
import IrregularNine14P07C0158

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26340 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 69 137 50 48 194 194 450), lower := (rows 37 266 69 137 50 48 64 128 256), losses := [] }

theorem u26340 : Upper (D 7) (R 7) [36,264,65,129,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26340 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26341 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 137 50 96 210 146 402), lower := (rows 37 266 69 137 50 96 64 128 256), losses := [] }

theorem u26341 : Upper (D 7) (R 7) [36,264,65,129,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26342 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 4, region := 69, targets := 128 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 266 69 137 50 160 82 210 338), lower := (rows 37 266 69 137 50 160 64 128 256), losses := [] }

theorem u26342 : Upper (D 7) (R 7) [36,264,65,129,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26343 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 266 69 137 82 34 240 176 432), lower := (rows 37 266 69 137 82 34 64 128 256), losses := [] }

theorem u26343 : Upper (D 7) (R 7) [36,264,65,129,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26344 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 266 69 137 82 48 226 162 418), lower := (rows 37 266 69 137 82 48 64 128 256), losses := [] }

theorem u26344 : Upper (D 7) (R 7) [36,264,65,129,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26344 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26345 : Route 9 := (fun mask => (mask,id))

def c26345 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26345 : Upper (D 7) (R 7) [36,264,65,129,66,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,129,66,128] 13 (by decide) (choices 1) [2,16,32] r26345 c26345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9450
  · exact u9451
  · exact u9452

def r26346 : Route 9 := (fun mask => (mask,id))

def c26346 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26346 : Upper (D 7) (R 7) [36,264,65,129,160,2] 13 := by
  apply FastRouting.sound _ _ [36,264,65,129,160,2] 13 (by decide) (choices 1) [2,16] r26346 c26346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9453
  · exact u9454

def b26347 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 69 137 176 48 66 194 322), lower := (rows 37 266 69 137 176 48 64 128 256), losses := [] }

theorem u26347 : Upper (D 7) (R 7) [36,264,65,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26347 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26348 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 137 176 96 82 146 274), lower := (rows 37 266 69 137 176 96 64 128 256), losses := [] }

theorem u26348 : Upper (D 7) (R 7) [36,264,65,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26349 : Route 9 := (fun mask => (mask,id))

def c26349 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26349 : Upper (D 7) (R 7) [36,264,65,129,192,2] 13 := by
  apply FastRouting.sound _ _ [36,264,65,129,192,2] 13 (by decide) (choices 1) [2,16,32] r26349 c26349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9455
  · exact u9456
  · exact u9457

def b26350 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 45, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 266 69 137 208 48 98 162 290), lower := (rows 37 266 69 137 208 48 64 128 256), losses := [] }

theorem u26350 : Upper (D 7) (R 7) [36,264,65,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26350 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26351 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 266 69 138 50 33 208 208 464), lower := (rows 37 266 69 138 50 33 64 128 256), losses := [] }

theorem u26351 : Upper (D 7) (R 7) [36,264,65,130,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26352 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 69 138 50 48 193 193 449), lower := (rows 37 266 69 138 50 48 64 128 256), losses := [] }

theorem u26352 : Upper (D 7) (R 7) [36,264,65,130,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26352 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26353 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 138 50 96 209 145 401), lower := (rows 37 266 69 138 50 96 64 128 256), losses := [] }

theorem u26353 : Upper (D 7) (R 7) [36,264,65,130,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26353 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26354 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 65 },{ cop := 4, region := 69, targets := 2 }], pairs := [(0,1),(2,1),(4,0),(4,6)], upper := (rows 37 266 69 138 50 160 81 209 337), lower := (rows 37 266 69 138 50 160 64 128 256), losses := [] }

theorem u26354 : Upper (D 7) (R 7) [36,264,65,130,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26355 : PairBound 9 := { available := 176, camps := [{ cop := 6, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 138 82 33 240 176 432), lower := (rows 37 266 69 138 82 33 64 128 256), losses := [] }

theorem u26355 : Upper (D 7) (R 7) [36,264,65,130,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26356 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(1,6),(3,6)], upper := (rows 37 266 69 138 82 48 225 161 417), lower := (rows 37 266 69 138 82 48 64 128 256), losses := [] }

theorem u26356 : Upper (D 7) (R 7) [36,264,65,130,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26356 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26357 : Route 9 := (fun mask => (mask,id))

def c26357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26357 : Upper (D 7) (R 7) [36,264,65,130,66,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,130,66,128] 13 (by decide) (choices 1) [1,16,32] r26357 c26357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9458
  · exact u9459
  · exact u9460

def b26358 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 266 69 138 145 34 112 240 368), lower := (rows 37 266 69 138 145 34 64 128 256), losses := [] }

theorem u26358 : Upper (D 7) (R 7) [36,264,65,130,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26359 : Route 9 := (fun mask => (mask,id))

def c26359 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26359 : Upper (D 7) (R 7) [36,264,65,130,129,16] 13 := by
  apply FastRouting.sound _ _ [36,264,65,130,129,16] 13 (by decide) (choices 1) [2,32] r26359 c26359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9461
  · exact u9462

def b26360 : PairBound 9 := { available := 50, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 138 145 96 114 178 306), lower := (rows 37 266 69 138 145 96 64 128 256), losses := [] }

theorem u26360 : Upper (D 7) (R 7) [36,264,65,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26361 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 266 69 138 176 33 82 210 338), lower := (rows 37 266 69 138 176 33 64 128 256), losses := [] }

theorem u26361 : Upper (D 7) (R 7) [36,264,65,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26362 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 3, region := 48, targets := 1 }], pairs := [(0,1),(2,1),(4,0),(4,1)], upper := (rows 37 266 69 138 176 34 81 209 337), lower := (rows 37 266 69 138 176 34 64 128 256), losses := [] }

theorem u26362 : Upper (D 7) (R 7) [36,264,65,130,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26362 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26363 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 69 138 176 48 67 195 323), lower := (rows 37 266 69 138 176 48 64 128 256), losses := [] }

theorem u26363 : Upper (D 7) (R 7) [36,264,65,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26363 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26364 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 138 176 96 83 147 275), lower := (rows 37 266 69 138 176 96 64 128 256), losses := [] }

theorem u26364 : Upper (D 7) (R 7) [36,264,65,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26365 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 138 208 33 114 178 306), lower := (rows 37 266 69 138 208 33 64 128 256), losses := [] }

theorem u26365 : Upper (D 7) (R 7) [36,264,65,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26366 : Route 9 := (fun mask => (mask,id))

def c26366 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26366 : Upper (D 7) (R 7) [36,264,65,130,192,2] 13 := by
  apply FastRouting.sound _ _ [36,264,65,130,192,2] 13 (by decide) (choices 1) [1,16,32] r26366 c26366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9463
  · exact u9464
  · exact u9465

def b26367 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 266 69 138 208 48 99 163 291), lower := (rows 37 266 69 138 208 48 64 128 256), losses := [] }

theorem u26367 : Upper (D 7) (R 7) [36,264,65,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26367 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26368 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 266 69 152 19 34 224 224 480), lower := (rows 37 266 69 152 19 34 64 128 256), losses := [] }

theorem u26368 : Upper (D 7) (R 7) [36,264,65,144,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26369 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 152 19 96 226 162 418), lower := (rows 37 266 69 152 19 96 64 128 256), losses := [] }

theorem u26369 : Upper (D 7) (R 7) [36,264,65,144,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26370 : Route 9 := (fun mask => (mask,id))

def c26370 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26370 : Upper (D 7) (R 7) [36,264,65,144,3,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,144,3,128] 13 (by decide) (choices 1) [2,32] r26370 c26370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9466
  · exact u9467

def b26371 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 266 69 152 50 33 194 194 450), lower := (rows 37 266 69 152 50 33 64 128 256), losses := [] }

theorem u26371 : Upper (D 7) (R 7) [36,264,65,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26372 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 266 69 152 50 34 193 193 449), lower := (rows 37 266 69 152 50 34 64 128 256), losses := [] }

theorem u26372 : Upper (D 7) (R 7) [36,264,65,144,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26373 : PairBound 9 := { available := 131, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 152 50 96 195 131 387), lower := (rows 37 266 69 152 50 96 64 128 256), losses := [] }

theorem u26373 : Upper (D 7) (R 7) [36,264,65,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26374 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(4,0),(4,6)], upper := (rows 37 266 69 152 50 160 67 195 323), lower := (rows 37 266 69 152 50 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 168 64 128 256), good := (rows 36 314 68 184 50 160 64 160 256) },{ target := 6, region := (rows 1 2 4 8 18 168 0 128 256), good := (rows 37 314 5 184 50 160 0 160 256) }] }

theorem u26374 : Upper (D 7) (R 7) [36,264,65,144,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26374 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26375 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 152 82 33 226 162 418), lower := (rows 37 266 69 152 82 33 64 128 256), losses := [] }

theorem u26375 : Upper (D 7) (R 7) [36,264,65,144,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26376 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 37, targets := 128 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 152 82 34 225 161 417), lower := (rows 37 266 69 152 82 34 64 128 256), losses := [] }

theorem u26376 : Upper (D 7) (R 7) [36,264,65,144,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26377 : Route 9 := (fun mask => (mask,id))

def c26377 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26377 : Upper (D 7) (R 7) [36,264,65,144,66,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,144,66,128] 13 (by decide) (choices 1) [1,2,32] r26377 c26377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9468
  · exact u9469
  · exact u9470

def b26378 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 196, targets := 34 }], pairs := [(1,0),(2,1),(2,5),(3,0)], upper := (rows 37 266 69 168 19 34 208 208 464), lower := (rows 37 266 69 168 19 34 64 128 256), losses := [] }

theorem u26378 : Upper (D 7) (R 7) [36,264,65,160,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26379 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 3, region := 322, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 266 69 168 19 48 194 194 450), lower := (rows 37 266 69 168 19 48 64 128 256), losses := [] }

theorem u26379 : Upper (D 7) (R 7) [36,264,65,160,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26379 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26380 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 168 19 96 210 146 402), lower := (rows 37 266 69 168 19 96 64 128 256), losses := [] }

theorem u26380 : Upper (D 7) (R 7) [36,264,65,160,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26381 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 266 69 168 19 160 82 210 338), lower := (rows 37 266 69 168 19 160 64 128 256), losses := [] }

theorem u26381 : Upper (D 7) (R 7) [36,264,65,160,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26382 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 266 69 168 82 33 210 146 402), lower := (rows 37 266 69 168 82 33 64 128 256), losses := [] }

theorem u26382 : Upper (D 7) (R 7) [36,264,65,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26383 : Route 9 := (fun mask => (mask,id))

def c26383 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26383 : Upper (D 7) (R 7) [36,264,65,160,66,2] 13 := by
  apply FastRouting.sound _ _ [36,264,65,160,66,2] 13 (by decide) (choices 1) [1,16,128] r26383 c26383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9471
  · exact u9472
  · exact u9473

def b26384 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 266 69 168 82 48 195 131 387), lower := (rows 37 266 69 168 82 48 64 128 256), losses := [] }

theorem u26384 : Upper (D 7) (R 7) [36,264,65,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26384 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26385 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 266 69 168 82 160 83 147 275), lower := (rows 37 266 69 168 82 160 64 128 256), losses := [] }

theorem u26385 : Upper (D 7) (R 7) [36,264,65,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26386 : Route 9 := (fun mask => (mask,id))

def c26386 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26386 : Upper (D 7) (R 7) [36,264,65,160,129,2] 13 := by
  apply FastRouting.sound _ _ [36,264,65,160,129,2] 13 (by decide) (choices 1) [2,16] r26386 c26386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9474
  · exact u9475

def b26387 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 69 168 145 48 66 194 322), lower := (rows 37 266 69 168 145 48 64 128 256), losses := [] }

theorem u26387 : Upper (D 7) (R 7) [36,264,65,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26387 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26388 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 168 145 96 82 146 274), lower := (rows 37 266 69 168 145 96 64 128 256), losses := [] }

theorem u26388 : Upper (D 7) (R 7) [36,264,65,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26389 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 266 69 168 146 33 82 210 338), lower := (rows 37 266 69 168 146 33 64 128 256), losses := [] }

theorem u26389 : Upper (D 7) (R 7) [36,264,65,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26390 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 40, targets := 65 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(3,0),(3,6)], upper := (rows 37 266 69 168 146 34 81 209 337), lower := (rows 37 266 69 168 146 34 64 128 256), losses := [] }

theorem u26390 : Upper (D 7) (R 7) [36,264,65,160,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26391 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 69 168 146 48 67 195 323), lower := (rows 37 266 69 168 146 48 64 128 256), losses := [] }

theorem u26391 : Upper (D 7) (R 7) [36,264,65,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26391 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26392 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 168 146 96 83 147 275), lower := (rows 37 266 69 168 146 96 64 128 256), losses := [] }

theorem u26392 : Upper (D 7) (R 7) [36,264,65,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26393 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 266 69 168 208 33 82 146 274), lower := (rows 37 266 69 168 208 33 64 128 256), losses := [] }

theorem u26393 : Upper (D 7) (R 7) [36,264,65,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26393 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26394 : Route 9 := (fun mask => (mask,id))

def c26394 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26394 : Upper (D 7) (R 7) [36,264,65,160,192,2] 13 := by
  apply FastRouting.sound _ _ [36,264,65,160,192,2] 13 (by decide) (choices 1) [1,2,16] r26394 c26394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9476
  · exact u9477
  · exact u9478

def b26395 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 69 168 208 48 67 131 259), lower := (rows 37 266 69 168 208 48 64 128 256), losses := [] }

theorem u26395 : Upper (D 7) (R 7) [36,264,65,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26395 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26396 : Route 9 := (fun mask => (mask,id))

def c26396 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u26396 : Upper (D 7) (R 7) [36,264,65,192,3,2] 13 := by
  apply FastRouting.sound _ _ [36,264,65,192,3,2] 13 (by decide) (choices 1) [16,32,128] r26396 c26396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9479
  · exact u9480
  · exact u9481

def r26397 : Route 9 := (fun mask => (mask,id))

def c26397 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26397 : Upper (D 7) (R 7) [36,264,65,192,3,16] 13 := by
  apply FastRouting.sound _ _ [36,264,65,192,3,16] 13 (by decide) (choices 1) [2,32,128] r26397 c26397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9482
  · exact u9483
  · exact u9484

def b26398 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 37, targets := 2 },{ cop := 4, region := 490, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 266 69 200 19 160 114 178 306), lower := (rows 37 266 69 200 19 160 64 128 256), losses := [] }

theorem u26398 : Upper (D 7) (R 7) [36,264,65,192,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26399 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 200 50 33 210 146 402), lower := (rows 37 266 69 200 50 33 64 128 256), losses := [] }

theorem u26399 : Upper (D 7) (R 7) [36,264,65,192,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26399 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u26399
end Delivery.IrregularNine14.P07
