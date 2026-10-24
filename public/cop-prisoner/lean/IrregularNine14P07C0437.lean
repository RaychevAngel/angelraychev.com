import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0156

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r26220 : Route 9 := (fun mask => (mask,id))

def c26220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26220 : Upper (D 7) (R 7) [36,264,18,3,65,128] 13 := by
  apply FastRouting.sound _ _ [36,264,18,3,65,128] 13 (by decide) (choices 1) [32,128] r26220 c26220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9368
  · exact u9369

def b26221 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 266 22 11 208 33 224 224 480), lower := (rows 37 266 22 11 208 33 64 128 256), losses := [] }

theorem u26221 : Upper (D 7) (R 7) [36,264,18,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26222 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,1)], upper := (rows 37 266 22 11 208 96 225 161 417), lower := (rows 37 266 22 11 208 96 64 128 256), losses := [] }

theorem u26222 : Upper (D 7) (R 7) [36,264,18,3,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26223 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 266 22 42 81 33 192 192 448), lower := (rows 37 266 22 42 81 33 64 128 256), losses := [] }

theorem u26223 : Upper (D 7) (R 7) [36,264,18,34,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26224 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,1)], upper := (rows 37 266 22 42 81 96 193 129 385), lower := (rows 37 266 22 42 81 96 64 128 256), losses := [] }

theorem u26224 : Upper (D 7) (R 7) [36,264,18,34,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26225 : Route 9 := (fun mask => (mask,id))

def c26225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26225 : Upper (D 7) (R 7) [36,264,18,34,65,128] 13 := by
  apply FastRouting.sound _ _ [36,264,18,34,65,128] 13 (by decide) (choices 1) [1,128] r26225 c26225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9370
  · exact u9371

def b26226 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 266 22 42 208 33 193 193 449), lower := (rows 37 266 22 42 208 33 64 128 256), losses := [] }

theorem u26226 : Upper (D 7) (R 7) [36,264,18,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26227 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,1)], upper := (rows 37 266 22 42 208 96 193 129 385), lower := (rows 37 266 22 42 208 96 64 128 256), losses := [] }

theorem u26227 : Upper (D 7) (R 7) [36,264,18,34,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26228 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 266 22 73 145 34 224 224 480), lower := (rows 37 266 22 73 145 34 64 128 256), losses := [] }

theorem u26228 : Upper (D 7) (R 7) [36,264,18,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26229 : Route 9 := (fun mask => (mask,id))

def c26229 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26229 : Upper (D 7) (R 7) [36,264,18,65,129,64] 13 := by
  apply FastRouting.sound _ _ [36,264,18,65,129,64] 13 (by decide) (choices 1) [2,32,128] r26229 c26229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9372
  · exact u9373
  · exact u9374

def b26230 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 418, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(3,7)], upper := (rows 37 266 22 73 145 160 98 226 354), lower := (rows 37 266 22 73 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 264 53 73 177 160 64 160 256) }] }

theorem u26230 : Upper (D 7) (R 7) [36,264,18,65,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26231 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 266 22 73 176 33 194 194 450), lower := (rows 37 266 22 73 176 33 64 128 256), losses := [] }

theorem u26231 : Upper (D 7) (R 7) [36,264,18,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26232 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(3,1),(3,5),(4,1)], upper := (rows 37 266 22 73 176 34 193 193 449), lower := (rows 37 266 22 73 176 34 64 128 256), losses := [] }

theorem u26232 : Upper (D 7) (R 7) [36,264,18,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26232 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26233 : Route 9 := (fun mask => (mask,id))

def c26233 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26233 : Upper (D 7) (R 7) [36,264,18,65,160,64] 13 := by
  apply FastRouting.sound _ _ [36,264,18,65,160,64] 13 (by decide) (choices 1) [1,2,128] r26233 c26233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9375
  · exact u9376
  · exact u9377

def b26234 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 22 73 176 160 67 195 323), lower := (rows 37 266 22 73 176 160 64 128 256), losses := [] }

theorem u26234 : Upper (D 7) (R 7) [36,264,18,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26235 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 33, targets := 64 },{ cop := 3, region := 418, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 266 22 73 208 33 226 162 418), lower := (rows 37 266 22 73 208 33 64 128 256), losses := [] }

theorem u26235 : Upper (D 7) (R 7) [36,264,18,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26236 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 266 22 73 208 34 225 161 417), lower := (rows 37 266 22 73 208 34 64 128 256), losses := [] }

theorem u26236 : Upper (D 7) (R 7) [36,264,18,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26237 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 161, targets := 64 },{ cop := 3, region := 418, targets := 64 }], pairs := [(0,6),(1,6),(1,7),(3,7)], upper := (rows 37 266 22 73 208 160 99 163 291), lower := (rows 37 266 22 73 208 160 64 128 256), losses := [] }

theorem u26237 : Upper (D 7) (R 7) [36,264,18,65,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26238 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 266 22 74 81 33 224 160 416), lower := (rows 37 266 22 74 81 33 64 128 256), losses := [] }

theorem u26238 : Upper (D 7) (R 7) [36,264,18,66,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26239 : Route 9 := (fun mask => (mask,id))

def c26239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26239 : Upper (D 7) (R 7) [36,264,18,66,65,128] 13 := by
  apply FastRouting.sound _ _ [36,264,18,66,65,128] 13 (by decide) (choices 1) [1,32,128] r26239 c26239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9378
  · exact u9379
  · exact u9380

def b26240 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 266 22 74 145 33 224 224 480), lower := (rows 37 266 22 74 145 33 64 128 256), losses := [] }

theorem u26240 : Upper (D 7) (R 7) [36,264,18,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26241 : Route 9 := (fun mask => (mask,id))

def c26241 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26241 : Upper (D 7) (R 7) [36,264,18,66,129,64] 13 := by
  apply FastRouting.sound _ _ [36,264,18,66,129,64] 13 (by decide) (choices 1) [1,32,128] r26241 c26241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9381
  · exact u9382
  · exact u9383

def b26242 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,1)], upper := (rows 37 266 22 74 145 160 97 225 353), lower := (rows 37 266 22 74 145 160 64 128 256), losses := [] }

theorem u26242 : Upper (D 7) (R 7) [36,264,18,66,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26243 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 2, region := 33, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 266 22 74 208 33 225 161 417), lower := (rows 37 266 22 74 208 33 64 128 256), losses := [] }

theorem u26243 : Upper (D 7) (R 7) [36,264,18,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26244 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,1)], upper := (rows 37 266 22 74 208 160 97 161 289), lower := (rows 37 266 22 74 208 160 64 128 256), losses := [] }

theorem u26244 : Upper (D 7) (R 7) [36,264,18,66,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26245 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 2, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(3,0)], upper := (rows 37 266 22 104 81 33 194 130 386), lower := (rows 37 266 22 104 81 33 64 128 256), losses := [] }

theorem u26245 : Upper (D 7) (R 7) [36,264,18,96,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26246 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 208, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,5)], upper := (rows 37 266 22 104 81 34 193 129 385), lower := (rows 37 266 22 104 81 34 64 128 256), losses := [] }

theorem u26246 : Upper (D 7) (R 7) [36,264,18,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26247 : Route 9 := (fun mask => (mask,id))

def c26247 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26247 : Upper (D 7) (R 7) [36,264,18,96,65,128] 13 := by
  apply FastRouting.sound _ _ [36,264,18,96,65,128] 13 (by decide) (choices 1) [1,2,128] r26247 c26247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9384
  · exact u9385
  · exact u9386

def b26248 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 266 22 104 145 33 194 194 450), lower := (rows 37 266 22 104 145 33 64 128 256), losses := [] }

theorem u26248 : Upper (D 7) (R 7) [36,264,18,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26249 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 266 22 104 145 34 193 193 449), lower := (rows 37 266 22 104 145 34 64 128 256), losses := [] }

theorem u26249 : Upper (D 7) (R 7) [36,264,18,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26250 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 37 266 22 104 145 96 195 131 387), lower := (rows 37 266 22 104 145 96 64 128 256), losses := [] }

theorem u26250 : Upper (D 7) (R 7) [36,264,18,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26251 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 266 22 104 145 160 67 195 323), lower := (rows 37 266 22 104 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 264 53 104 177 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 266 55 40 177 160 0 160 256) }] }

theorem u26251 : Upper (D 7) (R 7) [36,264,18,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26252 : Route 9 := (fun mask => (mask,id))

def c26252 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26252 : Upper (D 7) (R 7) [36,264,18,96,192,1] 13 := by
  apply FastRouting.sound _ _ [36,264,18,96,192,1] 13 (by decide) (choices 1) [1,2,128] r26252 c26252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9387
  · exact u9388
  · exact u9389

def b26253 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 208, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,5)], upper := (rows 37 266 22 104 208 34 193 129 385), lower := (rows 37 266 22 104 208 34 64 128 256), losses := [] }

theorem u26253 : Upper (D 7) (R 7) [36,264,18,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26254 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 4, region := 40, targets := 3 }], pairs := [(1,7),(3,0),(3,1),(3,7)], upper := (rows 37 266 22 104 208 160 67 131 259), lower := (rows 37 266 22 104 208 160 64 128 256), losses := [] }

theorem u26254 : Upper (D 7) (R 7) [36,264,18,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26255 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 2, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(3,0)], upper := (rows 37 266 22 200 81 33 226 162 418), lower := (rows 37 266 22 200 81 33 64 128 256), losses := [] }

theorem u26255 : Upper (D 7) (R 7) [36,264,18,192,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26256 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 266 22 200 81 34 225 161 417), lower := (rows 37 266 22 200 81 34 64 128 256), losses := [] }

theorem u26256 : Upper (D 7) (R 7) [36,264,18,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26257 : Route 9 := (fun mask => (mask,id))

def c26257 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26257 : Upper (D 7) (R 7) [36,264,18,192,65,128] 13 := by
  apply FastRouting.sound _ _ [36,264,18,192,65,128] 13 (by decide) (choices 1) [1,2,32] r26257 c26257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9390
  · exact u9391
  · exact u9392

def b26258 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,5),(3,5)], upper := (rows 37 266 22 200 112 33 195 131 387), lower := (rows 37 266 22 200 112 33 64 128 256), losses := [] }

theorem u26258 : Upper (D 7) (R 7) [36,264,18,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26259 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(3,1),(3,5),(4,1)], upper := (rows 37 266 22 200 112 34 193 129 385), lower := (rows 37 266 22 200 112 34 64 128 256), losses := [] }

theorem u26259 : Upper (D 7) (R 7) [36,264,18,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26260 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 3, region := 48, targets := 3 }], pairs := [(1,5),(3,5),(4,0),(4,1)], upper := (rows 37 266 22 200 112 160 67 131 259), lower := (rows 37 266 22 200 112 160 64 128 256), losses := [] }

theorem u26260 : Upper (D 7) (R 7) [36,264,18,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26261 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 266 69 11 176 34 208 208 464), lower := (rows 37 266 69 11 176 34 64 128 256), losses := [] }

theorem u26261 : Upper (D 7) (R 7) [36,264,65,3,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26262 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 69 11 176 48 194 194 450), lower := (rows 37 266 69 11 176 48 64 128 256), losses := [] }

theorem u26262 : Upper (D 7) (R 7) [36,264,65,3,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26262 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26263 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 11 176 96 210 146 402), lower := (rows 37 266 69 11 176 96 64 128 256), losses := [] }

theorem u26263 : Upper (D 7) (R 7) [36,264,65,3,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26264 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 69 11 176 160 82 210 338), lower := (rows 37 266 69 11 176 160 64 128 256), losses := [] }

theorem u26264 : Upper (D 7) (R 7) [36,264,65,3,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26265 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 266 69 11 208 34 240 176 432), lower := (rows 37 266 69 11 208 34 64 128 256), losses := [] }

theorem u26265 : Upper (D 7) (R 7) [36,264,65,3,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26266 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 266 69 11 208 48 226 162 418), lower := (rows 37 266 69 11 208 48 64 128 256), losses := [] }

theorem u26266 : Upper (D 7) (R 7) [36,264,65,3,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26266 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26267 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 4, region := 37, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 266 69 11 208 160 114 178 306), lower := (rows 37 266 69 11 208 160 64 128 256), losses := [] }

theorem u26267 : Upper (D 7) (R 7) [36,264,65,3,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26268 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 3, region := 418, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 266 69 25 82 34 224 160 416), lower := (rows 37 266 69 25 82 34 64 128 256), losses := [] }

theorem u26268 : Upper (D 7) (R 7) [36,264,65,17,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26269 : Route 9 := (fun mask => (mask,id))

def c26269 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26269 : Upper (D 7) (R 7) [36,264,65,17,66,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,17,66,128] 13 (by decide) (choices 1) [2,32,128] r26269 c26269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9393
  · exact u9394
  · exact u9395

def b26270 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 266 69 25 146 34 224 224 480), lower := (rows 37 266 69 25 146 34 64 128 256), losses := [] }

theorem u26270 : Upper (D 7) (R 7) [36,264,65,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26271 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 25 146 96 226 162 418), lower := (rows 37 266 69 25 146 96 64 128 256), losses := [] }

theorem u26271 : Upper (D 7) (R 7) [36,264,65,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26272 : Route 9 := (fun mask => (mask,id))

def c26272 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26272 : Upper (D 7) (R 7) [36,264,65,17,130,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,17,130,128] 13 (by decide) (choices 1) [2,32] r26272 c26272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9396
  · exact u9397

def r26273 : Route 9 := (fun mask => (mask,id))

def c26273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26273 : Upper (D 7) (R 7) [36,264,65,17,192,2] 13 := by
  apply FastRouting.sound _ _ [36,264,65,17,192,2] 13 (by decide) (choices 1) [2,32,128] r26273 c26273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9398
  · exact u9399
  · exact u9400

def b26274 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 3, region := 418, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 37 266 69 25 208 160 98 162 290), lower := (rows 37 266 69 25 208 160 64 128 256), losses := [] }

theorem u26274 : Upper (D 7) (R 7) [36,264,65,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26275 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 266 69 26 145 34 224 224 480), lower := (rows 37 266 69 26 145 34 64 128 256), losses := [] }

theorem u26275 : Upper (D 7) (R 7) [36,264,65,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26276 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 26 145 96 226 162 418), lower := (rows 37 266 69 26 145 96 64 128 256), losses := [] }

theorem u26276 : Upper (D 7) (R 7) [36,264,65,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26277 : Route 9 := (fun mask => (mask,id))

def c26277 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26277 : Upper (D 7) (R 7) [36,264,65,18,129,128] 13 := by
  apply FastRouting.sound _ _ [36,264,65,18,129,128] 13 (by decide) (choices 1) [2,32] r26277 c26277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9401
  · exact u9402

def b26278 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 266 69 26 176 33 194 194 450), lower := (rows 37 266 69 26 176 33 64 128 256), losses := [] }

theorem u26278 : Upper (D 7) (R 7) [36,264,65,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26279 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,1),(2,1),(2,5),(4,1)], upper := (rows 37 266 69 26 176 34 193 193 449), lower := (rows 37 266 69 26 176 34 64 128 256), losses := [] }

theorem u26279 : Upper (D 7) (R 7) [36,264,65,18,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u26279
end Delivery.IrregularNine14.P07
