import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0059
import IrregularNine14P07C0060

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16260 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 3, region := 229, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 13 50 69 266 146 33 224 224 480), lower := (rows 13 50 69 266 146 33 64 128 256), losses := [] }

theorem u16260 : Upper (D 7) (R 7) [12,48,65,258,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16261 : Route 9 := (fun mask => (mask,id))

def c16261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16261 : Upper (D 7) (R 7) [12,48,65,258,130,64] 13 := by
  apply FastRouting.sound _ _ [12,48,65,258,130,64] 13 (by decide) (choices 1) [1,32,128] r16261 c16261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3599
  · exact u3600
  · exact u3601

def b16262 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 69 266 146 160 97 225 353), lower := (rows 13 50 69 266 146 160 64 128 256), losses := [] }

theorem u16262 : Upper (D 7) (R 7) [12,48,65,258,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16263 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 392, targets := 64 }], pairs := [(1,0),(3,0),(3,6),(4,0)], upper := (rows 13 50 69 266 208 33 226 162 418), lower := (rows 13 50 69 266 208 33 64 128 256), losses := [] }

theorem u16263 : Upper (D 7) (R 7) [12,48,65,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16264 : Route 9 := (fun mask => (mask,id))

def c16264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16264 : Upper (D 7) (R 7) [12,48,65,258,192,2] 13 := by
  apply FastRouting.sound _ _ [12,48,65,258,192,2] 13 (by decide) (choices 1) [1,32,128] r16264 c16264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3602
  · exact u3603
  · exact u3604

def b16265 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 69 266 208 160 99 163 291), lower := (rows 13 50 69 266 208 160 64 128 256), losses := [] }

theorem u16265 : Upper (D 7) (R 7) [12,48,65,258,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16266 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 69 296 19 34 192 192 448), lower := (rows 13 50 69 296 19 34 64 128 256), losses := [] }

theorem u16266 : Upper (D 7) (R 7) [12,48,65,288,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16267 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 50, targets := 128 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 13 50 69 296 19 96 194 130 386), lower := (rows 13 50 69 296 19 96 64 128 256), losses := [] }

theorem u16267 : Upper (D 7) (R 7) [12,48,65,288,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16268 : Route 9 := (fun mask => (mask,id))

def c16268 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16268 : Upper (D 7) (R 7) [12,48,65,288,3,128] 13 := by
  apply FastRouting.sound _ _ [12,48,65,288,3,128] 13 (by decide) (choices 1) [2,128] r16268 c16268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3605
  · exact u3606

def b16269 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 50, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 50 69 296 82 33 194 130 386), lower := (rows 13 50 69 296 82 33 64 128 256), losses := [] }

theorem u16269 : Upper (D 7) (R 7) [12,48,65,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16270 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 50, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 69 296 82 34 193 129 385), lower := (rows 13 50 69 296 82 34 64 128 256), losses := [] }

theorem u16270 : Upper (D 7) (R 7) [12,48,65,288,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16271 : Route 9 := (fun mask => (mask,id))

def c16271 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16271 : Upper (D 7) (R 7) [12,48,65,288,66,128] 13 := by
  apply FastRouting.sound _ _ [12,48,65,288,66,128] 13 (by decide) (choices 1) [1,2,128] r16271 c16271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3607
  · exact u3608
  · exact u3609

def b16272 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 13 50 69 296 145 34 194 194 450), lower := (rows 13 50 69 296 145 34 64 128 256), losses := [] }

theorem u16272 : Upper (D 7) (R 7) [12,48,65,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16273 : Route 9 := (fun mask => (mask,id))

def c16273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16273 : Upper (D 7) (R 7) [12,48,65,288,129,64] 13 := by
  apply FastRouting.sound _ _ [12,48,65,288,129,64] 13 (by decide) (choices 1) [2,128] r16273 c16273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3610
  · exact u3611

def b16274 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 69 296 145 160 66 194 322), lower := (rows 13 50 69 296 145 160 64 128 256), losses := [] }

theorem u16274 : Upper (D 7) (R 7) [12,48,65,288,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16275 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 50 69 296 146 33 194 194 450), lower := (rows 13 50 69 296 146 33 64 128 256), losses := [] }

theorem u16275 : Upper (D 7) (R 7) [12,48,65,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16276 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 197, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 50 69 296 146 34 193 193 449), lower := (rows 13 50 69 296 146 34 64 128 256), losses := [] }

theorem u16276 : Upper (D 7) (R 7) [12,48,65,288,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16277 : Route 9 := (fun mask => (mask,id))

def c16277 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16277 : Upper (D 7) (R 7) [12,48,65,288,130,64] 13 := by
  apply FastRouting.sound _ _ [12,48,65,288,130,64] 13 (by decide) (choices 1) [1,2,128] r16277 c16277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3612
  · exact u3613
  · exact u3614

def b16278 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 69 296 146 160 67 195 323), lower := (rows 13 50 69 296 146 160 64 128 256), losses := [] }

theorem u16278 : Upper (D 7) (R 7) [12,48,65,288,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16279 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 50 69 296 208 33 194 130 386), lower := (rows 13 50 69 296 208 33 64 128 256), losses := [] }

theorem u16279 : Upper (D 7) (R 7) [12,48,65,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16280 : Route 9 := (fun mask => (mask,id))

def c16280 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16280 : Upper (D 7) (R 7) [12,48,65,288,192,2] 13 := by
  apply FastRouting.sound _ _ [12,48,65,288,192,2] 13 (by decide) (choices 1) [1,2,128] r16280 c16280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3615
  · exact u3616
  · exact u3617

def b16281 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 69 296 208 160 67 131 259), lower := (rows 13 50 69 296 208 160 64 128 256), losses := [] }

theorem u16281 : Upper (D 7) (R 7) [12,48,65,288,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16282 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 69 392 19 34 224 224 480), lower := (rows 13 50 69 392 19 34 64 128 256), losses := [] }

theorem u16282 : Upper (D 7) (R 7) [12,48,65,384,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16283 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 50, targets := 128 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 13 50 69 392 19 96 226 162 418), lower := (rows 13 50 69 392 19 96 64 128 256), losses := [] }

theorem u16283 : Upper (D 7) (R 7) [12,48,65,384,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16284 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(1,6),(3,0),(4,6)], upper := (rows 13 50 69 392 19 160 98 226 354), lower := (rows 13 50 69 392 19 160 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 8 21 168 0 128 256), good := (rows 63 50 23 424 19 160 0 160 256) }] }

theorem u16284 : Upper (D 7) (R 7) [12,48,65,384,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16285 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 50, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 50 69 392 82 33 226 162 418), lower := (rows 13 50 69 392 82 33 64 128 256), losses := [] }

theorem u16285 : Upper (D 7) (R 7) [12,48,65,384,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16286 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 50, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 69 392 82 34 225 161 417), lower := (rows 13 50 69 392 82 34 64 128 256), losses := [] }

theorem u16286 : Upper (D 7) (R 7) [12,48,65,384,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16286 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16287 : Route 9 := (fun mask => (mask,id))

def c16287 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16287 : Upper (D 7) (R 7) [12,48,65,384,66,128] 13 := by
  apply FastRouting.sound _ _ [12,48,65,384,66,128] 13 (by decide) (choices 1) [1,2,32] r16287 c16287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3618
  · exact u3619
  · exact u3620

def r16288 : Route 9 := (fun mask => (mask,id))

def c16288 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16288 : Upper (D 7) (R 7) [12,48,65,384,130,1] 13 := by
  apply FastRouting.sound _ _ [12,48,65,384,130,1] 13 (by decide) (choices 1) [2,32] r16288 c16288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3621
  · exact u3622

def b16289 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 69 392 146 34 97 225 353), lower := (rows 13 50 69 392 146 34 64 128 256), losses := [] }

theorem u16289 : Upper (D 7) (R 7) [12,48,65,384,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16290 : Route 9 := (fun mask => (mask,id))

def c16290 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16290 : Upper (D 7) (R 7) [12,48,65,384,130,64] 13 := by
  apply FastRouting.sound _ _ [12,48,65,384,130,64] 13 (by decide) (choices 1) [1,2,32] r16290 c16290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3623
  · exact u3624
  · exact u3625

def b16291 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 392, targets := 64 }], pairs := [(1,0),(3,0),(3,6),(4,0)], upper := (rows 13 50 69 392 208 33 98 162 290), lower := (rows 13 50 69 392 208 33 64 128 256), losses := [] }

theorem u16291 : Upper (D 7) (R 7) [12,48,65,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16292 : Route 9 := (fun mask => (mask,id))

def c16292 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16292 : Upper (D 7) (R 7) [12,48,65,384,192,2] 13 := by
  apply FastRouting.sound _ _ [12,48,65,384,192,2] 13 (by decide) (choices 1) [1,2,32] r16292 c16292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3626
  · exact u3627
  · exact u3628

def b16293 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 13 50 70 104 145 33 450 386 386), lower := (rows 13 50 70 104 145 33 64 128 256), losses := [] }

theorem u16293 : Upper (D 7) (R 7) [12,48,66,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16294 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 400, targets := 34 },{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,6)], upper := (rows 13 50 70 104 145 34 449 385 385), lower := (rows 13 50 70 104 145 34 64 128 256), losses := [] }

theorem u16294 : Upper (D 7) (R 7) [12,48,66,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16295 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 0, region := 434, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(3,7)], upper := (rows 13 50 70 104 145 160 323 387 259), lower := (rows 13 50 70 104 145 160 64 128 256), losses := [] }

theorem u16295 : Upper (D 7) (R 7) [12,48,66,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16296 : Route 9 := (fun mask => (mask,id))

def c16296 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16296 : Upper (D 7) (R 7) [12,48,66,96,129,256] 13 := by
  apply FastRouting.sound _ _ [12,48,66,96,129,256] 13 (by decide) (choices 1) [1,2,128] r16296 c16296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3629
  · exact u3630
  · exact u3631

def b16297 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 13 50 70 104 273 33 194 130 386), lower := (rows 13 50 70 104 273 33 64 128 256), losses := [] }

theorem u16297 : Upper (D 7) (R 7) [12,48,66,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16298 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 34 },{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,6)], upper := (rows 13 50 70 104 273 34 193 129 385), lower := (rows 13 50 70 104 273 34 64 128 256), losses := [] }

theorem u16298 : Upper (D 7) (R 7) [12,48,66,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16299 : Route 9 := (fun mask => (mask,id))

def c16299 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16299 : Upper (D 7) (R 7) [12,48,66,96,257,128] 13 := by
  apply FastRouting.sound _ _ [12,48,66,96,257,128] 13 (by decide) (choices 1) [1,2,128] r16299 c16299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3632
  · exact u3633
  · exact u3634

def b16300 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 13 50 70 104 400 33 195 131 387), lower := (rows 13 50 70 104 400 33 64 128 256), losses := [] }

theorem u16300 : Upper (D 7) (R 7) [12,48,66,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16301 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 34, targets := 193 },{ cop := 0, region := 400, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 50 70 104 400 34 193 129 385), lower := (rows 13 50 70 104 400 34 64 128 256), losses := [] }

theorem u16301 : Upper (D 7) (R 7) [12,48,66,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16302 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 434, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(3,7)], upper := (rows 13 50 70 104 400 160 67 131 259), lower := (rows 13 50 70 104 400 160 64 128 256), losses := [] }

theorem u16302 : Upper (D 7) (R 7) [12,48,66,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16303 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 4, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(3,0)], upper := (rows 13 50 70 138 273 33 224 224 480), lower := (rows 13 50 70 138 273 33 64 128 256), losses := [] }

theorem u16303 : Upper (D 7) (R 7) [12,48,66,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16304 : Route 9 := (fun mask => (mask,id))

def c16304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16304 : Upper (D 7) (R 7) [12,48,66,130,257,64] 13 := by
  apply FastRouting.sound _ _ [12,48,66,130,257,64] 13 (by decide) (choices 1) [1,32,128] r16304 c16304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3635
  · exact u3636
  · exact u3637

def r16305 : Route 9 := (fun mask => (mask,id))

def c16305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16305 : Upper (D 7) (R 7) [12,48,66,130,320,1] 13 := by
  apply FastRouting.sound _ _ [12,48,66,130,320,1] 13 (by decide) (choices 1) [1,32,128] r16305 c16305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3638
  · exact u3639
  · exact u3640

def r16306 : Route 9 := (fun mask => (mask,id))

def c16306 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16306 : Upper (D 7) (R 7) [12,48,66,130,320,128] 13 := by
  apply FastRouting.sound _ _ [12,48,66,130,320,128] 13 (by decide) (choices 1) [1,32] r16306 c16306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3641
  · exact u3642

def b16307 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 50 70 168 19 33 448 448 448), lower := (rows 13 50 70 168 19 33 64 128 256), losses := [] }

theorem u16307 : Upper (D 7) (R 7) [12,48,66,160,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16308 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 425, targets := 2 },{ cop := 4, region := 452, targets := 32 }], pairs := [(0,1),(0,6),(2,5),(3,1)], upper := (rows 13 50 70 168 19 96 449 385 385), lower := (rows 13 50 70 168 19 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 10 20 32 0 149 277), good := (rows 413 442 415 168 411 32 0 128 256) }] }

theorem u16308 : Upper (D 7) (R 7) [12,48,66,160,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16309 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 70 168 19 160 321 449 321), lower := (rows 13 50 70 168 19 160 64 128 256), losses := [] }

theorem u16309 : Upper (D 7) (R 7) [12,48,66,160,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16310 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 425, targets := 2 },{ cop := 4, region := 196, targets := 32 }], pairs := [(0,1),(2,5),(3,1)], upper := (rows 13 50 70 168 19 288 193 193 449), lower := (rows 13 50 70 168 19 288 64 128 256), losses := [] }

theorem u16310 : Upper (D 7) (R 7) [12,48,66,160,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16310 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16311 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(3,6)], upper := (rows 13 50 70 168 81 33 450 386 386), lower := (rows 13 50 70 168 81 33 64 128 256), losses := [] }

theorem u16311 : Upper (D 7) (R 7) [12,48,66,160,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16312 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 70 168 81 34 449 385 385), lower := (rows 13 50 70 168 81 34 64 128 256), losses := [] }

theorem u16312 : Upper (D 7) (R 7) [12,48,66,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16313 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 70 168 81 160 323 387 259), lower := (rows 13 50 70 168 81 160 64 128 256), losses := [] }

theorem u16313 : Upper (D 7) (R 7) [12,48,66,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16314 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 4, region := 418, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 13 50 70 168 81 288 195 131 387), lower := (rows 13 50 70 168 81 288 64 128 256), losses := [] }

theorem u16314 : Upper (D 7) (R 7) [12,48,66,160,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16314 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16315 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 42, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(3,6)], upper := (rows 13 50 70 168 145 33 322 450 322), lower := (rows 13 50 70 168 145 33 64 128 256), losses := [] }

theorem u16315 : Upper (D 7) (R 7) [12,48,66,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16316 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 50 70 168 145 34 321 449 321), lower := (rows 13 50 70 168 145 34 64 128 256), losses := [] }

theorem u16316 : Upper (D 7) (R 7) [12,48,66,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16317 : Route 9 := (fun mask => (mask,id))

def c16317 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u16317 : Upper (D 7) (R 7) [12,48,66,160,129,64] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,129,64] 13 (by decide) (choices 1) [1,2,256] r16317 c16317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3643
  · exact u3644
  · exact u3645

def r16318 : Route 9 := (fun mask => (mask,id))

def c16318 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16318 : Upper (D 7) (R 7) [12,48,66,160,129,256] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,129,256] 13 (by decide) (choices 1) [1,2] r16318 c16318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3646
  · exact u3647

def r16319 : Route 9 := (fun mask => (mask,id))

def c16319 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u16319 : Upper (D 7) (R 7) [12,48,66,160,192,1] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160,192,1] 13 (by decide) (choices 1) [1,2,256] r16319 c16319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3648
  · exact u3649
  · exact u3650

#print axioms u16319
end Delivery.IrregularNine14.P07
