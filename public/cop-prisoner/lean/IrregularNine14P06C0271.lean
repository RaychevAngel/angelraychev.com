import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0067
import IrregularNine14P06C0068

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16260 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 134 52 104 82 36 321 385 257), lower := (rows 11 134 52 104 82 36 64 128 256), losses := [] }

theorem u16260 : Upper (D 6) (R 6) [10,132,48,96,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16261 : Route 9 := (fun mask => (mask,id))

def c16261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16261 : Upper (D 6) (R 6) [10,132,48,96,66,256] 13 := by
  apply FastRouting.sound _ _ [10,132,48,96,66,256] 13 (by decide) (choices 1) [1,4] r16261 c16261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4045
  · exact u4046

def b16262 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 202, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 11 134 52 104 273 33 70 198 326), lower := (rows 11 134 52 104 273 33 64 128 256), losses := [] }

theorem u16262 : Upper (D 6) (R 6) [10,132,48,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16263 : Route 9 := (fun mask => (mask,id))

def c16263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16263 : Upper (D 6) (R 6) [10,132,48,96,257,2] 13 := by
  apply FastRouting.sound _ _ [10,132,48,96,257,2] 13 (by decide) (choices 1) [1,4] r16263 c16263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4047
  · exact u4048

def b16264 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 52 104 273 36 67 195 323), lower := (rows 11 134 52 104 273 36 64 128 256), losses := [] }

theorem u16264 : Upper (D 6) (R 6) [10,132,48,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16265 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 52 104 273 96 71 135 263), lower := (rows 11 134 52 104 273 96 64 128 256), losses := [] }

theorem u16265 : Upper (D 6) (R 6) [10,132,48,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16266 : Route 9 := (fun mask => (mask,id))

def c16266 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16266 : Upper (D 6) (R 6) [10,132,48,96,258,1] 13 := by
  apply FastRouting.sound _ _ [10,132,48,96,258,1] 13 (by decide) (choices 1) [1,4] r16266 c16266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4049
  · exact u4050

def b16267 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 52 104 274 36 65 193 321), lower := (rows 11 134 52 104 274 36 64 128 256), losses := [] }

theorem u16267 : Upper (D 6) (R 6) [10,132,48,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16268 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 52 104 274 96 69 133 261), lower := (rows 11 134 52 104 274 96 64 128 256), losses := [] }

theorem u16268 : Upper (D 6) (R 6) [10,132,48,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16269 : Route 9 := (fun mask => (mask,id))

def c16269 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16269 : Upper (D 6) (R 6) [10,132,48,96,260,1] 13 := by
  apply FastRouting.sound _ _ [10,132,48,96,260,1] 13 (by decide) (choices 1) [1,2] r16269 c16269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4051
  · exact u4052

def r16270 : Route 9 := (fun mask => (mask,id))

def c16270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16270 : Upper (D 6) (R 6) [10,132,48,96,260,2] 13 := by
  apply FastRouting.sound _ _ [10,132,48,96,260,2] 13 (by decide) (choices 1) [1] r16270 c16270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u4053

def b16271 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 52 104 276 96 67 131 259), lower := (rows 11 134 52 104 276 96 64 128 256), losses := [] }

theorem u16271 : Upper (D 6) (R 6) [10,132,48,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16272 : Route 9 := (fun mask => (mask,id))

def c16272 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16272 : Upper (D 6) (R 6) [10,132,48,96,320,1] 13 := by
  apply FastRouting.sound _ _ [10,132,48,96,320,1] 13 (by decide) (choices 1) [1,2,4] r16272 c16272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4054
  · exact u4055
  · exact u4056

def r16273 : Route 9 := (fun mask => (mask,id))

def c16273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16273 : Upper (D 6) (R 6) [10,132,48,96,320,2] 13 := by
  apply FastRouting.sound _ _ [10,132,48,96,320,2] 13 (by decide) (choices 1) [1,4] r16273 c16273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4057
  · exact u4058

def b16274 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 134 52 104 336 36 67 131 259), lower := (rows 11 134 52 104 336 36 64 128 256), losses := [] }

theorem u16274 : Upper (D 6) (R 6) [10,132,48,96,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16275 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 166, targets := 1 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 11 134 52 265 81 34 100 228 356), lower := (rows 11 134 52 265 81 34 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 8 16 35 0 128 256), good := (rows 43 166 52 297 53 34 0 128 256) }] }

theorem u16275 : Upper (D 6) (R 6) [10,132,48,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16276 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 134 52 265 81 36 98 226 354), lower := (rows 11 134 52 265 81 36 64 128 256), losses := [] }

theorem u16276 : Upper (D 6) (R 6) [10,132,48,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16277 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 52 265 81 96 102 166 294), lower := (rows 11 134 52 265 81 96 64 128 256), losses := [] }

theorem u16277 : Upper (D 6) (R 6) [10,132,48,257,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16278 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 52 265 82 33 100 228 356), lower := (rows 11 134 52 265 82 33 64 128 256), losses := [] }

theorem u16278 : Upper (D 6) (R 6) [10,132,48,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16279 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 52 265 82 36 97 225 353), lower := (rows 11 134 52 265 82 36 64 128 256), losses := [] }

theorem u16279 : Upper (D 6) (R 6) [10,132,48,257,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16280 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 52 265 82 96 101 165 293), lower := (rows 11 134 52 265 82 96 64 128 256), losses := [] }

theorem u16280 : Upper (D 6) (R 6) [10,132,48,257,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16281 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 52 265 84 33 98 226 354), lower := (rows 11 134 52 265 84 33 64 128 256), losses := [] }

theorem u16281 : Upper (D 6) (R 6) [10,132,48,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16282 : Route 9 := (fun mask => (mask,id))

def c16282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16282 : Upper (D 6) (R 6) [10,132,48,257,68,2] 13 := by
  apply FastRouting.sound _ _ [10,132,48,257,68,2] 13 (by decide) (choices 1) [1,32] r16282 c16282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4059
  · exact u4060

def b16283 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 134 52 265 84 96 99 163 291), lower := (rows 11 134 52 265 84 96 64 128 256), losses := [] }

theorem u16283 : Upper (D 6) (R 6) [10,132,48,257,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16284 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 458, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 11 134 52 268 81 33 98 226 354), lower := (rows 11 134 52 268 81 33 64 128 256), losses := [] }

theorem u16284 : Upper (D 6) (R 6) [10,132,48,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16285 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 112, targets := 4 }], pairs := [(2,0),(2,6),(4,2)], upper := (rows 11 134 52 268 81 34 97 225 353), lower := (rows 11 134 52 268 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 35 64 128 256), good := (rows 42 166 52 268 116 34 64 128 256) },{ target := 6, region := (rows 1 2 20 8 16 35 0 128 256), good := (rows 43 166 52 268 53 34 0 128 256) }] }

theorem u16285 : Upper (D 6) (R 6) [10,132,48,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16286 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 52 268 81 96 99 163 291), lower := (rows 11 134 52 268 81 96 64 128 256), losses := [] }

theorem u16286 : Upper (D 6) (R 6) [10,132,48,260,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16287 : Route 9 := (fun mask => (mask,id))

def c16287 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16287 : Upper (D 6) (R 6) [10,132,48,260,66,1] 13 := by
  apply FastRouting.sound _ _ [10,132,48,260,66,1] 13 (by decide) (choices 1) [1,32] r16287 c16287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4061
  · exact u4062

def b16288 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 52 268 82 96 97 161 289), lower := (rows 11 134 52 268 82 96 64 128 256), losses := [] }

theorem u16288 : Upper (D 6) (R 6) [10,132,48,260,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16289 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 458, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 11 134 52 296 81 33 70 198 326), lower := (rows 11 134 52 296 81 33 64 128 256), losses := [] }

theorem u16289 : Upper (D 6) (R 6) [10,132,48,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16290 : Route 9 := (fun mask => (mask,id))

def c16290 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16290 : Upper (D 6) (R 6) [10,132,48,288,65,2] 13 := by
  apply FastRouting.sound _ _ [10,132,48,288,65,2] 13 (by decide) (choices 1) [1,4] r16290 c16290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4063
  · exact u4064

def b16291 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 52 296 81 36 67 195 323), lower := (rows 11 134 52 296 81 36 64 128 256), losses := [] }

theorem u16291 : Upper (D 6) (R 6) [10,132,48,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16292 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 52 296 81 96 71 135 263), lower := (rows 11 134 52 296 81 96 64 128 256), losses := [] }

theorem u16292 : Upper (D 6) (R 6) [10,132,48,288,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16293 : Route 9 := (fun mask => (mask,id))

def c16293 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16293 : Upper (D 6) (R 6) [10,132,48,288,66,1] 13 := by
  apply FastRouting.sound _ _ [10,132,48,288,66,1] 13 (by decide) (choices 1) [1,4] r16293 c16293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4065
  · exact u4066

def b16294 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 52 296 82 36 65 193 321), lower := (rows 11 134 52 296 82 36 64 128 256), losses := [] }

theorem u16294 : Upper (D 6) (R 6) [10,132,48,288,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16295 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 52 296 82 96 69 133 261), lower := (rows 11 134 52 296 82 96 64 128 256), losses := [] }

theorem u16295 : Upper (D 6) (R 6) [10,132,48,288,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16296 : Route 9 := (fun mask => (mask,id))

def c16296 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16296 : Upper (D 6) (R 6) [10,132,48,288,68,1] 13 := by
  apply FastRouting.sound _ _ [10,132,48,288,68,1] 13 (by decide) (choices 1) [1,2] r16296 c16296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4067
  · exact u4068

def r16297 : Route 9 := (fun mask => (mask,id))

def c16297 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16297 : Upper (D 6) (R 6) [10,132,48,288,68,2] 13 := by
  apply FastRouting.sound _ _ [10,132,48,288,68,2] 13 (by decide) (choices 1) [1] r16297 c16297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u4069

def b16298 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 134 52 296 84 96 67 131 259), lower := (rows 11 134 52 296 84 96 64 128 256), losses := [] }

theorem u16298 : Upper (D 6) (R 6) [10,132,48,288,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16299 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 134 52 328 21 33 98 226 354), lower := (rows 11 134 52 328 21 33 64 128 256), losses := [] }

theorem u16299 : Upper (D 6) (R 6) [10,132,48,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16300 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 1, region := 361, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 134 52 328 21 34 97 225 353), lower := (rows 11 134 52 328 21 34 64 128 256), losses := [] }

theorem u16300 : Upper (D 6) (R 6) [10,132,48,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16301 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 361, targets := 4 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 11 134 52 328 21 96 99 163 291), lower := (rows 11 134 52 328 21 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 17 104 64 128 256), good := (rows 61 132 52 360 21 96 96 128 256) }] }

theorem u16301 : Upper (D 6) (R 6) [10,132,48,320,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16302 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 458, targets := 1 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 11 134 52 328 81 33 102 166 294), lower := (rows 11 134 52 328 81 33 64 128 256), losses := [] }

theorem u16302 : Upper (D 6) (R 6) [10,132,48,320,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16303 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 134 52 328 81 34 101 165 293), lower := (rows 11 134 52 328 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 35 64 128 256), good := (rows 42 166 52 328 116 34 64 128 256) }] }

theorem u16303 : Upper (D 6) (R 6) [10,132,48,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16304 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,0),(2,1)], upper := (rows 11 134 52 328 81 36 99 163 291), lower := (rows 11 134 52 328 81 36 64 128 256), losses := [] }

theorem u16304 : Upper (D 6) (R 6) [10,132,48,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16305 : Route 9 := (fun mask => (mask,id))

def c16305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16305 : Upper (D 6) (R 6) [10,132,48,320,66,1] 13 := by
  apply FastRouting.sound _ _ [10,132,48,320,66,1] 13 (by decide) (choices 1) [1,4,32] r16305 c16305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4070
  · exact u4071
  · exact u4072

def b16306 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 52 328 82 36 97 161 289), lower := (rows 11 134 52 328 82 36 64 128 256), losses := [] }

theorem u16306 : Upper (D 6) (R 6) [10,132,48,320,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16307 : Route 9 := (fun mask => (mask,id))

def c16307 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16307 : Upper (D 6) (R 6) [10,132,48,320,68,1] 13 := by
  apply FastRouting.sound _ _ [10,132,48,320,68,1] 13 (by decide) (choices 1) [1,2,32] r16307 c16307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4073
  · exact u4074
  · exact u4075

def r16308 : Route 9 := (fun mask => (mask,id))

def c16308 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16308 : Upper (D 6) (R 6) [10,132,48,320,68,2] 13 := by
  apply FastRouting.sound _ _ [10,132,48,320,68,2] 13 (by decide) (choices 1) [1,32] r16308 c16308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4076
  · exact u4077

def b16309 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 100 25 276 33 98 226 354), lower := (rows 11 134 100 25 276 33 64 128 256), losses := [] }

theorem u16309 : Upper (D 6) (R 6) [10,132,96,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m16310_1 : Upper (D 6) (R 6) [10,132,96,17,260,2,1] 13 :=
  permutation_upper _ _ _ [10,132,96,17,260,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4078

def r16310 : Route 9 := (fun mask => (mask,id))

def c16310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16310 : Upper (D 6) (R 6) [10,132,96,17,260,2] 13 := by
  apply FastRouting.sound _ _ [10,132,96,17,260,2] 13 (by decide) (choices 1) [1,32] r16310 c16310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16310_1
  · exact u4079

def b16311 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 25 276 96 99 163 291), lower := (rows 11 134 100 25 276 96 64 128 256), losses := [] }

theorem u16311 : Upper (D 6) (R 6) [10,132,96,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16312 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 100 25 304 33 70 198 326), lower := (rows 11 134 100 25 304 33 64 128 256), losses := [] }

theorem u16312 : Upper (D 6) (R 6) [10,132,96,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16313 : Route 9 := (fun mask => (mask,id))

def c16313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16313 : Upper (D 6) (R 6) [10,132,96,17,288,2] 13 := by
  apply FastRouting.sound _ _ [10,132,96,17,288,2] 13 (by decide) (choices 1) [1,4] r16313 c16313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4080
  · exact u4081

def r16314 : Route 9 := (fun mask => (mask,id))

def c16314 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16314 : Upper (D 6) (R 6) [10,132,96,17,288,4] 13 := by
  apply FastRouting.sound _ _ [10,132,96,17,288,4] 13 (by decide) (choices 1) [1,2] r16314 c16314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4082
  · exact u4083

def b16315 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 25 304 96 71 135 263), lower := (rows 11 134 100 25 304 96 64 128 256), losses := [] }

theorem u16315 : Upper (D 6) (R 6) [10,132,96,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16316 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 198, targets := 1 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(2,0),(4,2)], upper := (rows 11 134 100 28 273 33 98 226 354), lower := (rows 11 134 100 28 273 33 64 128 256), losses := [] }

theorem u16316 : Upper (D 6) (R 6) [10,132,96,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m16317_1 : Upper (D 6) (R 6) [10,132,96,20,257,2,1] 13 :=
  permutation_upper _ _ _ [10,132,96,20,257,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4084

def r16317 : Route 9 := (fun mask => (mask,id))

def c16317 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16317 : Upper (D 6) (R 6) [10,132,96,20,257,2] 13 := by
  apply FastRouting.sound _ _ [10,132,96,20,257,2] 13 (by decide) (choices 1) [1,32] r16317 c16317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16317_1
  · exact u4085

def b16318 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 28 273 96 99 163 291), lower := (rows 11 134 100 28 273 96 64 128 256), losses := [] }

theorem u16318 : Upper (D 6) (R 6) [10,132,96,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16319 : Route 9 := (fun mask => (mask,id))

def c16319 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16319 : Upper (D 6) (R 6) [10,132,96,20,258,1] 13 := by
  apply FastRouting.sound _ _ [10,132,96,20,258,1] 13 (by decide) (choices 1) [1,32] r16319 c16319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4086
  · exact u4087

#print axioms u16319
end Delivery.IrregularNine14.P06
