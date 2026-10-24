import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0316
import IrregularNine14P06C0317

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r35280 : Route 9 := (fun mask => (mask,id))

def c35280 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35280 : Upper (D 6) (R 6) [24,96,130,3,36] 13 := by
  apply FastRouting.sound _ _ [24,96,130,3,36] 13 (by decide) (choices 1) [1,4,64,256] r35280 c35280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18995
  · exact u18996
  · exact u18997
  · exact u18998

def b35281 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 98 134 11 112 293 325 389 261), lower := (rows 25 98 134 11 112 32 64 128 256), losses := [] }

theorem u35281 : Upper (D 6) (R 6) [24,96,130,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35282 : Route 9 := (fun mask => (mask,id))

def c35282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35282 : Upper (D 6) (R 6) [24,96,130,3,257] 13 := by
  apply FastRouting.sound _ _ [24,96,130,3,257] 13 (by decide) (choices 1) [4,64] r35282 c35282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18999
  · exact u19000

def r35283 : Route 9 := (fun mask => (mask,id))

def c35283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35283 : Upper (D 6) (R 6) [24,96,130,3,260] 13 := by
  apply FastRouting.sound _ _ [24,96,130,3,260] 13 (by decide) (choices 1) [1,4,64] r35283 c35283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19001
  · exact u19002
  · exact u19003

def r35284 : Route 9 := (fun mask => (mask,id))

def c35284 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35284 : Upper (D 6) (R 6) [24,96,130,3,288] 13 := by
  apply FastRouting.sound _ _ [24,96,130,3,288] 13 (by decide) (choices 1) [1,4,64] r35284 c35284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19004
  · exact u19005
  · exact u19006

def b35285 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 25, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 98 134 13 21 354 354 482 354), lower := (rows 25 98 134 13 21 32 64 128 256), losses := [] }

theorem u35285 : Upper (D 6) (R 6) [24,96,130,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35286 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 98 134 13 22 353 353 481 353), lower := (rows 25 98 134 13 22 32 64 128 256), losses := [] }

theorem u35286 : Upper (D 6) (R 6) [24,96,130,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35287 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 1, region := 388, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 25 98 134 13 49 358 326 454 326), lower := (rows 25 98 134 13 49 32 64 128 256), losses := [] }

theorem u35287 : Upper (D 6) (R 6) [24,96,130,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35288 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 25 98 134 13 50 357 325 453 325), lower := (rows 25 98 134 13 50 32 64 128 256), losses := [] }

theorem u35288 : Upper (D 6) (R 6) [24,96,130,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35289 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 98 134 13 52 355 323 451 323), lower := (rows 25 98 134 13 52 32 64 128 256), losses := [] }

theorem u35289 : Upper (D 6) (R 6) [24,96,130,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35290 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 25 98 134 13 112 295 327 391 263), lower := (rows 25 98 134 13 112 32 64 128 256), losses := [] }

theorem u35290 : Upper (D 6) (R 6) [24,96,130,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35291 : Route 9 := (fun mask => (mask,id))

def c35291 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35291 : Upper (D 6) (R 6) [24,96,130,5,257] 13 := by
  apply FastRouting.sound _ _ [24,96,130,5,257] 13 (by decide) (choices 1) [2,4,64] r35291 c35291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19007
  · exact u19008
  · exact u19009

def r35292 : Route 9 := (fun mask => (mask,id))

def c35292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35292 : Upper (D 6) (R 6) [24,96,130,5,258] 13 := by
  apply FastRouting.sound _ _ [24,96,130,5,258] 13 (by decide) (choices 1) [1,4,64] r35292 c35292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19010
  · exact u19011
  · exact u19012

def b35293 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 98 134 13 276 99 99 227 355), lower := (rows 25 98 134 13 276 32 64 128 256), losses := [] }

theorem u35293 : Upper (D 6) (R 6) [24,96,130,5,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35294 : Route 9 := (fun mask => (mask,id))

def c35294 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35294 : Upper (D 6) (R 6) [24,96,130,5,288] 13 := by
  apply FastRouting.sound _ _ [24,96,130,5,288] 13 (by decide) (choices 1) [1,2,4,64] r35294 c35294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19013
  · exact u19014
  · exact u19015
  · exact u19016

def b35295 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 98 134 14 49 357 325 453 325), lower := (rows 25 98 134 14 49 32 64 128 256), losses := [] }

theorem u35295 : Upper (D 6) (R 6) [24,96,130,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35296 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 98 134 14 52 353 321 449 321), lower := (rows 25 98 134 14 52 32 64 128 256), losses := [] }

theorem u35296 : Upper (D 6) (R 6) [24,96,130,6,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35297 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 98 134 14 273 101 101 229 357), lower := (rows 25 98 134 14 273 32 64 128 256), losses := [] }

theorem u35297 : Upper (D 6) (R 6) [24,96,130,6,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35298 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 98 134 14 276 97 97 225 353), lower := (rows 25 98 134 14 276 32 64 128 256), losses := [] }

theorem u35298 : Upper (D 6) (R 6) [24,96,130,6,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35299 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 98 134 14 304 101 69 197 325), lower := (rows 25 98 134 14 304 32 64 128 256), losses := [] }

theorem u35299 : Upper (D 6) (R 6) [24,96,130,6,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35300 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 25, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 98 134 41 81 294 326 390 262), lower := (rows 25 98 134 41 81 32 64 128 256), losses := [] }

theorem u35300 : Upper (D 6) (R 6) [24,96,130,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35301 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 98 134 41 82 293 325 389 261), lower := (rows 25 98 134 41 82 32 64 128 256), losses := [] }

theorem u35301 : Upper (D 6) (R 6) [24,96,130,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35302 : Route 9 := (fun mask => (mask,id))

def c35302 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35302 : Upper (D 6) (R 6) [24,96,130,33,68] 13 := by
  apply FastRouting.sound _ _ [24,96,130,33,68] 13 (by decide) (choices 1) [1,2,4,256] r35302 c35302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19017
  · exact u19018
  · exact u19019
  · exact u19020

def b35303 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 230, targets := 1 },{ cop := 1, region := 132, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 25 98 134 41 273 102 70 198 326), lower := (rows 25 98 134 41 273 32 64 128 256), losses := [] }

theorem u35303 : Upper (D 6) (R 6) [24,96,130,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35304 : Route 9 := (fun mask => (mask,id))

def c35304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35304 : Upper (D 6) (R 6) [24,96,130,33,258] 13 := by
  apply FastRouting.sound _ _ [24,96,130,33,258] 13 (by decide) (choices 1) [1,4,64] r35304 c35304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19021
  · exact u19022
  · exact u19023

def r35305 : Route 9 := (fun mask => (mask,id))

def c35305 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35305 : Upper (D 6) (R 6) [24,96,130,33,260] 13 := by
  apply FastRouting.sound _ _ [24,96,130,33,260] 13 (by decide) (choices 1) [1,2,4,64] r35305 c35305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19024
  · exact u19025
  · exact u19026
  · exact u19027

def r35306 : Route 9 := (fun mask => (mask,id))

def c35306 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35306 : Upper (D 6) (R 6) [24,96,130,33,320] 13 := by
  apply FastRouting.sound _ _ [24,96,130,33,320] 13 (by decide) (choices 1) [1,2,4] r35306 c35306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19028
  · exact u19029
  · exact u19030

def b35307 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 98 134 42 84 293 325 389 261), lower := (rows 25 98 134 42 84 32 64 128 256), losses := [] }

theorem u35307 : Upper (D 6) (R 6) [24,96,130,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35308 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 98 134 42 273 101 69 197 325), lower := (rows 25 98 134 42 273 32 64 128 256), losses := [] }

theorem u35308 : Upper (D 6) (R 6) [24,96,130,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35309 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 98 134 42 276 101 69 197 325), lower := (rows 25 98 134 42 276 32 64 128 256), losses := [] }

theorem u35309 : Upper (D 6) (R 6) [24,96,130,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35310 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 98 134 42 336 37 69 133 261), lower := (rows 25 98 134 42 336 32 64 128 256), losses := [] }

theorem u35310 : Upper (D 6) (R 6) [24,96,130,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35311 : Route 9 := (fun mask => (mask,id))

def c35311 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35311 : Upper (D 6) (R 6) [24,96,130,36,68] 13 := by
  apply FastRouting.sound _ _ [24,96,130,36,68] 13 (by decide) (choices 1) [1,2,256] r35311 c35311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19031
  · exact u19032
  · exact u19033

def r35312 : Route 9 := (fun mask => (mask,id))

def c35312 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35312 : Upper (D 6) (R 6) [24,96,130,36,257] 13 := by
  apply FastRouting.sound _ _ [24,96,130,36,257] 13 (by decide) (choices 1) [1,2,4,64] r35312 c35312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19034
  · exact u19035
  · exact u19036
  · exact u19037

def r35313 : Route 9 := (fun mask => (mask,id))

def c35313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35313 : Upper (D 6) (R 6) [24,96,130,36,258] 13 := by
  apply FastRouting.sound _ _ [24,96,130,36,258] 13 (by decide) (choices 1) [1,4,64] r35313 c35313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19038
  · exact u19039
  · exact u19040

def r35314 : Route 9 := (fun mask => (mask,id))

def c35314 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35314 : Upper (D 6) (R 6) [24,96,130,36,260] 13 := by
  apply FastRouting.sound _ _ [24,96,130,36,260] 13 (by decide) (choices 1) [1,2,64] r35314 c35314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19041
  · exact u19042
  · exact u19043

def r35315 : Route 9 := (fun mask => (mask,id))

def c35315 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35315 : Upper (D 6) (R 6) [24,96,130,36,320] 13 := by
  apply FastRouting.sound _ _ [24,96,130,36,320] 13 (by decide) (choices 1) [1,2,4] r35315 c35315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19044
  · exact u19045
  · exact u19046

def b35316 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 8, targets := 5 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,2)], upper := (rows 25 98 134 104 273 39 71 135 263), lower := (rows 25 98 134 104 273 32 64 128 256), losses := [] }

theorem u35316 : Upper (D 6) (R 6) [24,96,130,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35317 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 8, targets := 5 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,2)], upper := (rows 25 98 134 104 274 37 69 133 261), lower := (rows 25 98 134 104 274 32 64 128 256), losses := [] }

theorem u35317 : Upper (D 6) (R 6) [24,96,130,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35318 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 8, targets := 5 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,2)], upper := (rows 25 98 134 104 276 39 71 135 263), lower := (rows 25 98 134 104 276 32 64 128 256), losses := [] }

theorem u35318 : Upper (D 6) (R 6) [24,96,130,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35319 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 98 164 11 19 356 324 452 324), lower := (rows 25 98 164 11 19 32 64 128 256), losses := [] }

theorem u35319 : Upper (D 6) (R 6) [24,96,160,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35320 : Route 9 := (fun mask => (mask,id))

def c35320 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35320 : Upper (D 6) (R 6) [24,96,160,3,5] 13 := by
  apply FastRouting.sound _ _ [24,96,160,3,5] 13 (by decide) (choices 1) [2,4,64,256] r35320 c35320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19047
  · exact u19048
  · exact u19049
  · exact u19050

def b35321 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 98 164 11 22 357 325 453 325), lower := (rows 25 98 164 11 22 32 64 128 256), losses := [] }

theorem u35321 : Upper (D 6) (R 6) [24,96,160,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35322 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 25, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 25 98 164 11 81 294 326 390 262), lower := (rows 25 98 164 11 81 32 64 128 256), losses := [] }

theorem u35322 : Upper (D 6) (R 6) [24,96,160,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35323 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 25, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 25 98 164 11 82 293 325 389 261), lower := (rows 25 98 164 11 82 32 64 128 256), losses := [] }

theorem u35323 : Upper (D 6) (R 6) [24,96,160,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35324 : Route 9 := (fun mask => (mask,id))

def c35324 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35324 : Upper (D 6) (R 6) [24,96,160,3,68] 13 := by
  apply FastRouting.sound _ _ [24,96,160,3,68] 13 (by decide) (choices 1) [1,2,4,256] r35324 c35324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19051
  · exact u19052
  · exact u19053
  · exact u19054

def r35325 : Route 9 := (fun mask => (mask,id))

def c35325 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35325 : Upper (D 6) (R 6) [24,96,160,3,257] 13 := by
  apply FastRouting.sound _ _ [24,96,160,3,257] 13 (by decide) (choices 1) [2,4,64] r35325 c35325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19055
  · exact u19056
  · exact u19057

def b35326 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 98 164 11 274 101 69 197 325), lower := (rows 25 98 164 11 274 32 64 128 256), losses := [] }

theorem u35326 : Upper (D 6) (R 6) [24,96,160,3,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35327 : Route 9 := (fun mask => (mask,id))

def c35327 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35327 : Upper (D 6) (R 6) [24,96,160,3,260] 13 := by
  apply FastRouting.sound _ _ [24,96,160,3,260] 13 (by decide) (choices 1) [1,2,4,64] r35327 c35327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19058
  · exact u19059
  · exact u19060
  · exact u19061

def r35328 : Route 9 := (fun mask => (mask,id))

def c35328 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35328 : Upper (D 6) (R 6) [24,96,160,3,320] 13 := by
  apply FastRouting.sound _ _ [24,96,160,3,320] 13 (by decide) (choices 1) [1,2,4] r35328 c35328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19062
  · exact u19063
  · exact u19064

def b35329 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 25, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 98 164 13 21 354 322 450 322), lower := (rows 25 98 164 13 21 32 64 128 256), losses := [] }

theorem u35329 : Upper (D 6) (R 6) [24,96,160,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35330 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 9, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 98 164 13 22 355 323 451 323), lower := (rows 25 98 164 13 22 32 64 128 256), losses := [] }

theorem u35330 : Upper (D 6) (R 6) [24,96,160,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35331 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 1, region := 388, targets := 64 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 25 98 164 13 81 294 326 390 262), lower := (rows 25 98 164 13 81 32 64 128 256), losses := [] }

theorem u35331 : Upper (D 6) (R 6) [24,96,160,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35332 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 25 98 164 13 82 295 327 391 263), lower := (rows 25 98 164 13 82 32 64 128 256), losses := [] }

theorem u35332 : Upper (D 6) (R 6) [24,96,160,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35333 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 98 164 13 84 291 323 387 259), lower := (rows 25 98 164 13 84 32 64 128 256), losses := [] }

theorem u35333 : Upper (D 6) (R 6) [24,96,160,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35334 : Route 9 := (fun mask => (mask,id))

def c35334 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35334 : Upper (D 6) (R 6) [24,96,160,5,257] 13 := by
  apply FastRouting.sound _ _ [24,96,160,5,257] 13 (by decide) (choices 1) [2,4,64] r35334 c35334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19065
  · exact u19066
  · exact u19067

def r35335 : Route 9 := (fun mask => (mask,id))

def c35335 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35335 : Upper (D 6) (R 6) [24,96,160,5,258] 13 := by
  apply FastRouting.sound _ _ [24,96,160,5,258] 13 (by decide) (choices 1) [1,2,4,64] r35335 c35335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19068
  · exact u19069
  · exact u19070
  · exact u19071

def b35336 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 98 164 13 276 99 67 195 323), lower := (rows 25 98 164 13 276 32 64 128 256), losses := [] }

theorem u35336 : Upper (D 6) (R 6) [24,96,160,5,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35337 : Route 9 := (fun mask => (mask,id))

def c35337 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35337 : Upper (D 6) (R 6) [24,96,160,5,320] 13 := by
  apply FastRouting.sound _ _ [24,96,160,5,320] 13 (by decide) (choices 1) [1,2,4] r35337 c35337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19072
  · exact u19073
  · exact u19074

def b35338 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 17, targets := 32 },{ cop := 3, region := 17, targets := 64 }], pairs := [(0,5),(0,6),(4,5)], upper := (rows 25 98 164 14 22 353 321 449 321), lower := (rows 25 98 164 14 22 32 64 128 256), losses := [] }

theorem u35338 : Upper (D 6) (R 6) [24,96,160,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35339 : Route 9 := (fun mask => (mask,id))

def c35339 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35339 : Upper (D 6) (R 6) [24,96,160,6,65] 13 := by
  apply FastRouting.sound _ _ [24,96,160,6,65] 13 (by decide) (choices 1) [1,2,4,256] r35339 c35339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19075
  · exact u19076
  · exact u19077
  · exact u19078

#print axioms u35339
end Delivery.IrregularNine14.P06
