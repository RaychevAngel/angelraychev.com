import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0132

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24240 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 140 11 208 33 338 402 274), lower := (rows 37 98 140 11 208 33 64 128 256), losses := [] }

theorem u24240 : Upper (D 7) (R 7) [36,96,136,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24241 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 140 11 208 34 337 401 273), lower := (rows 37 98 140 11 208 34 64 128 256), losses := [] }

theorem u24241 : Upper (D 7) (R 7) [36,96,136,3,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24242 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 140 11 208 48 323 387 259), lower := (rows 37 98 140 11 208 48 64 128 256), losses := [] }

theorem u24242 : Upper (D 7) (R 7) [36,96,136,3,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24242 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24243 : Route 9 := (fun mask => (mask,id))

def c24243 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24243 : Upper (D 7) (R 7) [36,96,136,3,192,256] 13 := by
  apply FastRouting.sound _ _ [36,96,136,3,192,256] 13 (by decide) (choices 1) [1,2,16] r24243 c24243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7960
  · exact u7961
  · exact u7962

def b24244 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 140 11 273 34 208 208 464), lower := (rows 37 98 140 11 273 34 64 128 256), losses := [] }

theorem u24244 : Upper (D 7) (R 7) [36,96,136,3,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24245 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 0, region := 194, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 37 98 140 11 273 48 194 194 450), lower := (rows 37 98 140 11 273 48 64 128 256), losses := [] }

theorem u24245 : Upper (D 7) (R 7) [36,96,136,3,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24245 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24246 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 11 273 96 210 146 402), lower := (rows 37 98 140 11 273 96 64 128 256), losses := [] }

theorem u24246 : Upper (D 7) (R 7) [36,96,136,3,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24247 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 11 273 160 82 210 338), lower := (rows 37 98 140 11 273 160 64 128 256), losses := [] }

theorem u24247 : Upper (D 7) (R 7) [36,96,136,3,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24248 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 140 11 274 33 208 208 464), lower := (rows 37 98 140 11 274 33 64 128 256), losses := [] }

theorem u24248 : Upper (D 7) (R 7) [36,96,136,3,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24249 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 196, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 37 98 140 11 274 48 193 193 449), lower := (rows 37 98 140 11 274 48 64 128 256), losses := [] }

theorem u24249 : Upper (D 7) (R 7) [36,96,136,3,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24249 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24250 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 11 274 96 209 145 401), lower := (rows 37 98 140 11 274 96 64 128 256), losses := [] }

theorem u24250 : Upper (D 7) (R 7) [36,96,136,3,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24251 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 11 274 160 81 209 337), lower := (rows 37 98 140 11 274 160 64 128 256), losses := [] }

theorem u24251 : Upper (D 7) (R 7) [36,96,136,3,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24252 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 140 11 336 33 210 146 402), lower := (rows 37 98 140 11 336 33 64 128 256), losses := [] }

theorem u24252 : Upper (D 7) (R 7) [36,96,136,3,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24253 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 140 11 336 34 209 145 401), lower := (rows 37 98 140 11 336 34 64 128 256), losses := [] }

theorem u24253 : Upper (D 7) (R 7) [36,96,136,3,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24254 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 140 11 336 48 195 131 387), lower := (rows 37 98 140 11 336 48 64 128 256), losses := [] }

theorem u24254 : Upper (D 7) (R 7) [36,96,136,3,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24254 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24255 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 11 336 160 83 147 275), lower := (rows 37 98 140 11 336 160 64 128 256), losses := [] }

theorem u24255 : Upper (D 7) (R 7) [36,96,136,3,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24256 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 140 11 400 33 82 210 338), lower := (rows 37 98 140 11 400 33 64 128 256), losses := [] }

theorem u24256 : Upper (D 7) (R 7) [36,96,136,3,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24257 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 140 11 400 34 81 209 337), lower := (rows 37 98 140 11 400 34 64 128 256), losses := [] }

theorem u24257 : Upper (D 7) (R 7) [36,96,136,3,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24258 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 196, targets := 32 }], pairs := [(1,7),(2,5),(3,7)], upper := (rows 37 98 140 11 400 48 67 195 323), lower := (rows 37 98 140 11 400 48 64 128 256), losses := [] }

theorem u24258 : Upper (D 7) (R 7) [36,96,136,3,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24258 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24259 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 11 400 96 83 147 275), lower := (rows 37 98 140 11 400 96 64 128 256), losses := [] }

theorem u24259 : Upper (D 7) (R 7) [36,96,136,3,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24260 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 140 25 146 33 322 450 322), lower := (rows 37 98 140 25 146 33 64 128 256), losses := [] }

theorem u24260 : Upper (D 7) (R 7) [36,96,136,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24261 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,6)], upper := (rows 37 98 140 25 146 34 321 449 321), lower := (rows 37 98 140 25 146 34 64 128 256), losses := [] }

theorem u24261 : Upper (D 7) (R 7) [36,96,136,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24262 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 25 146 96 323 387 259), lower := (rows 37 98 140 25 146 96 64 128 256), losses := [] }

theorem u24262 : Upper (D 7) (R 7) [36,96,136,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24263 : Route 9 := (fun mask => (mask,id))

def c24263 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24263 : Upper (D 7) (R 7) [36,96,136,17,130,256] 13 := by
  apply FastRouting.sound _ _ [36,96,136,17,130,256] 13 (by decide) (choices 1) [1,2] r24263 c24263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7963
  · exact u7964

def b24264 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 140 25 208 33 322 386 258), lower := (rows 37 98 140 25 208 33 64 128 256), losses := [] }

theorem u24264 : Upper (D 7) (R 7) [36,96,136,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24265 : Route 9 := (fun mask => (mask,id))

def c24265 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u24265 : Upper (D 7) (R 7) [36,96,136,17,192,2] 13 := by
  apply FastRouting.sound _ _ [36,96,136,17,192,2] 13 (by decide) (choices 1) [1,2,256] r24265 c24265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7965
  · exact u7966
  · exact u7967

def r24266 : Route 9 := (fun mask => (mask,id))

def c24266 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24266 : Upper (D 7) (R 7) [36,96,136,17,192,256] 13 := by
  apply FastRouting.sound _ _ [36,96,136,17,192,256] 13 (by decide) (choices 1) [1,2] r24266 c24266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7968
  · exact u7969

def b24267 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 140 25 274 33 194 194 450), lower := (rows 37 98 140 25 274 33 64 128 256), losses := [] }

theorem u24267 : Upper (D 7) (R 7) [36,96,136,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24268 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,1),(2,5)], upper := (rows 37 98 140 25 274 34 193 193 449), lower := (rows 37 98 140 25 274 34 64 128 256), losses := [] }

theorem u24268 : Upper (D 7) (R 7) [36,96,136,17,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24269 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 25 274 96 195 131 387), lower := (rows 37 98 140 25 274 96 64 128 256), losses := [] }

theorem u24269 : Upper (D 7) (R 7) [36,96,136,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24270 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 25 274 160 67 195 323), lower := (rows 37 98 140 25 274 160 64 128 256), losses := [] }

theorem u24270 : Upper (D 7) (R 7) [36,96,136,17,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24271 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 140 25 336 33 194 130 386), lower := (rows 37 98 140 25 336 33 64 128 256), losses := [] }

theorem u24271 : Upper (D 7) (R 7) [36,96,136,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24272 : Route 9 := (fun mask => (mask,id))

def c24272 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24272 : Upper (D 7) (R 7) [36,96,136,17,320,2] 13 := by
  apply FastRouting.sound _ _ [36,96,136,17,320,2] 13 (by decide) (choices 1) [1,2,128] r24272 c24272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7970
  · exact u7971
  · exact u7972

def b24273 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 25 336 160 67 131 259), lower := (rows 37 98 140 25 336 160 64 128 256), losses := [] }

theorem u24273 : Upper (D 7) (R 7) [36,96,136,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24274 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 140 25 400 33 66 194 322), lower := (rows 37 98 140 25 400 33 64 128 256), losses := [] }

theorem u24274 : Upper (D 7) (R 7) [36,96,136,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24275 : Route 9 := (fun mask => (mask,id))

def c24275 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24275 : Upper (D 7) (R 7) [36,96,136,17,384,2] 13 := by
  apply FastRouting.sound _ _ [36,96,136,17,384,2] 13 (by decide) (choices 1) [1,2] r24275 c24275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7973
  · exact u7974

def b24276 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 25 400 96 67 131 259), lower := (rows 37 98 140 25 400 96 64 128 256), losses := [] }

theorem u24276 : Upper (D 7) (R 7) [36,96,136,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24277 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 388, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 98 140 26 81 33 450 386 386), lower := (rows 37 98 140 26 81 33 64 128 256), losses := [] }

theorem u24277 : Upper (D 7) (R 7) [36,96,136,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24278 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 98 140 26 81 34 449 385 385), lower := (rows 37 98 140 26 81 34 64 128 256), losses := [] }

theorem u24278 : Upper (D 7) (R 7) [36,96,136,18,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24279 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 26 81 160 323 387 259), lower := (rows 37 98 140 26 81 160 64 128 256), losses := [] }

theorem u24279 : Upper (D 7) (R 7) [36,96,136,18,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24280 : Route 9 := (fun mask => (mask,id))

def c24280 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24280 : Upper (D 7) (R 7) [36,96,136,18,65,256] 13 := by
  apply FastRouting.sound _ _ [36,96,136,18,65,256] 13 (by decide) (choices 1) [1,2,128] r24280 c24280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7975
  · exact u7976
  · exact u7977

def b24281 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 98 140 26 145 33 322 450 322), lower := (rows 37 98 140 26 145 33 64 128 256), losses := [] }

theorem u24281 : Upper (D 7) (R 7) [36,96,136,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24282 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,5)], upper := (rows 37 98 140 26 145 34 321 449 321), lower := (rows 37 98 140 26 145 34 64 128 256), losses := [] }

theorem u24282 : Upper (D 7) (R 7) [36,96,136,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24283 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 26 145 96 323 387 259), lower := (rows 37 98 140 26 145 96 64 128 256), losses := [] }

theorem u24283 : Upper (D 7) (R 7) [36,96,136,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24284 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 362, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 98 140 26 145 288 67 195 323), lower := (rows 37 98 140 26 145 288 64 128 256), losses := [] }

theorem u24284 : Upper (D 7) (R 7) [36,96,136,18,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24284 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24285 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 196, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 98 140 26 273 33 194 194 450), lower := (rows 37 98 140 26 273 33 64 128 256), losses := [] }

theorem u24285 : Upper (D 7) (R 7) [36,96,136,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24286 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 37 98 140 26 273 34 193 193 449), lower := (rows 37 98 140 26 273 34 64 128 256), losses := [] }

theorem u24286 : Upper (D 7) (R 7) [36,96,136,18,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24286 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24287 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 26 273 96 195 131 387), lower := (rows 37 98 140 26 273 96 64 128 256), losses := [] }

theorem u24287 : Upper (D 7) (R 7) [36,96,136,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24288 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 26 273 160 67 195 323), lower := (rows 37 98 140 26 273 160 64 128 256), losses := [] }

theorem u24288 : Upper (D 7) (R 7) [36,96,136,18,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24289 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(2,6)], upper := (rows 37 98 140 26 336 33 195 131 387), lower := (rows 37 98 140 26 336 33 64 128 256), losses := [] }

theorem u24289 : Upper (D 7) (R 7) [36,96,136,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24290 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 98 140 26 336 34 193 129 385), lower := (rows 37 98 140 26 336 34 64 128 256), losses := [] }

theorem u24290 : Upper (D 7) (R 7) [36,96,136,18,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24291 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 26 336 160 67 131 259), lower := (rows 37 98 140 26 336 160 64 128 256), losses := [] }

theorem u24291 : Upper (D 7) (R 7) [36,96,136,18,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24292 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 140 26 400 33 67 195 323), lower := (rows 37 98 140 26 400 33 64 128 256), losses := [] }

theorem u24292 : Upper (D 7) (R 7) [36,96,136,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24293 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,5)], upper := (rows 37 98 140 26 400 34 65 193 321), lower := (rows 37 98 140 26 400 34 64 128 256), losses := [] }

theorem u24293 : Upper (D 7) (R 7) [36,96,136,18,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24294 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 26 400 96 67 131 259), lower := (rows 37 98 140 26 400 96 64 128 256), losses := [] }

theorem u24294 : Upper (D 7) (R 7) [36,96,136,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24295 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 98 140 73 19 34 464 400 400), lower := (rows 37 98 140 73 19 34 64 128 256), losses := [] }

theorem u24295 : Upper (D 7) (R 7) [36,96,136,65,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24296 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 50, targets := 128 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,7),(2,5),(4,7)], upper := (rows 37 98 140 73 19 48 450 386 386), lower := (rows 37 98 140 73 19 48 64 128 256), losses := [] }

theorem u24296 : Upper (D 7) (R 7) [36,96,136,65,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24296 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24297 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 73 19 160 338 402 274), lower := (rows 37 98 140 73 19 160 64 128 256), losses := [] }

theorem u24297 : Upper (D 7) (R 7) [36,96,136,65,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24298 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 204, targets := 32 },{ cop := 4, region := 482, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 37 98 140 73 19 288 210 146 402), lower := (rows 37 98 140 73 19 288 64 128 256), losses := [] }

theorem u24298 : Upper (D 7) (R 7) [36,96,136,65,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24298 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24299 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 34, targets := 129 },{ cop := 4, region := 362, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 37 98 140 73 145 34 338 402 274), lower := (rows 37 98 140 73 145 34 64 128 256), losses := [{ target := 7, region := (rows 5 90 4 24 16 126 80 0 272), good := (rows 37 98 47 107 379 34 98 0 256) }] }

theorem u24299 : Upper (D 7) (R 7) [36,96,136,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u24299
end Delivery.IrregularNine14.P07
