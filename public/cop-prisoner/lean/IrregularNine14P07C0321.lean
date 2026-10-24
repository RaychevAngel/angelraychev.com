import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0087
import IrregularNine14P07C0088

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19260 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 88 273 34 232 168 424), lower := (rows 35 70 133 88 273 34 64 128 256), losses := [] }

theorem u19260 : Upper (D 7) (R 7) [34,68,129,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19261 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(1,0),(2,6),(4,6)], upper := (rows 35 70 133 88 273 40 226 162 418), lower := (rows 35 70 133 88 273 40 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 56 65 129 257), good := (rows 482 70 454 120 504 40 64 128 256) }] }

theorem u19261 : Upper (D 7) (R 7) [34,68,129,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19261 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19262 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 35 70 133 88 273 160 106 170 298), lower := (rows 35 70 133 88 273 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 24 273 160 0 160 256) },{ target := 7, region := (rows 1 6 4 31 21 32 65 0 257), good := (rows 379 94 351 88 345 32 64 0 256) }] }

theorem u19262 : Upper (D 7) (R 7) [34,68,129,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19263 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 88 274 33 232 168 424), lower := (rows 35 70 133 88 274 33 64 128 256), losses := [] }

theorem u19263 : Upper (D 7) (R 7) [34,68,129,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19264 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 0, region := 132, targets := 2 }], pairs := [(2,1),(2,6),(4,6)], upper := (rows 35 70 133 88 274 40 225 161 417), lower := (rows 35 70 133 88 274 40 64 128 256), losses := [] }

theorem u19264 : Upper (D 7) (R 7) [34,68,129,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19264 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19265 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 35 70 133 88 274 160 105 169 297), lower := (rows 35 70 133 88 274 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 24 275 160 0 160 256) },{ target := 7, region := (rows 1 6 4 15 21 32 65 0 257), good := (rows 379 94 351 88 282 32 64 0 256) }] }

theorem u19265 : Upper (D 7) (R 7) [34,68,129,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19266 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(4,0)], upper := (rows 35 70 133 88 280 33 226 162 418), lower := (rows 35 70 133 88 280 33 64 128 256), losses := [] }

theorem u19266 : Upper (D 7) (R 7) [34,68,129,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19267 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 88 280 34 225 161 417), lower := (rows 35 70 133 88 280 34 64 128 256), losses := [] }

theorem u19267 : Upper (D 7) (R 7) [34,68,129,80,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19268 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,7)], upper := (rows 35 70 133 88 280 160 99 163 291), lower := (rows 35 70 133 88 280 160 64 128 256), losses := [] }

theorem u19268 : Upper (D 7) (R 7) [34,68,129,80,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19269 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 88 304 33 202 138 394), lower := (rows 35 70 133 88 304 33 64 128 256), losses := [] }

theorem u19269 : Upper (D 7) (R 7) [34,68,129,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19270 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 88 304 34 201 137 393), lower := (rows 35 70 133 88 304 34 64 128 256), losses := [] }

theorem u19270 : Upper (D 7) (R 7) [34,68,129,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19271 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(1,5),(2,5),(2,6)], upper := (rows 35 70 133 88 304 40 195 131 387), lower := (rows 35 70 133 88 304 40 64 128 256), losses := [] }

theorem u19271 : Upper (D 7) (R 7) [34,68,129,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19271 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19272 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 35 70 133 88 304 160 75 139 267), lower := (rows 35 70 133 88 304 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 24 304 160 0 160 256) },{ target := 7, region := (rows 1 6 4 13 17 32 69 0 261), good := (rows 379 334 351 88 304 32 64 0 256) }] }

theorem u19272 : Upper (D 7) (R 7) [34,68,129,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19273 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 88 400 33 106 170 298), lower := (rows 35 70 133 88 400 33 64 128 256), losses := [] }

theorem u19273 : Upper (D 7) (R 7) [34,68,129,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19274 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 88 400 34 105 169 297), lower := (rows 35 70 133 88 400 34 64 128 256), losses := [] }

theorem u19274 : Upper (D 7) (R 7) [34,68,129,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19275 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(1,7),(2,6),(4,6)], upper := (rows 35 70 133 88 400 40 99 163 291), lower := (rows 35 70 133 88 400 40 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 16 40 65 0 257), good := (rows 355 70 327 120 272 40 64 0 256) }] }

theorem u19275 : Upper (D 7) (R 7) [34,68,129,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19275 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19276 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,0),(3,7),(4,0)], upper := (rows 35 70 133 104 146 33 344 408 280), lower := (rows 35 70 133 104 146 33 64 128 256), losses := [] }

theorem u19276 : Upper (D 7) (R 7) [34,68,129,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19277 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 133 104 146 40 337 401 273), lower := (rows 35 70 133 104 146 40 64 128 256), losses := [] }

theorem u19277 : Upper (D 7) (R 7) [34,68,129,96,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19277 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19278 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 133 104 146 48 329 393 265), lower := (rows 35 70 133 104 146 48 64 128 256), losses := [] }

theorem u19278 : Upper (D 7) (R 7) [34,68,129,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19278 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19279 : Route 9 := (fun mask => (mask,id))

def c19279 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19279 : Upper (D 7) (R 7) [34,68,129,96,130,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,130,256] 13 (by decide) (choices 1) [1,8,16] r19279 c19279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5275
  · exact u5276
  · exact u5277

def b19280 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,0),(3,7),(4,0)], upper := (rows 35 70 133 104 152 33 338 402 274), lower := (rows 35 70 133 104 152 33 64 128 256), losses := [] }

theorem u19280 : Upper (D 7) (R 7) [34,68,129,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19281 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 104 152 34 337 401 273), lower := (rows 35 70 133 104 152 34 64 128 256), losses := [] }

theorem u19281 : Upper (D 7) (R 7) [34,68,129,96,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19282 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(1,5),(2,5),(2,6)], upper := (rows 35 70 133 104 152 48 323 387 259), lower := (rows 35 70 133 104 152 48 64 128 256), losses := [] }

theorem u19282 : Upper (D 7) (R 7) [34,68,129,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19282 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19283 : Route 9 := (fun mask => (mask,id))

def c19283 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19283 : Upper (D 7) (R 7) [34,68,129,96,136,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,136,256] 13 (by decide) (choices 1) [1,2,16] r19283 c19283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5278
  · exact u5279
  · exact u5280

def b19284 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 104 273 34 216 152 408), lower := (rows 35 70 133 104 273 34 64 128 256), losses := [] }

theorem u19284 : Upper (D 7) (R 7) [34,68,129,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19285 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 133 104 273 40 210 146 402), lower := (rows 35 70 133 104 273 40 64 128 256), losses := [] }

theorem u19285 : Upper (D 7) (R 7) [34,68,129,96,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19285 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19286 : Route 9 := (fun mask => (mask,id))

def c19286 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19286 : Upper (D 7) (R 7) [34,68,129,96,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,257,16] 13 (by decide) (choices 1) [2,8,128] r19286 c19286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5281
  · exact u5282
  · exact u5283

def b19287 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,0),(3,1),(3,7),(4,7)], upper := (rows 35 70 133 104 273 160 90 154 282), lower := (rows 35 70 133 104 273 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 164 64 128 256), good := (rows 42 110 164 104 272 160 64 160 256) },{ target := 1, region := (rows 1 0 4 10 16 164 64 128 256), good := (rows 41 108 165 104 273 160 64 160 256) }] }

theorem u19287 : Upper (D 7) (R 7) [34,68,129,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19288 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,0),(3,7),(4,0)], upper := (rows 35 70 133 104 274 33 216 152 408), lower := (rows 35 70 133 104 274 33 64 128 256), losses := [] }

theorem u19288 : Upper (D 7) (R 7) [34,68,129,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19289 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 133 104 274 40 209 145 401), lower := (rows 35 70 133 104 274 40 64 128 256), losses := [] }

theorem u19289 : Upper (D 7) (R 7) [34,68,129,96,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19289 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19290 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 133 104 274 48 201 137 393), lower := (rows 35 70 133 104 274 48 64 128 256), losses := [] }

theorem u19290 : Upper (D 7) (R 7) [34,68,129,96,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19290 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19291 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,0),(3,1),(3,7),(4,7)], upper := (rows 35 70 133 104 274 160 89 153 281), lower := (rows 35 70 133 104 274 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 164 64 128 256), good := (rows 42 110 164 104 282 160 64 160 256) },{ target := 1, region := (rows 1 0 4 10 16 164 64 128 256), good := (rows 41 108 165 104 280 160 64 160 256) }] }

theorem u19291 : Upper (D 7) (R 7) [34,68,129,96,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19292 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,0),(3,7),(4,0)], upper := (rows 35 70 133 104 280 33 210 146 402), lower := (rows 35 70 133 104 280 33 64 128 256), losses := [] }

theorem u19292 : Upper (D 7) (R 7) [34,68,129,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19293 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 104 280 34 209 145 401), lower := (rows 35 70 133 104 280 34 64 128 256), losses := [] }

theorem u19293 : Upper (D 7) (R 7) [34,68,129,96,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19294 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(1,5),(2,5),(2,6)], upper := (rows 35 70 133 104 280 48 195 131 387), lower := (rows 35 70 133 104 280 48 64 128 256), losses := [] }

theorem u19294 : Upper (D 7) (R 7) [34,68,129,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19294 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19295 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,0),(3,1),(3,7),(4,7)], upper := (rows 35 70 133 104 280 160 83 147 275), lower := (rows 35 70 133 104 280 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 164 64 128 256), good := (rows 42 110 164 104 280 160 64 160 256) },{ target := 1, region := (rows 1 0 4 10 16 164 64 128 256), good := (rows 41 108 165 104 280 160 64 160 256) }] }

theorem u19295 : Upper (D 7) (R 7) [34,68,129,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19296 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,0),(3,7),(4,0)], upper := (rows 35 70 133 104 400 33 90 154 282), lower := (rows 35 70 133 104 400 33 64 128 256), losses := [] }

theorem u19296 : Upper (D 7) (R 7) [34,68,129,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19297 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 104 400 34 89 153 281), lower := (rows 35 70 133 104 400 34 64 128 256), losses := [] }

theorem u19297 : Upper (D 7) (R 7) [34,68,129,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19298 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 133 104 400 40 83 147 275), lower := (rows 35 70 133 104 400 40 64 128 256), losses := [] }

theorem u19298 : Upper (D 7) (R 7) [34,68,129,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19298 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19299 : Route 9 := (fun mask => (mask,id))

def c19299 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19299 : Upper (D 7) (R 7) [34,68,129,96,384,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,384,16] 13 (by decide) (choices 1) [1,2,8] r19299 c19299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5284
  · exact u5285
  · exact u5286

def b19300 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 70 133 138 273 40 112 240 368), lower := (rows 35 70 133 138 273 40 64 128 256), losses := [] }

theorem u19300 : Upper (D 7) (R 7) [34,68,129,130,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19300 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19301 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 369, targets := 128 },{ cop := 0, region := 200, targets := 1 }], pairs := [(0,7),(3,0),(4,7)], upper := (rows 35 70 133 138 273 48 104 232 360), lower := (rows 35 70 133 138 273 48 64 128 256), losses := [] }

theorem u19301 : Upper (D 7) (R 7) [34,68,129,130,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19301 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19302 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 138 273 96 120 184 312), lower := (rows 35 70 133 138 273 96 64 128 256), losses := [] }

theorem u19302 : Upper (D 7) (R 7) [34,68,129,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19303 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 138 280 33 112 240 368), lower := (rows 35 70 133 138 280 33 64 128 256), losses := [] }

theorem u19303 : Upper (D 7) (R 7) [34,68,129,130,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19304 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 369, targets := 128 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,7),(2,1),(4,7)], upper := (rows 35 70 133 138 280 48 97 225 353), lower := (rows 35 70 133 138 280 48 64 128 256), losses := [] }

theorem u19304 : Upper (D 7) (R 7) [34,68,129,130,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19304 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19305 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 138 280 96 113 177 305), lower := (rows 35 70 133 138 280 96 64 128 256), losses := [] }

theorem u19305 : Upper (D 7) (R 7) [34,68,129,130,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19305 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19306 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 138 304 33 88 216 344), lower := (rows 35 70 133 138 304 33 64 128 256), losses := [] }

theorem u19306 : Upper (D 7) (R 7) [34,68,129,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19307 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 70 133 138 304 40 81 209 337), lower := (rows 35 70 133 138 304 40 64 128 256), losses := [] }

theorem u19307 : Upper (D 7) (R 7) [34,68,129,130,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19307 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19308 : PairBound 9 := { available := 73, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 70 133 138 304 48 73 201 329), lower := (rows 35 70 133 138 304 48 64 128 256), losses := [] }

theorem u19308 : Upper (D 7) (R 7) [34,68,129,130,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19308 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19309 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 138 304 96 89 153 281), lower := (rows 35 70 133 138 304 96 64 128 256), losses := [] }

theorem u19309 : Upper (D 7) (R 7) [34,68,129,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19310 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 138 336 33 120 184 312), lower := (rows 35 70 133 138 336 33 64 128 256), losses := [] }

theorem u19310 : Upper (D 7) (R 7) [34,68,129,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19311 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 70 133 138 336 40 113 177 305), lower := (rows 35 70 133 138 336 40 64 128 256), losses := [] }

theorem u19311 : Upper (D 7) (R 7) [34,68,129,130,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19311 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19312 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 70 133 138 336 48 105 169 297), lower := (rows 35 70 133 138 336 48 64 128 256), losses := [] }

theorem u19312 : Upper (D 7) (R 7) [34,68,129,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19312 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19313 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 152 273 34 104 232 360), lower := (rows 35 70 133 152 273 34 64 128 256), losses := [] }

theorem u19313 : Upper (D 7) (R 7) [34,68,129,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19314 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(1,0),(3,0),(4,7)], upper := (rows 35 70 133 152 273 40 98 226 354), lower := (rows 35 70 133 152 273 40 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 56 65 129 257), good := (rows 482 70 454 184 504 40 64 128 256) }] }

theorem u19314 : Upper (D 7) (R 7) [34,68,129,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19314 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19315 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 152 273 96 106 170 298), lower := (rows 35 70 133 152 273 96 64 128 256), losses := [] }

theorem u19315 : Upper (D 7) (R 7) [34,68,129,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19316 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 152 274 33 104 232 360), lower := (rows 35 70 133 152 274 33 64 128 256), losses := [] }

theorem u19316 : Upper (D 7) (R 7) [34,68,129,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19317 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 196, targets := 2 },{ cop := 0, region := 336, targets := 128 }], pairs := [(1,7),(2,1),(4,7)], upper := (rows 35 70 133 152 274 40 97 225 353), lower := (rows 35 70 133 152 274 40 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 21 40 65 0 257), good := (rows 371 86 343 56 274 40 64 0 256) }] }

theorem u19317 : Upper (D 7) (R 7) [34,68,129,144,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19317 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19318 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 152 274 96 105 169 297), lower := (rows 35 70 133 152 274 96 64 128 256), losses := [] }

theorem u19318 : Upper (D 7) (R 7) [34,68,129,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19319 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 70 133 152 280 33 98 226 354), lower := (rows 35 70 133 152 280 33 64 128 256), losses := [] }

theorem u19319 : Upper (D 7) (R 7) [34,68,129,144,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u19319
end Delivery.IrregularNine14.P07
