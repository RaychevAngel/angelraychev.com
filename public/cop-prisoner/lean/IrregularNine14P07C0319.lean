import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0087

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19140 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 25 146 96 360 424 296), lower := (rows 35 70 133 25 146 96 64 128 256), losses := [] }

theorem u19140 : Upper (D 7) (R 7) [34,68,129,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19141 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 361, targets := 128 },{ cop := 3, region := 484, targets := 2 }], pairs := [(0,7),(2,1),(3,7)], upper := (rows 35 70 133 25 146 288 104 232 360), lower := (rows 35 70 133 25 146 288 64 128 256), losses := [] }

theorem u19141 : Upper (D 7) (R 7) [34,68,129,17,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19141 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19142 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 25 176 34 328 456 328), lower := (rows 35 70 133 25 176 34 64 128 256), losses := [] }

theorem u19142 : Upper (D 7) (R 7) [34,68,129,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19143 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 56, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 35 70 133 25 176 40 322 450 322), lower := (rows 35 70 133 25 176 40 64 128 256), losses := [] }

theorem u19143 : Upper (D 7) (R 7) [34,68,129,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19143 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19144 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 25 176 96 330 394 266), lower := (rows 35 70 133 25 176 96 64 128 256), losses := [] }

theorem u19144 : Upper (D 7) (R 7) [34,68,129,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19145 : Route 9 := (fun mask => (mask,id))

def c19145 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19145 : Upper (D 7) (R 7) [34,68,129,17,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,160,256] 13 (by decide) (choices 1) [2,8] r19145 c19145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5236
  · exact u5237

def b19146 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 25 208 34 360 424 296), lower := (rows 35 70 133 25 208 34 64 128 256), losses := [] }

theorem u19146 : Upper (D 7) (R 7) [34,68,129,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19147 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 464, targets := 1 },{ cop := 0, region := 388, targets := 64 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 35 70 133 25 208 40 354 418 290), lower := (rows 35 70 133 25 208 40 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 29 40 65 129 257), good := (rows 498 86 470 504 208 56 64 128 256) }] }

theorem u19147 : Upper (D 7) (R 7) [34,68,129,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19147 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19148 : Route 9 := (fun mask => (mask,id))

def c19148 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19148 : Upper (D 7) (R 7) [34,68,129,17,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,192,256] 13 (by decide) (choices 1) [2,8,32] r19148 c19148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5238
  · exact u5239
  · exact u5240

def b19149 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 70 133 25 274 40 224 224 480), lower := (rows 35 70 133 25 274 40 64 128 256), losses := [] }

theorem u19149 : Upper (D 7) (R 7) [34,68,129,17,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19149 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19150 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 25 274 96 232 168 424), lower := (rows 35 70 133 25 274 96 64 128 256), losses := [] }

theorem u19150 : Upper (D 7) (R 7) [34,68,129,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19151 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 228, targets := 2 }], pairs := [(0,6),(2,1),(3,7),(4,7)], upper := (rows 35 70 133 25 274 160 104 232 360), lower := (rows 35 70 133 25 274 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 24 16 164 0 128 256), good := (rows 35 39 165 25 283 160 0 160 256) }] }

theorem u19151 : Upper (D 7) (R 7) [34,68,129,17,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19152 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 25 280 34 224 224 480), lower := (rows 35 70 133 25 280 34 64 128 256), losses := [] }

theorem u19152 : Upper (D 7) (R 7) [34,68,129,17,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19153 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 25 280 96 226 162 418), lower := (rows 35 70 133 25 280 96 64 128 256), losses := [] }

theorem u19153 : Upper (D 7) (R 7) [34,68,129,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19154 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(3,7),(4,0),(4,7)], upper := (rows 35 70 133 25 280 160 98 226 354), lower := (rows 35 70 133 25 280 160 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 24 175 71 135 263), good := (rows 482 486 486 504 312 160 64 160 256) }] }

theorem u19154 : Upper (D 7) (R 7) [34,68,129,17,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19155 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 25 304 34 200 200 456), lower := (rows 35 70 133 25 304 34 64 128 256), losses := [] }

theorem u19155 : Upper (D 7) (R 7) [34,68,129,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19156 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 0, region := 464, targets := 1 }], pairs := [(1,5),(2,5),(4,0)], upper := (rows 35 70 133 25 304 40 194 194 450), lower := (rows 35 70 133 25 304 40 64 128 256), losses := [] }

theorem u19156 : Upper (D 7) (R 7) [34,68,129,17,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19156 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19157 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 25 304 96 202 138 394), lower := (rows 35 70 133 25 304 96 64 128 256), losses := [] }

theorem u19157 : Upper (D 7) (R 7) [34,68,129,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19158 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5),(3,7),(4,7)], upper := (rows 35 70 133 25 304 160 74 202 330), lower := (rows 35 70 133 25 304 160 64 128 256), losses := [] }

theorem u19158 : Upper (D 7) (R 7) [34,68,129,17,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19159 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 25 336 34 232 168 424), lower := (rows 35 70 133 25 336 34 64 128 256), losses := [] }

theorem u19159 : Upper (D 7) (R 7) [34,68,129,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19160 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 464, targets := 1 },{ cop := 0, region := 132, targets := 64 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 35 70 133 25 336 40 226 162 418), lower := (rows 35 70 133 25 336 40 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 29 40 65 129 257), good := (rows 498 86 470 504 336 56 64 128 256) }] }

theorem u19160 : Upper (D 7) (R 7) [34,68,129,17,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19160 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19161 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 35 70 133 25 336 160 106 170 298), lower := (rows 35 70 133 25 336 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 25 272 160 0 160 256) },{ target := 7, region := (rows 1 6 4 13 29 32 65 0 257), good := (rows 379 94 351 345 336 32 64 0 256) }] }

theorem u19161 : Upper (D 7) (R 7) [34,68,129,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19162 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 25 400 34 104 232 360), lower := (rows 35 70 133 25 400 34 64 128 256), losses := [] }

theorem u19162 : Upper (D 7) (R 7) [34,68,129,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19163 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 464, targets := 1 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 35 70 133 25 400 40 98 226 354), lower := (rows 35 70 133 25 400 40 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 29 40 65 129 257), good := (rows 498 86 470 504 400 56 64 128 256) },{ target := 7, region := (rows 1 6 4 8 16 40 65 0 257), good := (rows 355 70 327 377 272 40 64 0 256) }] }

theorem u19163 : Upper (D 7) (R 7) [34,68,129,17,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19163 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19164 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 25 400 96 106 170 298), lower := (rows 35 70 133 25 400 96 64 128 256), losses := [] }

theorem u19164 : Upper (D 7) (R 7) [34,68,129,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19165 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 57, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 70 133 26 81 40 480 416 416), lower := (rows 35 70 133 26 81 40 64 128 256), losses := [] }

theorem u19165 : Upper (D 7) (R 7) [34,68,129,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19165 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19166 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,7)], upper := (rows 35 70 133 26 81 160 360 424 296), lower := (rows 35 70 133 26 81 160 64 128 256), losses := [] }

theorem u19166 : Upper (D 7) (R 7) [34,68,129,18,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19167 : Route 9 := (fun mask => (mask,id))

def c19167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u19167 : Upper (D 7) (R 7) [34,68,129,18,65,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,65,256] 13 (by decide) (choices 1) [8,32,128] r19167 c19167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5241
  · exact u5242
  · exact u5243

def b19168 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 57, targets := 128 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(3,0),(3,7),(4,7)], upper := (rows 35 70 133 26 112 33 456 392 392), lower := (rows 35 70 133 26 112 33 64 128 256), losses := [] }

theorem u19168 : Upper (D 7) (R 7) [34,68,129,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19169 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 57, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 70 133 26 112 40 449 385 385), lower := (rows 35 70 133 26 112 40 64 128 256), losses := [] }

theorem u19169 : Upper (D 7) (R 7) [34,68,129,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19169 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19170 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,7)], upper := (rows 35 70 133 26 112 160 329 393 265), lower := (rows 35 70 133 26 112 160 64 128 256), losses := [] }

theorem u19170 : Upper (D 7) (R 7) [34,68,129,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19171 : Route 9 := (fun mask => (mask,id))

def c19171 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19171 : Upper (D 7) (R 7) [34,68,129,18,96,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,96,256] 13 (by decide) (choices 1) [1,8,128] r19171 c19171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5244
  · exact u5245
  · exact u5246

def b19172 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 70 133 26 152 33 352 480 352), lower := (rows 35 70 133 26 152 33 64 128 256), losses := [] }

theorem u19172 : Upper (D 7) (R 7) [34,68,129,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19173 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 26 152 96 353 417 289), lower := (rows 35 70 133 26 152 96 64 128 256), losses := [] }

theorem u19173 : Upper (D 7) (R 7) [34,68,129,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19174 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,7),(1,7),(2,1)], upper := (rows 35 70 133 26 152 288 97 225 353), lower := (rows 35 70 133 26 152 288 64 128 256), losses := [] }

theorem u19174 : Upper (D 7) (R 7) [34,68,129,18,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19174 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19175 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 26 176 33 328 456 328), lower := (rows 35 70 133 26 176 33 64 128 256), losses := [] }

theorem u19175 : Upper (D 7) (R 7) [34,68,129,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19176 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 70 133 26 176 40 321 449 321), lower := (rows 35 70 133 26 176 40 64 128 256), losses := [] }

theorem u19176 : Upper (D 7) (R 7) [34,68,129,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19176 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19177 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 26 176 96 329 393 265), lower := (rows 35 70 133 26 176 96 64 128 256), losses := [] }

theorem u19177 : Upper (D 7) (R 7) [34,68,129,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19178 : Route 9 := (fun mask => (mask,id))

def c19178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19178 : Upper (D 7) (R 7) [34,68,129,18,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,160,256] 13 (by decide) (choices 1) [1,8] r19178 c19178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5247
  · exact u5248

def b19179 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 26 208 33 360 424 296), lower := (rows 35 70 133 26 208 33 64 128 256), losses := [] }

theorem u19179 : Upper (D 7) (R 7) [34,68,129,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19180 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 70 133 26 208 40 353 417 289), lower := (rows 35 70 133 26 208 40 64 128 256), losses := [] }

theorem u19180 : Upper (D 7) (R 7) [34,68,129,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19180 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19181 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 3, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 70 133 26 208 288 105 169 297), lower := (rows 35 70 133 26 208 288 64 128 256), losses := [] }

theorem u19181 : Upper (D 7) (R 7) [34,68,129,18,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19181 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19182 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 70 133 26 273 40 224 224 480), lower := (rows 35 70 133 26 273 40 64 128 256), losses := [] }

theorem u19182 : Upper (D 7) (R 7) [34,68,129,18,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19182 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19183 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 26 273 96 232 168 424), lower := (rows 35 70 133 26 273 96 64 128 256), losses := [] }

theorem u19183 : Upper (D 7) (R 7) [34,68,129,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19184 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 35 70 133 26 273 160 104 232 360), lower := (rows 35 70 133 26 273 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 27 273 160 0 160 256) },{ target := 7, region := (rows 1 6 4 15 21 32 65 0 257), good := (rows 379 94 351 26 345 32 64 0 256) }] }

theorem u19184 : Upper (D 7) (R 7) [34,68,129,18,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19185 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 26 280 33 224 224 480), lower := (rows 35 70 133 26 280 33 64 128 256), losses := [] }

theorem u19185 : Upper (D 7) (R 7) [34,68,129,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19186 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 132, targets := 2 }], pairs := [(2,1),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 26 280 96 225 161 417), lower := (rows 35 70 133 26 280 96 64 128 256), losses := [] }

theorem u19186 : Upper (D 7) (R 7) [34,68,129,18,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19187 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,6),(2,1),(3,7),(4,7)], upper := (rows 35 70 133 26 280 160 97 225 353), lower := (rows 35 70 133 26 280 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 27 280 160 0 160 256) }] }

theorem u19187 : Upper (D 7) (R 7) [34,68,129,18,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19188 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 26 304 33 200 200 456), lower := (rows 35 70 133 26 304 33 64 128 256), losses := [] }

theorem u19188 : Upper (D 7) (R 7) [34,68,129,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19189 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 70 133 26 304 40 193 193 449), lower := (rows 35 70 133 26 304 40 64 128 256), losses := [] }

theorem u19189 : Upper (D 7) (R 7) [34,68,129,18,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19189 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19190 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 26 304 96 201 137 393), lower := (rows 35 70 133 26 304 96 64 128 256), losses := [] }

theorem u19190 : Upper (D 7) (R 7) [34,68,129,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19191 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 35 70 133 26 304 160 73 201 329), lower := (rows 35 70 133 26 304 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 27 304 160 0 160 256) },{ target := 7, region := (rows 1 6 4 13 17 32 69 0 261), good := (rows 379 334 351 26 304 32 64 0 256) }] }

theorem u19191 : Upper (D 7) (R 7) [34,68,129,18,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19192 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 26 336 33 232 168 424), lower := (rows 35 70 133 26 336 33 64 128 256), losses := [] }

theorem u19192 : Upper (D 7) (R 7) [34,68,129,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19193 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 70 133 26 336 40 225 161 417), lower := (rows 35 70 133 26 336 40 64 128 256), losses := [] }

theorem u19193 : Upper (D 7) (R 7) [34,68,129,18,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19193 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19194 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,7)], upper := (rows 35 70 133 26 336 160 105 169 297), lower := (rows 35 70 133 26 336 160 64 128 256), losses := [] }

theorem u19194 : Upper (D 7) (R 7) [34,68,129,18,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19195 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 26 400 33 104 232 360), lower := (rows 35 70 133 26 400 33 64 128 256), losses := [] }

theorem u19195 : Upper (D 7) (R 7) [34,68,129,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19196 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 70 133 26 400 40 97 225 353), lower := (rows 35 70 133 26 400 40 64 128 256), losses := [] }

theorem u19196 : Upper (D 7) (R 7) [34,68,129,18,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19196 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19197 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 26 400 96 105 169 297), lower := (rows 35 70 133 26 400 96 64 128 256), losses := [] }

theorem u19197 : Upper (D 7) (R 7) [34,68,129,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19198 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 56 81 34 456 392 392), lower := (rows 35 70 133 56 81 34 64 128 256), losses := [] }

theorem u19198 : Upper (D 7) (R 7) [34,68,129,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19199 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 70 133 56 81 40 450 386 386), lower := (rows 35 70 133 56 81 40 64 128 256), losses := [] }

theorem u19199 : Upper (D 7) (R 7) [34,68,129,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19199 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u19199
end Delivery.IrregularNine14.P07
