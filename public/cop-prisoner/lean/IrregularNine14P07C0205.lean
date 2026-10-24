import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0020

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12300 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 76 152 112 33 450 386 386), lower := (rows 7 35 76 152 112 33 64 128 256), losses := [] }

theorem u12300 : Upper (D 7) (R 7) [6,33,72,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12301 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 76 152 112 34 449 385 385), lower := (rows 7 35 76 152 112 34 64 128 256), losses := [] }

theorem u12301 : Upper (D 7) (R 7) [6,33,72,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12302 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(1,6),(4,0),(4,7)], upper := (rows 7 35 76 152 112 160 323 387 259), lower := (rows 7 35 76 152 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 22 34 124 184 112 160 64 160 256) }] }

theorem u12302 : Upper (D 7) (R 7) [6,33,72,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12303 : Route 9 := (fun mask => (mask,id))

def c12303 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12303 : Upper (D 7) (R 7) [6,33,72,144,96,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,96,256] 13 (by decide) (choices 1) [1,2,128] r12303 c12303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1202
  · exact u1203
  · exact u1204

def b12304 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 152 273 34 224 224 480), lower := (rows 7 35 76 152 273 34 64 128 256), losses := [] }

theorem u12304 : Upper (D 7) (R 7) [6,33,72,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12305 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 152 273 96 226 162 418), lower := (rows 7 35 76 152 273 96 64 128 256), losses := [] }

theorem u12305 : Upper (D 7) (R 7) [6,33,72,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12305 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12306 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(2,0),(3,0),(4,7)], upper := (rows 7 35 76 152 273 160 98 226 354), lower := (rows 7 35 76 152 273 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 187 67 131 259), good := (rows 486 482 108 188 508 160 64 160 256) },{ target := 6, region := (rows 5 6 4 8 16 168 0 128 256), good := (rows 7 35 47 184 273 160 0 160 256) }] }

theorem u12306 : Upper (D 7) (R 7) [6,33,72,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12307 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 152 274 33 224 224 480), lower := (rows 7 35 76 152 274 33 64 128 256), losses := [] }

theorem u12307 : Upper (D 7) (R 7) [6,33,72,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12308 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 152 274 96 225 161 417), lower := (rows 7 35 76 152 274 96 64 128 256), losses := [] }

theorem u12308 : Upper (D 7) (R 7) [6,33,72,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12309 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(2,1),(3,1),(4,7)], upper := (rows 7 35 76 152 274 160 97 225 353), lower := (rows 7 35 76 152 274 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 187 67 131 259), good := (rows 485 481 108 188 508 160 64 160 256) },{ target := 6, region := (rows 5 6 4 8 16 168 0 128 256), good := (rows 7 35 47 184 274 160 0 160 256) }] }

theorem u12309 : Upper (D 7) (R 7) [6,33,72,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12310 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 152 304 33 194 194 450), lower := (rows 7 35 76 152 304 33 64 128 256), losses := [] }

theorem u12310 : Upper (D 7) (R 7) [6,33,72,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12311 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 152 304 34 193 193 449), lower := (rows 7 35 76 152 304 34 64 128 256), losses := [] }

theorem u12311 : Upper (D 7) (R 7) [6,33,72,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12312 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 152 304 96 195 131 387), lower := (rows 7 35 76 152 304 96 64 128 256), losses := [] }

theorem u12312 : Upper (D 7) (R 7) [6,33,72,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12313 : Route 9 := (fun mask => (mask,id))

def c12313 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12313 : Upper (D 7) (R 7) [6,33,72,144,288,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,288,128] 13 (by decide) (choices 1) [1,2] r12313 c12313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1205
  · exact u1206

def b12314 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 7 35 76 152 336 33 226 162 418), lower := (rows 7 35 76 152 336 33 64 128 256), losses := [] }

theorem u12314 : Upper (D 7) (R 7) [6,33,72,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12315 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 7 35 76 152 336 34 225 161 417), lower := (rows 7 35 76 152 336 34 64 128 256), losses := [] }

theorem u12315 : Upper (D 7) (R 7) [6,33,72,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12316 : Route 9 := (fun mask => (mask,id))

def c12316 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12316 : Upper (D 7) (R 7) [6,33,72,144,320,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,320,128] 13 (by decide) (choices 1) [1,2,32] r12316 c12316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1207
  · exact u1208
  · exact u1209

def b12317 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 76 168 81 34 464 400 400), lower := (rows 7 35 76 168 81 34 64 128 256), losses := [] }

theorem u12317 : Upper (D 7) (R 7) [6,33,72,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12318 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 51, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 35 76 168 81 48 450 386 386), lower := (rows 7 35 76 168 81 48 64 128 256), losses := [] }

theorem u12318 : Upper (D 7) (R 7) [6,33,72,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12318 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12319 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 35 76 168 81 160 338 402 274), lower := (rows 7 35 76 168 81 160 64 128 256), losses := [] }

theorem u12319 : Upper (D 7) (R 7) [6,33,72,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12320 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,6),(3,6),(4,5)], upper := (rows 7 35 76 168 81 288 210 146 402), lower := (rows 7 35 76 168 81 288 64 128 256), losses := [] }

theorem u12320 : Upper (D 7) (R 7) [6,33,72,160,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12320 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12321 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 76 168 82 33 464 400 400), lower := (rows 7 35 76 168 82 33 64 128 256), losses := [] }

theorem u12321 : Upper (D 7) (R 7) [6,33,72,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12322 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 51, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 35 76 168 82 48 449 385 385), lower := (rows 7 35 76 168 82 48 64 128 256), losses := [] }

theorem u12322 : Upper (D 7) (R 7) [6,33,72,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12322 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12323 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 35 76 168 82 160 337 401 273), lower := (rows 7 35 76 168 82 160 64 128 256), losses := [] }

theorem u12323 : Upper (D 7) (R 7) [6,33,72,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12324 : Route 9 := (fun mask => (mask,id))

def c12324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12324 : Upper (D 7) (R 7) [6,33,72,160,66,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,66,256] 13 (by decide) (choices 1) [1,16,128] r12324 c12324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1210
  · exact u1211
  · exact u1212

def b12325 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 168 145 34 336 464 336), lower := (rows 7 35 76 168 145 34 64 128 256), losses := [] }

theorem u12325 : Upper (D 7) (R 7) [6,33,72,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12326 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 76 168 145 48 322 450 322), lower := (rows 7 35 76 168 145 48 64 128 256), losses := [] }

theorem u12326 : Upper (D 7) (R 7) [6,33,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12326 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12327 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 168 145 96 338 402 274), lower := (rows 7 35 76 168 145 96 64 128 256), losses := [] }

theorem u12327 : Upper (D 7) (R 7) [6,33,72,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12328 : Route 9 := (fun mask => (mask,id))

def c12328 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12328 : Upper (D 7) (R 7) [6,33,72,160,129,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,129,256] 13 (by decide) (choices 1) [2,16] r12328 c12328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1213
  · exact u1214

def b12329 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 168 146 33 336 464 336), lower := (rows 7 35 76 168 146 33 64 128 256), losses := [] }

theorem u12329 : Upper (D 7) (R 7) [6,33,72,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12330 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 76 168 146 48 321 449 321), lower := (rows 7 35 76 168 146 48 64 128 256), losses := [] }

theorem u12330 : Upper (D 7) (R 7) [6,33,72,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12330 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12331 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 168 146 96 337 401 273), lower := (rows 7 35 76 168 146 96 64 128 256), losses := [] }

theorem u12331 : Upper (D 7) (R 7) [6,33,72,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12332 : Route 9 := (fun mask => (mask,id))

def c12332 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12332 : Upper (D 7) (R 7) [6,33,72,160,130,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,130,256] 13 (by decide) (choices 1) [1,16] r12332 c12332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1215
  · exact u1216

def b12333 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 168 208 33 338 402 274), lower := (rows 7 35 76 168 208 33 64 128 256), losses := [] }

theorem u12333 : Upper (D 7) (R 7) [6,33,72,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12334 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 168 208 34 337 401 273), lower := (rows 7 35 76 168 208 34 64 128 256), losses := [] }

theorem u12334 : Upper (D 7) (R 7) [6,33,72,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12335 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 76 168 208 48 323 387 259), lower := (rows 7 35 76 168 208 48 64 128 256), losses := [] }

theorem u12335 : Upper (D 7) (R 7) [6,33,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12335 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12336 : Route 9 := (fun mask => (mask,id))

def c12336 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12336 : Upper (D 7) (R 7) [6,33,72,160,192,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,192,256] 13 (by decide) (choices 1) [1,2,16] r12336 c12336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1217
  · exact u1218
  · exact u1219

def b12337 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 168 273 34 208 208 464), lower := (rows 7 35 76 168 273 34 64 128 256), losses := [] }

theorem u12337 : Upper (D 7) (R 7) [6,33,72,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12338 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 7 35 76 168 273 48 194 194 450), lower := (rows 7 35 76 168 273 48 64 128 256), losses := [] }

theorem u12338 : Upper (D 7) (R 7) [6,33,72,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12338 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12339 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 168 273 96 210 146 402), lower := (rows 7 35 76 168 273 96 64 128 256), losses := [] }

theorem u12339 : Upper (D 7) (R 7) [6,33,72,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12340 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 35 76 168 273 160 82 210 338), lower := (rows 7 35 76 168 273 160 64 128 256), losses := [] }

theorem u12340 : Upper (D 7) (R 7) [6,33,72,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12341 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 168 274 33 208 208 464), lower := (rows 7 35 76 168 274 33 64 128 256), losses := [] }

theorem u12341 : Upper (D 7) (R 7) [6,33,72,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12342 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 204, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 35 76 168 274 48 193 193 449), lower := (rows 7 35 76 168 274 48 64 128 256), losses := [] }

theorem u12342 : Upper (D 7) (R 7) [6,33,72,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12342 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12343 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 168 274 96 209 145 401), lower := (rows 7 35 76 168 274 96 64 128 256), losses := [] }

theorem u12343 : Upper (D 7) (R 7) [6,33,72,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12344 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 35 76 168 274 160 81 209 337), lower := (rows 7 35 76 168 274 160 64 128 256), losses := [] }

theorem u12344 : Upper (D 7) (R 7) [6,33,72,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12345 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 168 336 33 210 146 402), lower := (rows 7 35 76 168 336 33 64 128 256), losses := [] }

theorem u12345 : Upper (D 7) (R 7) [6,33,72,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12346 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 168 336 34 209 145 401), lower := (rows 7 35 76 168 336 34 64 128 256), losses := [] }

theorem u12346 : Upper (D 7) (R 7) [6,33,72,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12347 : Route 9 := (fun mask => (mask,id))

def c12347 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12347 : Upper (D 7) (R 7) [6,33,72,160,320,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,320,16] 13 (by decide) (choices 1) [1,2,128] r12347 c12347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1220
  · exact u1221
  · exact u1222

def b12348 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 35 76 168 336 160 83 147 275), lower := (rows 7 35 76 168 336 160 64 128 256), losses := [] }

theorem u12348 : Upper (D 7) (R 7) [6,33,72,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12349 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 168 400 33 82 210 338), lower := (rows 7 35 76 168 400 33 64 128 256), losses := [] }

theorem u12349 : Upper (D 7) (R 7) [6,33,72,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12350 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 76 168 400 34 81 209 337), lower := (rows 7 35 76 168 400 34 64 128 256), losses := [] }

theorem u12350 : Upper (D 7) (R 7) [6,33,72,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12351 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 76 168 400 48 67 195 323), lower := (rows 7 35 76 168 400 48 64 128 256), losses := [] }

theorem u12351 : Upper (D 7) (R 7) [6,33,72,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12351 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12352 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 168 400 96 83 147 275), lower := (rows 7 35 76 168 400 96 64 128 256), losses := [] }

theorem u12352 : Upper (D 7) (R 7) [6,33,72,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12353 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 51, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 35 76 265 82 48 224 160 416), lower := (rows 7 35 76 265 82 48 64 128 256), losses := [] }

theorem u12353 : Upper (D 7) (R 7) [6,33,72,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12353 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12354 : Route 9 := (fun mask => (mask,id))

def c12354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12354 : Upper (D 7) (R 7) [6,33,72,257,66,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257,66,128] 13 (by decide) (choices 1) [16,32,128] r12354 c12354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1223
  · exact u1224
  · exact u1225

def b12355 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 76 265 112 34 208 144 400), lower := (rows 7 35 76 265 112 34 64 128 256), losses := [] }

theorem u12355 : Upper (D 7) (R 7) [6,33,72,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12356 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 76 265 112 48 194 130 386), lower := (rows 7 35 76 265 112 48 64 128 256), losses := [] }

theorem u12356 : Upper (D 7) (R 7) [6,33,72,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12356 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12357 : Route 9 := (fun mask => (mask,id))

def c12357 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12357 : Upper (D 7) (R 7) [6,33,72,257,96,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257,96,128] 13 (by decide) (choices 1) [2,16,128] r12357 c12357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1226
  · exact u1227
  · exact u1228

def b12358 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 460, targets := 2 },{ cop := 0, region := 240, targets := 1 }], pairs := [(2,1),(3,1),(4,0)], upper := (rows 7 35 76 265 146 48 224 224 480), lower := (rows 7 35 76 265 146 48 64 128 256), losses := [] }

theorem u12358 : Upper (D 7) (R 7) [6,33,72,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12358 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12359 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 76 265 146 96 240 176 432), lower := (rows 7 35 76 265 146 96 64 128 256), losses := [] }

theorem u12359 : Upper (D 7) (R 7) [6,33,72,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u12359
end Delivery.IrregularNine14.P07
