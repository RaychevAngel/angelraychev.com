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

def b19200 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 35 70 133 56 81 160 330 394 266), lower := (rows 35 70 133 56 81 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 56 17 160 0 160 256) },{ target := 7, region := (rows 1 6 4 9 21 32 69 0 261), good := (rows 379 342 351 56 345 32 64 0 256) }] }

theorem u19200 : Upper (D 7) (R 7) [34,68,129,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19201 : Route 9 := (fun mask => (mask,id))

def c19201 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19201 : Upper (D 7) (R 7) [34,68,129,48,65,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,65,256] 13 (by decide) (choices 1) [2,8,128] r19201 c19201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5249
  · exact u5250
  · exact u5251

def b19202 : PairBound 9 := { available := 328, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(2,6),(3,0),(3,6)], upper := (rows 35 70 133 56 146 33 328 456 328), lower := (rows 35 70 133 56 146 33 64 128 256), losses := [] }

theorem u19202 : Upper (D 7) (R 7) [34,68,129,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19203 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 133 56 146 40 321 449 321), lower := (rows 35 70 133 56 146 40 64 128 256), losses := [] }

theorem u19203 : Upper (D 7) (R 7) [34,68,129,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19203 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19204 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 56 146 96 329 393 265), lower := (rows 35 70 133 56 146 96 64 128 256), losses := [] }

theorem u19204 : Upper (D 7) (R 7) [34,68,129,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19205 : Route 9 := (fun mask => (mask,id))

def c19205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19205 : Upper (D 7) (R 7) [34,68,129,48,130,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,130,256] 13 (by decide) (choices 1) [1,8] r19205 c19205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5252
  · exact u5253

def b19206 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 56 208 33 330 394 266), lower := (rows 35 70 133 56 208 33 64 128 256), losses := [] }

theorem u19206 : Upper (D 7) (R 7) [34,68,129,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19207 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 56 208 34 329 393 265), lower := (rows 35 70 133 56 208 34 64 128 256), losses := [] }

theorem u19207 : Upper (D 7) (R 7) [34,68,129,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19208 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 70 133 56 208 40 323 387 259), lower := (rows 35 70 133 56 208 40 64 128 256), losses := [] }

theorem u19208 : Upper (D 7) (R 7) [34,68,129,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19208 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19209 : Route 9 := (fun mask => (mask,id))

def c19209 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19209 : Upper (D 7) (R 7) [34,68,129,48,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,192,256] 13 (by decide) (choices 1) [1,2,8] r19209 c19209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5254
  · exact u5255
  · exact u5256

def b19210 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 56 273 34 200 200 456), lower := (rows 35 70 133 56 273 34 64 128 256), losses := [] }

theorem u19210 : Upper (D 7) (R 7) [34,68,129,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19211 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 70 133 56 273 40 194 194 450), lower := (rows 35 70 133 56 273 40 64 128 256), losses := [] }

theorem u19211 : Upper (D 7) (R 7) [34,68,129,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19211 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19212 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 56 273 96 202 138 394), lower := (rows 35 70 133 56 273 96 64 128 256), losses := [] }

theorem u19212 : Upper (D 7) (R 7) [34,68,129,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19213 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 35 70 133 56 273 160 74 202 330), lower := (rows 35 70 133 56 273 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 56 273 160 0 160 256) },{ target := 7, region := (rows 1 6 4 9 21 32 69 0 261), good := (rows 379 342 351 56 345 32 64 0 256) }] }

theorem u19213 : Upper (D 7) (R 7) [34,68,129,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19214 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 133 56 274 33 200 200 456), lower := (rows 35 70 133 56 274 33 64 128 256), losses := [] }

theorem u19214 : Upper (D 7) (R 7) [34,68,129,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19215 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 70 133 56 274 40 193 193 449), lower := (rows 35 70 133 56 274 40 64 128 256), losses := [] }

theorem u19215 : Upper (D 7) (R 7) [34,68,129,48,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19215 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19216 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 56 274 96 201 137 393), lower := (rows 35 70 133 56 274 96 64 128 256), losses := [] }

theorem u19216 : Upper (D 7) (R 7) [34,68,129,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19217 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 35 70 133 56 274 160 73 201 329), lower := (rows 35 70 133 56 274 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 56 275 160 0 160 256) },{ target := 7, region := (rows 1 6 4 9 23 32 69 0 261), good := (rows 379 342 351 56 274 32 64 0 256) }] }

theorem u19217 : Upper (D 7) (R 7) [34,68,129,48,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19218 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5),(3,0),(4,0)], upper := (rows 35 70 133 56 280 33 194 194 450), lower := (rows 35 70 133 56 280 33 64 128 256), losses := [] }

theorem u19218 : Upper (D 7) (R 7) [34,68,129,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19219 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 56 280 34 193 193 449), lower := (rows 35 70 133 56 280 34 64 128 256), losses := [] }

theorem u19219 : Upper (D 7) (R 7) [34,68,129,48,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19220 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 56 280 96 195 131 387), lower := (rows 35 70 133 56 280 96 64 128 256), losses := [] }

theorem u19220 : Upper (D 7) (R 7) [34,68,129,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19221 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 0, region := 344, targets := 128 }], pairs := [(1,5),(2,5),(3,7),(4,7)], upper := (rows 35 70 133 56 280 160 67 195 323), lower := (rows 35 70 133 56 280 160 64 128 256), losses := [] }

theorem u19221 : Upper (D 7) (R 7) [34,68,129,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19222 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 56 336 33 202 138 394), lower := (rows 35 70 133 56 336 33 64 128 256), losses := [] }

theorem u19222 : Upper (D 7) (R 7) [34,68,129,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19223 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 56 336 34 201 137 393), lower := (rows 35 70 133 56 336 34 64 128 256), losses := [] }

theorem u19223 : Upper (D 7) (R 7) [34,68,129,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19224 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 70 133 56 336 40 195 131 387), lower := (rows 35 70 133 56 336 40 64 128 256), losses := [] }

theorem u19224 : Upper (D 7) (R 7) [34,68,129,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19224 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19225 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 35 70 133 56 336 160 75 139 267), lower := (rows 35 70 133 56 336 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 56 272 160 0 160 256) },{ target := 7, region := (rows 1 6 4 9 23 32 69 0 261), good := (rows 379 342 351 56 336 32 64 0 256) }] }

theorem u19225 : Upper (D 7) (R 7) [34,68,129,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19225 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19226 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 56 400 33 74 202 330), lower := (rows 35 70 133 56 400 33 64 128 256), losses := [] }

theorem u19226 : Upper (D 7) (R 7) [34,68,129,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19227 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 56 400 34 73 201 329), lower := (rows 35 70 133 56 400 34 64 128 256), losses := [] }

theorem u19227 : Upper (D 7) (R 7) [34,68,129,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19228 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 70 133 56 400 40 67 195 323), lower := (rows 35 70 133 56 400 40 64 128 256), losses := [] }

theorem u19228 : Upper (D 7) (R 7) [34,68,129,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19228 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19229 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 133 56 400 96 75 139 267), lower := (rows 35 70 133 56 400 96 64 128 256), losses := [] }

theorem u19229 : Upper (D 7) (R 7) [34,68,129,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19230 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(2,6),(4,6)], upper := (rows 35 70 133 73 146 40 368 432 304), lower := (rows 35 70 133 73 146 40 64 128 256), losses := [] }

theorem u19230 : Upper (D 7) (R 7) [34,68,129,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19230 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19231 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 133 73 146 48 360 424 296), lower := (rows 35 70 133 73 146 48 64 128 256), losses := [] }

theorem u19231 : Upper (D 7) (R 7) [34,68,129,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19231 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19232 : Route 9 := (fun mask => (mask,id))

def c19232 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19232 : Upper (D 7) (R 7) [34,68,129,65,130,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,130,256] 13 (by decide) (choices 1) [8,16,32] r19232 c19232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5257
  · exact u5258
  · exact u5259

def b19233 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 73 152 34 368 432 304), lower := (rows 35 70 133 73 152 34 64 128 256), losses := [] }

theorem u19233 : Upper (D 7) (R 7) [34,68,129,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19234 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 388, targets := 64 },{ cop := 0, region := 328, targets := 128 }], pairs := [(1,0),(2,6),(3,7)], upper := (rows 35 70 133 73 152 48 354 418 290), lower := (rows 35 70 133 73 152 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 24 56 65 129 257), good := (rows 482 70 454 504 184 48 64 128 256) }] }

theorem u19234 : Upper (D 7) (R 7) [34,68,129,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19234 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19235 : Route 9 := (fun mask => (mask,id))

def c19235 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19235 : Upper (D 7) (R 7) [34,68,129,65,136,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,136,256] 13 (by decide) (choices 1) [2,16,32] r19235 c19235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5260
  · exact u5261
  · exact u5262

def b19236 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 73 176 34 344 408 280), lower := (rows 35 70 133 73 176 34 64 128 256), losses := [] }

theorem u19236 : Upper (D 7) (R 7) [34,68,129,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19237 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(2,6),(4,6)], upper := (rows 35 70 133 73 176 40 338 402 274), lower := (rows 35 70 133 73 176 40 64 128 256), losses := [] }

theorem u19237 : Upper (D 7) (R 7) [34,68,129,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19237 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19238 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 133 73 176 48 330 394 266), lower := (rows 35 70 133 73 176 48 64 128 256), losses := [] }

theorem u19238 : Upper (D 7) (R 7) [34,68,129,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19238 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19239 : Route 9 := (fun mask => (mask,id))

def c19239 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19239 : Upper (D 7) (R 7) [34,68,129,65,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,160,256] 13 (by decide) (choices 1) [2,8,16] r19239 c19239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5263
  · exact u5264
  · exact u5265

def b19240 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(2,6),(4,6)], upper := (rows 35 70 133 73 274 40 240 176 432), lower := (rows 35 70 133 73 274 40 64 128 256), losses := [] }

theorem u19240 : Upper (D 7) (R 7) [34,68,129,65,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19240 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19241 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 133 73 274 48 232 168 424), lower := (rows 35 70 133 73 274 48 64 128 256), losses := [] }

theorem u19241 : Upper (D 7) (R 7) [34,68,129,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19241 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19242 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 35 70 133 73 274 160 120 184 312), lower := (rows 35 70 133 73 274 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 9 275 160 0 160 256) },{ target := 7, region := (rows 1 6 4 13 21 32 65 0 257), good := (rows 379 94 351 345 274 32 64 0 256) }] }

theorem u19242 : Upper (D 7) (R 7) [34,68,129,65,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19243 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 73 280 34 240 176 432), lower := (rows 35 70 133 73 280 34 64 128 256), losses := [] }

theorem u19243 : Upper (D 7) (R 7) [34,68,129,65,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19244 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 132, targets := 64 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 35 70 133 73 280 48 226 162 418), lower := (rows 35 70 133 73 280 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 24 56 65 129 257), good := (rows 482 70 454 504 312 48 64 128 256) }] }

theorem u19244 : Upper (D 7) (R 7) [34,68,129,65,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19244 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19245 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 35 70 133 73 280 160 114 178 306), lower := (rows 35 70 133 73 280 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 9 280 160 0 160 256) },{ target := 7, region := (rows 1 6 4 13 29 32 65 0 257), good := (rows 379 94 351 345 280 32 64 0 256) }] }

theorem u19245 : Upper (D 7) (R 7) [34,68,129,65,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19246 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 73 304 34 216 152 408), lower := (rows 35 70 133 73 304 34 64 128 256), losses := [] }

theorem u19246 : Upper (D 7) (R 7) [34,68,129,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19247 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(2,6),(4,6)], upper := (rows 35 70 133 73 304 40 210 146 402), lower := (rows 35 70 133 73 304 40 64 128 256), losses := [] }

theorem u19247 : Upper (D 7) (R 7) [34,68,129,65,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19247 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19248 : PairBound 9 := { available := 138, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 70 133 73 304 48 202 138 394), lower := (rows 35 70 133 73 304 48 64 128 256), losses := [] }

theorem u19248 : Upper (D 7) (R 7) [34,68,129,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19248 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19249 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 35 70 133 73 304 160 90 154 282), lower := (rows 35 70 133 73 304 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 165 9 304 160 0 160 256) },{ target := 7, region := (rows 1 6 4 13 17 32 69 0 261), good := (rows 379 334 351 345 304 32 64 0 256) }] }

theorem u19249 : Upper (D 7) (R 7) [34,68,129,65,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19250 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 73 400 34 120 184 312), lower := (rows 35 70 133 73 400 34 64 128 256), losses := [] }

theorem u19250 : Upper (D 7) (R 7) [34,68,129,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19251 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(2,6),(4,6)], upper := (rows 35 70 133 73 400 40 114 178 306), lower := (rows 35 70 133 73 400 40 64 128 256), losses := [] }

theorem u19251 : Upper (D 7) (R 7) [34,68,129,65,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19251 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19252 : Route 9 := (fun mask => (mask,id))

def c19252 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19252 : Upper (D 7) (R 7) [34,68,129,65,384,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,384,16] 13 (by decide) (choices 1) [2,8,32] r19252 c19252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5266
  · exact u5267
  · exact u5268

def b19253 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 88 146 33 360 424 296), lower := (rows 35 70 133 88 146 33 64 128 256), losses := [] }

theorem u19253 : Upper (D 7) (R 7) [34,68,129,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19254 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(2,6),(4,6)], upper := (rows 35 70 133 88 146 40 353 417 289), lower := (rows 35 70 133 88 146 40 64 128 256), losses := [] }

theorem u19254 : Upper (D 7) (R 7) [34,68,129,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19254 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19255 : Route 9 := (fun mask => (mask,id))

def c19255 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19255 : Upper (D 7) (R 7) [34,68,129,80,130,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,130,256] 13 (by decide) (choices 1) [1,8,32] r19255 c19255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5269
  · exact u5270
  · exact u5271

def b19256 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 133 88 176 33 330 394 266), lower := (rows 35 70 133 88 176 33 64 128 256), losses := [] }

theorem u19256 : Upper (D 7) (R 7) [34,68,129,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19257 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 133 88 176 34 329 393 265), lower := (rows 35 70 133 88 176 34 64 128 256), losses := [] }

theorem u19257 : Upper (D 7) (R 7) [34,68,129,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19258 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(1,5),(2,5),(2,6)], upper := (rows 35 70 133 88 176 40 323 387 259), lower := (rows 35 70 133 88 176 40 64 128 256), losses := [] }

theorem u19258 : Upper (D 7) (R 7) [34,68,129,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19258 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19259 : Route 9 := (fun mask => (mask,id))

def c19259 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19259 : Upper (D 7) (R 7) [34,68,129,80,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,160,256] 13 (by decide) (choices 1) [1,2,8] r19259 c19259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5272
  · exact u5273
  · exact u5274

#print axioms u19259
end Delivery.IrregularNine14.P07
