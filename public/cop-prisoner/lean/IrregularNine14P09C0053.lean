import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0005
import IrregularNine14P09C0006

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3180 : Route 9 := (fun mask => (mask,id))

def c3180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3180 : Upper (D 9) (R 9) [6,33,72,160,192,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,192,256] 13 (by decide) (choices 1) [1,16,256] r3180 c3180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u343
  · exact u344
  · exact u345

def b3181 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 34, targets := 448 },{ cop := 1, region := 460, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(2,0)], upper := (rows 7 35 76 168 273 48 448 448 448), lower := (rows 7 35 76 168 273 48 64 128 256), losses := [] }

theorem u3181 : Upper (D 9) (R 9) [6,33,72,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3181 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3182 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 76 168 273 96 464 400 400), lower := (rows 7 35 76 168 273 96 64 128 256), losses := [] }

theorem u3182 : Upper (D 9) (R 9) [6,33,72,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3182 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3183 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 7 35 76 168 273 160 336 464 336), lower := (rows 7 35 76 168 273 160 64 128 256), losses := [] }

theorem u3183 : Upper (D 9) (R 9) [6,33,72,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3183 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3184 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 236, targets := 1 },{ cop := 4, region := 34, targets := 192 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,6),(1,7),(2,0),(3,0),(4,5)], upper := (rows 7 35 76 168 273 288 208 208 464), lower := (rows 7 35 76 168 273 288 64 128 256), losses := [] }

theorem u3184 : Upper (D 9) (R 9) [6,33,72,160,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3184 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3185 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 35 76 168 336 33 464 400 400), lower := (rows 7 35 76 168 336 33 64 128 256), losses := [] }

theorem u3185 : Upper (D 9) (R 9) [6,33,72,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3185 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3186 : Route 9 := (fun mask => (mask,id))

def c3186 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3186 : Upper (D 9) (R 9) [6,33,72,160,320,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,320,16] 13 (by decide) (choices 1) [1,128,256] r3186 c3186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u346
  · exact u347
  · exact u348

def b3187 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 7 35 76 168 336 160 337 401 273), lower := (rows 7 35 76 168 336 160 64 128 256), losses := [] }

theorem u3187 : Upper (D 9) (R 9) [6,33,72,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3187 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3188 : Route 9 := (fun mask => (mask,id))

def c3188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3188 : Upper (D 9) (R 9) [6,33,72,160,320,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,320,256] 13 (by decide) (choices 1) [1,16,128] r3188 c3188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u349
  · exact u350
  · exact u351

def b3189 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 35 76 168 400 33 336 464 336), lower := (rows 7 35 76 168 400 33 64 128 256), losses := [] }

theorem u3189 : Upper (D 9) (R 9) [6,33,72,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3189 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3190 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 76 168 400 48 321 449 321), lower := (rows 7 35 76 168 400 48 64 128 256), losses := [] }

theorem u3190 : Upper (D 9) (R 9) [6,33,72,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3190 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3191 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 76 168 400 96 337 401 273), lower := (rows 7 35 76 168 400 96 64 128 256), losses := [] }

theorem u3191 : Upper (D 9) (R 9) [6,33,72,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3191 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3192 : Route 9 := (fun mask => (mask,id))

def c3192 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3192 : Upper (D 9) (R 9) [6,33,72,160,384,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,384,256] 13 (by decide) (choices 1) [1,16] r3192 c3192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u352
  · exact u353

def b3193 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 51, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 7 35 76 392 81 48 480 416 416), lower := (rows 7 35 76 392 81 48 64 128 256), losses := [] }

theorem u3193 : Upper (D 9) (R 9) [6,33,72,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3193 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3194 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 428, targets := 1 },{ cop := 4, region := 426, targets := 64 },{ cop := 1, region := 336, targets := 128 }], pairs := [(1,6),(2,0),(3,0),(3,6),(4,7)], upper := (rows 7 35 76 392 81 160 368 432 304), lower := (rows 7 35 76 392 81 160 64 128 256), losses := [] }

theorem u3194 : Upper (D 9) (R 9) [6,33,72,384,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3194 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3195 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 51, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 7 35 76 392 112 33 464 400 400), lower := (rows 7 35 76 392 112 33 64 128 256), losses := [] }

theorem u3195 : Upper (D 9) (R 9) [6,33,72,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3195 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3196 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 51, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 7 35 76 392 112 48 449 385 385), lower := (rows 7 35 76 392 112 48 64 128 256), losses := [] }

theorem u3196 : Upper (D 9) (R 9) [6,33,72,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3196 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3197 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(4,0),(4,7)], upper := (rows 7 35 76 392 112 160 337 401 273), lower := (rows 7 35 76 392 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 22 34 124 424 112 160 64 160 256) },{ target := 6, region := (rows 5 6 4 8 16 168 0 128 256), good := (rows 7 35 47 424 48 160 0 160 256) },{ target := 8, region := (rows 5 6 4 8 20 168 64 128 0), good := (rows 23 35 127 168 112 160 64 160 0) }] }

theorem u3197 : Upper (D 9) (R 9) [6,33,72,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3197 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3198 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 320 }], pairs := [(1,6),(1,8),(2,0),(3,0)], upper := (rows 7 35 76 392 145 48 352 480 352), lower := (rows 7 35 76 392 145 48 64 128 256), losses := [] }

theorem u3198 : Upper (D 9) (R 9) [6,33,72,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3198 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3199 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 76 392 145 96 368 432 304), lower := (rows 7 35 76 392 145 96 64 128 256), losses := [] }

theorem u3199 : Upper (D 9) (R 9) [6,33,72,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3199 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3200 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 364, targets := 1 },{ cop := 1, region := 208, targets := 256 },{ cop := 4, region := 354, targets := 128 }], pairs := [(0,6),(1,7),(2,0),(3,0),(4,8)], upper := (rows 7 35 76 392 145 288 112 240 368), lower := (rows 7 35 76 392 145 288 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 296 0 128 256), good := (rows 7 35 47 424 145 288 0 128 288) }] }

theorem u3200 : Upper (D 9) (R 9) [6,33,72,384,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3200 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3201 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 35 76 392 176 33 336 464 336), lower := (rows 7 35 76 392 176 33 64 128 256), losses := [] }

theorem u3201 : Upper (D 9) (R 9) [6,33,72,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3201 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3202 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 35 76 392 176 48 321 449 321), lower := (rows 7 35 76 392 176 48 64 128 256), losses := [] }

theorem u3202 : Upper (D 9) (R 9) [6,33,72,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3202 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3203 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 76 392 176 96 337 401 273), lower := (rows 7 35 76 392 176 96 64 128 256), losses := [] }

theorem u3203 : Upper (D 9) (R 9) [6,33,72,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3203 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3204 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 65 },{ cop := 1, region := 208, targets := 256 }], pairs := [(0,6),(1,6),(4,0),(4,6),(4,8)], upper := (rows 7 35 76 392 176 288 81 209 337), lower := (rows 7 35 76 392 176 288 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 24 296 0 128 256), good := (rows 7 35 63 440 176 288 0 128 288) }] }

theorem u3204 : Upper (D 9) (R 9) [6,33,72,384,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3204 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3205 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 35 76 392 208 33 368 432 304), lower := (rows 7 35 76 392 208 33 64 128 256), losses := [] }

theorem u3205 : Upper (D 9) (R 9) [6,33,72,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3205 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3206 : Route 9 := (fun mask => (mask,id))

def c3206 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3206 : Upper (D 9) (R 9) [6,33,72,384,192,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,192,16] 13 (by decide) (choices 1) [1,32,256] r3206 c3206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u354
  · exact u355
  · exact u356

def b3207 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 208, targets := 256 }], pairs := [(0,6),(0,7),(1,6),(1,7),(4,8)], upper := (rows 7 35 76 392 208 288 113 177 305), lower := (rows 7 35 76 392 208 288 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 296 0 128 256), good := (rows 7 35 47 424 144 288 0 128 288) },{ target := 7, region := (rows 5 6 4 8 16 296 64 0 256), good := (rows 7 35 111 296 80 288 64 0 288) }] }

theorem u3207 : Upper (D 9) (R 9) [6,33,72,384,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3207 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3208 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 59, targets := 256 },{ cop := 1, region := 344, targets := 128 }], pairs := [(0,8),(1,8),(3,7),(3,8),(4,8)], upper := (rows 7 35 196 25 88 160 352 416 288), lower := (rows 7 35 196 25 88 160 64 128 256), losses := [] }

theorem u3208 : Upper (D 9) (R 9) [6,33,192,17,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3208 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3209 : Route 9 := (fun mask => (mask,id))

def c3209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3209 : Upper (D 9) (R 9) [6,33,192,17,72,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,72,256] 13 (by decide) (choices 1) [32,128,256] r3209 c3209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u357
  · exact u358
  · exact u359

def b3210 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 59, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 7 35 196 25 112 40 448 384 384), lower := (rows 7 35 196 25 112 40 64 128 256), losses := [] }

theorem u3210 : Upper (D 9) (R 9) [6,33,192,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3210 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3211 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 59, targets := 256 },{ cop := 1, region := 344, targets := 128 }], pairs := [(0,8),(1,8),(3,7),(3,8),(4,8)], upper := (rows 7 35 196 25 112 160 328 392 264), lower := (rows 7 35 196 25 112 160 64 128 256), losses := [] }

theorem u3211 : Upper (D 9) (R 9) [6,33,192,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3211 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3212 : Route 9 := (fun mask => (mask,id))

def c3212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3212 : Upper (D 9) (R 9) [6,33,192,17,96,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,96,256] 13 (by decide) (choices 1) [8,128,256] r3212 c3212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u360
  · exact u361
  · exact u362

def b3213 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 196 25 280 96 480 416 416), lower := (rows 7 35 196 25 280 96 64 128 256), losses := [] }

theorem u3213 : Upper (D 9) (R 9) [6,33,192,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3213 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3214 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 3, region := 500, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(4,0)], upper := (rows 7 35 196 25 280 288 224 224 480), lower := (rows 7 35 196 25 280 288 64 128 256), losses := [] }

theorem u3214 : Upper (D 9) (R 9) [6,33,192,17,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3214 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3215 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 34, targets := 448 },{ cop := 1, region := 452, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(2,0)], upper := (rows 7 35 196 25 304 40 448 448 448), lower := (rows 7 35 196 25 304 40 64 128 256), losses := [] }

theorem u3215 : Upper (D 9) (R 9) [6,33,192,17,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3215 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3216 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 196 25 304 96 456 392 392), lower := (rows 7 35 196 25 304 96 64 128 256), losses := [] }

theorem u3216 : Upper (D 9) (R 9) [6,33,192,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3216 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3217 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 35 196 25 304 288 200 200 456), lower := (rows 7 35 196 25 304 288 64 128 256), losses := [] }

theorem u3217 : Upper (D 9) (R 9) [6,33,192,17,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3217 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3218 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 384 }], pairs := [(1,7),(1,8),(2,0),(4,0)], upper := (rows 7 35 196 25 336 40 480 416 416), lower := (rows 7 35 196 25 336 40 64 128 256), losses := [] }

theorem u3218 : Upper (D 9) (R 9) [6,33,192,17,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3218 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3219 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 35, targets := 320 },{ cop := 1, region := 344, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(3,7)], upper := (rows 7 35 196 25 336 160 360 424 296), lower := (rows 7 35 196 25 336 160 64 128 256), losses := [] }

theorem u3219 : Upper (D 9) (R 9) [6,33,192,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3219 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3220 : Route 9 := (fun mask => (mask,id))

def c3220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3220 : Upper (D 9) (R 9) [6,33,192,17,320,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,320,256] 13 (by decide) (choices 1) [8,32,128] r3220 c3220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u363
  · exact u364
  · exact u365

def b3221 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 59, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 35 196 56 88 33 448 384 384), lower := (rows 7 35 196 56 88 33 64 128 256), losses := [] }

theorem u3221 : Upper (D 9) (R 9) [6,33,192,48,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3221 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3222 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 59, targets := 256 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 35 196 56 88 160 321 385 257), lower := (rows 7 35 196 56 88 160 64 128 256), losses := [] }

theorem u3222 : Upper (D 9) (R 9) [6,33,192,48,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3222 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3223 : Route 9 := (fun mask => (mask,id))

def c3223 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3223 : Upper (D 9) (R 9) [6,33,192,48,72,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,72,256] 13 (by decide) (choices 1) [1,128,256] r3223 c3223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u366
  · exact u367
  · exact u368

def b3224 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 42, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(3,6)], upper := (rows 7 35 196 56 273 40 448 448 448), lower := (rows 7 35 196 56 273 40 64 128 256), losses := [] }

theorem u3224 : Upper (D 9) (R 9) [6,33,192,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3224 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3225 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,6)], upper := (rows 7 35 196 56 273 96 456 392 392), lower := (rows 7 35 196 56 273 96 64 128 256), losses := [] }

theorem u3225 : Upper (D 9) (R 9) [6,33,192,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3225 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3226 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 42, targets := 192 },{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 196 56 273 288 200 200 456), lower := (rows 7 35 196 56 273 288 64 128 256), losses := [] }

theorem u3226 : Upper (D 9) (R 9) [6,33,192,48,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3226 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3227 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 35 196 56 280 33 448 448 448), lower := (rows 7 35 196 56 280 33 64 128 256), losses := [] }

theorem u3227 : Upper (D 9) (R 9) [6,33,192,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3227 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3228 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(0,7),(0,8),(1,7),(1,8)], upper := (rows 7 35 196 56 280 96 449 385 385), lower := (rows 7 35 196 56 280 96 64 128 256), losses := [] }

theorem u3228 : Upper (D 9) (R 9) [6,33,192,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3228 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3229 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 24, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0),(4,6)], upper := (rows 7 35 196 56 280 288 193 193 449), lower := (rows 7 35 196 56 280 288 64 128 256), losses := [] }

theorem u3229 : Upper (D 9) (R 9) [6,33,192,48,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3229 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3230 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 35 196 56 336 33 456 392 392), lower := (rows 7 35 196 56 336 33 64 128 256), losses := [] }

theorem u3230 : Upper (D 9) (R 9) [6,33,192,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3230 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3231 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 40, targets := 449 }], pairs := [(3,0),(3,6),(3,7),(3,8)], upper := (rows 7 35 196 56 336 40 449 385 385), lower := (rows 7 35 196 56 336 40 64 128 256), losses := [] }

theorem u3231 : Upper (D 9) (R 9) [6,33,192,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3231 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3232 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 35, targets := 320 },{ cop := 1, region := 344, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(3,7)], upper := (rows 7 35 196 56 336 160 329 393 265), lower := (rows 7 35 196 56 336 160 64 128 256), losses := [] }

theorem u3232 : Upper (D 9) (R 9) [6,33,192,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3232 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3233 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,6)], upper := (rows 7 35 196 56 336 288 201 137 393), lower := (rows 7 35 196 56 336 288 64 128 256), losses := [] }

theorem u3233 : Upper (D 9) (R 9) [6,33,192,48,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3233 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3234 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 59, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 35 196 73 152 48 352 416 288), lower := (rows 7 35 196 73 152 48 64 128 256), losses := [] }

theorem u3234 : Upper (D 9) (R 9) [6,33,192,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3234 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3235 : Route 9 := (fun mask => (mask,id))

def c3235 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u3235 : Upper (D 9) (R 9) [6,33,192,65,136,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,136,256] 13 (by decide) (choices 1) [16,32,256] r3235 c3235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u369
  · exact u370
  · exact u371

def b3236 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 59, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 35 196 73 176 40 336 400 272), lower := (rows 7 35 196 73 176 40 64 128 256), losses := [] }

theorem u3236 : Upper (D 9) (R 9) [6,33,192,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3236 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3237 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 59, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 35 196 73 176 48 328 392 264), lower := (rows 7 35 196 73 176 48 64 128 256), losses := [] }

theorem u3237 : Upper (D 9) (R 9) [6,33,192,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3237 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3238 : Route 9 := (fun mask => (mask,id))

def c3238 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3238 : Upper (D 9) (R 9) [6,33,192,65,160,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,160,256] 13 (by decide) (choices 1) [8,16,256] r3238 c3238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u372
  · exact u373
  · exact u374

def b3239 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 436, targets := 1 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(2,0),(4,0),(4,6)], upper := (rows 7 35 196 73 280 48 480 416 416), lower := (rows 7 35 196 73 280 48 64 128 256), losses := [] }

theorem u3239 : Upper (D 9) (R 9) [6,33,192,65,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3239 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u3239
end Delivery.IrregularNine14.P09
