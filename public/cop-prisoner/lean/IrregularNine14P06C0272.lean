import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0068

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16320 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 28 274 96 97 161 289), lower := (rows 11 134 100 28 274 96 64 128 256), losses := [] }

theorem u16320 : Upper (D 6) (R 6) [10,132,96,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16321 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 100 41 81 34 340 404 276), lower := (rows 11 134 100 41 81 34 64 128 256), losses := [] }

theorem u16321 : Upper (D 6) (R 6) [10,132,96,33,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16322 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 134 100 41 81 36 338 402 274), lower := (rows 11 134 100 41 81 36 64 128 256), losses := [] }

theorem u16322 : Upper (D 6) (R 6) [10,132,96,33,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16323 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 100 41 81 48 326 390 262), lower := (rows 11 134 100 41 81 48 64 128 256), losses := [] }

theorem u16323 : Upper (D 6) (R 6) [10,132,96,33,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16323 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16324 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 134 100 41 81 288 86 150 278), lower := (rows 11 134 100 41 81 288 64 128 256), losses := [] }

theorem u16324 : Upper (D 6) (R 6) [10,132,96,33,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16324 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16325 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 100 41 82 33 340 404 276), lower := (rows 11 134 100 41 82 33 64 128 256), losses := [] }

theorem u16325 : Upper (D 6) (R 6) [10,132,96,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16326 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 134 100 41 82 36 337 401 273), lower := (rows 11 134 100 41 82 36 64 128 256), losses := [] }

theorem u16326 : Upper (D 6) (R 6) [10,132,96,33,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16327 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 134 100 41 82 48 325 389 261), lower := (rows 11 134 100 41 82 48 64 128 256), losses := [] }

theorem u16327 : Upper (D 6) (R 6) [10,132,96,33,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16327 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16328 : Route 9 := (fun mask => (mask,id))

def c16328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16328 : Upper (D 6) (R 6) [10,132,96,33,66,256] 13 := by
  apply FastRouting.sound _ _ [10,132,96,33,66,256] 13 (by decide) (choices 1) [1,4,16] r16328 c16328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4088
  · exact u4089
  · exact u4090

def b16329 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 100 41 273 34 84 212 340), lower := (rows 11 134 100 41 273 34 64 128 256), losses := [] }

theorem u16329 : Upper (D 6) (R 6) [10,132,96,33,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16330 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 134 100 41 273 36 82 210 338), lower := (rows 11 134 100 41 273 36 64 128 256), losses := [] }

theorem u16330 : Upper (D 6) (R 6) [10,132,96,33,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16331 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 11 134 100 41 273 48 70 198 326), lower := (rows 11 134 100 41 273 48 64 128 256), losses := [] }

theorem u16331 : Upper (D 6) (R 6) [10,132,96,33,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16331 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16332 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 41 273 96 86 150 278), lower := (rows 11 134 100 41 273 96 64 128 256), losses := [] }

theorem u16332 : Upper (D 6) (R 6) [10,132,96,33,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16333 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 100 41 274 33 84 212 340), lower := (rows 11 134 100 41 274 33 64 128 256), losses := [] }

theorem u16333 : Upper (D 6) (R 6) [10,132,96,33,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16334 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 134 100 41 274 36 81 209 337), lower := (rows 11 134 100 41 274 36 64 128 256), losses := [] }

theorem u16334 : Upper (D 6) (R 6) [10,132,96,33,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16335 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 134 100 41 274 48 69 197 325), lower := (rows 11 134 100 41 274 48 64 128 256), losses := [] }

theorem u16335 : Upper (D 6) (R 6) [10,132,96,33,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16335 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16336 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 41 274 96 85 149 277), lower := (rows 11 134 100 41 274 96 64 128 256), losses := [] }

theorem u16336 : Upper (D 6) (R 6) [10,132,96,33,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16337 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 100 41 276 33 82 210 338), lower := (rows 11 134 100 41 276 33 64 128 256), losses := [] }

theorem u16337 : Upper (D 6) (R 6) [10,132,96,33,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16338 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 100 41 276 34 81 209 337), lower := (rows 11 134 100 41 276 34 64 128 256), losses := [] }

theorem u16338 : Upper (D 6) (R 6) [10,132,96,33,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16339 : Route 9 := (fun mask => (mask,id))

def c16339 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16339 : Upper (D 6) (R 6) [10,132,96,33,260,16] 13 := by
  apply FastRouting.sound _ _ [10,132,96,33,260,16] 13 (by decide) (choices 1) [1,2] r16339 c16339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4091
  · exact u4092

def b16340 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 41 276 96 83 147 275), lower := (rows 11 134 100 41 276 96 64 128 256), losses := [] }

theorem u16340 : Upper (D 6) (R 6) [10,132,96,33,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16341 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 100 41 336 33 86 150 278), lower := (rows 11 134 100 41 336 33 64 128 256), losses := [] }

theorem u16341 : Upper (D 6) (R 6) [10,132,96,33,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16342 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 100 41 336 34 85 149 277), lower := (rows 11 134 100 41 336 34 64 128 256), losses := [] }

theorem u16342 : Upper (D 6) (R 6) [10,132,96,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16343 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 134 100 41 336 36 83 147 275), lower := (rows 11 134 100 41 336 36 64 128 256), losses := [] }

theorem u16343 : Upper (D 6) (R 6) [10,132,96,33,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16344 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 100 41 336 48 71 135 263), lower := (rows 11 134 100 41 336 48 64 128 256), losses := [] }

theorem u16344 : Upper (D 6) (R 6) [10,132,96,33,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16344 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16345 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 386, targets := 33 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(1,5),(2,1)], upper := (rows 11 134 100 56 81 33 326 390 262), lower := (rows 11 134 100 56 81 33 64 128 256), losses := [] }

theorem u16345 : Upper (D 6) (R 6) [10,132,96,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16346 : PairBound 9 := { available := 261, camps := [], pairs := [(0,2),(2,0),(3,0)], upper := (rows 11 134 100 56 81 34 325 389 261), lower := (rows 11 134 100 56 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 64 128 256), good := (rows 42 166 100 60 124 34 64 128 256) },{ target := 2, region := (rows 35 2 0 30 20 35 64 128 256), good := (rows 43 187 121 57 121 43 64 128 256) }] }

theorem u16346 : Upper (D 6) (R 6) [10,132,96,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16347 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 134 100 56 81 36 323 387 259), lower := (rows 11 134 100 56 81 36 64 128 256), losses := [] }

theorem u16347 : Upper (D 6) (R 6) [10,132,96,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16348 : Route 9 := (fun mask => (mask,id))

def c16348 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16348 : Upper (D 6) (R 6) [10,132,96,48,65,256] 13 := by
  apply FastRouting.sound _ _ [10,132,96,48,65,256] 13 (by decide) (choices 1) [1,2,4] r16348 c16348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4093
  · exact u4094
  · exact u4095

def b16349 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 100 56 82 33 325 389 261), lower := (rows 11 134 100 56 82 33 64 128 256), losses := [] }

theorem u16349 : Upper (D 6) (R 6) [10,132,96,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16350 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 134 100 56 82 36 321 385 257), lower := (rows 11 134 100 56 82 36 64 128 256), losses := [] }

theorem u16350 : Upper (D 6) (R 6) [10,132,96,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16351 : Route 9 := (fun mask => (mask,id))

def c16351 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16351 : Upper (D 6) (R 6) [10,132,96,48,66,256] 13 := by
  apply FastRouting.sound _ _ [10,132,96,48,66,256] 13 (by decide) (choices 1) [1,4] r16351 c16351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4096
  · exact u4097

def b16352 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 134 100 56 273 33 70 198 326), lower := (rows 11 134 100 56 273 33 64 128 256), losses := [] }

theorem u16352 : Upper (D 6) (R 6) [10,132,96,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16353 : PairBound 9 := { available := 69, camps := [], pairs := [(3,0),(3,2),(3,6)], upper := (rows 11 134 100 56 273 34 69 197 325), lower := (rows 11 134 100 56 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 35 64 128 256), good := (rows 42 166 100 56 312 34 64 128 256) },{ target := 2, region := (rows 1 2 0 24 16 35 64 128 256), good := (rows 43 162 96 56 313 34 64 128 256) },{ target := 6, region := (rows 1 2 4 24 16 35 0 128 256), good := (rows 43 166 36 56 313 34 0 128 256) }] }

theorem u16353 : Upper (D 6) (R 6) [10,132,96,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16354 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 11 134 100 56 273 36 67 195 323), lower := (rows 11 134 100 56 273 36 64 128 256), losses := [] }

theorem u16354 : Upper (D 6) (R 6) [10,132,96,48,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16355 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 56 273 96 71 135 263), lower := (rows 11 134 100 56 273 96 64 128 256), losses := [] }

theorem u16355 : Upper (D 6) (R 6) [10,132,96,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16355 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16356 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 100 56 274 33 69 197 325), lower := (rows 11 134 100 56 274 33 64 128 256), losses := [] }

theorem u16356 : Upper (D 6) (R 6) [10,132,96,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16357 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 11 134 100 56 274 36 65 193 321), lower := (rows 11 134 100 56 274 36 64 128 256), losses := [] }

theorem u16357 : Upper (D 6) (R 6) [10,132,96,48,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16358 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 56 274 96 69 133 261), lower := (rows 11 134 100 56 274 96 64 128 256), losses := [] }

theorem u16358 : Upper (D 6) (R 6) [10,132,96,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16359 : Route 9 := (fun mask => (mask,id))

def c16359 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16359 : Upper (D 6) (R 6) [10,132,96,48,260,1] 13 := by
  apply FastRouting.sound _ _ [10,132,96,48,260,1] 13 (by decide) (choices 1) [1,2] r16359 c16359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4098
  · exact u4099

def r16360 : Route 9 := (fun mask => (mask,id))

def c16360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16360 : Upper (D 6) (R 6) [10,132,96,48,260,2] 13 := by
  apply FastRouting.sound _ _ [10,132,96,48,260,2] 13 (by decide) (choices 1) [1] r16360 c16360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u4100

def b16361 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 56 276 96 67 131 259), lower := (rows 11 134 100 56 276 96 64 128 256), losses := [] }

theorem u16361 : Upper (D 6) (R 6) [10,132,96,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16362 : Route 9 := (fun mask => (mask,id))

def c16362 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16362 : Upper (D 6) (R 6) [10,132,96,48,320,1] 13 := by
  apply FastRouting.sound _ _ [10,132,96,48,320,1] 13 (by decide) (choices 1) [1,2,4] r16362 c16362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4101
  · exact u4102
  · exact u4103

def r16363 : Route 9 := (fun mask => (mask,id))

def c16363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16363 : Upper (D 6) (R 6) [10,132,96,48,320,2] 13 := by
  apply FastRouting.sound _ _ [10,132,96,48,320,2] 13 (by decide) (choices 1) [1,4] r16363 c16363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4104
  · exact u4105

def b16364 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 134 100 56 336 36 67 131 259), lower := (rows 11 134 100 56 336 36 64 128 256), losses := [] }

theorem u16364 : Upper (D 6) (R 6) [10,132,96,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16365 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(2,0),(3,2)], upper := (rows 11 134 100 265 21 34 112 240 368), lower := (rows 11 134 100 265 21 34 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 35 80 144 272), good := (rows 43 162 96 297 505 34 64 128 256) }] }

theorem u16365 : Upper (D 6) (R 6) [10,132,96,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16366 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 134 100 265 21 48 98 226 354), lower := (rows 11 134 100 265 21 48 64 128 256), losses := [] }

theorem u16366 : Upper (D 6) (R 6) [10,132,96,257,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16366 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16367 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 265 21 96 114 178 306), lower := (rows 11 134 100 265 21 96 64 128 256), losses := [] }

theorem u16367 : Upper (D 6) (R 6) [10,132,96,257,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16368 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 4, region := 198, targets := 1 }], pairs := [(1,0),(4,2),(4,6)], upper := (rows 11 134 100 265 49 34 84 212 340), lower := (rows 11 134 100 265 49 34 64 128 256), losses := [] }

theorem u16368 : Upper (D 6) (R 6) [10,132,96,257,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16369 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 198, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 134 100 265 49 36 82 210 338), lower := (rows 11 134 100 265 49 36 64 128 256), losses := [] }

theorem u16369 : Upper (D 6) (R 6) [10,132,96,257,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16370 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 100 265 49 48 70 198 326), lower := (rows 11 134 100 265 49 48 64 128 256), losses := [] }

theorem u16370 : Upper (D 6) (R 6) [10,132,96,257,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16370 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16371 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 265 49 96 86 150 278), lower := (rows 11 134 100 265 49 96 64 128 256), losses := [] }

theorem u16371 : Upper (D 6) (R 6) [10,132,96,257,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16372 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 100 265 50 33 84 212 340), lower := (rows 11 134 100 265 50 33 64 128 256), losses := [] }

theorem u16372 : Upper (D 6) (R 6) [10,132,96,257,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16373 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 100 265 50 36 81 209 337), lower := (rows 11 134 100 265 50 36 64 128 256), losses := [] }

theorem u16373 : Upper (D 6) (R 6) [10,132,96,257,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16374 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 134 100 265 50 48 69 197 325), lower := (rows 11 134 100 265 50 48 64 128 256), losses := [] }

theorem u16374 : Upper (D 6) (R 6) [10,132,96,257,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16374 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16375 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 265 50 96 85 149 277), lower := (rows 11 134 100 265 50 96 64 128 256), losses := [] }

theorem u16375 : Upper (D 6) (R 6) [10,132,96,257,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16376 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 100 268 49 33 82 210 338), lower := (rows 11 134 100 268 49 33 64 128 256), losses := [] }

theorem u16376 : Upper (D 6) (R 6) [10,132,96,260,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16377 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 332, targets := 2 },{ cop := 0, region := 48, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 134 100 268 49 34 81 209 337), lower := (rows 11 134 100 268 49 34 64 128 256), losses := [] }

theorem u16377 : Upper (D 6) (R 6) [10,132,96,260,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16378 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 100 268 49 48 67 195 323), lower := (rows 11 134 100 268 49 48 64 128 256), losses := [] }

theorem u16378 : Upper (D 6) (R 6) [10,132,96,260,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16378 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16379 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 134 100 268 49 96 83 147 275), lower := (rows 11 134 100 268 49 96 64 128 256), losses := [] }

theorem u16379 : Upper (D 6) (R 6) [10,132,96,260,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u16379
end Delivery.IrregularNine14.P06
