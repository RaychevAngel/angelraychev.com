import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0088

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18240 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 386 100 41 22 96 85 149 277), lower := (rows 11 386 100 41 22 96 64 128 256), losses := [] }

theorem u18240 : Upper (D 6) (R 6) [10,384,96,33,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18241 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 386 100 41 81 34 84 148 276), lower := (rows 11 386 100 41 81 34 64 128 256), losses := [] }

theorem u18241 : Upper (D 6) (R 6) [10,384,96,33,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18242 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 386 100 41 81 36 86 150 278), lower := (rows 11 386 100 41 81 36 64 128 256), losses := [] }

theorem u18242 : Upper (D 6) (R 6) [10,384,96,33,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18243 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 386 100 41 81 48 70 134 262), lower := (rows 11 386 100 41 81 48 64 128 256), losses := [] }

theorem u18243 : Upper (D 6) (R 6) [10,384,96,33,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18243 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18244 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 386 100 41 82 33 84 148 276), lower := (rows 11 386 100 41 82 33 64 128 256), losses := [] }

theorem u18244 : Upper (D 6) (R 6) [10,384,96,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18245 : Route 9 := (fun mask => (mask,id))

def c18245 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18245 : Upper (D 6) (R 6) [10,384,96,33,66,4] 13 := by
  apply FastRouting.sound _ _ [10,384,96,33,66,4] 13 (by decide) (choices 1) [1,4,16] r18245 c18245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5304
  · exact u5305
  · exact u5306

def b18246 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 11 386 100 41 82 48 69 133 261), lower := (rows 11 386 100 41 82 48 64 128 256), losses := [] }

theorem u18246 : Upper (D 6) (R 6) [10,384,96,33,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18246 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18247 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 386 100 56 21 33 70 198 326), lower := (rows 11 386 100 56 21 33 64 128 256), losses := [] }

theorem u18247 : Upper (D 6) (R 6) [10,384,96,48,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18248 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(2,1),(3,0)], upper := (rows 11 386 100 56 21 34 69 197 325), lower := (rows 11 386 100 56 21 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 35 64 128 256), good := (rows 42 418 100 56 60 34 64 128 256) },{ target := 1, region := (rows 1 0 12 8 17 32 81 145 273), good := (rows 477 384 100 508 469 32 64 128 256) }] }

theorem u18248 : Upper (D 6) (R 6) [10,384,96,48,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18249 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 451, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 386 100 56 21 36 67 195 323), lower := (rows 11 386 100 56 21 36 64 128 256), losses := [] }

theorem u18249 : Upper (D 6) (R 6) [10,384,96,48,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18250 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 386 100 56 21 96 71 135 263), lower := (rows 11 386 100 56 21 96 64 128 256), losses := [] }

theorem u18250 : Upper (D 6) (R 6) [10,384,96,48,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18251 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 386 100 56 22 33 69 197 325), lower := (rows 11 386 100 56 22 33 64 128 256), losses := [] }

theorem u18251 : Upper (D 6) (R 6) [10,384,96,48,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18252 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 451, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 386 100 56 22 36 65 193 321), lower := (rows 11 386 100 56 22 36 64 128 256), losses := [] }

theorem u18252 : Upper (D 6) (R 6) [10,384,96,48,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18253 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 386 100 56 22 96 69 133 261), lower := (rows 11 386 100 56 22 96 64 128 256), losses := [] }

theorem u18253 : Upper (D 6) (R 6) [10,384,96,48,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18254 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 386, targets := 33 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(1,5),(2,1)], upper := (rows 11 386 100 56 81 33 70 134 262), lower := (rows 11 386 100 56 81 33 64 128 256), losses := [] }

theorem u18254 : Upper (D 6) (R 6) [10,384,96,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18255 : PairBound 9 := { available := 5, camps := [], pairs := [(2,0),(3,0),(3,2)], upper := (rows 11 386 100 56 81 34 69 133 261), lower := (rows 11 386 100 56 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 64 128 256), good := (rows 42 418 100 60 124 34 64 128 256) },{ target := 2, region := (rows 1 2 0 24 16 35 64 128 256), good := (rows 43 418 96 56 121 34 64 128 256) }] }

theorem u18255 : Upper (D 6) (R 6) [10,384,96,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18256 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 386 100 56 81 36 71 135 263), lower := (rows 11 386 100 56 81 36 64 128 256), losses := [] }

theorem u18256 : Upper (D 6) (R 6) [10,384,96,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18257 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 386 100 56 82 33 69 133 261), lower := (rows 11 386 100 56 82 33 64 128 256), losses := [] }

theorem u18257 : Upper (D 6) (R 6) [10,384,96,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18258 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 386 100 56 82 36 69 133 261), lower := (rows 11 386 100 56 82 36 64 128 256), losses := [] }

theorem u18258 : Upper (D 6) (R 6) [10,384,96,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18259 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 464, targets := 5 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(4,0),(4,2)], upper := (rows 25 35 69 14 146 36 352 480 352), lower := (rows 25 35 69 14 146 36 64 128 256), losses := [] }

theorem u18259 : Upper (D 6) (R 6) [24,33,65,6,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18260 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 2, region := 34, targets := 4 },{ cop := 3, region := 496, targets := 1 }], pairs := [(1,2),(2,1),(4,0)], upper := (rows 25 35 69 14 146 96 356 420 292), lower := (rows 25 35 69 14 146 96 64 128 256), losses := [] }

theorem u18260 : Upper (D 6) (R 6) [24,33,65,6,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18261 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 3, region := 496, targets := 1 }], pairs := [(2,1),(4,0)], upper := (rows 25 35 69 14 146 288 100 228 356), lower := (rows 25 35 69 14 146 288 64 128 256), losses := [] }

theorem u18261 : Upper (D 6) (R 6) [24,33,65,6,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18261 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18262 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 2 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 25 35 69 14 400 34 100 228 356), lower := (rows 25 35 69 14 400 34 64 128 256), losses := [] }

theorem u18262 : Upper (D 6) (R 6) [24,33,65,6,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18263 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 464, targets := 5 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(4,0),(4,2)], upper := (rows 25 35 69 14 400 36 98 226 354), lower := (rows 25 35 69 14 400 36 64 128 256), losses := [] }

theorem u18263 : Upper (D 6) (R 6) [24,33,65,6,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m18264_2 : Upper (D 6) (R 6) [24,33,65,6,384,64,2] 13 :=
  permutation_upper _ _ _ [24,33,65,6,384,4,32] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5308

theorem m18264_4 : Upper (D 6) (R 6) [24,33,65,6,384,64,4] 13 :=
  permutation_upper _ _ _ [24,33,65,6,384,2,32] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5307

def r18264 : Route 9 := (fun mask => (mask,id))

def c18264 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18264 : Upper (D 6) (R 6) [24,33,65,6,384,64] 13 := by
  apply FastRouting.sound _ _ [24,33,65,6,384,64] 13 (by decide) (choices 1) [2,4,32] r18264 c18264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m18264_2
  · exact m18264_4
  · exact u5309

def b18265 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 324, targets := 34 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 25 35 69 44 146 34 324 452 324), lower := (rows 25 35 69 44 146 34 64 128 256), losses := [] }

theorem u18265 : Upper (D 6) (R 6) [24,33,65,36,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18266 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 25 35 69 44 146 36 322 450 322), lower := (rows 25 35 69 44 146 36 64 128 256), losses := [] }

theorem u18266 : Upper (D 6) (R 6) [24,33,65,36,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18267 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 25 35 69 44 146 96 326 390 262), lower := (rows 25 35 69 44 146 96 64 128 256), losses := [] }

theorem u18267 : Upper (D 6) (R 6) [24,33,65,36,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18268 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 25 35 69 44 146 288 70 198 326), lower := (rows 25 35 69 44 146 288 64 128 256), losses := [] }

theorem u18268 : Upper (D 6) (R 6) [24,33,65,36,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18268 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18269 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 32 }], pairs := [(1,2),(1,6),(2,5)], upper := (rows 25 35 69 44 400 34 70 198 326), lower := (rows 25 35 69 44 400 34 64 128 256), losses := [] }

theorem u18269 : Upper (D 6) (R 6) [24,33,65,36,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18270 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 25 35 69 44 400 36 66 194 322), lower := (rows 25 35 69 44 400 36 64 128 256), losses := [] }

theorem u18270 : Upper (D 6) (R 6) [24,33,65,36,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18271 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 25 35 69 44 400 96 70 134 262), lower := (rows 25 35 69 44 400 96 64 128 256), losses := [] }

theorem u18271 : Upper (D 6) (R 6) [24,33,65,36,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18272 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(2,1),(3,0)], upper := (rows 25 35 69 138 274 36 100 228 356), lower := (rows 25 35 69 138 274 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 18 36 100 164 292), good := (rows 24 506 484 154 282 484 64 128 256) }] }

theorem u18272 : Upper (D 6) (R 6) [24,33,65,130,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18273 : Route 9 := (fun mask => (mask,id))

def c18273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18273 : Upper (D 6) (R 6) [24,33,65,130,258,64] 13 := by
  apply FastRouting.sound _ _ [24,33,65,130,258,64] 13 (by decide) (choices 1) [4,32] r18273 c18273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5310
  · exact u5311

def b18274 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 2 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 25 35 69 138 276 34 100 228 356), lower := (rows 25 35 69 138 276 34 64 128 256), losses := [] }

theorem u18274 : Upper (D 6) (R 6) [24,33,65,130,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18275 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 200, targets := 5 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,2)], upper := (rows 25 35 69 138 276 36 98 226 354), lower := (rows 25 35 69 138 276 36 64 128 256), losses := [] }

theorem u18275 : Upper (D 6) (R 6) [24,33,65,130,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m18276_2 : Upper (D 6) (R 6) [24,33,65,130,260,64,2] 13 :=
  permutation_upper _ _ _ [24,33,65,130,260,4,32] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5313

theorem m18276_4 : Upper (D 6) (R 6) [24,33,65,130,260,64,4] 13 :=
  permutation_upper _ _ _ [24,33,65,130,260,2,32] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5312

def r18276 : Route 9 := (fun mask => (mask,id))

def c18276 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18276 : Upper (D 6) (R 6) [24,33,65,130,260,64] 13 := by
  apply FastRouting.sound _ _ [24,33,65,130,260,64] 13 (by decide) (choices 1) [2,4,32] r18276 c18276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m18276_2
  · exact m18276_4
  · exact u5314

def b18277 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 68, targets := 34 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 25 35 69 138 304 34 68 196 324), lower := (rows 25 35 69 138 304 34 64 128 256), losses := [] }

theorem u18277 : Upper (D 6) (R 6) [24,33,65,130,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18278 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(2,5),(3,5)], upper := (rows 25 35 69 138 304 36 70 198 326), lower := (rows 25 35 69 138 304 36 64 128 256), losses := [] }

theorem u18278 : Upper (D 6) (R 6) [24,33,65,130,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18279 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(2,5),(3,5)], upper := (rows 25 35 69 138 304 96 70 134 262), lower := (rows 25 35 69 138 304 96 64 128 256), losses := [] }

theorem u18279 : Upper (D 6) (R 6) [24,33,65,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18280 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 2 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 25 35 69 138 336 34 100 164 292), lower := (rows 25 35 69 138 336 34 64 128 256), losses := [] }

theorem u18280 : Upper (D 6) (R 6) [24,33,65,130,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18281 : Route 9 := (fun mask => (mask,id))

def c18281 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18281 : Upper (D 6) (R 6) [24,33,65,130,320,4] 13 := by
  apply FastRouting.sound _ _ [24,33,65,130,320,4] 13 (by decide) (choices 1) [2,4,32] r18281 c18281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5315
  · exact u5316
  · exact u5317

def b18282 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 464, targets := 4 }], pairs := [(2,0),(4,0),(4,2)], upper := (rows 25 35 70 13 146 36 352 480 352), lower := (rows 25 35 70 13 146 36 64 128 256), losses := [] }

theorem u18282 : Upper (D 6) (R 6) [24,33,66,5,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18283 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 25 35 70 13 146 96 356 420 292), lower := (rows 25 35 70 13 146 96 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 100 64 128 256), good := (rows 27 35 98 43 146 96 96 128 256) }] }

theorem u18283 : Upper (D 6) (R 6) [24,33,66,5,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18284 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 25 35 70 13 146 288 100 228 356), lower := (rows 25 35 70 13 146 288 64 128 256), losses := [] }

theorem u18284 : Upper (D 6) (R 6) [24,33,66,5,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18284 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18285 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 70 13 400 34 100 228 356), lower := (rows 25 35 70 13 400 34 64 128 256), losses := [] }

theorem u18285 : Upper (D 6) (R 6) [24,33,66,5,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18286 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 464, targets := 4 }], pairs := [(2,0),(4,0),(4,2)], upper := (rows 25 35 70 13 400 36 98 226 354), lower := (rows 25 35 70 13 400 36 64 128 256), losses := [] }

theorem u18286 : Upper (D 6) (R 6) [24,33,66,5,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18287 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 25 35 70 13 400 96 102 166 294), lower := (rows 25 35 70 13 400 96 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 100 64 128 256), good := (rows 27 35 98 43 400 96 96 128 256) }] }

theorem u18287 : Upper (D 6) (R 6) [24,33,66,5,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18288 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 70 104 146 33 324 388 260), lower := (rows 25 35 70 104 146 33 64 128 256), losses := [] }

theorem u18288 : Upper (D 6) (R 6) [24,33,66,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18289 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 25 35 70 104 146 36 325 389 261), lower := (rows 25 35 70 104 146 36 64 128 256), losses := [] }

theorem u18289 : Upper (D 6) (R 6) [24,33,66,96,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18290 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 25 35 70 104 146 288 69 133 261), lower := (rows 25 35 70 104 146 288 64 128 256), losses := [] }

theorem u18290 : Upper (D 6) (R 6) [24,33,66,96,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18290 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18291 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 70 104 148 33 326 390 262), lower := (rows 25 35 70 104 148 33 64 128 256), losses := [] }

theorem u18291 : Upper (D 6) (R 6) [24,33,66,96,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18292 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 324, targets := 32 }], pairs := [(1,2),(1,6),(2,5)], upper := (rows 25 35 70 104 148 34 325 389 261), lower := (rows 25 35 70 104 148 34 64 128 256), losses := [] }

theorem u18292 : Upper (D 6) (R 6) [24,33,66,96,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18293 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 25 35 70 104 148 36 323 387 259), lower := (rows 25 35 70 104 148 36 64 128 256), losses := [] }

theorem u18293 : Upper (D 6) (R 6) [24,33,66,96,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18294 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 25 35 70 104 148 288 71 135 263), lower := (rows 25 35 70 104 148 288 64 128 256), losses := [] }

theorem u18294 : Upper (D 6) (R 6) [24,33,66,96,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18294 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18295 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 70 104 400 33 70 134 262), lower := (rows 25 35 70 104 400 33 64 128 256), losses := [] }

theorem u18295 : Upper (D 6) (R 6) [24,33,66,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18296 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 32 }], pairs := [(1,2),(1,6),(2,5)], upper := (rows 25 35 70 104 400 34 69 133 261), lower := (rows 25 35 70 104 400 34 64 128 256), losses := [] }

theorem u18296 : Upper (D 6) (R 6) [24,33,66,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18297 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 25 35 70 104 400 36 71 135 263), lower := (rows 25 35 70 104 400 36 64 128 256), losses := [] }

theorem u18297 : Upper (D 6) (R 6) [24,33,66,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18298 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 340, targets := 1 }], pairs := [(0,1),(2,0),(4,0)], upper := (rows 25 35 70 137 274 36 100 228 356), lower := (rows 25 35 70 137 274 36 64 128 256), losses := [{ target := 1, region := (rows 17 0 4 10 16 36 100 164 292), good := (rows 25 489 492 137 281 484 64 128 256) }] }

theorem u18298 : Upper (D 6) (R 6) [24,33,66,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18299 : Route 9 := (fun mask => (mask,id))

def c18299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18299 : Upper (D 6) (R 6) [24,33,66,129,258,64] 13 := by
  apply FastRouting.sound _ _ [24,33,66,129,258,64] 13 (by decide) (choices 1) [4,32] r18299 c18299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5318
  · exact u5319

#print axioms u18299
end Delivery.IrregularNine14.P06
