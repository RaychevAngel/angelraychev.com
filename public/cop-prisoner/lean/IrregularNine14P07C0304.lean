import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0081

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18240 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 28 140 273 96 226 162 418), lower := (rows 35 67 28 140 273 96 64 128 256), losses := [] }

theorem u18240 : Upper (D 7) (R 7) [34,65,24,132,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18241 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 339, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 28 140 273 160 98 226 354), lower := (rows 35 67 28 140 273 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 187 67 131 259), good := (rows 482 482 60 172 508 160 64 160 256) }] }

theorem u18241 : Upper (D 7) (R 7) [34,65,24,132,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18242 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 28 140 304 33 194 194 450), lower := (rows 35 67 28 140 304 33 64 128 256), losses := [] }

theorem u18242 : Upper (D 7) (R 7) [34,65,24,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18243 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 140 304 34 193 193 449), lower := (rows 35 67 28 140 304 34 64 128 256), losses := [] }

theorem u18243 : Upper (D 7) (R 7) [34,65,24,132,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18244 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 28 140 304 96 195 131 387), lower := (rows 35 67 28 140 304 96 64 128 256), losses := [] }

theorem u18244 : Upper (D 7) (R 7) [34,65,24,132,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18245 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 0, region := 66, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(4,7)], upper := (rows 35 67 28 140 304 160 67 195 323), lower := (rows 35 67 28 140 304 160 64 128 256), losses := [] }

theorem u18245 : Upper (D 7) (R 7) [34,65,24,132,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18246 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 28 168 208 33 326 390 262), lower := (rows 35 67 28 168 208 33 64 128 256), losses := [] }

theorem u18246 : Upper (D 7) (R 7) [34,65,24,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18247 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 168 208 34 325 389 261), lower := (rows 35 67 28 168 208 34 64 128 256), losses := [] }

theorem u18247 : Upper (D 7) (R 7) [34,65,24,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18248 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 28 168 208 36 323 387 259), lower := (rows 35 67 28 168 208 36 64 128 256), losses := [] }

theorem u18248 : Upper (D 7) (R 7) [34,65,24,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18248 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m18249_1 : Upper (D 7) (R 7) [34,65,24,160,192,256,1] 13 :=
  permutation_upper _ _ _ [34,65,24,160,192,2,256] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4897

theorem m18249_2 : Upper (D 7) (R 7) [34,65,24,160,192,256,2] 13 :=
  permutation_upper _ _ _ [34,65,24,160,192,1,256] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4896

theorem m18249_4 : Upper (D 7) (R 7) [34,65,24,160,192,256,4] 13 :=
  permutation_upper _ _ _ [34,65,24,160,192,4,256] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4898

def r18249 : Route 9 := (fun mask => (mask,id))

def c18249 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18249 : Upper (D 7) (R 7) [34,65,24,160,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,192,256] 13 (by decide) (choices 1) [1,2,4] r18249 c18249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m18249_1
  · exact m18249_2
  · exact m18249_4

def b18250 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 168 273 34 196 196 452), lower := (rows 35 67 28 168 273 34 64 128 256), losses := [] }

theorem u18250 : Upper (D 7) (R 7) [34,65,24,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18251 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 200, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 35 67 28 168 273 36 194 194 450), lower := (rows 35 67 28 168 273 36 64 128 256), losses := [] }

theorem u18251 : Upper (D 7) (R 7) [34,65,24,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18251 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18252 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 28 168 273 96 198 134 390), lower := (rows 35 67 28 168 273 96 64 128 256), losses := [] }

theorem u18252 : Upper (D 7) (R 7) [34,65,24,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18253 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 67 28 168 273 160 70 198 326), lower := (rows 35 67 28 168 273 160 64 128 256), losses := [] }

theorem u18253 : Upper (D 7) (R 7) [34,65,24,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18254 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 28 168 274 33 196 196 452), lower := (rows 35 67 28 168 274 33 64 128 256), losses := [] }

theorem u18254 : Upper (D 7) (R 7) [34,65,24,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18255 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(1,5),(3,1),(4,5)], upper := (rows 35 67 28 168 274 36 193 193 449), lower := (rows 35 67 28 168 274 36 64 128 256), losses := [] }

theorem u18255 : Upper (D 7) (R 7) [34,65,24,160,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18255 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18256 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 28 168 274 96 197 133 389), lower := (rows 35 67 28 168 274 96 64 128 256), losses := [] }

theorem u18256 : Upper (D 7) (R 7) [34,65,24,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18257 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 67 28 168 274 160 69 197 325), lower := (rows 35 67 28 168 274 160 64 128 256), losses := [] }

theorem u18257 : Upper (D 7) (R 7) [34,65,24,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18258 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 28 168 276 33 194 194 450), lower := (rows 35 67 28 168 276 33 64 128 256), losses := [] }

theorem u18258 : Upper (D 7) (R 7) [34,65,24,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18259 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 168 276 34 193 193 449), lower := (rows 35 67 28 168 276 34 64 128 256), losses := [] }

theorem u18259 : Upper (D 7) (R 7) [34,65,24,160,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18260 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 28 168 276 96 195 131 387), lower := (rows 35 67 28 168 276 96 64 128 256), losses := [] }

theorem u18260 : Upper (D 7) (R 7) [34,65,24,160,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18261 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 67 28 168 276 160 67 195 323), lower := (rows 35 67 28 168 276 160 64 128 256), losses := [] }

theorem u18261 : Upper (D 7) (R 7) [34,65,24,160,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18262 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 28 168 336 33 198 134 390), lower := (rows 35 67 28 168 336 33 64 128 256), losses := [] }

theorem u18262 : Upper (D 7) (R 7) [34,65,24,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18263 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 168 336 34 197 133 389), lower := (rows 35 67 28 168 336 34 64 128 256), losses := [] }

theorem u18263 : Upper (D 7) (R 7) [34,65,24,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18264 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 136, targets := 64 }], pairs := [(1,5),(3,6),(4,5)], upper := (rows 35 67 28 168 336 36 195 131 387), lower := (rows 35 67 28 168 336 36 64 128 256), losses := [] }

theorem u18264 : Upper (D 7) (R 7) [34,65,24,160,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18264 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18265 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 67 28 168 336 160 71 135 263), lower := (rows 35 67 28 168 336 160 64 128 256), losses := [] }

theorem u18265 : Upper (D 7) (R 7) [34,65,24,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18266 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 35 67 28 168 400 33 70 198 326), lower := (rows 35 67 28 168 400 33 64 128 256), losses := [] }

theorem u18266 : Upper (D 7) (R 7) [34,65,24,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18267 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 168 400 34 69 197 325), lower := (rows 35 67 28 168 400 34 64 128 256), losses := [] }

theorem u18267 : Upper (D 7) (R 7) [34,65,24,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18268 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 28 168 400 36 67 195 323), lower := (rows 35 67 28 168 400 36 64 128 256), losses := [] }

theorem u18268 : Upper (D 7) (R 7) [34,65,24,160,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18268 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18269 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 28 168 400 96 71 135 263), lower := (rows 35 67 28 168 400 96 64 128 256), losses := [] }

theorem u18269 : Upper (D 7) (R 7) [34,65,24,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18270 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 88 145 34 452 388 388), lower := (rows 35 67 44 88 145 34 64 128 256), losses := [] }

theorem u18270 : Upper (D 7) (R 7) [34,65,40,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18271 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 44 88 145 36 450 386 386), lower := (rows 35 67 44 88 145 36 64 128 256), losses := [] }

theorem u18271 : Upper (D 7) (R 7) [34,65,40,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18271 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18272 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(2,1)], upper := (rows 35 67 44 88 145 160 326 390 262), lower := (rows 35 67 44 88 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 66 44 124 176 160 64 160 256) },{ target := 1, region := (rows 1 0 12 8 16 176 64 128 256), good := (rows 33 65 44 124 177 160 64 160 256) }] }

theorem u18272 : Upper (D 7) (R 7) [34,65,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18273 : Route 9 := (fun mask => (mask,id))

def c18273 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18273 : Upper (D 7) (R 7) [34,65,40,80,129,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,129,256] 13 (by decide) (choices 1) [2,4,128] r18273 c18273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4899
  · exact u4900
  · exact u4901

def b18274 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 88 146 33 452 388 388), lower := (rows 35 67 44 88 146 33 64 128 256), losses := [] }

theorem u18274 : Upper (D 7) (R 7) [34,65,40,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18275 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 44 88 146 36 449 385 385), lower := (rows 35 67 44 88 146 36 64 128 256), losses := [] }

theorem u18275 : Upper (D 7) (R 7) [34,65,40,80,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18275 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18276 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,0)], upper := (rows 35 67 44 88 146 160 325 389 261), lower := (rows 35 67 44 88 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 66 44 124 178 160 64 160 256) }] }

theorem u18276 : Upper (D 7) (R 7) [34,65,40,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18277 : Route 9 := (fun mask => (mask,id))

def c18277 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18277 : Upper (D 7) (R 7) [34,65,40,80,130,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,130,256] 13 (by decide) (choices 1) [1,4,128] r18277 c18277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4902
  · exact u4903
  · exact u4904

def b18278 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 88 148 33 450 386 386), lower := (rows 35 67 44 88 148 33 64 128 256), losses := [] }

theorem u18278 : Upper (D 7) (R 7) [34,65,40,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18279 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 88 148 34 449 385 385), lower := (rows 35 67 44 88 148 34 64 128 256), losses := [] }

theorem u18279 : Upper (D 7) (R 7) [34,65,40,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18280 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 0, region := 322, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(1,5),(1,7)], upper := (rows 35 67 44 88 148 160 323 387 259), lower := (rows 35 67 44 88 148 160 64 128 256), losses := [] }

theorem u18280 : Upper (D 7) (R 7) [34,65,40,80,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18281 : Route 9 := (fun mask => (mask,id))

def c18281 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18281 : Upper (D 7) (R 7) [34,65,40,80,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,132,256] 13 (by decide) (choices 1) [1,2,128] r18281 c18281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4905
  · exact u4906
  · exact u4907

def b18282 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 88 273 34 196 132 388), lower := (rows 35 67 44 88 273 34 64 128 256), losses := [] }

theorem u18282 : Upper (D 7) (R 7) [34,65,40,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18283 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 44 88 273 36 194 130 386), lower := (rows 35 67 44 88 273 36 64 128 256), losses := [] }

theorem u18283 : Upper (D 7) (R 7) [34,65,40,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18283 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18284 : Route 9 := (fun mask => (mask,id))

def c18284 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18284 : Upper (D 7) (R 7) [34,65,40,80,257,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,257,128] 13 (by decide) (choices 1) [2,4,128] r18284 c18284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4908
  · exact u4909
  · exact u4910

def b18285 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 88 274 33 196 132 388), lower := (rows 35 67 44 88 274 33 64 128 256), losses := [] }

theorem u18285 : Upper (D 7) (R 7) [34,65,40,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18286 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 44 88 274 36 193 129 385), lower := (rows 35 67 44 88 274 36 64 128 256), losses := [] }

theorem u18286 : Upper (D 7) (R 7) [34,65,40,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18286 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18287 : Route 9 := (fun mask => (mask,id))

def c18287 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18287 : Upper (D 7) (R 7) [34,65,40,80,258,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,258,128] 13 (by decide) (choices 1) [1,4,128] r18287 c18287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4911
  · exact u4912
  · exact u4913

def b18288 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 88 276 33 194 130 386), lower := (rows 35 67 44 88 276 33 64 128 256), losses := [] }

theorem u18288 : Upper (D 7) (R 7) [34,65,40,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18289 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 88 276 34 193 129 385), lower := (rows 35 67 44 88 276 34 64 128 256), losses := [] }

theorem u18289 : Upper (D 7) (R 7) [34,65,40,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18290 : Route 9 := (fun mask => (mask,id))

def c18290 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18290 : Upper (D 7) (R 7) [34,65,40,80,260,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,260,128] 13 (by decide) (choices 1) [1,2,128] r18290 c18290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4914
  · exact u4915
  · exact u4916

def b18291 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 88 400 33 198 134 390), lower := (rows 35 67 44 88 400 33 64 128 256), losses := [] }

theorem u18291 : Upper (D 7) (R 7) [34,65,40,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18292 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 88 400 34 197 133 389), lower := (rows 35 67 44 88 400 34 64 128 256), losses := [] }

theorem u18292 : Upper (D 7) (R 7) [34,65,40,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18293 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 474, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 44 88 400 36 195 131 387), lower := (rows 35 67 44 88 400 36 64 128 256), losses := [] }

theorem u18293 : Upper (D 7) (R 7) [34,65,40,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18293 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18294 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(2,1)], upper := (rows 35 67 44 88 400 160 71 135 263), lower := (rows 35 67 44 88 400 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 66 44 124 432 160 64 160 256) },{ target := 1, region := (rows 1 0 12 8 16 176 64 128 256), good := (rows 33 65 44 124 432 160 64 160 256) }] }

theorem u18294 : Upper (D 7) (R 7) [34,65,40,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18295 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 137 146 36 336 464 336), lower := (rows 35 67 44 137 146 36 64 128 256), losses := [] }

theorem u18295 : Upper (D 7) (R 7) [34,65,40,129,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18295 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18296 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 67 44 137 146 48 324 452 324), lower := (rows 35 67 44 137 146 48 64 128 256), losses := [] }

theorem u18296 : Upper (D 7) (R 7) [34,65,40,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18296 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18297 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 44 137 146 96 340 404 276), lower := (rows 35 67 44 137 146 96 64 128 256), losses := [] }

theorem u18297 : Upper (D 7) (R 7) [34,65,40,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18298 : Route 9 := (fun mask => (mask,id))

def c18298 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18298 : Upper (D 7) (R 7) [34,65,40,129,130,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,130,256] 13 (by decide) (choices 1) [4,16] r18298 c18298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4917
  · exact u4918

def b18299 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 137 148 34 336 464 336), lower := (rows 35 67 44 137 148 34 64 128 256), losses := [] }

theorem u18299 : Upper (D 7) (R 7) [34,65,40,129,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u18299
end Delivery.IrregularNine14.P07
