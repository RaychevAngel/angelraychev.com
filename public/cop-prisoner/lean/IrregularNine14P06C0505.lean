import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0197

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30300 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 164 73 52 355 323 451 323), lower := (rows 11 22 164 73 52 32 64 128 256), losses := [] }

theorem u30300 : Upper (D 6) (R 6) [10,20,160,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30301 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 22 164 73 81 294 358 422 294), lower := (rows 11 22 164 73 81 32 64 128 256), losses := [] }

theorem u30301 : Upper (D 6) (R 6) [10,20,160,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30302 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 22 164 73 82 293 357 421 293), lower := (rows 11 22 164 73 82 32 64 128 256), losses := [] }

theorem u30302 : Upper (D 6) (R 6) [10,20,160,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30303 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 11, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 22 164 73 84 291 355 419 291), lower := (rows 11 22 164 73 84 32 64 128 256), losses := [] }

theorem u30303 : Upper (D 6) (R 6) [10,20,160,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30304 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 0, region := 420, targets := 64 }], pairs := [(0,5),(2,6),(3,5)], upper := (rows 11 22 164 73 112 295 327 391 263), lower := (rows 11 22 164 73 112 32 64 128 256), losses := [] }

theorem u30304 : Upper (D 6) (R 6) [10,20,160,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30305 : Route 9 := (fun mask => (mask,id))

def c30305 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30305 : Upper (D 6) (R 6) [10,20,160,65,257] 13 := by
  apply FastRouting.sound _ _ [10,20,160,65,257] 13 (by decide) (choices 1) [2,4,64] r30305 c30305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11821
  · exact u11822
  · exact u11823

def r30306 : Route 9 := (fun mask => (mask,id))

def c30306 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30306 : Upper (D 6) (R 6) [10,20,160,65,258] 13 := by
  apply FastRouting.sound _ _ [10,20,160,65,258] 13 (by decide) (choices 1) [1,4,64] r30306 c30306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11824
  · exact u11825
  · exact u11826

def b30307 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 164 73 276 99 99 227 355), lower := (rows 11 22 164 73 276 32 64 128 256), losses := [] }

theorem u30307 : Upper (D 6) (R 6) [10,20,160,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30308 : Route 9 := (fun mask => (mask,id))

def c30308 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30308 : Upper (D 6) (R 6) [10,20,160,65,288] 13 := by
  apply FastRouting.sound _ _ [10,20,160,65,288] 13 (by decide) (choices 1) [1,2,4,64] r30308 c30308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11827
  · exact u11828
  · exact u11829
  · exact u11830

def r30309 : Route 9 := (fun mask => (mask,id))

def c30309 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30309 : Upper (D 6) (R 6) [10,20,160,65,320] 13 := by
  apply FastRouting.sound _ _ [10,20,160,65,320] 13 (by decide) (choices 1) [1,2,4] r30309 c30309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11831
  · exact u11832
  · exact u11833

def b30310 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 19, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 22 164 76 19 353 353 481 353), lower := (rows 11 22 164 76 19 32 64 128 256), losses := [] }

theorem u30310 : Upper (D 6) (R 6) [10,20,160,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30311 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 164 76 49 355 323 451 323), lower := (rows 11 22 164 76 49 32 64 128 256), losses := [] }

theorem u30311 : Upper (D 6) (R 6) [10,20,160,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30312 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 164 76 50 353 321 449 321), lower := (rows 11 22 164 76 50 32 64 128 256), losses := [] }

theorem u30312 : Upper (D 6) (R 6) [10,20,160,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30313 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 22 164 76 81 291 355 419 291), lower := (rows 11 22 164 76 81 32 64 128 256), losses := [] }

theorem u30313 : Upper (D 6) (R 6) [10,20,160,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30314 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 22 164 76 82 289 353 417 289), lower := (rows 11 22 164 76 82 32 64 128 256), losses := [] }

theorem u30314 : Upper (D 6) (R 6) [10,20,160,68,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30315 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 164 76 112 291 323 387 259), lower := (rows 11 22 164 76 112 32 64 128 256), losses := [] }

theorem u30315 : Upper (D 6) (R 6) [10,20,160,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30316 : Route 9 := (fun mask => (mask,id))

def c30316 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30316 : Upper (D 6) (R 6) [10,20,160,68,257] 13 := by
  apply FastRouting.sound _ _ [10,20,160,68,257] 13 (by decide) (choices 1) [1,2,64] r30316 c30316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11834
  · exact u11835
  · exact u11836

def b30317 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 164 76 274 97 97 225 353), lower := (rows 11 22 164 76 274 32 64 128 256), losses := [] }

theorem u30317 : Upper (D 6) (R 6) [10,20,160,68,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30318 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 164 76 304 99 67 195 323), lower := (rows 11 22 164 76 304 32 64 128 256), losses := [] }

theorem u30318 : Upper (D 6) (R 6) [10,20,160,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30319 : Route 9 := (fun mask => (mask,id))

def c30319 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30319 : Upper (D 6) (R 6) [10,20,160,68,320] 13 := by
  apply FastRouting.sound _ _ [10,20,160,68,320] 13 (by decide) (choices 1) [1,2] r30319 c30319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11837
  · exact u11838

def b30320 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 22 164 104 19 357 325 453 325), lower := (rows 11 22 164 104 19 32 64 128 256), losses := [] }

theorem u30320 : Upper (D 6) (R 6) [10,20,160,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30321 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 361, targets := 4 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 22 164 104 21 355 323 451 323), lower := (rows 11 22 164 104 21 32 64 128 256), losses := [] }

theorem u30321 : Upper (D 6) (R 6) [10,20,160,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30322 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 18, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 164 104 22 353 321 449 321), lower := (rows 11 22 164 104 22 32 64 128 256), losses := [] }

theorem u30322 : Upper (D 6) (R 6) [10,20,160,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30323 : Route 9 := (fun mask => (mask,id))

def c30323 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30323 : Upper (D 6) (R 6) [10,20,160,96,65] 13 := by
  apply FastRouting.sound _ _ [10,20,160,96,65] 13 (by decide) (choices 1) [1,2,4,256] r30323 c30323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11839
  · exact u11840
  · exact u11841
  · exact u11842

def b30324 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 420, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 22 164 104 82 293 325 389 261), lower := (rows 11 22 164 104 82 32 64 128 256), losses := [] }

theorem u30324 : Upper (D 6) (R 6) [10,20,160,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30325 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 164 104 84 291 323 387 259), lower := (rows 11 22 164 104 84 32 64 128 256), losses := [] }

theorem u30325 : Upper (D 6) (R 6) [10,20,160,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30326 : Route 9 := (fun mask => (mask,id))

def c30326 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30326 : Upper (D 6) (R 6) [10,20,160,96,257] 13 := by
  apply FastRouting.sound _ _ [10,20,160,96,257] 13 (by decide) (choices 1) [1,2,4,64] r30326 c30326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11843
  · exact u11844
  · exact u11845
  · exact u11846

def r30327 : Route 9 := (fun mask => (mask,id))

def c30327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30327 : Upper (D 6) (R 6) [10,20,160,96,258] 13 := by
  apply FastRouting.sound _ _ [10,20,160,96,258] 13 (by decide) (choices 1) [1,4,64] r30327 c30327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11847
  · exact u11848
  · exact u11849

def b30328 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 164 104 276 99 67 195 323), lower := (rows 11 22 164 104 276 32 64 128 256), losses := [] }

theorem u30328 : Upper (D 6) (R 6) [10,20,160,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30329 : Route 9 := (fun mask => (mask,id))

def c30329 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30329 : Upper (D 6) (R 6) [10,20,160,96,320] 13 := by
  apply FastRouting.sound _ _ [10,20,160,96,320] 13 (by decide) (choices 1) [1,2,4] r30329 c30329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11850
  · exact u11851
  · exact u11852

def b30330 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 22 164 265 19 100 100 228 356), lower := (rows 11 22 164 265 19 32 64 128 256), losses := [] }

theorem u30330 : Upper (D 6) (R 6) [10,20,160,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30331 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 361, targets := 4 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 22 164 265 21 98 98 226 354), lower := (rows 11 22 164 265 21 32 64 128 256), losses := [] }

theorem u30331 : Upper (D 6) (R 6) [10,20,160,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30332 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 18, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 164 265 22 97 97 225 353), lower := (rows 11 22 164 265 22 32 64 128 256), losses := [] }

theorem u30332 : Upper (D 6) (R 6) [10,20,160,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30333 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 4, region := 198, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 22 164 265 49 102 70 198 326), lower := (rows 11 22 164 265 49 32 64 128 256), losses := [] }

theorem u30333 : Upper (D 6) (R 6) [10,20,160,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30334 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 164 265 50 101 69 197 325), lower := (rows 11 22 164 265 50 32 64 128 256), losses := [] }

theorem u30334 : Upper (D 6) (R 6) [10,20,160,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30335 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 164 265 52 99 67 195 323), lower := (rows 11 22 164 265 52 32 64 128 256), losses := [] }

theorem u30335 : Upper (D 6) (R 6) [10,20,160,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30336 : Route 9 := (fun mask => (mask,id))

def c30336 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30336 : Upper (D 6) (R 6) [10,20,160,257,65] 13 := by
  apply FastRouting.sound _ _ [10,20,160,257,65] 13 (by decide) (choices 1) [2,4,64] r30336 c30336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11853
  · exact u11854
  · exact u11855

def r30337 : Route 9 := (fun mask => (mask,id))

def c30337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30337 : Upper (D 6) (R 6) [10,20,160,257,66] 13 := by
  apply FastRouting.sound _ _ [10,20,160,257,66] 13 (by decide) (choices 1) [1,4,64] r30337 c30337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11856
  · exact u11857
  · exact u11858

def b30338 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 164 265 84 99 99 227 355), lower := (rows 11 22 164 265 84 32 64 128 256), losses := [] }

theorem u30338 : Upper (D 6) (R 6) [10,20,160,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30339 : Route 9 := (fun mask => (mask,id))

def c30339 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30339 : Upper (D 6) (R 6) [10,20,160,257,96] 13 := by
  apply FastRouting.sound _ _ [10,20,160,257,96] 13 (by decide) (choices 1) [1,2,4,64] r30339 c30339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11859
  · exact u11860
  · exact u11861
  · exact u11862

def b30340 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 19, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 22 164 268 19 97 97 225 353), lower := (rows 11 22 164 268 19 32 64 128 256), losses := [] }

theorem u30340 : Upper (D 6) (R 6) [10,20,160,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30341 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 164 268 49 99 67 195 323), lower := (rows 11 22 164 268 49 32 64 128 256), losses := [] }

theorem u30341 : Upper (D 6) (R 6) [10,20,160,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30342 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 164 268 50 97 65 193 321), lower := (rows 11 22 164 268 50 32 64 128 256), losses := [] }

theorem u30342 : Upper (D 6) (R 6) [10,20,160,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30343 : Route 9 := (fun mask => (mask,id))

def c30343 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30343 : Upper (D 6) (R 6) [10,20,160,260,65] 13 := by
  apply FastRouting.sound _ _ [10,20,160,260,65] 13 (by decide) (choices 1) [1,2,64] r30343 c30343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11863
  · exact u11864
  · exact u11865

def b30344 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 112, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 164 268 82 97 97 225 353), lower := (rows 11 22 164 268 82 32 64 128 256), losses := [] }

theorem u30344 : Upper (D 6) (R 6) [10,20,160,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30345 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 329, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 164 268 112 99 67 195 323), lower := (rows 11 22 164 268 112 32 64 128 256), losses := [] }

theorem u30345 : Upper (D 6) (R 6) [10,20,160,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30346 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 22 164 296 19 101 69 197 325), lower := (rows 11 22 164 296 19 32 64 128 256), losses := [] }

theorem u30346 : Upper (D 6) (R 6) [10,20,160,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30347 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 361, targets := 4 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 22 164 296 21 99 67 195 323), lower := (rows 11 22 164 296 21 32 64 128 256), losses := [] }

theorem u30347 : Upper (D 6) (R 6) [10,20,160,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30348 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 18, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 164 296 22 97 65 193 321), lower := (rows 11 22 164 296 22 32 64 128 256), losses := [] }

theorem u30348 : Upper (D 6) (R 6) [10,20,160,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30349 : Route 9 := (fun mask => (mask,id))

def c30349 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30349 : Upper (D 6) (R 6) [10,20,160,288,65] 13 := by
  apply FastRouting.sound _ _ [10,20,160,288,65] 13 (by decide) (choices 1) [1,2,4,64] r30349 c30349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11866
  · exact u11867
  · exact u11868
  · exact u11869

def r30350 : Route 9 := (fun mask => (mask,id))

def c30350 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30350 : Upper (D 6) (R 6) [10,20,160,288,66] 13 := by
  apply FastRouting.sound _ _ [10,20,160,288,66] 13 (by decide) (choices 1) [1,4,64] r30350 c30350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11870
  · exact u11871
  · exact u11872

def b30351 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 164 296 84 99 67 195 323), lower := (rows 11 22 164 296 84 32 64 128 256), losses := [] }

theorem u30351 : Upper (D 6) (R 6) [10,20,160,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30352 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 22 164 328 19 101 101 229 357), lower := (rows 11 22 164 328 19 32 64 128 256), losses := [] }

theorem u30352 : Upper (D 6) (R 6) [10,20,160,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30353 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 164 328 21 99 99 227 355), lower := (rows 11 22 164 328 21 32 64 128 256), losses := [] }

theorem u30353 : Upper (D 6) (R 6) [10,20,160,320,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30354 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 18, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 164 328 22 97 97 225 353), lower := (rows 11 22 164 328 22 32 64 128 256), losses := [] }

theorem u30354 : Upper (D 6) (R 6) [10,20,160,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30355 : Route 9 := (fun mask => (mask,id))

def c30355 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30355 : Upper (D 6) (R 6) [10,20,160,320,33] 13 := by
  apply FastRouting.sound _ _ [10,20,160,320,33] 13 (by decide) (choices 1) [1,2,4,64] r30355 c30355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11873
  · exact u11874
  · exact u11875
  · exact u11876

def b30356 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 164 328 50 101 69 197 325), lower := (rows 11 22 164 328 50 32 64 128 256), losses := [] }

theorem u30356 : Upper (D 6) (R 6) [10,20,160,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30357 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 164 328 52 99 67 195 323), lower := (rows 11 22 164 328 52 32 64 128 256), losses := [] }

theorem u30357 : Upper (D 6) (R 6) [10,20,160,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30358 : Route 9 := (fun mask => (mask,id))

def c30358 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30358 : Upper (D 6) (R 6) [10,20,160,320,65] 13 := by
  apply FastRouting.sound _ _ [10,20,160,320,65] 13 (by decide) (choices 1) [1,2,4] r30358 c30358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11877
  · exact u11878
  · exact u11879

def b30359 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 164, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 22 164 328 82 37 101 165 293), lower := (rows 11 22 164 328 82 32 64 128 256), losses := [] }

theorem u30359 : Upper (D 6) (R 6) [10,20,160,320,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u30359
end Delivery.IrregularNine14.P06
