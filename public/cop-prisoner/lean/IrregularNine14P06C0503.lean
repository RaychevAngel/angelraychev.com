import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0195
import IrregularNine14P06C0196

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30180 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 393, targets := 32 },{ cop := 1, region := 393, targets := 64 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 100 140 112 291 323 387 259), lower := (rows 11 22 100 140 112 32 64 128 256), losses := [] }

theorem u30180 : Upper (D 6) (R 6) [10,20,96,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30181 : Route 9 := (fun mask => (mask,id))

def c30181 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30181 : Upper (D 6) (R 6) [10,20,96,132,257] 13 := by
  apply FastRouting.sound _ _ [10,20,96,132,257] 13 (by decide) (choices 1) [1,2,64] r30181 c30181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11707
  · exact u11708
  · exact u11709

def b30182 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 100 140 274 97 97 225 353), lower := (rows 11 22 100 140 274 32 64 128 256), losses := [] }

theorem u30182 : Upper (D 6) (R 6) [10,20,96,132,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30183 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 201, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 100 140 304 99 67 195 323), lower := (rows 11 22 100 140 304 32 64 128 256), losses := [] }

theorem u30183 : Upper (D 6) (R 6) [10,20,96,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30184 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 22 100 168 19 357 325 453 325), lower := (rows 11 22 100 168 19 32 64 128 256), losses := [] }

theorem u30184 : Upper (D 6) (R 6) [10,20,96,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30185 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 489, targets := 4 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 22 100 168 21 355 323 451 323), lower := (rows 11 22 100 168 21 32 64 128 256), losses := [] }

theorem u30185 : Upper (D 6) (R 6) [10,20,96,160,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30186 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 18, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 100 168 22 353 321 449 321), lower := (rows 11 22 100 168 22 32 64 128 256), losses := [] }

theorem u30186 : Upper (D 6) (R 6) [10,20,96,160,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30187 : Route 9 := (fun mask => (mask,id))

def c30187 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30187 : Upper (D 6) (R 6) [10,20,96,160,65] 13 := by
  apply FastRouting.sound _ _ [10,20,96,160,65] 13 (by decide) (choices 1) [1,2,4,256] r30187 c30187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11710
  · exact u11711
  · exact u11712
  · exact u11713

def b30188 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 18, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 11 22 100 168 82 293 325 389 261), lower := (rows 11 22 100 168 82 32 64 128 256), losses := [] }

theorem u30188 : Upper (D 6) (R 6) [10,20,96,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30189 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 18, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 11 22 100 168 84 291 323 387 259), lower := (rows 11 22 100 168 84 32 64 128 256), losses := [] }

theorem u30189 : Upper (D 6) (R 6) [10,20,96,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30190 : Route 9 := (fun mask => (mask,id))

def c30190 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30190 : Upper (D 6) (R 6) [10,20,96,160,257] 13 := by
  apply FastRouting.sound _ _ [10,20,96,160,257] 13 (by decide) (choices 1) [1,2,4,64] r30190 c30190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11714
  · exact u11715
  · exact u11716
  · exact u11717

def r30191 : Route 9 := (fun mask => (mask,id))

def c30191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30191 : Upper (D 6) (R 6) [10,20,96,160,258] 13 := by
  apply FastRouting.sound _ _ [10,20,96,160,258] 13 (by decide) (choices 1) [1,4,64] r30191 c30191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11718
  · exact u11719
  · exact u11720

def b30192 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 100 168 276 99 67 195 323), lower := (rows 11 22 100 168 276 32 64 128 256), losses := [] }

theorem u30192 : Upper (D 6) (R 6) [10,20,96,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30193 : Route 9 := (fun mask => (mask,id))

def c30193 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30193 : Upper (D 6) (R 6) [10,20,96,160,320] 13 := by
  apply FastRouting.sound _ _ [10,20,96,160,320] 13 (by decide) (choices 1) [1,2,4] r30193 c30193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11721
  · exact u11722
  · exact u11723

def b30194 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 22 100 392 19 101 101 229 357), lower := (rows 11 22 100 392 19 32 64 128 256), losses := [] }

theorem u30194 : Upper (D 6) (R 6) [10,20,96,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30195 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 100 392 21 99 99 227 355), lower := (rows 11 22 100 392 21 32 64 128 256), losses := [] }

theorem u30195 : Upper (D 6) (R 6) [10,20,96,384,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30196 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 18, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 100 392 22 97 97 225 353), lower := (rows 11 22 100 392 22 32 64 128 256), losses := [] }

theorem u30196 : Upper (D 6) (R 6) [10,20,96,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30197 : Route 9 := (fun mask => (mask,id))

def c30197 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30197 : Upper (D 6) (R 6) [10,20,96,384,33] 13 := by
  apply FastRouting.sound _ _ [10,20,96,384,33] 13 (by decide) (choices 1) [1,2,4,64] r30197 c30197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11724
  · exact u11725
  · exact u11726
  · exact u11727

def b30198 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 100 392 50 101 69 197 325), lower := (rows 11 22 100 392 50 32 64 128 256), losses := [] }

theorem u30198 : Upper (D 6) (R 6) [10,20,96,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30199 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 100 392 52 99 67 195 323), lower := (rows 11 22 100 392 52 32 64 128 256), losses := [] }

theorem u30199 : Upper (D 6) (R 6) [10,20,96,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30200 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 393, targets := 32 },{ cop := 1, region := 393, targets := 64 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 100 392 112 39 71 135 263), lower := (rows 11 22 100 392 112 32 64 128 256), losses := [] }

theorem u30200 : Upper (D 6) (R 6) [10,20,96,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30201 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 22 133 41 22 352 352 480 352), lower := (rows 11 22 133 41 22 32 64 128 256), losses := [] }

theorem u30201 : Upper (D 6) (R 6) [10,20,129,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30202 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 22 133 41 50 356 324 452 324), lower := (rows 11 22 133 41 50 32 64 128 256), losses := [] }

theorem u30202 : Upper (D 6) (R 6) [10,20,129,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30203 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 22 133 41 52 354 322 450 322), lower := (rows 11 22 133 41 52 32 64 128 256), losses := [] }

theorem u30203 : Upper (D 6) (R 6) [10,20,129,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30204 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 22 133 41 82 356 356 484 356), lower := (rows 11 22 133 41 82 32 64 128 256), losses := [] }

theorem u30204 : Upper (D 6) (R 6) [10,20,129,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30205 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 361, targets := 4 },{ cop := 2, region := 370, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 22 133 41 84 354 354 482 354), lower := (rows 11 22 133 41 84 32 64 128 256), losses := [] }

theorem u30205 : Upper (D 6) (R 6) [10,20,129,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30206 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 0, region := 452, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 11 22 133 41 112 358 326 454 326), lower := (rows 11 22 133 41 112 32 64 128 256), losses := [] }

theorem u30206 : Upper (D 6) (R 6) [10,20,129,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30207 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 2, region := 370, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 22 133 41 274 100 100 228 356), lower := (rows 11 22 133 41 274 32 64 128 256), losses := [] }

theorem u30207 : Upper (D 6) (R 6) [10,20,129,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30208 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 2, region := 370, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 22 133 41 276 98 98 226 354), lower := (rows 11 22 133 41 276 32 64 128 256), losses := [] }

theorem u30208 : Upper (D 6) (R 6) [10,20,129,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30209 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 0, region := 196, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 11 22 133 41 304 102 70 198 326), lower := (rows 11 22 133 41 304 32 64 128 256), losses := [] }

theorem u30209 : Upper (D 6) (R 6) [10,20,129,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30210 : Route 9 := (fun mask => (mask,id))

def c30210 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30210 : Upper (D 6) (R 6) [10,20,129,33,320] 13 := by
  apply FastRouting.sound _ _ [10,20,129,33,320] 13 (by decide) (choices 1) [2,4,64] r30210 c30210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11728
  · exact u11729
  · exact u11730

def b30211 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 19, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 22 133 44 19 352 352 480 352), lower := (rows 11 22 133 44 19 32 64 128 256), losses := [] }

theorem u30211 : Upper (D 6) (R 6) [10,20,129,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30212 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 19, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 22 133 44 49 354 322 450 322), lower := (rows 11 22 133 44 49 32 64 128 256), losses := [] }

theorem u30212 : Upper (D 6) (R 6) [10,20,129,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30213 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 19, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 22 133 44 50 353 321 449 321), lower := (rows 11 22 133 44 50 32 64 128 256), losses := [] }

theorem u30213 : Upper (D 6) (R 6) [10,20,129,36,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30214 : Route 9 := (fun mask => (mask,id))

def c30214 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30214 : Upper (D 6) (R 6) [10,20,129,36,65] 13 := by
  apply FastRouting.sound _ _ [10,20,129,36,65] 13 (by decide) (choices 1) [2,64,256] r30214 c30214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11731
  · exact u11732
  · exact u11733

def b30215 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 133 44 82 353 353 481 353), lower := (rows 11 22 133 44 82 32 64 128 256), losses := [] }

theorem u30215 : Upper (D 6) (R 6) [10,20,129,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30216 : Route 9 := (fun mask => (mask,id))

def c30216 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30216 : Upper (D 6) (R 6) [10,20,129,36,96] 13 := by
  apply FastRouting.sound _ _ [10,20,129,36,96] 13 (by decide) (choices 1) [1,2,64,256] r30216 c30216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11734
  · exact u11735
  · exact u11736
  · exact u11737

def r30217 : Route 9 := (fun mask => (mask,id))

def c30217 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30217 : Upper (D 6) (R 6) [10,20,129,36,257] 13 := by
  apply FastRouting.sound _ _ [10,20,129,36,257] 13 (by decide) (choices 1) [2,64] r30217 c30217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11738
  · exact u11739

def b30218 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 133 44 274 97 97 225 353), lower := (rows 11 22 133 44 274 32 64 128 256), losses := [] }

theorem u30218 : Upper (D 6) (R 6) [10,20,129,36,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30219 : Route 9 := (fun mask => (mask,id))

def c30219 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30219 : Upper (D 6) (R 6) [10,20,129,36,288] 13 := by
  apply FastRouting.sound _ _ [10,20,129,36,288] 13 (by decide) (choices 1) [1,2,64] r30219 c30219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11740
  · exact u11741
  · exact u11742

def r30220 : Route 9 := (fun mask => (mask,id))

def c30220 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30220 : Upper (D 6) (R 6) [10,20,129,36,320] 13 := by
  apply FastRouting.sound _ _ [10,20,129,36,320] 13 (by decide) (choices 1) [1,2,64] r30220 c30220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11743
  · exact u11744
  · exact u11745

def b30221 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 22 133 104 19 356 356 484 356), lower := (rows 11 22 133 104 19 32 64 128 256), losses := [] }

theorem u30221 : Upper (D 6) (R 6) [10,20,129,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30222 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 22 133 104 21 354 354 482 354), lower := (rows 11 22 133 104 21 32 64 128 256), losses := [] }

theorem u30222 : Upper (D 6) (R 6) [10,20,129,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30223 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 18, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 133 104 22 353 353 481 353), lower := (rows 11 22 133 104 22 32 64 128 256), losses := [] }

theorem u30223 : Upper (D 6) (R 6) [10,20,129,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30224 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 454, targets := 32 },{ cop := 1, region := 360, targets := 1 }], pairs := [(1,5),(2,5),(3,0)], upper := (rows 11 22 133 104 49 358 326 454 326), lower := (rows 11 22 133 104 49 32 64 128 256), losses := [] }

theorem u30224 : Upper (D 6) (R 6) [10,20,129,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30225 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 22 133 104 50 357 325 453 325), lower := (rows 11 22 133 104 50 32 64 128 256), losses := [] }

theorem u30225 : Upper (D 6) (R 6) [10,20,129,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30226 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 133 104 52 355 323 451 323), lower := (rows 11 22 133 104 52 32 64 128 256), losses := [] }

theorem u30226 : Upper (D 6) (R 6) [10,20,129,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30227 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 22 133 104 112 295 327 391 263), lower := (rows 11 22 133 104 112 32 64 128 256), losses := [] }

theorem u30227 : Upper (D 6) (R 6) [10,20,129,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30228 : Route 9 := (fun mask => (mask,id))

def c30228 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30228 : Upper (D 6) (R 6) [10,20,129,96,257] 13 := by
  apply FastRouting.sound _ _ [10,20,129,96,257] 13 (by decide) (choices 1) [2,4,64] r30228 c30228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11746
  · exact u11747
  · exact u11748

def r30229 : Route 9 := (fun mask => (mask,id))

def c30229 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30229 : Upper (D 6) (R 6) [10,20,129,96,258] 13 := by
  apply FastRouting.sound _ _ [10,20,129,96,258] 13 (by decide) (choices 1) [1,4,64] r30229 c30229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11749
  · exact u11750
  · exact u11751

def b30230 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 133 104 276 99 99 227 355), lower := (rows 11 22 133 104 276 32 64 128 256), losses := [] }

theorem u30230 : Upper (D 6) (R 6) [10,20,129,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30231 : Route 9 := (fun mask => (mask,id))

def c30231 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30231 : Upper (D 6) (R 6) [10,20,129,96,288] 13 := by
  apply FastRouting.sound _ _ [10,20,129,96,288] 13 (by decide) (choices 1) [1,2,4,64] r30231 c30231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11752
  · exact u11753
  · exact u11754
  · exact u11755

def b30232 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 22 133 265 22 96 96 224 352), lower := (rows 11 22 133 265 22 32 64 128 256), losses := [] }

theorem u30232 : Upper (D 6) (R 6) [10,20,129,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30233 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 114, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 22 133 265 50 100 100 228 356), lower := (rows 11 22 133 265 50 32 64 128 256), losses := [] }

theorem u30233 : Upper (D 6) (R 6) [10,20,129,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30234 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 361, targets := 4 },{ cop := 2, region := 114, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 22 133 265 52 98 98 226 354), lower := (rows 11 22 133 265 52 32 64 128 256), losses := [] }

theorem u30234 : Upper (D 6) (R 6) [10,20,129,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30235 : Route 9 := (fun mask => (mask,id))

def c30235 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30235 : Upper (D 6) (R 6) [10,20,129,257,96] 13 := by
  apply FastRouting.sound _ _ [10,20,129,257,96] 13 (by decide) (choices 1) [2,4,64] r30235 c30235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11756
  · exact u11757
  · exact u11758

def b30236 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 19, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 22 133 268 19 96 96 224 352), lower := (rows 11 22 133 268 19 32 64 128 256), losses := [] }

theorem u30236 : Upper (D 6) (R 6) [10,20,129,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30237 : Route 9 := (fun mask => (mask,id))

def c30237 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30237 : Upper (D 6) (R 6) [10,20,129,260,33] 13 := by
  apply FastRouting.sound _ _ [10,20,129,260,33] 13 (by decide) (choices 1) [2,64] r30237 c30237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11759
  · exact u11760

def b30238 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 112, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 22 133 268 50 97 97 225 353), lower := (rows 11 22 133 268 50 32 64 128 256), losses := [] }

theorem u30238 : Upper (D 6) (R 6) [10,20,129,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30239 : Route 9 := (fun mask => (mask,id))

def c30239 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30239 : Upper (D 6) (R 6) [10,20,129,260,96] 13 := by
  apply FastRouting.sound _ _ [10,20,129,260,96] 13 (by decide) (choices 1) [1,2,64] r30239 c30239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11761
  · exact u11762
  · exact u11763

#print axioms u30239
end Delivery.IrregularNine14.P06
