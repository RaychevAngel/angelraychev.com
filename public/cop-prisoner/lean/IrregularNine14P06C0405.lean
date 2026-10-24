import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0124
import IrregularNine14P06C0125

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24300 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 276, targets := 64 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 276 73 22 96 101 165 293), lower := (rows 35 138 276 73 22 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 16 104 64 128 256), good := (rows 35 171 272 105 19 96 96 128 256) }] }

theorem u24300 : Upper (D 6) (R 6) [34,136,272,65,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24301 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 276 73 52 33 70 198 326), lower := (rows 35 138 276 73 52 33 64 128 256), losses := [] }

theorem u24301 : Upper (D 6) (R 6) [34,136,272,65,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24302 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 276 73 52 34 69 197 325), lower := (rows 35 138 276 73 52 34 64 128 256), losses := [] }

theorem u24302 : Upper (D 6) (R 6) [34,136,272,65,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24303 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 276 73 52 36 67 195 323), lower := (rows 35 138 276 73 52 36 64 128 256), losses := [] }

theorem u24303 : Upper (D 6) (R 6) [34,136,272,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24304 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 276, targets := 64 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 276 73 52 96 71 135 263), lower := (rows 35 138 276 73 52 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 16 104 64 128 256), good := (rows 35 171 272 105 48 96 96 128 256) }] }

theorem u24304 : Upper (D 6) (R 6) [34,136,272,65,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24305 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 276 73 82 33 100 164 292), lower := (rows 35 138 276 73 82 33 64 128 256), losses := [] }

theorem u24305 : Upper (D 6) (R 6) [34,136,272,65,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24306 : Route 9 := (fun mask => (mask,id))

def c24306 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24306 : Upper (D 6) (R 6) [34,136,272,65,66,4] 13 := by
  apply FastRouting.sound _ _ [34,136,272,65,66,4] 13 (by decide) (choices 1) [1,4,32] r24306 c24306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7499
  · exact u7500
  · exact u7501

def b24307 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 276 73 84 33 102 166 294), lower := (rows 35 138 276 73 84 33 64 128 256), losses := [] }

theorem u24307 : Upper (D 6) (R 6) [34,136,272,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24308 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 276 73 84 34 101 165 293), lower := (rows 35 138 276 73 84 34 64 128 256), losses := [] }

theorem u24308 : Upper (D 6) (R 6) [34,136,272,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24309 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 276 73 84 36 99 163 291), lower := (rows 35 138 276 73 84 36 64 128 256), losses := [] }

theorem u24309 : Upper (D 6) (R 6) [34,136,272,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24310 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 276 73 112 33 70 134 262), lower := (rows 35 138 276 73 112 33 64 128 256), losses := [] }

theorem u24310 : Upper (D 6) (R 6) [34,136,272,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24311 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 276 73 112 34 69 133 261), lower := (rows 35 138 276 73 112 34 64 128 256), losses := [] }

theorem u24311 : Upper (D 6) (R 6) [34,136,272,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24312 : Route 9 := (fun mask => (mask,id))

def c24312 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24312 : Upper (D 6) (R 6) [34,136,272,65,96,4] 13 := by
  apply FastRouting.sound _ _ [34,136,272,65,96,4] 13 (by decide) (choices 1) [1,2,4] r24312 c24312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7502
  · exact u7503
  · exact u7504

def b24313 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 276 74 21 33 100 228 356), lower := (rows 35 138 276 74 21 33 64 128 256), losses := [] }

theorem u24313 : Upper (D 6) (R 6) [34,136,272,66,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24314 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 276 74 21 36 97 225 353), lower := (rows 35 138 276 74 21 36 64 128 256), losses := [] }

theorem u24314 : Upper (D 6) (R 6) [34,136,272,66,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24315 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 276, targets := 2 },{ cop := 0, region := 276, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 276 74 21 96 101 165 293), lower := (rows 35 138 276 74 21 96 64 128 256), losses := [] }

theorem u24315 : Upper (D 6) (R 6) [34,136,272,66,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24316 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 276 74 52 33 69 197 325), lower := (rows 35 138 276 74 52 33 64 128 256), losses := [] }

theorem u24316 : Upper (D 6) (R 6) [34,136,272,66,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24317 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 276 74 52 36 65 193 321), lower := (rows 35 138 276 74 52 36 64 128 256), losses := [] }

theorem u24317 : Upper (D 6) (R 6) [34,136,272,66,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24318 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 2 },{ cop := 0, region := 276, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 276 74 52 96 69 133 261), lower := (rows 35 138 276 74 52 96 64 128 256), losses := [] }

theorem u24318 : Upper (D 6) (R 6) [34,136,272,66,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24319 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 276 74 84 33 101 165 293), lower := (rows 35 138 276 74 84 33 64 128 256), losses := [] }

theorem u24319 : Upper (D 6) (R 6) [34,136,272,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24320 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 276 74 84 36 97 161 289), lower := (rows 35 138 276 74 84 36 64 128 256), losses := [] }

theorem u24320 : Upper (D 6) (R 6) [34,136,272,66,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24321 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 276 74 112 33 69 133 261), lower := (rows 35 138 276 74 112 33 64 128 256), losses := [] }

theorem u24321 : Upper (D 6) (R 6) [34,136,272,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24322 : Route 9 := (fun mask => (mask,id))

def c24322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24322 : Upper (D 6) (R 6) [34,136,272,66,96,4] 13 := by
  apply FastRouting.sound _ _ [34,136,272,66,96,4] 13 (by decide) (choices 1) [1,4] r24322 c24322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7505
  · exact u7506

def b24323 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 276 76 21 33 98 226 354), lower := (rows 35 138 276 76 21 33 64 128 256), losses := [] }

theorem u24323 : Upper (D 6) (R 6) [34,136,272,68,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24324 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 276 76 21 34 97 225 353), lower := (rows 35 138 276 76 21 34 64 128 256), losses := [] }

theorem u24324 : Upper (D 6) (R 6) [34,136,272,68,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24325 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 276 76 21 96 99 163 291), lower := (rows 35 138 276 76 21 96 64 128 256), losses := [] }

theorem u24325 : Upper (D 6) (R 6) [34,136,272,68,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24326 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 276 76 22 33 97 225 353), lower := (rows 35 138 276 76 22 33 64 128 256), losses := [] }

theorem u24326 : Upper (D 6) (R 6) [34,136,272,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24327 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 276 76 22 96 97 161 289), lower := (rows 35 138 276 76 22 96 64 128 256), losses := [] }

theorem u24327 : Upper (D 6) (R 6) [34,136,272,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24328 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 276 76 52 33 67 195 323), lower := (rows 35 138 276 76 52 33 64 128 256), losses := [] }

theorem u24328 : Upper (D 6) (R 6) [34,136,272,68,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24329 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 276 76 52 34 65 193 321), lower := (rows 35 138 276 76 52 34 64 128 256), losses := [] }

theorem u24329 : Upper (D 6) (R 6) [34,136,272,68,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24330 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 3, region := 48, targets := 1 }], pairs := [(2,6),(4,0),(4,6)], upper := (rows 35 138 276 76 52 96 67 131 259), lower := (rows 35 138 276 76 52 96 64 128 256), losses := [] }

theorem u24330 : Upper (D 6) (R 6) [34,136,272,68,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24331 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 138 276 76 81 33 102 166 294), lower := (rows 35 138 276 76 81 33 64 128 256), losses := [] }

theorem u24331 : Upper (D 6) (R 6) [34,136,272,68,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24332 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 276 76 81 34 101 165 293), lower := (rows 35 138 276 76 81 34 64 128 256), losses := [] }

theorem u24332 : Upper (D 6) (R 6) [34,136,272,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24333 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 0, region := 80, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 35 138 276 76 81 36 99 163 291), lower := (rows 35 138 276 76 81 36 64 128 256), losses := [] }

theorem u24333 : Upper (D 6) (R 6) [34,136,272,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24334 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 138 276 76 112 33 71 135 263), lower := (rows 35 138 276 76 112 33 64 128 256), losses := [] }

theorem u24334 : Upper (D 6) (R 6) [34,136,272,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24335 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 276 76 112 34 69 133 261), lower := (rows 35 138 276 76 112 34 64 128 256), losses := [] }

theorem u24335 : Upper (D 6) (R 6) [34,136,272,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24336 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 138 276 76 112 36 67 131 259), lower := (rows 35 138 276 76 112 36 64 128 256), losses := [] }

theorem u24336 : Upper (D 6) (R 6) [34,136,272,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24337 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 276 104 21 33 70 198 326), lower := (rows 35 138 276 104 21 33 64 128 256), losses := [] }

theorem u24337 : Upper (D 6) (R 6) [34,136,272,96,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24338 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 276 104 21 34 69 197 325), lower := (rows 35 138 276 104 21 34 64 128 256), losses := [] }

theorem u24338 : Upper (D 6) (R 6) [34,136,272,96,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24339 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 276 104 21 36 67 195 323), lower := (rows 35 138 276 104 21 36 64 128 256), losses := [] }

theorem u24339 : Upper (D 6) (R 6) [34,136,272,96,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24340 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 138 276 104 21 96 71 135 263), lower := (rows 35 138 276 104 21 96 64 128 256), losses := [] }

theorem u24340 : Upper (D 6) (R 6) [34,136,272,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24341 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 276 104 22 33 69 197 325), lower := (rows 35 138 276 104 22 33 64 128 256), losses := [] }

theorem u24341 : Upper (D 6) (R 6) [34,136,272,96,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24342 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 276 104 22 36 65 193 321), lower := (rows 35 138 276 104 22 36 64 128 256), losses := [] }

theorem u24342 : Upper (D 6) (R 6) [34,136,272,96,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24343 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 138 276 104 22 96 69 133 261), lower := (rows 35 138 276 104 22 96 64 128 256), losses := [] }

theorem u24343 : Upper (D 6) (R 6) [34,136,272,96,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24344 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 276 104 81 33 70 134 262), lower := (rows 35 138 276 104 81 33 64 128 256), losses := [] }

theorem u24344 : Upper (D 6) (R 6) [34,136,272,96,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24345 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 276 104 81 34 69 133 261), lower := (rows 35 138 276 104 81 34 64 128 256), losses := [] }

theorem u24345 : Upper (D 6) (R 6) [34,136,272,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24346 : Route 9 := (fun mask => (mask,id))

def c24346 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24346 : Upper (D 6) (R 6) [34,136,272,96,65,4] 13 := by
  apply FastRouting.sound _ _ [34,136,272,96,65,4] 13 (by decide) (choices 1) [1,2,4] r24346 c24346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7507
  · exact u7508
  · exact u7509

def b24347 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 276 104 84 33 71 135 263), lower := (rows 35 138 276 104 84 33 64 128 256), losses := [] }

theorem u24347 : Upper (D 6) (R 6) [34,136,272,96,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24348 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 276 104 84 34 69 133 261), lower := (rows 35 138 276 104 84 34 64 128 256), losses := [] }

theorem u24348 : Upper (D 6) (R 6) [34,136,272,96,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24349 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 276 104 84 36 67 131 259), lower := (rows 35 138 276 104 84 36 64 128 256), losses := [] }

theorem u24349 : Upper (D 6) (R 6) [34,136,272,96,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24350 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 292 13 81 34 84 212 340), lower := (rows 35 138 292 13 81 34 64 128 256), losses := [] }

theorem u24350 : Upper (D 6) (R 6) [34,136,288,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24351 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 138 292 13 81 36 82 210 338), lower := (rows 35 138 292 13 81 36 64 128 256), losses := [] }

theorem u24351 : Upper (D 6) (R 6) [34,136,288,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24352 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 138 292 13 81 48 70 198 326), lower := (rows 35 138 292 13 81 48 64 128 256), losses := [] }

theorem u24352 : Upper (D 6) (R 6) [34,136,288,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24352 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24353 : Route 9 := (fun mask => (mask,id))

def c24353 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24353 : Upper (D 6) (R 6) [34,136,288,5,65,64] 13 := by
  apply FastRouting.sound _ _ [34,136,288,5,65,64] 13 (by decide) (choices 1) [2,4,16] r24353 c24353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7510
  · exact u7511
  · exact u7512

def b24354 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 138 292 13 82 33 84 212 340), lower := (rows 35 138 292 13 82 33 64 128 256), losses := [] }

theorem u24354 : Upper (D 6) (R 6) [34,136,288,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24355 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 138 292 13 82 36 81 209 337), lower := (rows 35 138 292 13 82 36 64 128 256), losses := [] }

theorem u24355 : Upper (D 6) (R 6) [34,136,288,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24355 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24356 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 292 13 82 48 69 197 325), lower := (rows 35 138 292 13 82 48 64 128 256), losses := [] }

theorem u24356 : Upper (D 6) (R 6) [34,136,288,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24356 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24357 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 35 138 292 13 82 96 85 149 277), lower := (rows 35 138 292 13 82 96 64 128 256), losses := [] }

theorem u24357 : Upper (D 6) (R 6) [34,136,288,5,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24358 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 138 292 13 84 33 82 210 338), lower := (rows 35 138 292 13 84 33 64 128 256), losses := [] }

theorem u24358 : Upper (D 6) (R 6) [34,136,288,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24359 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 292 13 84 34 81 209 337), lower := (rows 35 138 292 13 84 34 64 128 256), losses := [] }

theorem u24359 : Upper (D 6) (R 6) [34,136,288,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u24359
end Delivery.IrregularNine14.P06
