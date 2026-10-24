import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0130

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25320 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 12, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 386 76 44 22 96 81 145 273), lower := (rows 35 386 76 44 22 96 64 128 256), losses := [] }

theorem u25320 : Upper (D 6) (R 6) [34,384,72,36,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25321 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 44, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 386 76 44 81 33 86 150 278), lower := (rows 35 386 76 44 81 33 64 128 256), losses := [] }

theorem u25321 : Upper (D 6) (R 6) [34,384,72,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25322 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 386 76 44 81 34 85 149 277), lower := (rows 35 386 76 44 81 34 64 128 256), losses := [] }

theorem u25322 : Upper (D 6) (R 6) [34,384,72,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25323 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 386 76 44 81 36 83 147 275), lower := (rows 35 386 76 44 81 36 64 128 256), losses := [] }

theorem u25323 : Upper (D 6) (R 6) [34,384,72,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25324 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 386 76 44 81 48 71 135 263), lower := (rows 35 386 76 44 81 48 64 128 256), losses := [] }

theorem u25324 : Upper (D 6) (R 6) [34,384,72,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25324 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25325 : Route 9 := (fun mask => (mask,id))

def c25325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25325 : Upper (D 6) (R 6) [34,384,72,36,66,1] 13 := by
  apply FastRouting.sound _ _ [34,384,72,36,66,1] 13 (by decide) (choices 1) [1,4,16] r25325 c25325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7841
  · exact u7842
  · exact u7843

def b25326 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 386 76 44 82 36 81 145 273), lower := (rows 35 386 76 44 82 36 64 128 256), losses := [] }

theorem u25326 : Upper (D 6) (R 6) [34,384,72,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25327 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 386 76 44 82 48 69 133 261), lower := (rows 35 386 76 44 82 48 64 128 256), losses := [] }

theorem u25327 : Upper (D 6) (R 6) [34,384,72,36,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25327 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25328 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 386 76 56 21 33 70 198 326), lower := (rows 35 386 76 56 21 33 64 128 256), losses := [] }

theorem u25328 : Upper (D 6) (R 6) [34,384,72,48,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25329 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 386 76 56 21 34 69 197 325), lower := (rows 35 386 76 56 21 34 64 128 256), losses := [] }

theorem u25329 : Upper (D 6) (R 6) [34,384,72,48,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25330 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 386 76 56 21 36 67 195 323), lower := (rows 35 386 76 56 21 36 64 128 256), losses := [] }

theorem u25330 : Upper (D 6) (R 6) [34,384,72,48,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25331 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 386, targets := 32 },{ cop := 4, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(3,0)], upper := (rows 35 386 76 56 21 96 71 135 263), lower := (rows 35 386 76 56 21 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 64 128 256), good := (rows 34 386 108 56 60 96 96 128 256) }] }

theorem u25331 : Upper (D 6) (R 6) [34,384,72,48,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25332 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 386 76 56 22 33 69 197 325), lower := (rows 35 386 76 56 22 33 64 128 256), losses := [] }

theorem u25332 : Upper (D 6) (R 6) [34,384,72,48,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25333 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 450, targets := 36 },{ cop := 4, region := 40, targets := 1 }], pairs := [(1,2),(1,5),(3,0)], upper := (rows 35 386 76 56 22 36 65 193 321), lower := (rows 35 386 76 56 22 36 64 128 256), losses := [] }

theorem u25333 : Upper (D 6) (R 6) [34,384,72,48,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25334 : PairBound 9 := { available := 5, camps := [], pairs := [(0,2),(3,0),(3,1)], upper := (rows 35 386 76 56 22 96 69 133 261), lower := (rows 35 386 76 56 22 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 64 128 256), good := (rows 34 386 108 56 62 96 96 128 256) },{ target := 1, region := (rows 1 0 4 24 16 100 64 128 256), good := (rows 33 384 108 56 60 96 96 128 256) },{ target := 2, region := (rows 17 2 0 24 16 100 64 128 256), good := (rows 35 386 104 57 59 96 96 128 256) }] }

theorem u25334 : Upper (D 6) (R 6) [34,384,72,48,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25335 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 386 76 56 81 33 70 134 262), lower := (rows 35 386 76 56 81 33 64 128 256), losses := [] }

theorem u25335 : Upper (D 6) (R 6) [34,384,72,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25336 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 386 76 56 81 34 69 133 261), lower := (rows 35 386 76 56 81 34 64 128 256), losses := [] }

theorem u25336 : Upper (D 6) (R 6) [34,384,72,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25337 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 386 76 56 81 36 71 135 263), lower := (rows 35 386 76 56 81 36 64 128 256), losses := [] }

theorem u25337 : Upper (D 6) (R 6) [34,384,72,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25338 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 386 76 56 82 33 69 133 261), lower := (rows 35 386 76 56 82 33 64 128 256), losses := [] }

theorem u25338 : Upper (D 6) (R 6) [34,384,72,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25339 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 386 76 56 82 36 69 133 261), lower := (rows 35 386 76 56 82 36 64 128 256), losses := [] }

theorem u25339 : Upper (D 6) (R 6) [34,384,72,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25340 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 386 100 13 22 33 88 216 344), lower := (rows 35 386 100 13 22 33 64 128 256), losses := [] }

theorem u25340 : Upper (D 6) (R 6) [34,384,96,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25341 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 386 100 13 22 40 81 209 337), lower := (rows 35 386 100 13 22 40 64 128 256), losses := [] }

theorem u25341 : Upper (D 6) (R 6) [34,384,96,5,6,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25341 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25342 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 386 100 13 22 48 73 201 329), lower := (rows 35 386 100 13 22 48 64 128 256), losses := [] }

theorem u25342 : Upper (D 6) (R 6) [34,384,96,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25342 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25343 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 386 100 13 22 96 89 153 281), lower := (rows 35 386 100 13 22 96 64 128 256), losses := [] }

theorem u25343 : Upper (D 6) (R 6) [34,384,96,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25344 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 386 100 13 26 33 84 212 340), lower := (rows 35 386 100 13 26 33 64 128 256), losses := [] }

theorem u25344 : Upper (D 6) (R 6) [34,384,96,5,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25345 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 386 100 13 26 36 81 209 337), lower := (rows 35 386 100 13 26 36 64 128 256), losses := [] }

theorem u25345 : Upper (D 6) (R 6) [34,384,96,5,10,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25346 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 386 100 13 26 48 69 197 325), lower := (rows 35 386 100 13 26 48 64 128 256), losses := [] }

theorem u25346 : Upper (D 6) (R 6) [34,384,96,5,10,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25346 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25347 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 386 100 13 26 96 85 149 277), lower := (rows 35 386 100 13 26 96 64 128 256), losses := [] }

theorem u25347 : Upper (D 6) (R 6) [34,384,96,5,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25348 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 386 100 13 81 34 92 156 284), lower := (rows 35 386 100 13 81 34 64 128 256), losses := [] }

theorem u25348 : Upper (D 6) (R 6) [34,384,96,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25349 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 386 100 13 81 36 90 154 282), lower := (rows 35 386 100 13 81 36 64 128 256), losses := [] }

theorem u25349 : Upper (D 6) (R 6) [34,384,96,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25350 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 386 100 13 81 40 86 150 278), lower := (rows 35 386 100 13 81 40 64 128 256), losses := [] }

theorem u25350 : Upper (D 6) (R 6) [34,384,96,5,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25350 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25351 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 386 100 13 81 48 78 142 270), lower := (rows 35 386 100 13 81 48 64 128 256), losses := [] }

theorem u25351 : Upper (D 6) (R 6) [34,384,96,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25351 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25352 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 386 100 13 82 33 92 156 284), lower := (rows 35 386 100 13 82 33 64 128 256), losses := [] }

theorem u25352 : Upper (D 6) (R 6) [34,384,96,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25353 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 386 100 13 82 36 89 153 281), lower := (rows 35 386 100 13 82 36 64 128 256), losses := [] }

theorem u25353 : Upper (D 6) (R 6) [34,384,96,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25354 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 386 100 13 82 40 85 149 277), lower := (rows 35 386 100 13 82 40 64 128 256), losses := [] }

theorem u25354 : Upper (D 6) (R 6) [34,384,96,5,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25354 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25355 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 386 100 13 82 48 77 141 269), lower := (rows 35 386 100 13 82 48 64 128 256), losses := [] }

theorem u25355 : Upper (D 6) (R 6) [34,384,96,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25355 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25356 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 386 100 13 88 33 86 150 278), lower := (rows 35 386 100 13 88 33 64 128 256), losses := [] }

theorem u25356 : Upper (D 6) (R 6) [34,384,96,5,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25357 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 386 100 13 88 34 85 149 277), lower := (rows 35 386 100 13 88 34 64 128 256), losses := [] }

theorem u25357 : Upper (D 6) (R 6) [34,384,96,5,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25358 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 386 100 13 88 36 83 147 275), lower := (rows 35 386 100 13 88 36 64 128 256), losses := [] }

theorem u25358 : Upper (D 6) (R 6) [34,384,96,5,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25359 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 386 100 13 88 48 71 135 263), lower := (rows 35 386 100 13 88 48 64 128 256), losses := [] }

theorem u25359 : Upper (D 6) (R 6) [34,384,96,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25359 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25360 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 386 100 14 25 33 84 212 340), lower := (rows 35 386 100 14 25 33 64 128 256), losses := [] }

theorem u25360 : Upper (D 6) (R 6) [34,384,96,6,9,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25361 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 49, targets := 64 },{ cop := 4, region := 450, targets := 4 }], pairs := [(0,6),(1,2),(4,6)], upper := (rows 35 386 100 14 25 36 81 209 337), lower := (rows 35 386 100 14 25 36 64 128 256), losses := [] }

theorem u25361 : Upper (D 6) (R 6) [34,384,96,6,9,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25362 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 386 100 14 25 48 69 197 325), lower := (rows 35 386 100 14 25 48 64 128 256), losses := [] }

theorem u25362 : Upper (D 6) (R 6) [34,384,96,6,9,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25362 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25363 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 386 100 14 25 96 85 149 277), lower := (rows 35 386 100 14 25 96 64 128 256), losses := [] }

theorem u25363 : Upper (D 6) (R 6) [34,384,96,6,9,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25364 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 36, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 386 100 14 81 33 92 156 284), lower := (rows 35 386 100 14 81 33 64 128 256), losses := [] }

theorem u25364 : Upper (D 6) (R 6) [34,384,96,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25365 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 386 100 14 81 36 89 153 281), lower := (rows 35 386 100 14 81 36 64 128 256), losses := [] }

theorem u25365 : Upper (D 6) (R 6) [34,384,96,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25366 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 386 100 14 81 40 85 149 277), lower := (rows 35 386 100 14 81 40 64 128 256), losses := [] }

theorem u25366 : Upper (D 6) (R 6) [34,384,96,6,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25366 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25367 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 386 100 14 81 48 77 141 269), lower := (rows 35 386 100 14 81 48 64 128 256), losses := [] }

theorem u25367 : Upper (D 6) (R 6) [34,384,96,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25367 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25368 : Route 9 := (fun mask => (mask,id))

def c25368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25368 : Upper (D 6) (R 6) [34,384,96,6,72,1] 13 := by
  apply FastRouting.sound _ _ [34,384,96,6,72,1] 13 (by decide) (choices 1) [1,4,16] r25368 c25368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7844
  · exact u7845
  · exact u7846

def b25369 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 386 100 14 88 36 81 145 273), lower := (rows 35 386 100 14 88 36 64 128 256), losses := [] }

theorem u25369 : Upper (D 6) (R 6) [34,384,96,6,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25370 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 386 100 14 88 48 69 133 261), lower := (rows 35 386 100 14 88 48 64 128 256), losses := [] }

theorem u25370 : Upper (D 6) (R 6) [34,384,96,6,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25370 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25371 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 386 100 25 28 33 70 198 326), lower := (rows 35 386 100 25 28 33 64 128 256), losses := [] }

theorem u25371 : Upper (D 6) (R 6) [34,384,96,17,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25372 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 386 100 25 28 34 69 197 325), lower := (rows 35 386 100 25 28 34 64 128 256), losses := [] }

theorem u25372 : Upper (D 6) (R 6) [34,384,96,17,12,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25373 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 450, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 386 100 25 28 36 67 195 323), lower := (rows 35 386 100 25 28 36 64 128 256), losses := [] }

theorem u25373 : Upper (D 6) (R 6) [34,384,96,17,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25374 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 386 100 25 28 96 71 135 263), lower := (rows 35 386 100 25 28 96 64 128 256), losses := [] }

theorem u25374 : Upper (D 6) (R 6) [34,384,96,17,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25375 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 386 100 25 82 33 76 140 268), lower := (rows 35 386 100 25 82 33 64 128 256), losses := [] }

theorem u25375 : Upper (D 6) (R 6) [34,384,96,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25376 : Route 9 := (fun mask => (mask,id))

def c25376 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25376 : Upper (D 6) (R 6) [34,384,96,17,66,4] 13 := by
  apply FastRouting.sound _ _ [34,384,96,17,66,4] 13 (by decide) (choices 1) [1,4,8] r25376 c25376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7847
  · exact u7848
  · exact u7849

def b25377 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 386 100 25 82 40 69 133 261), lower := (rows 35 386 100 25 82 40 64 128 256), losses := [] }

theorem u25377 : Upper (D 6) (R 6) [34,384,96,17,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25377 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25378 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 386 100 25 88 33 70 134 262), lower := (rows 35 386 100 25 88 33 64 128 256), losses := [] }

theorem u25378 : Upper (D 6) (R 6) [34,384,96,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25379 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 386 100 25 88 34 69 133 261), lower := (rows 35 386 100 25 88 34 64 128 256), losses := [] }

theorem u25379 : Upper (D 6) (R 6) [34,384,96,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u25379
end Delivery.IrregularNine14.P06
