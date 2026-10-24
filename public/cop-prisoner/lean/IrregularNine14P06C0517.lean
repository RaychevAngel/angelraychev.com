import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0215
import IrregularNine14P06C0216
import IrregularNine14P06C0217

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r31020 : Route 9 := (fun mask => (mask,id))

def c31020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31020 : Upper (D 6) (R 6) [10,33,384,20,66] 13 := by
  apply FastRouting.sound _ _ [10,33,384,20,66] 13 (by decide) (choices 1) [1,4,64] r31020 c31020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12956
  · exact u12957
  · exact u12958

def b31021 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 388 28 84 99 99 227 355), lower := (rows 11 35 388 28 84 32 64 128 256), losses := [] }

theorem u31021 : Upper (D 6) (R 6) [10,33,384,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31022 : Route 9 := (fun mask => (mask,id))

def c31022 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31022 : Upper (D 6) (R 6) [10,33,384,20,96] 13 := by
  apply FastRouting.sound _ _ [10,33,384,20,96] 13 (by decide) (choices 1) [1,2,4,64] r31022 c31022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12959
  · exact u12960
  · exact u12961
  · exact u12962

def b31023 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 388 73 22 116 116 244 372), lower := (rows 11 35 388 73 22 32 64 128 256), losses := [] }

theorem u31023 : Upper (D 6) (R 6) [10,33,384,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31024 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 35 388 73 50 116 84 212 340), lower := (rows 11 35 388 73 50 32 64 128 256), losses := [] }

theorem u31024 : Upper (D 6) (R 6) [10,33,384,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31025 : Route 9 := (fun mask => (mask,id))

def c31025 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31025 : Upper (D 6) (R 6) [10,33,384,65,36] 13 := by
  apply FastRouting.sound _ _ [10,33,384,65,36] 13 (by decide) (choices 1) [2,4,16,64] r31025 c31025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12963
  · exact u12964
  · exact u12965
  · exact u12966

def b31026 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 388 73 82 52 116 180 308), lower := (rows 11 35 388 73 82 32 64 128 256), losses := [] }

theorem u31026 : Upper (D 6) (R 6) [10,33,384,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31027 : Route 9 := (fun mask => (mask,id))

def c31027 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31027 : Upper (D 6) (R 6) [10,33,384,65,68] 13 := by
  apply FastRouting.sound _ _ [10,33,384,65,68] 13 (by decide) (choices 1) [2,4,16] r31027 c31027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12967
  · exact u12968
  · exact u12969

def b31028 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 388 73 112 54 86 150 278), lower := (rows 11 35 388 73 112 32 64 128 256), losses := [] }

theorem u31028 : Upper (D 6) (R 6) [10,33,384,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31029 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 388 76 19 116 116 244 372), lower := (rows 11 35 388 76 19 32 64 128 256), losses := [] }

theorem u31029 : Upper (D 6) (R 6) [10,33,384,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31030 : Route 9 := (fun mask => (mask,id))

def c31030 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31030 : Upper (D 6) (R 6) [10,33,384,68,5] 13 := by
  apply FastRouting.sound _ _ [10,33,384,68,5] 13 (by decide) (choices 1) [2,16,64] r31030 c31030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12970
  · exact u12971
  · exact u12972

def r31031 : Route 9 := (fun mask => (mask,id))

def c31031 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31031 : Upper (D 6) (R 6) [10,33,384,68,6] 13 := by
  apply FastRouting.sound _ _ [10,33,384,68,6] 13 (by decide) (choices 1) [1,16,64] r31031 c31031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12973
  · exact u12974
  · exact u12975

def b31032 : PairBound 9 := { available := 86, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 388 76 49 118 86 214 342), lower := (rows 11 35 388 76 49 32 64 128 256), losses := [] }

theorem u31032 : Upper (D 6) (R 6) [10,33,384,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31033 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 388 76 50 117 85 213 341), lower := (rows 11 35 388 76 50 32 64 128 256), losses := [] }

theorem u31033 : Upper (D 6) (R 6) [10,33,384,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31034 : Route 9 := (fun mask => (mask,id))

def c31034 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31034 : Upper (D 6) (R 6) [10,33,384,68,36] 13 := by
  apply FastRouting.sound _ _ [10,33,384,68,36] 13 (by decide) (choices 1) [1,2,16,64] r31034 c31034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12976
  · exact u12977
  · exact u12978
  · exact u12979

def r31035 : Route 9 := (fun mask => (mask,id))

def c31035 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31035 : Upper (D 6) (R 6) [10,33,384,68,65] 13 := by
  apply FastRouting.sound _ _ [10,33,384,68,65] 13 (by decide) (choices 1) [2,4,16] r31035 c31035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12980
  · exact u12981
  · exact u12982

def r31036 : Route 9 := (fun mask => (mask,id))

def c31036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31036 : Upper (D 6) (R 6) [10,33,384,68,66] 13 := by
  apply FastRouting.sound _ _ [10,33,384,68,66] 13 (by decide) (choices 1) [1,4,16] r31036 c31036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12983
  · exact u12984
  · exact u12985

def b31037 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 388 76 84 51 115 179 307), lower := (rows 11 35 388 76 84 32 64 128 256), losses := [] }

theorem u31037 : Upper (D 6) (R 6) [10,33,384,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31038 : Route 9 := (fun mask => (mask,id))

def c31038 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31038 : Upper (D 6) (R 6) [10,33,384,68,96] 13 := by
  apply FastRouting.sound _ _ [10,33,384,68,96] 13 (by decide) (choices 1) [1,2,4,16] r31038 c31038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12986
  · exact u12987
  · exact u12988
  · exact u12989

def b31039 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 388 88 19 100 100 228 356), lower := (rows 11 35 388 88 19 32 64 128 256), losses := [] }

theorem u31039 : Upper (D 6) (R 6) [10,33,384,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31040 : Route 9 := (fun mask => (mask,id))

def c31040 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31040 : Upper (D 6) (R 6) [10,33,384,80,5] 13 := by
  apply FastRouting.sound _ _ [10,33,384,80,5] 13 (by decide) (choices 1) [2,4,64] r31040 c31040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12990
  · exact u12991
  · exact u12992

def r31041 : Route 9 := (fun mask => (mask,id))

def c31041 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31041 : Upper (D 6) (R 6) [10,33,384,80,6] 13 := by
  apply FastRouting.sound _ _ [10,33,384,80,6] 13 (by decide) (choices 1) [1,4,64] r31041 c31041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12993
  · exact u12994
  · exact u12995

def b31042 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 388 88 49 102 70 198 326), lower := (rows 11 35 388 88 49 32 64 128 256), losses := [] }

theorem u31042 : Upper (D 6) (R 6) [10,33,384,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31043 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 388 88 50 101 69 197 325), lower := (rows 11 35 388 88 50 32 64 128 256), losses := [] }

theorem u31043 : Upper (D 6) (R 6) [10,33,384,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31044 : Route 9 := (fun mask => (mask,id))

def c31044 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31044 : Upper (D 6) (R 6) [10,33,384,80,36] 13 := by
  apply FastRouting.sound _ _ [10,33,384,80,36] 13 (by decide) (choices 1) [1,2,4,64] r31044 c31044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12996
  · exact u12997
  · exact u12998
  · exact u12999

def b31045 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 35 388 88 81 38 102 166 294), lower := (rows 11 35 388 88 81 32 64 128 256), losses := [] }

theorem u31045 : Upper (D 6) (R 6) [10,33,384,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31046 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 388 88 82 37 101 165 293), lower := (rows 11 35 388 88 82 32 64 128 256), losses := [] }

theorem u31046 : Upper (D 6) (R 6) [10,33,384,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31047 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 35 388 88 84 39 103 167 295), lower := (rows 11 35 388 88 84 32 64 128 256), losses := [] }

theorem u31047 : Upper (D 6) (R 6) [10,33,384,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31048 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 388 88 112 39 71 135 263), lower := (rows 11 35 388 88 112 32 64 128 256), losses := [] }

theorem u31048 : Upper (D 6) (R 6) [10,33,384,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31049 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 69 25 22 480 480 480 480), lower := (rows 11 38 69 25 22 32 64 128 256), losses := [] }

theorem u31049 : Upper (D 6) (R 6) [10,36,65,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31050 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 69 25 50 484 452 452 452), lower := (rows 11 38 69 25 50 32 64 128 256), losses := [] }

theorem u31050 : Upper (D 6) (R 6) [10,36,65,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31051 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 25 52 482 450 450 450), lower := (rows 11 38 69 25 52 32 64 128 256), losses := [] }

theorem u31051 : Upper (D 6) (R 6) [10,36,65,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31052 : PairBound 9 := { available := 420, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 69 25 82 420 484 420 420), lower := (rows 11 38 69 25 82 32 64 128 256), losses := [] }

theorem u31052 : Upper (D 6) (R 6) [10,36,65,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31053 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 24, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 38 69 25 84 418 482 418 418), lower := (rows 11 38 69 25 84 32 64 128 256), losses := [] }

theorem u31053 : Upper (D 6) (R 6) [10,36,65,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31054 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 0, region := 452, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 11 38 69 25 112 422 454 390 390), lower := (rows 11 38 69 25 112 32 64 128 256), losses := [] }

theorem u31054 : Upper (D 6) (R 6) [10,36,65,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31054 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31055 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 69 25 146 356 356 484 356), lower := (rows 11 38 69 25 146 32 64 128 256), losses := [] }

theorem u31055 : Upper (D 6) (R 6) [10,36,65,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31056 : Route 9 := (fun mask => (mask,id))

def c31056 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31056 : Upper (D 6) (R 6) [10,36,65,17,132] 13 := by
  apply FastRouting.sound _ _ [10,36,65,17,132] 13 (by decide) (choices 1) [2,64,256] r31056 c31056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13000
  · exact u13001
  · exact u13002

def b31057 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 0, region := 324, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 11 38 69 25 176 358 326 454 326), lower := (rows 11 38 69 25 176 32 64 128 256), losses := [] }

theorem u31057 : Upper (D 6) (R 6) [10,36,65,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31058 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 2, region := 290, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 38 69 25 208 294 358 422 294), lower := (rows 11 38 69 25 208 32 64 128 256), losses := [] }

theorem u31058 : Upper (D 6) (R 6) [10,36,65,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31059 : Route 9 := (fun mask => (mask,id))

def c31059 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31059 : Upper (D 6) (R 6) [10,36,65,17,384] 13 := by
  apply FastRouting.sound _ _ [10,36,65,17,384] 13 (by decide) (choices 1) [2,4,64] r31059 c31059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13003
  · exact u13004
  · exact u13005

def b31060 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 69 28 19 480 480 480 480), lower := (rows 11 38 69 28 19 32 64 128 256), losses := [] }

theorem u31060 : Upper (D 6) (R 6) [10,36,65,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31061 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 28 49 482 450 450 450), lower := (rows 11 38 69 28 49 32 64 128 256), losses := [] }

theorem u31061 : Upper (D 6) (R 6) [10,36,65,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31062 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 28 50 481 449 449 449), lower := (rows 11 38 69 28 50 32 64 128 256), losses := [] }

theorem u31062 : Upper (D 6) (R 6) [10,36,65,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31063 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 24, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 38 69 28 81 418 482 418 418), lower := (rows 11 38 69 28 81 32 64 128 256), losses := [] }

theorem u31063 : Upper (D 6) (R 6) [10,36,65,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31064 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 13, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 38 69 28 82 417 481 417 417), lower := (rows 11 38 69 28 82 32 64 128 256), losses := [] }

theorem u31064 : Upper (D 6) (R 6) [10,36,65,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31065 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 0, region := 496, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 69 28 112 419 451 387 387), lower := (rows 11 38 69 28 112 32 64 128 256), losses := [] }

theorem u31065 : Upper (D 6) (R 6) [10,36,65,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31066 : Route 9 := (fun mask => (mask,id))

def c31066 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31066 : Upper (D 6) (R 6) [10,36,65,20,129] 13 := by
  apply FastRouting.sound _ _ [10,36,65,20,129] 13 (by decide) (choices 1) [2,64,256] r31066 c31066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13006
  · exact u13007
  · exact u13008

def r31067 : Route 9 := (fun mask => (mask,id))

def c31067 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31067 : Upper (D 6) (R 6) [10,36,65,20,130] 13 := by
  apply FastRouting.sound _ _ [10,36,65,20,130] 13 (by decide) (choices 1) [1,64,256] r31067 c31067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13009
  · exact u13010
  · exact u13011

def r31068 : Route 9 := (fun mask => (mask,id))

def c31068 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31068 : Upper (D 6) (R 6) [10,36,65,20,160] 13 := by
  apply FastRouting.sound _ _ [10,36,65,20,160] 13 (by decide) (choices 1) [1,2,64,256] r31068 c31068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13012
  · exact u13013
  · exact u13014
  · exact u13015

def b31069 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 291, targets := 64 },{ cop := 0, region := 496, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 69 28 208 291 355 419 291), lower := (rows 11 38 69 28 208 32 64 128 256), losses := [] }

theorem u31069 : Upper (D 6) (R 6) [10,36,65,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31070 : Route 9 := (fun mask => (mask,id))

def c31070 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31070 : Upper (D 6) (R 6) [10,36,65,20,384] 13 := by
  apply FastRouting.sound _ _ [10,36,65,20,384] 13 (by decide) (choices 1) [1,2,64] r31070 c31070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13016
  · exact u13017
  · exact u13018

def b31071 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 69 56 19 484 452 452 452), lower := (rows 11 38 69 56 19 32 64 128 256), losses := [] }

theorem u31071 : Upper (D 6) (R 6) [10,36,65,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31072 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 56 21 482 450 450 450), lower := (rows 11 38 69 56 21 32 64 128 256), losses := [] }

theorem u31072 : Upper (D 6) (R 6) [10,36,65,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31073 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 56 22 481 449 449 449), lower := (rows 11 38 69 56 22 32 64 128 256), losses := [] }

theorem u31073 : Upper (D 6) (R 6) [10,36,65,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31074 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 38 69 56 81 422 454 390 390), lower := (rows 11 38 69 56 81 32 64 128 256), losses := [] }

theorem u31074 : Upper (D 6) (R 6) [10,36,65,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31075 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 452, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 38 69 56 82 421 453 389 389), lower := (rows 11 38 69 56 82 32 64 128 256), losses := [] }

theorem u31075 : Upper (D 6) (R 6) [10,36,65,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31076 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 69 56 84 419 451 387 387), lower := (rows 11 38 69 56 84 32 64 128 256), losses := [] }

theorem u31076 : Upper (D 6) (R 6) [10,36,65,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31077 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 290, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 38 69 56 145 358 326 454 326), lower := (rows 11 38 69 56 145 32 64 128 256), losses := [] }

theorem u31077 : Upper (D 6) (R 6) [10,36,65,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31078 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 324, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 38 69 56 146 357 325 453 325), lower := (rows 11 38 69 56 146 32 64 128 256), losses := [] }

theorem u31078 : Upper (D 6) (R 6) [10,36,65,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31079 : Route 9 := (fun mask => (mask,id))

def c31079 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31079 : Upper (D 6) (R 6) [10,36,65,48,132] 13 := by
  apply FastRouting.sound _ _ [10,36,65,48,132] 13 (by decide) (choices 1) [1,2,64,256] r31079 c31079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13019
  · exact u13020
  · exact u13021
  · exact u13022

#print axioms u31079
end Delivery.IrregularNine14.P06
