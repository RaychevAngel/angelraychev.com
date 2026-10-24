import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0129

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25020 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 268 26 21 96 101 165 293), lower := (rows 35 194 268 26 21 96 64 128 256), losses := [] }

theorem u25020 : Upper (D 6) (R 6) [34,192,264,18,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25021 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 194 268 26 52 33 69 197 325), lower := (rows 35 194 268 26 52 33 64 128 256), losses := [{ target := 6, region := (rows 11 2 4 8 20 47 0 128 256), good := (rows 35 163 317 59 52 33 0 128 256) }] }

theorem u25021 : Upper (D 6) (R 6) [34,192,264,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25022 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 268 26 52 36 65 193 321), lower := (rows 35 194 268 26 52 36 64 128 256), losses := [] }

theorem u25022 : Upper (D 6) (R 6) [34,192,264,18,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25023 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 268 26 52 96 69 133 261), lower := (rows 35 194 268 26 52 96 64 128 256), losses := [] }

theorem u25023 : Upper (D 6) (R 6) [34,192,264,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25024 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 194 268 26 81 33 100 164 292), lower := (rows 35 194 268 26 81 33 64 128 256), losses := [] }

theorem u25024 : Upper (D 6) (R 6) [34,192,264,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25025 : Route 9 := (fun mask => (mask,id))

def c25025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25025 : Upper (D 6) (R 6) [34,192,264,18,65,4] 13 := by
  apply FastRouting.sound _ _ [34,192,264,18,65,4] 13 (by decide) (choices 1) [1,4,32] r25025 c25025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7768
  · exact u7769
  · exact u7770

def b25026 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 293, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 268 26 84 33 101 165 293), lower := (rows 35 194 268 26 84 33 64 128 256), losses := [] }

theorem u25026 : Upper (D 6) (R 6) [34,192,264,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25027 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 293, targets := 64 },{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 268 26 84 36 97 161 289), lower := (rows 35 194 268 26 84 36 64 128 256), losses := [] }

theorem u25027 : Upper (D 6) (R 6) [34,192,264,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25028 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 194 268 26 112 33 69 133 261), lower := (rows 35 194 268 26 112 33 64 128 256), losses := [] }

theorem u25028 : Upper (D 6) (R 6) [34,192,264,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25029 : Route 9 := (fun mask => (mask,id))

def c25029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25029 : Upper (D 6) (R 6) [34,192,264,18,96,4] 13 := by
  apply FastRouting.sound _ _ [34,192,264,18,96,4] 13 (by decide) (choices 1) [1,4] r25029 c25029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7771
  · exact u7772

def b25030 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 268 28 81 33 102 166 294), lower := (rows 35 194 268 28 81 33 64 128 256), losses := [] }

theorem u25030 : Upper (D 6) (R 6) [34,192,264,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25031 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 28 81 34 101 165 293), lower := (rows 35 194 268 28 81 34 64 128 256), losses := [] }

theorem u25031 : Upper (D 6) (R 6) [34,192,264,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25032 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 194 268 28 81 36 99 163 291), lower := (rows 35 194 268 28 81 36 64 128 256), losses := [] }

theorem u25032 : Upper (D 6) (R 6) [34,192,264,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25033 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 268 28 112 33 71 135 263), lower := (rows 35 194 268 28 112 33 64 128 256), losses := [] }

theorem u25033 : Upper (D 6) (R 6) [34,192,264,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25034 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 28 112 34 69 133 261), lower := (rows 35 194 268 28 112 34 64 128 256), losses := [] }

theorem u25034 : Upper (D 6) (R 6) [34,192,264,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25035 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 194 268 28 112 36 67 131 259), lower := (rows 35 194 268 28 112 36 64 128 256), losses := [] }

theorem u25035 : Upper (D 6) (R 6) [34,192,264,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25036 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 268 44 22 33 81 209 337), lower := (rows 35 194 268 44 22 33 64 128 256), losses := [] }

theorem u25036 : Upper (D 6) (R 6) [34,192,264,36,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25037 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 268 44 22 48 65 193 321), lower := (rows 35 194 268 44 22 48 64 128 256), losses := [] }

theorem u25037 : Upper (D 6) (R 6) [34,192,264,36,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25037 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25038 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 268 44 22 96 81 145 273), lower := (rows 35 194 268 44 22 96 64 128 256), losses := [] }

theorem u25038 : Upper (D 6) (R 6) [34,192,264,36,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25039 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 268 44 81 33 86 150 278), lower := (rows 35 194 268 44 81 33 64 128 256), losses := [] }

theorem u25039 : Upper (D 6) (R 6) [34,192,264,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25040 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 44 81 34 85 149 277), lower := (rows 35 194 268 44 81 34 64 128 256), losses := [] }

theorem u25040 : Upper (D 6) (R 6) [34,192,264,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25041 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 268 44 81 36 83 147 275), lower := (rows 35 194 268 44 81 36 64 128 256), losses := [] }

theorem u25041 : Upper (D 6) (R 6) [34,192,264,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25042 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 268 44 81 48 71 135 263), lower := (rows 35 194 268 44 81 48 64 128 256), losses := [] }

theorem u25042 : Upper (D 6) (R 6) [34,192,264,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25042 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25043 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 268 44 84 33 83 147 275), lower := (rows 35 194 268 44 84 33 64 128 256), losses := [] }

theorem u25043 : Upper (D 6) (R 6) [34,192,264,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25044 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 44 84 34 81 145 273), lower := (rows 35 194 268 44 84 34 64 128 256), losses := [] }

theorem u25044 : Upper (D 6) (R 6) [34,192,264,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25045 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 194 268 44 84 48 67 131 259), lower := (rows 35 194 268 44 84 48 64 128 256), losses := [] }

theorem u25045 : Upper (D 6) (R 6) [34,192,264,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25045 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25046 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 268 56 21 33 70 198 326), lower := (rows 35 194 268 56 21 33 64 128 256), losses := [] }

theorem u25046 : Upper (D 6) (R 6) [34,192,264,48,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25047 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 56 21 34 69 197 325), lower := (rows 35 194 268 56 21 34 64 128 256), losses := [] }

theorem u25047 : Upper (D 6) (R 6) [34,192,264,48,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25048 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 194 268 56 21 36 67 195 323), lower := (rows 35 194 268 56 21 36 64 128 256), losses := [] }

theorem u25048 : Upper (D 6) (R 6) [34,192,264,48,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25049 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 268 56 21 96 71 135 263), lower := (rows 35 194 268 56 21 96 64 128 256), losses := [] }

theorem u25049 : Upper (D 6) (R 6) [34,192,264,48,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25050 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 194 268 56 22 33 69 197 325), lower := (rows 35 194 268 56 22 33 64 128 256), losses := [] }

theorem u25050 : Upper (D 6) (R 6) [34,192,264,48,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25051 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 194, targets := 36 },{ cop := 4, region := 40, targets := 1 }], pairs := [(1,2),(1,5),(3,0)], upper := (rows 35 194 268 56 22 36 65 193 321), lower := (rows 35 194 268 56 22 36 64 128 256), losses := [] }

theorem u25051 : Upper (D 6) (R 6) [34,192,264,48,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25052 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 268 56 22 96 69 133 261), lower := (rows 35 194 268 56 22 96 64 128 256), losses := [] }

theorem u25052 : Upper (D 6) (R 6) [34,192,264,48,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25053 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 268 56 81 33 70 134 262), lower := (rows 35 194 268 56 81 33 64 128 256), losses := [] }

theorem u25053 : Upper (D 6) (R 6) [34,192,264,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25054 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 56 81 34 69 133 261), lower := (rows 35 194 268 56 81 34 64 128 256), losses := [] }

theorem u25054 : Upper (D 6) (R 6) [34,192,264,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25054 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25055 : Route 9 := (fun mask => (mask,id))

def c25055 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25055 : Upper (D 6) (R 6) [34,192,264,48,65,4] 13 := by
  apply FastRouting.sound _ _ [34,192,264,48,65,4] 13 (by decide) (choices 1) [1,2,4] r25055 c25055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7773
  · exact u7774
  · exact u7775

def r25056 : Route 9 := (fun mask => (mask,id))

def c25056 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25056 : Upper (D 6) (R 6) [34,192,264,48,68,1] 13 := by
  apply FastRouting.sound _ _ [34,192,264,48,68,1] 13 (by decide) (choices 1) [1,2,4] r25056 c25056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7776
  · exact u7777
  · exact u7778

def b25057 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 56 84 34 69 133 261), lower := (rows 35 194 268 56 84 34 64 128 256), losses := [] }

theorem u25057 : Upper (D 6) (R 6) [34,192,264,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25058 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 194 268 56 84 36 67 131 259), lower := (rows 35 194 268 56 84 36 64 128 256), losses := [] }

theorem u25058 : Upper (D 6) (R 6) [34,192,264,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25059 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 73 21 34 116 180 308), lower := (rows 35 194 268 73 21 34 64 128 256), losses := [] }

theorem u25059 : Upper (D 6) (R 6) [34,192,264,65,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25060 : Route 9 := (fun mask => (mask,id))

def c25060 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25060 : Upper (D 6) (R 6) [34,192,264,65,5,4] 13 := by
  apply FastRouting.sound _ _ [34,192,264,65,5,4] 13 (by decide) (choices 1) [2,16,32] r25060 c25060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7779
  · exact u7780
  · exact u7781

def r25061 : Route 9 := (fun mask => (mask,id))

def c25061 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25061 : Upper (D 6) (R 6) [34,192,264,65,5,16] 13 := by
  apply FastRouting.sound _ _ [34,192,264,65,5,16] 13 (by decide) (choices 1) [2,4,32] r25061 c25061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7782
  · exact u7783
  · exact u7784

def b25062 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 194 268 73 22 33 116 180 308), lower := (rows 35 194 268 73 22 33 64 128 256), losses := [] }

theorem u25062 : Upper (D 6) (R 6) [34,192,264,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25063 : Route 9 := (fun mask => (mask,id))

def c25063 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25063 : Upper (D 6) (R 6) [34,192,264,65,6,4] 13 := by
  apply FastRouting.sound _ _ [34,192,264,65,6,4] 13 (by decide) (choices 1) [1,16,32] r25063 c25063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7785
  · exact u7786
  · exact u7787

def b25064 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 268 73 22 48 101 165 293), lower := (rows 35 194 268 73 22 48 64 128 256), losses := [] }

theorem u25064 : Upper (D 6) (R 6) [34,192,264,65,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25064 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25065 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 4, region := 194, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 35 194 268 73 52 33 86 150 278), lower := (rows 35 194 268 73 52 33 64 128 256), losses := [] }

theorem u25065 : Upper (D 6) (R 6) [34,192,264,65,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25066 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 73 52 34 85 149 277), lower := (rows 35 194 268 73 52 34 64 128 256), losses := [] }

theorem u25066 : Upper (D 6) (R 6) [34,192,264,65,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25067 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 268 73 52 36 83 147 275), lower := (rows 35 194 268 73 52 36 64 128 256), losses := [] }

theorem u25067 : Upper (D 6) (R 6) [34,192,264,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25068 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 268 73 52 48 71 135 263), lower := (rows 35 194 268 73 52 48 64 128 256), losses := [] }

theorem u25068 : Upper (D 6) (R 6) [34,192,264,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25068 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25069 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 226, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 268 76 21 33 114 178 306), lower := (rows 35 194 268 76 21 33 64 128 256), losses := [] }

theorem u25069 : Upper (D 6) (R 6) [34,192,264,68,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25070 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 76 21 34 113 177 305), lower := (rows 35 194 268 76 21 34 64 128 256), losses := [] }

theorem u25070 : Upper (D 6) (R 6) [34,192,264,68,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25071 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 194 268 76 21 48 99 163 291), lower := (rows 35 194 268 76 21 48 64 128 256), losses := [] }

theorem u25071 : Upper (D 6) (R 6) [34,192,264,68,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25071 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25072 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 195, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 268 76 52 33 83 147 275), lower := (rows 35 194 268 76 52 33 64 128 256), losses := [] }

theorem u25072 : Upper (D 6) (R 6) [34,192,264,68,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25073 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 76 52 34 81 145 273), lower := (rows 35 194 268 76 52 34 64 128 256), losses := [] }

theorem u25073 : Upper (D 6) (R 6) [34,192,264,68,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25074 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 268 76 52 48 67 131 259), lower := (rows 35 194 268 76 52 48 64 128 256), losses := [] }

theorem u25074 : Upper (D 6) (R 6) [34,192,264,68,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25074 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25075 : Route 9 := (fun mask => (mask,id))

def c25075 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25075 : Upper (D 6) (R 6) [34,192,264,80,5,1] 13 := by
  apply FastRouting.sound _ _ [34,192,264,80,5,1] 13 (by decide) (choices 1) [2,4,32] r25075 c25075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7788
  · exact u7789
  · exact u7790

def b25076 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 88 21 34 101 165 293), lower := (rows 35 194 268 88 21 34 64 128 256), losses := [] }

theorem u25076 : Upper (D 6) (R 6) [34,192,264,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25077 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 194 268 88 21 36 99 163 291), lower := (rows 35 194 268 88 21 36 64 128 256), losses := [{ target := 2, region := (rows 33 51 0 24 16 32 97 161 289), good := (rows 483 194 264 90 475 483 64 128 256) }] }

theorem u25077 : Upper (D 6) (R 6) [34,192,264,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25078 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 268 88 22 33 101 165 293), lower := (rows 35 194 268 88 22 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 16 59 0 152 280), good := (rows 35 163 428 445 439 33 0 128 256) }] }

theorem u25078 : Upper (D 6) (R 6) [34,192,264,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25079 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 195, targets := 4 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 268 88 22 36 97 161 289), lower := (rows 35 194 268 88 22 36 64 128 256), losses := [] }

theorem u25079 : Upper (D 6) (R 6) [34,192,264,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u25079
end Delivery.IrregularNine14.P06
