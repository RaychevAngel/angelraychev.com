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

def b25200 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 386 44 28 81 34 69 197 325), lower := (rows 35 386 44 28 81 34 64 128 256), losses := [] }

theorem u25200 : Upper (D 6) (R 6) [34,384,40,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25201 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 386 44 28 81 36 67 195 323), lower := (rows 35 386 44 28 81 36 64 128 256), losses := [] }

theorem u25201 : Upper (D 6) (R 6) [34,384,40,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25202 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 386 44 28 81 96 71 135 263), lower := (rows 35 386 44 28 81 96 64 128 256), losses := [] }

theorem u25202 : Upper (D 6) (R 6) [34,384,40,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25203 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 386 44 28 82 33 69 197 325), lower := (rows 35 386 44 28 82 33 64 128 256), losses := [] }

theorem u25203 : Upper (D 6) (R 6) [34,384,40,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25204 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 386 44 28 82 36 65 193 321), lower := (rows 35 386 44 28 82 36 64 128 256), losses := [] }

theorem u25204 : Upper (D 6) (R 6) [34,384,40,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25205 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 386 44 28 82 96 69 133 261), lower := (rows 35 386 44 28 82 96 64 128 256), losses := [] }

theorem u25205 : Upper (D 6) (R 6) [34,384,40,20,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25206 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 386 44 73 22 33 84 212 340), lower := (rows 35 386 44 73 22 33 64 128 256), losses := [] }

theorem u25206 : Upper (D 6) (R 6) [34,384,40,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25207 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 386 44 73 22 36 81 209 337), lower := (rows 35 386 44 73 22 36 64 128 256), losses := [] }

theorem u25207 : Upper (D 6) (R 6) [34,384,40,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25208 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 386 44 73 22 48 69 197 325), lower := (rows 35 386 44 73 22 48 64 128 256), losses := [] }

theorem u25208 : Upper (D 6) (R 6) [34,384,40,65,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25208 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25209 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 386 44 73 22 96 85 149 277), lower := (rows 35 386 44 73 22 96 64 128 256), losses := [] }

theorem u25209 : Upper (D 6) (R 6) [34,384,40,65,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25210 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 386 44 73 82 33 84 148 276), lower := (rows 35 386 44 73 82 33 64 128 256), losses := [] }

theorem u25210 : Upper (D 6) (R 6) [34,384,40,65,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25211 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 386 44 73 82 36 85 149 277), lower := (rows 35 386 44 73 82 36 64 128 256), losses := [] }

theorem u25211 : Upper (D 6) (R 6) [34,384,40,65,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25212 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 386 44 73 82 48 69 133 261), lower := (rows 35 386 44 73 82 48 64 128 256), losses := [] }

theorem u25212 : Upper (D 6) (R 6) [34,384,40,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25212 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25213 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 386 44 73 84 33 86 150 278), lower := (rows 35 386 44 73 84 33 64 128 256), losses := [] }

theorem u25213 : Upper (D 6) (R 6) [34,384,40,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25214 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 386 44 73 84 34 85 149 277), lower := (rows 35 386 44 73 84 34 64 128 256), losses := [] }

theorem u25214 : Upper (D 6) (R 6) [34,384,40,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25215 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 386 44 73 84 36 83 147 275), lower := (rows 35 386 44 73 84 36 64 128 256), losses := [] }

theorem u25215 : Upper (D 6) (R 6) [34,384,40,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25216 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 386 44 73 84 48 71 135 263), lower := (rows 35 386 44 73 84 48 64 128 256), losses := [] }

theorem u25216 : Upper (D 6) (R 6) [34,384,40,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25216 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25217 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 386 44 74 21 33 84 212 340), lower := (rows 35 386 44 74 21 33 64 128 256), losses := [] }

theorem u25217 : Upper (D 6) (R 6) [34,384,40,66,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25218 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 386 44 74 21 36 81 209 337), lower := (rows 35 386 44 74 21 36 64 128 256), losses := [] }

theorem u25218 : Upper (D 6) (R 6) [34,384,40,66,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25219 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 386 44 74 21 48 69 197 325), lower := (rows 35 386 44 74 21 48 64 128 256), losses := [] }

theorem u25219 : Upper (D 6) (R 6) [34,384,40,66,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25219 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25220 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 386 44 74 21 96 85 149 277), lower := (rows 35 386 44 74 21 96 64 128 256), losses := [] }

theorem u25220 : Upper (D 6) (R 6) [34,384,40,66,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25221 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 386 44 74 81 33 84 148 276), lower := (rows 35 386 44 74 81 33 64 128 256), losses := [] }

theorem u25221 : Upper (D 6) (R 6) [34,384,40,66,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25222 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 386 44 74 81 36 85 149 277), lower := (rows 35 386 44 74 81 36 64 128 256), losses := [] }

theorem u25222 : Upper (D 6) (R 6) [34,384,40,66,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25223 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 386 44 74 81 48 69 133 261), lower := (rows 35 386 44 74 81 48 64 128 256), losses := [] }

theorem u25223 : Upper (D 6) (R 6) [34,384,40,66,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25223 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25224 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 386 44 74 84 33 85 149 277), lower := (rows 35 386 44 74 84 33 64 128 256), losses := [] }

theorem u25224 : Upper (D 6) (R 6) [34,384,40,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25225 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 386 44 74 84 36 81 145 273), lower := (rows 35 386 44 74 84 36 64 128 256), losses := [] }

theorem u25225 : Upper (D 6) (R 6) [34,384,40,66,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25226 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 386 44 74 84 48 69 133 261), lower := (rows 35 386 44 74 84 48 64 128 256), losses := [] }

theorem u25226 : Upper (D 6) (R 6) [34,384,40,66,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25226 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25227 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 483, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 386 44 76 22 33 81 209 337), lower := (rows 35 386 44 76 22 33 64 128 256), losses := [] }

theorem u25227 : Upper (D 6) (R 6) [34,384,40,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25228 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 386 44 76 22 48 65 193 321), lower := (rows 35 386 44 76 22 48 64 128 256), losses := [] }

theorem u25228 : Upper (D 6) (R 6) [34,384,40,68,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25228 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25229 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 12, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 386 44 76 22 96 81 145 273), lower := (rows 35 386 44 76 22 96 64 128 256), losses := [] }

theorem u25229 : Upper (D 6) (R 6) [34,384,40,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25230 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 44, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 386 44 76 81 33 86 150 278), lower := (rows 35 386 44 76 81 33 64 128 256), losses := [] }

theorem u25230 : Upper (D 6) (R 6) [34,384,40,68,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25231 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 386 44 76 81 34 85 149 277), lower := (rows 35 386 44 76 81 34 64 128 256), losses := [] }

theorem u25231 : Upper (D 6) (R 6) [34,384,40,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25232 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 386 44 76 81 36 83 147 275), lower := (rows 35 386 44 76 81 36 64 128 256), losses := [] }

theorem u25232 : Upper (D 6) (R 6) [34,384,40,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25233 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 386 44 76 81 48 71 135 263), lower := (rows 35 386 44 76 81 48 64 128 256), losses := [] }

theorem u25233 : Upper (D 6) (R 6) [34,384,40,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25233 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25234 : Route 9 := (fun mask => (mask,id))

def c25234 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25234 : Upper (D 6) (R 6) [34,384,40,68,66,1] 13 := by
  apply FastRouting.sound _ _ [34,384,40,68,66,1] 13 (by decide) (choices 1) [1,4,16] r25234 c25234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7820
  · exact u7821
  · exact u7822

def b25235 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 386 44 76 82 36 81 145 273), lower := (rows 35 386 44 76 82 36 64 128 256), losses := [] }

theorem u25235 : Upper (D 6) (R 6) [34,384,40,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25236 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 386 44 76 82 48 69 133 261), lower := (rows 35 386 44 76 82 48 64 128 256), losses := [] }

theorem u25236 : Upper (D 6) (R 6) [34,384,40,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25236 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25237 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 386 44 88 21 33 70 198 326), lower := (rows 35 386 44 88 21 33 64 128 256), losses := [] }

theorem u25237 : Upper (D 6) (R 6) [34,384,40,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25238 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 386 44 88 21 34 69 197 325), lower := (rows 35 386 44 88 21 34 64 128 256), losses := [] }

theorem u25238 : Upper (D 6) (R 6) [34,384,40,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25239 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 386 44 88 21 36 67 195 323), lower := (rows 35 386 44 88 21 36 64 128 256), losses := [] }

theorem u25239 : Upper (D 6) (R 6) [34,384,40,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25240 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 386 44 88 21 96 71 135 263), lower := (rows 35 386 44 88 21 96 64 128 256), losses := [] }

theorem u25240 : Upper (D 6) (R 6) [34,384,40,80,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25241 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 386 44 88 22 33 69 197 325), lower := (rows 35 386 44 88 22 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 16 59 0 128 256), good := (rows 35 419 44 61 55 33 0 128 256) }] }

theorem u25241 : Upper (D 6) (R 6) [34,384,40,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25242 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 386 44 88 22 36 65 193 321), lower := (rows 35 386 44 88 22 36 64 128 256), losses := [] }

theorem u25242 : Upper (D 6) (R 6) [34,384,40,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25243 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 386 44 88 22 96 69 133 261), lower := (rows 35 386 44 88 22 96 64 128 256), losses := [] }

theorem u25243 : Upper (D 6) (R 6) [34,384,40,80,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25244 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 386 70 13 52 33 88 216 344), lower := (rows 35 386 70 13 52 33 64 128 256), losses := [] }

theorem u25244 : Upper (D 6) (R 6) [34,384,66,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25245 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 386 70 13 52 40 81 209 337), lower := (rows 35 386 70 13 52 40 64 128 256), losses := [] }

theorem u25245 : Upper (D 6) (R 6) [34,384,66,5,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25245 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25246 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 386 70 13 52 48 73 201 329), lower := (rows 35 386 70 13 52 48 64 128 256), losses := [] }

theorem u25246 : Upper (D 6) (R 6) [34,384,66,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25246 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25247 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 386 70 13 52 96 89 153 281), lower := (rows 35 386 70 13 52 96 64 128 256), losses := [] }

theorem u25247 : Upper (D 6) (R 6) [34,384,66,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25248 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 386 70 13 56 33 84 212 340), lower := (rows 35 386 70 13 56 33 64 128 256), losses := [] }

theorem u25248 : Upper (D 6) (R 6) [34,384,66,5,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25249 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 386 70 13 56 36 81 209 337), lower := (rows 35 386 70 13 56 36 64 128 256), losses := [] }

theorem u25249 : Upper (D 6) (R 6) [34,384,66,5,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25250 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 386 70 13 56 48 69 197 325), lower := (rows 35 386 70 13 56 48 64 128 256), losses := [] }

theorem u25250 : Upper (D 6) (R 6) [34,384,66,5,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25250 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25251 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 33, targets := 4 },{ cop := 3, region := 112, targets := 2 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 386 70 13 56 96 85 149 277), lower := (rows 35 386 70 13 56 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 100 64 128 256), good := (rows 34 386 102 60 56 96 96 128 256) }] }

theorem u25251 : Upper (D 6) (R 6) [34,384,66,5,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25252 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 49, targets := 4 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 386 70 13 112 33 92 156 284), lower := (rows 35 386 70 13 112 33 64 128 256), losses := [] }

theorem u25252 : Upper (D 6) (R 6) [34,384,66,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25253 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 386 70 13 112 36 89 153 281), lower := (rows 35 386 70 13 112 36 64 128 256), losses := [] }

theorem u25253 : Upper (D 6) (R 6) [34,384,66,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25254 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 386 70 13 112 40 85 149 277), lower := (rows 35 386 70 13 112 40 64 128 256), losses := [] }

theorem u25254 : Upper (D 6) (R 6) [34,384,66,5,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25254 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25255 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 386 70 13 112 48 77 141 269), lower := (rows 35 386 70 13 112 48 64 128 256), losses := [] }

theorem u25255 : Upper (D 6) (R 6) [34,384,66,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25255 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25256 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 386 70 25 28 33 100 228 356), lower := (rows 35 386 70 25 28 33 64 128 256), losses := [] }

theorem u25256 : Upper (D 6) (R 6) [34,384,66,17,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25257 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 386 70 25 28 36 97 225 353), lower := (rows 35 386 70 25 28 36 64 128 256), losses := [] }

theorem u25257 : Upper (D 6) (R 6) [34,384,66,17,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m25258_1 : Upper (D 6) (R 6) [34,384,66,17,12,64,1] 13 :=
  permutation_upper _ _ _ [34,384,66,17,12,4,32] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7824

theorem m25258_4 : Upper (D 6) (R 6) [34,384,66,17,12,64,4] 13 :=
  permutation_upper _ _ _ [34,384,66,17,12,1,32] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7823

def r25258 : Route 9 := (fun mask => (mask,id))

def c25258 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25258 : Upper (D 6) (R 6) [34,384,66,17,12,64] 13 := by
  apply FastRouting.sound _ _ [34,384,66,17,12,64] 13 (by decide) (choices 1) [1,4,32] r25258 c25258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m25258_1
  · exact m25258_4
  · exact u7825

def b25259 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 386 70 25 52 33 76 204 332), lower := (rows 35 386 70 25 52 33 64 128 256), losses := [] }

theorem u25259 : Upper (D 6) (R 6) [34,384,66,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u25259
end Delivery.IrregularNine14.P06
