import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0110

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22200 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 100 13 82 40 340 404 276), lower := (rows 35 131 100 13 82 40 64 128 256), losses := [] }

theorem u22200 : Upper (D 6) (R 6) [34,129,96,5,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22200 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22201 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 13 82 48 332 396 268), lower := (rows 35 131 100 13 82 48 64 128 256), losses := [] }

theorem u22201 : Upper (D 6) (R 6) [34,129,96,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22201 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22202 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 131 100 13 82 288 92 156 284), lower := (rows 35 131 100 13 82 288 64 128 256), losses := [] }

theorem u22202 : Upper (D 6) (R 6) [34,129,96,5,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22202 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22203 : PairBound 9 := { available := 276, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 13 88 34 340 404 276), lower := (rows 35 131 100 13 88 34 64 128 256), losses := [] }

theorem u22203 : Upper (D 6) (R 6) [34,129,96,5,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22204 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 100 13 88 36 338 402 274), lower := (rows 35 131 100 13 88 36 64 128 256), losses := [] }

theorem u22204 : Upper (D 6) (R 6) [34,129,96,5,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22205 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 13 88 48 326 390 262), lower := (rows 35 131 100 13 88 48 64 128 256), losses := [] }

theorem u22205 : Upper (D 6) (R 6) [34,129,96,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22205 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22206 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 131 100 13 88 288 86 150 278), lower := (rows 35 131 100 13 88 288 64 128 256), losses := [] }

theorem u22206 : Upper (D 6) (R 6) [34,129,96,5,72,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22206 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22207 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 100 13 274 36 88 216 344), lower := (rows 35 131 100 13 274 36 64 128 256), losses := [] }

theorem u22207 : Upper (D 6) (R 6) [34,129,96,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22208 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 100 13 274 40 84 212 340), lower := (rows 35 131 100 13 274 40 64 128 256), losses := [] }

theorem u22208 : Upper (D 6) (R 6) [34,129,96,5,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22208 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22209 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 100 13 274 48 76 204 332), lower := (rows 35 131 100 13 274 48 64 128 256), losses := [] }

theorem u22209 : Upper (D 6) (R 6) [34,129,96,5,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22209 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22210 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 13 274 96 92 156 284), lower := (rows 35 131 100 13 274 96 64 128 256), losses := [] }

theorem u22210 : Upper (D 6) (R 6) [34,129,96,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22211 : PairBound 9 := { available := 88, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 13 276 34 88 216 344), lower := (rows 35 131 100 13 276 34 64 128 256), losses := [] }

theorem u22211 : Upper (D 6) (R 6) [34,129,96,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22212 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 100 13 276 40 82 210 338), lower := (rows 35 131 100 13 276 40 64 128 256), losses := [] }

theorem u22212 : Upper (D 6) (R 6) [34,129,96,5,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22212 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22213 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 131 100 13 276 48 74 202 330), lower := (rows 35 131 100 13 276 48 64 128 256), losses := [] }

theorem u22213 : Upper (D 6) (R 6) [34,129,96,5,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22213 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22214 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 13 276 96 90 154 282), lower := (rows 35 131 100 13 276 96 64 128 256), losses := [] }

theorem u22214 : Upper (D 6) (R 6) [34,129,96,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22215 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 13 280 34 84 212 340), lower := (rows 35 131 100 13 280 34 64 128 256), losses := [] }

theorem u22215 : Upper (D 6) (R 6) [34,129,96,5,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22216 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 100 13 280 36 82 210 338), lower := (rows 35 131 100 13 280 36 64 128 256), losses := [] }

theorem u22216 : Upper (D 6) (R 6) [34,129,96,5,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22217 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 131 100 13 280 48 70 198 326), lower := (rows 35 131 100 13 280 48 64 128 256), losses := [] }

theorem u22217 : Upper (D 6) (R 6) [34,129,96,5,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22217 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22218 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 13 280 96 86 150 278), lower := (rows 35 131 100 13 280 96 64 128 256), losses := [] }

theorem u22218 : Upper (D 6) (R 6) [34,129,96,5,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22219 : PairBound 9 := { available := 28, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 13 336 34 92 156 284), lower := (rows 35 131 100 13 336 34 64 128 256), losses := [] }

theorem u22219 : Upper (D 6) (R 6) [34,129,96,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22220 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 131 100 13 336 36 90 154 282), lower := (rows 35 131 100 13 336 36 64 128 256), losses := [] }

theorem u22220 : Upper (D 6) (R 6) [34,129,96,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22221 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 100 13 336 40 86 150 278), lower := (rows 35 131 100 13 336 40 64 128 256), losses := [] }

theorem u22221 : Upper (D 6) (R 6) [34,129,96,5,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22221 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22222 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 13 336 48 78 142 270), lower := (rows 35 131 100 13 336 48 64 128 256), losses := [] }

theorem u22222 : Upper (D 6) (R 6) [34,129,96,5,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22222 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22223 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 49, targets := 64 },{ cop := 4, region := 356, targets := 1 }], pairs := [(0,6),(2,0),(4,6)], upper := (rows 35 131 100 14 25 36 336 464 336), lower := (rows 35 131 100 14 25 36 64 128 256), losses := [] }

theorem u22223 : Upper (D 6) (R 6) [34,129,96,6,9,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22224 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 100 14 25 48 324 452 324), lower := (rows 35 131 100 14 25 48 64 128 256), losses := [] }

theorem u22224 : Upper (D 6) (R 6) [34,129,96,6,9,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22224 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22225 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 14 25 96 340 404 276), lower := (rows 35 131 100 14 25 96 64 128 256), losses := [] }

theorem u22225 : Upper (D 6) (R 6) [34,129,96,6,9,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22226 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 14 25 288 84 212 340), lower := (rows 35 131 100 14 25 288 64 128 256), losses := [] }

theorem u22226 : Upper (D 6) (R 6) [34,129,96,6,9,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22226 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22227 : PairBound 9 := { available := 280, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 100 14 81 36 344 408 280), lower := (rows 35 131 100 14 81 36 64 128 256), losses := [] }

theorem u22227 : Upper (D 6) (R 6) [34,129,96,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22228 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 100 14 81 40 340 404 276), lower := (rows 35 131 100 14 81 40 64 128 256), losses := [] }

theorem u22228 : Upper (D 6) (R 6) [34,129,96,6,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22228 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22229 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 14 81 48 332 396 268), lower := (rows 35 131 100 14 81 48 64 128 256), losses := [] }

theorem u22229 : Upper (D 6) (R 6) [34,129,96,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22229 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22230 : Route 9 := (fun mask => (mask,id))

def c22230 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22230 : Upper (D 6) (R 6) [34,129,96,6,65,256] 13 := by
  apply FastRouting.sound _ _ [34,129,96,6,65,256] 13 (by decide) (choices 1) [4,8,16] r22230 c22230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6640
  · exact u6641
  · exact u6642

def b22231 : PairBound 9 := { available := 276, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 14 88 33 340 404 276), lower := (rows 35 131 100 14 88 33 64 128 256), losses := [] }

theorem u22231 : Upper (D 6) (R 6) [34,129,96,6,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22232 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 100 14 88 36 337 401 273), lower := (rows 35 131 100 14 88 36 64 128 256), losses := [] }

theorem u22232 : Upper (D 6) (R 6) [34,129,96,6,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22233 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 14 88 48 325 389 261), lower := (rows 35 131 100 14 88 48 64 128 256), losses := [] }

theorem u22233 : Upper (D 6) (R 6) [34,129,96,6,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22233 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22234 : Route 9 := (fun mask => (mask,id))

def c22234 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22234 : Upper (D 6) (R 6) [34,129,96,6,72,256] 13 := by
  apply FastRouting.sound _ _ [34,129,96,6,72,256] 13 (by decide) (choices 1) [1,4,16] r22234 c22234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6643
  · exact u6644
  · exact u6645

def b22235 : PairBound 9 := { available := 88, camps := [{ cop := 6, region := 36, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 100 14 273 36 88 216 344), lower := (rows 35 131 100 14 273 36 64 128 256), losses := [] }

theorem u22235 : Upper (D 6) (R 6) [34,129,96,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22236 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 100 14 273 40 84 212 340), lower := (rows 35 131 100 14 273 40 64 128 256), losses := [] }

theorem u22236 : Upper (D 6) (R 6) [34,129,96,6,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22236 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22237 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 100 14 273 48 76 204 332), lower := (rows 35 131 100 14 273 48 64 128 256), losses := [] }

theorem u22237 : Upper (D 6) (R 6) [34,129,96,6,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22237 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22238 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 14 273 96 92 156 284), lower := (rows 35 131 100 14 273 96 64 128 256), losses := [] }

theorem u22238 : Upper (D 6) (R 6) [34,129,96,6,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22239 : PairBound 9 := { available := 88, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 14 276 33 88 216 344), lower := (rows 35 131 100 14 276 33 64 128 256), losses := [] }

theorem u22239 : Upper (D 6) (R 6) [34,129,96,6,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22240 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 100 14 276 40 81 209 337), lower := (rows 35 131 100 14 276 40 64 128 256), losses := [] }

theorem u22240 : Upper (D 6) (R 6) [34,129,96,6,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22240 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22241 : Route 9 := (fun mask => (mask,id))

def c22241 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22241 : Upper (D 6) (R 6) [34,129,96,6,260,16] 13 := by
  apply FastRouting.sound _ _ [34,129,96,6,260,16] 13 (by decide) (choices 1) [1,8] r22241 c22241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6646
  · exact u6647

def b22242 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 14 276 96 89 153 281), lower := (rows 35 131 100 14 276 96 64 128 256), losses := [] }

theorem u22242 : Upper (D 6) (R 6) [34,129,96,6,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22243 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 14 280 33 84 212 340), lower := (rows 35 131 100 14 280 33 64 128 256), losses := [] }

theorem u22243 : Upper (D 6) (R 6) [34,129,96,6,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22244 : PairBound 9 := { available := 81, camps := [{ cop := 6, region := 36, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 100 14 280 36 81 209 337), lower := (rows 35 131 100 14 280 36 64 128 256), losses := [] }

theorem u22244 : Upper (D 6) (R 6) [34,129,96,6,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22245 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 100 14 280 48 69 197 325), lower := (rows 35 131 100 14 280 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 13 8 24 56 67 131 259), good := (rows 485 453 100 508 316 48 64 128 256) }] }

theorem u22245 : Upper (D 6) (R 6) [34,129,96,6,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22245 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22246 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 14 280 96 85 149 277), lower := (rows 35 131 100 14 280 96 64 128 256), losses := [] }

theorem u22246 : Upper (D 6) (R 6) [34,129,96,6,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22247 : PairBound 9 := { available := 28, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 14 336 33 92 156 284), lower := (rows 35 131 100 14 336 33 64 128 256), losses := [] }

theorem u22247 : Upper (D 6) (R 6) [34,129,96,6,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22248 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 100 14 336 36 89 153 281), lower := (rows 35 131 100 14 336 36 64 128 256), losses := [] }

theorem u22248 : Upper (D 6) (R 6) [34,129,96,6,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22249 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 131 100 14 336 40 85 149 277), lower := (rows 35 131 100 14 336 40 64 128 256), losses := [] }

theorem u22249 : Upper (D 6) (R 6) [34,129,96,6,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22249 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22250 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 100 14 336 48 77 141 269), lower := (rows 35 131 100 14 336 48 64 128 256), losses := [] }

theorem u22250 : Upper (D 6) (R 6) [34,129,96,6,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22250 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22251 : Route 9 := (fun mask => (mask,id))

def c22251 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u22251 : Upper (D 6) (R 6) [34,129,96,17,66,4] 13 := by
  apply FastRouting.sound _ _ [34,129,96,17,66,4] 13 (by decide) (choices 1) [4,8,256] r22251 c22251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6648
  · exact u6649
  · exact u6650

def b22252 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 100 25 82 40 324 388 260), lower := (rows 35 131 100 25 82 40 64 128 256), losses := [] }

theorem u22252 : Upper (D 6) (R 6) [34,129,96,17,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22252 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22253 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 100 25 82 288 76 140 268), lower := (rows 35 131 100 25 82 288 64 128 256), losses := [] }

theorem u22253 : Upper (D 6) (R 6) [34,129,96,17,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22253 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22254 : Route 9 := (fun mask => (mask,id))

def c22254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22254 : Upper (D 6) (R 6) [34,129,96,17,258,4] 13 := by
  apply FastRouting.sound _ _ [34,129,96,17,258,4] 13 (by decide) (choices 1) [4,8] r22254 c22254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6651
  · exact u6652

def b22255 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 100 25 274 40 68 196 324), lower := (rows 35 131 100 25 274 40 64 128 256), losses := [] }

theorem u22255 : Upper (D 6) (R 6) [34,129,96,17,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22255 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22256 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 131 100 25 274 96 76 140 268), lower := (rows 35 131 100 25 274 96 64 128 256), losses := [] }

theorem u22256 : Upper (D 6) (R 6) [34,129,96,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22257 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 100 25 276 34 76 204 332), lower := (rows 35 131 100 25 276 34 64 128 256), losses := [] }

theorem u22257 : Upper (D 6) (R 6) [34,129,96,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22258 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 194, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 131 100 25 276 36 74 202 330), lower := (rows 35 131 100 25 276 36 64 128 256), losses := [] }

theorem u22258 : Upper (D 6) (R 6) [34,129,96,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22259 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 131 100 25 276 40 70 198 326), lower := (rows 35 131 100 25 276 40 64 128 256), losses := [] }

theorem u22259 : Upper (D 6) (R 6) [34,129,96,17,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22259 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u22259
end Delivery.IrregularNine14.P06
