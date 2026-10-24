import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0100

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20220 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 44 280 48 67 195 323), lower := (rows 35 70 133 44 280 48 64 128 256), losses := [] }

theorem u20220 : Upper (D 6) (R 6) [34,68,129,36,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20220 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20221 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 44 280 96 83 147 275), lower := (rows 35 70 133 44 280 96 64 128 256), losses := [] }

theorem u20221 : Upper (D 6) (R 6) [34,68,129,36,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20222 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 133 44 336 33 90 154 282), lower := (rows 35 70 133 44 336 33 64 128 256), losses := [] }

theorem u20222 : Upper (D 6) (R 6) [34,68,129,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20223 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 44 336 34 89 153 281), lower := (rows 35 70 133 44 336 34 64 128 256), losses := [] }

theorem u20223 : Upper (D 6) (R 6) [34,68,129,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20224 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 44 336 40 83 147 275), lower := (rows 35 70 133 44 336 40 64 128 256), losses := [] }

theorem u20224 : Upper (D 6) (R 6) [34,68,129,36,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20224 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20225 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 133 44 336 48 75 139 267), lower := (rows 35 70 133 44 336 48 64 128 256), losses := [] }

theorem u20225 : Upper (D 6) (R 6) [34,68,129,36,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20225 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20226 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 56 81 34 332 396 268), lower := (rows 35 70 133 56 81 34 64 128 256), losses := [] }

theorem u20226 : Upper (D 6) (R 6) [34,68,129,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20227 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 56 81 36 330 394 266), lower := (rows 35 70 133 56 81 36 64 128 256), losses := [] }

theorem u20227 : Upper (D 6) (R 6) [34,68,129,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20228 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 133 56 81 40 326 390 262), lower := (rows 35 70 133 56 81 40 64 128 256), losses := [] }

theorem u20228 : Upper (D 6) (R 6) [34,68,129,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20228 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20229 : Route 9 := (fun mask => (mask,id))

def c20229 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20229 : Upper (D 6) (R 6) [34,68,129,48,65,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,65,256] 13 (by decide) (choices 1) [2,4,8] r20229 c20229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6022
  · exact u6023
  · exact u6024

def b20230 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 56 273 34 76 204 332), lower := (rows 35 70 133 56 273 34 64 128 256), losses := [] }

theorem u20230 : Upper (D 6) (R 6) [34,68,129,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20231 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 56 273 36 74 202 330), lower := (rows 35 70 133 56 273 36 64 128 256), losses := [] }

theorem u20231 : Upper (D 6) (R 6) [34,68,129,48,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20232 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 133 56 273 40 70 198 326), lower := (rows 35 70 133 56 273 40 64 128 256), losses := [] }

theorem u20232 : Upper (D 6) (R 6) [34,68,129,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20232 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20233 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 56 273 96 78 142 270), lower := (rows 35 70 133 56 273 96 64 128 256), losses := [] }

theorem u20233 : Upper (D 6) (R 6) [34,68,129,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20234 : PairBound 9 := { available := 76, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 133 56 274 33 76 204 332), lower := (rows 35 70 133 56 274 33 64 128 256), losses := [] }

theorem u20234 : Upper (D 6) (R 6) [34,68,129,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20235 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 56 274 36 73 201 329), lower := (rows 35 70 133 56 274 36 64 128 256), losses := [] }

theorem u20235 : Upper (D 6) (R 6) [34,68,129,48,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20236 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 70 133 56 274 40 69 197 325), lower := (rows 35 70 133 56 274 40 64 128 256), losses := [] }

theorem u20236 : Upper (D 6) (R 6) [34,68,129,48,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20236 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20237 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 56 274 96 77 141 269), lower := (rows 35 70 133 56 274 96 64 128 256), losses := [] }

theorem u20237 : Upper (D 6) (R 6) [34,68,129,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20238 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 133 56 276 33 74 202 330), lower := (rows 35 70 133 56 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 22 4 9 22 32 77 141 269), good := (rows 506 470 478 506 470 488 64 128 256) }] }

theorem u20238 : Upper (D 6) (R 6) [34,68,129,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20239 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 56 276 34 73 201 329), lower := (rows 35 70 133 56 276 34 64 128 256), losses := [] }

theorem u20239 : Upper (D 6) (R 6) [34,68,129,48,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20240 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 133 56 276 40 67 195 323), lower := (rows 35 70 133 56 276 40 64 128 256), losses := [] }

theorem u20240 : Upper (D 6) (R 6) [34,68,129,48,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20240 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20241 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 56 276 96 75 139 267), lower := (rows 35 70 133 56 276 96 64 128 256), losses := [] }

theorem u20241 : Upper (D 6) (R 6) [34,68,129,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20242 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 70 133 56 280 33 70 198 326), lower := (rows 35 70 133 56 280 33 64 128 256), losses := [] }

theorem u20242 : Upper (D 6) (R 6) [34,68,129,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20243 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 56 280 34 69 197 325), lower := (rows 35 70 133 56 280 34 64 128 256), losses := [] }

theorem u20243 : Upper (D 6) (R 6) [34,68,129,48,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20244 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(3,2),(4,2)], upper := (rows 35 70 133 56 280 36 67 195 323), lower := (rows 35 70 133 56 280 36 64 128 256), losses := [] }

theorem u20244 : Upper (D 6) (R 6) [34,68,129,48,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20245 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 56 280 96 71 135 263), lower := (rows 35 70 133 56 280 96 64 128 256), losses := [] }

theorem u20245 : Upper (D 6) (R 6) [34,68,129,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20246 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 133 56 336 33 78 142 270), lower := (rows 35 70 133 56 336 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 9 22 32 68 132 260), good := (rows 58 470 478 56 336 40 64 128 256) }] }

theorem u20246 : Upper (D 6) (R 6) [34,68,129,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20247 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 56 336 34 77 141 269), lower := (rows 35 70 133 56 336 34 64 128 256), losses := [] }

theorem u20247 : Upper (D 6) (R 6) [34,68,129,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20248 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 56 336 36 75 139 267), lower := (rows 35 70 133 56 336 36 64 128 256), losses := [] }

theorem u20248 : Upper (D 6) (R 6) [34,68,129,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20249 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 133 56 336 40 71 135 263), lower := (rows 35 70 133 56 336 40 64 128 256), losses := [] }

theorem u20249 : Upper (D 6) (R 6) [34,68,129,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20249 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20250 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 73 274 36 120 184 312), lower := (rows 35 70 133 73 274 36 64 128 256), losses := [] }

theorem u20250 : Upper (D 6) (R 6) [34,68,129,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20251 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 133 73 274 40 116 180 308), lower := (rows 35 70 133 73 274 40 64 128 256), losses := [] }

theorem u20251 : Upper (D 6) (R 6) [34,68,129,65,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20251 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20252 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 73 274 48 108 172 300), lower := (rows 35 70 133 73 274 48 64 128 256), losses := [] }

theorem u20252 : Upper (D 6) (R 6) [34,68,129,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20252 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20253 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 73 276 34 120 184 312), lower := (rows 35 70 133 73 276 34 64 128 256), losses := [] }

theorem u20253 : Upper (D 6) (R 6) [34,68,129,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20254 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 133 73 276 40 114 178 306), lower := (rows 35 70 133 73 276 40 64 128 256), losses := [] }

theorem u20254 : Upper (D 6) (R 6) [34,68,129,65,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20254 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20255 : Route 9 := (fun mask => (mask,id))

def c20255 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20255 : Upper (D 6) (R 6) [34,68,129,65,260,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,260,16] 13 (by decide) (choices 1) [2,8,32] r20255 c20255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6025
  · exact u6026
  · exact u6027

def b20256 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 73 280 34 116 180 308), lower := (rows 35 70 133 73 280 34 64 128 256), losses := [] }

theorem u20256 : Upper (D 6) (R 6) [34,68,129,65,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20257 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 73 280 36 114 178 306), lower := (rows 35 70 133 73 280 36 64 128 256), losses := [] }

theorem u20257 : Upper (D 6) (R 6) [34,68,129,65,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20258 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 133 73 280 48 102 166 294), lower := (rows 35 70 133 73 280 48 64 128 256), losses := [{ target := 6, region := (rows 1 2 13 8 24 56 0 129 257), good := (rows 423 6 389 445 316 48 0 128 256) }] }

theorem u20258 : Upper (D 6) (R 6) [34,68,129,65,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20258 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20259 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 73 304 34 92 156 284), lower := (rows 35 70 133 73 304 34 64 128 256), losses := [] }

theorem u20259 : Upper (D 6) (R 6) [34,68,129,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20260 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 73 304 36 90 154 282), lower := (rows 35 70 133 73 304 36 64 128 256), losses := [] }

theorem u20260 : Upper (D 6) (R 6) [34,68,129,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20261 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 133 73 304 40 86 150 278), lower := (rows 35 70 133 73 304 40 64 128 256), losses := [] }

theorem u20261 : Upper (D 6) (R 6) [34,68,129,65,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20261 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20262 : PairBound 9 := { available := 14, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 133 73 304 48 78 142 270), lower := (rows 35 70 133 73 304 48 64 128 256), losses := [] }

theorem u20262 : Upper (D 6) (R 6) [34,68,129,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20262 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20263 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 88 273 34 108 172 300), lower := (rows 35 70 133 88 273 34 64 128 256), losses := [] }

theorem u20263 : Upper (D 6) (R 6) [34,68,129,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20264 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 88 273 36 106 170 298), lower := (rows 35 70 133 88 273 36 64 128 256), losses := [] }

theorem u20264 : Upper (D 6) (R 6) [34,68,129,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20265 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 133 88 273 40 102 166 294), lower := (rows 35 70 133 88 273 40 64 128 256), losses := [] }

theorem u20265 : Upper (D 6) (R 6) [34,68,129,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20265 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20266 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 70 133 88 274 33 108 172 300), lower := (rows 35 70 133 88 274 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 16 63 0 136 264), good := (rows 35 39 165 445 307 33 0 128 256) }] }

theorem u20266 : Upper (D 6) (R 6) [34,68,129,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20267 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 88 274 36 105 169 297), lower := (rows 35 70 133 88 274 36 64 128 256), losses := [] }

theorem u20267 : Upper (D 6) (R 6) [34,68,129,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20268 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 133 88 274 40 101 165 293), lower := (rows 35 70 133 88 274 40 64 128 256), losses := [] }

theorem u20268 : Upper (D 6) (R 6) [34,68,129,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20268 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20269 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 133 88 276 33 106 170 298), lower := (rows 35 70 133 88 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 14 20 32 65 129 257), good := (rows 490 94 478 88 286 480 64 128 256) }] }

theorem u20269 : Upper (D 6) (R 6) [34,68,129,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20270 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 88 276 34 105 169 297), lower := (rows 35 70 133 88 276 34 64 128 256), losses := [] }

theorem u20270 : Upper (D 6) (R 6) [34,68,129,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20271 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 133 88 276 40 99 163 291), lower := (rows 35 70 133 88 276 40 64 128 256), losses := [] }

theorem u20271 : Upper (D 6) (R 6) [34,68,129,80,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20271 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20272 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 70 133 88 280 33 102 166 294), lower := (rows 35 70 133 88 280 33 64 128 256), losses := [] }

theorem u20272 : Upper (D 6) (R 6) [34,68,129,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20273 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 88 280 34 101 165 293), lower := (rows 35 70 133 88 280 34 64 128 256), losses := [] }

theorem u20273 : Upper (D 6) (R 6) [34,68,129,80,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20274 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 88 280 36 99 163 291), lower := (rows 35 70 133 88 280 36 64 128 256), losses := [] }

theorem u20274 : Upper (D 6) (R 6) [34,68,129,80,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20275 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 133 88 304 33 78 142 270), lower := (rows 35 70 133 88 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 13 17 32 70 134 262), good := (rows 506 462 478 88 304 56 64 128 256) }] }

theorem u20275 : Upper (D 6) (R 6) [34,68,129,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20276 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 88 304 34 77 141 269), lower := (rows 35 70 133 88 304 34 64 128 256), losses := [] }

theorem u20276 : Upper (D 6) (R 6) [34,68,129,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20277 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 88 304 36 75 139 267), lower := (rows 35 70 133 88 304 36 64 128 256), losses := [] }

theorem u20277 : Upper (D 6) (R 6) [34,68,129,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20278 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 88 304 40 71 135 263), lower := (rows 35 70 133 88 304 40 64 128 256), losses := [] }

theorem u20278 : Upper (D 6) (R 6) [34,68,129,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20278 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20279 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 104 273 34 92 156 284), lower := (rows 35 70 133 104 273 34 64 128 256), losses := [] }

theorem u20279 : Upper (D 6) (R 6) [34,68,129,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20279
end Delivery.IrregularNine14.P06
