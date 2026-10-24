import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0007

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6300 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 74 148 266 112 36 68 129 257), lower := (rows 35 74 148 266 112 36 68 128 256), losses := [] }

theorem u6300 : Upper (D 6) (R 6) [34,72,144,258,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6301 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 83, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 74 148 296 81 36 65 134 262), lower := (rows 35 74 148 296 81 36 65 128 256), losses := [] }

theorem u6301 : Upper (D 6) (R 6) [34,72,144,288,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6302 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 74 148 296 81 36 66 133 261), lower := (rows 35 74 148 296 81 36 66 128 256), losses := [] }

theorem u6302 : Upper (D 6) (R 6) [34,72,144,288,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6303 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 264, targets := 68 },{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(3,2),(3,6)], upper := (rows 35 74 148 296 81 36 68 131 259), lower := (rows 35 74 148 296 81 36 68 128 256), losses := [] }

theorem u6303 : Upper (D 6) (R 6) [34,72,144,288,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6304 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 436, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 74 164 25 22 288 65 196 324), lower := (rows 35 74 164 25 22 288 65 128 256), losses := [] }

theorem u6304 : Upper (D 6) (R 6) [34,72,160,17,6,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6304 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6305 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 2 },{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2),(2,1)], upper := (rows 35 74 164 25 22 288 68 193 321), lower := (rows 35 74 164 25 22 288 68 128 256), losses := [] }

theorem u6305 : Upper (D 6) (R 6) [34,72,160,17,6,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6305 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6306 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 74 164 268 22 33 65 208 336), lower := (rows 35 74 164 268 22 33 65 128 256), losses := [] }

theorem u6306 : Upper (D 6) (R 6) [34,72,160,260,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6307 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 82, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 74 164 268 22 33 80 193 321), lower := (rows 35 74 164 268 22 33 80 128 256), losses := [] }

theorem u6307 : Upper (D 6) (R 6) [34,72,160,260,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6307 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6308 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 266, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 164 268 84 33 65 146 274), lower := (rows 35 74 164 268 84 33 65 128 256), losses := [] }

theorem u6308 : Upper (D 6) (R 6) [34,72,160,260,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6309 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 74 164 268 84 33 66 145 273), lower := (rows 35 74 164 268 84 33 66 128 256), losses := [] }

theorem u6309 : Upper (D 6) (R 6) [34,72,160,260,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6310 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 82, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 74 164 268 84 33 80 131 259), lower := (rows 35 74 164 268 84 33 80 128 256), losses := [] }

theorem u6310 : Upper (D 6) (R 6) [34,72,160,260,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6310 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6311 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 436, targets := 1 },{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 35 74 196 25 274 36 65 164 292), lower := (rows 35 74 196 25 274 36 65 128 256), losses := [] }

theorem u6311 : Upper (D 6) (R 6) [34,72,192,17,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6312 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 280, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 196 25 274 36 68 161 289), lower := (rows 35 74 196 25 274 36 68 128 256), losses := [] }

theorem u6312 : Upper (D 6) (R 6) [34,72,192,17,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6313 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 35 74 196 25 274 36 96 133 261), lower := (rows 35 74 196 25 274 36 96 128 256), losses := [{ target := 0, region := (rows 0 10 132 8 16 164 229 128 256), good := (rows 98 74 228 90 274 100 96 228 256) }] }

theorem u6313 : Upper (D 6) (R 6) [34,72,192,17,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6314 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 436, targets := 1 },{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 35 74 196 25 276 36 65 162 290), lower := (rows 35 74 196 25 276 36 65 128 256), losses := [] }

theorem u6314 : Upper (D 6) (R 6) [34,72,192,17,260,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6315 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 196 25 276 36 66 161 289), lower := (rows 35 74 196 25 276 36 66 128 256), losses := [] }

theorem u6315 : Upper (D 6) (R 6) [34,72,192,17,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6316 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 35 74 196 25 276 36 96 131 259), lower := (rows 35 74 196 25 276 36 96 128 256), losses := [{ target := 0, region := (rows 0 10 132 8 16 180 253 128 256), good := (rows 98 74 228 122 372 100 96 228 256) }] }

theorem u6316 : Upper (D 6) (R 6) [34,72,192,17,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6317 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 196 25 304 36 65 134 262), lower := (rows 35 74 196 25 304 36 65 128 256), losses := [] }

theorem u6317 : Upper (D 6) (R 6) [34,72,192,17,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6318 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 196 25 304 36 66 133 261), lower := (rows 35 74 196 25 304 36 66 128 256), losses := [] }

theorem u6318 : Upper (D 6) (R 6) [34,72,192,17,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6319 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 280, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 196 25 304 36 68 131 259), lower := (rows 35 74 196 25 304 36 68 128 256), losses := [] }

theorem u6319 : Upper (D 6) (R 6) [34,72,192,17,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6320 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 74, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 196 26 273 36 65 164 292), lower := (rows 35 74 196 26 273 36 65 128 256), losses := [] }

theorem u6320 : Upper (D 6) (R 6) [34,72,192,18,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6321 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 280, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 196 26 273 36 68 161 289), lower := (rows 35 74 196 26 273 36 68 128 256), losses := [] }

theorem u6321 : Upper (D 6) (R 6) [34,72,192,18,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6322 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 7, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 74 196 26 273 36 96 133 261), lower := (rows 35 74 196 26 273 36 96 128 256), losses := [] }

theorem u6322 : Upper (D 6) (R 6) [34,72,192,18,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6323 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 67, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 196 56 273 36 65 134 262), lower := (rows 35 74 196 56 273 36 65 128 256), losses := [] }

theorem u6323 : Upper (D 6) (R 6) [34,72,192,48,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6324 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 35 74 196 56 273 36 66 133 261), lower := (rows 35 74 196 56 273 36 66 128 256), losses := [] }

theorem u6324 : Upper (D 6) (R 6) [34,72,192,48,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6325 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 280, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 196 56 273 36 68 131 259), lower := (rows 35 74 196 56 273 36 68 128 256), losses := [] }

theorem u6325 : Upper (D 6) (R 6) [34,72,192,48,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6326 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 196 265 21 36 66 176 304), lower := (rows 35 74 196 265 21 36 66 128 256), losses := [] }

theorem u6326 : Upper (D 6) (R 6) [34,72,192,257,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6327 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 264, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 35 74 196 265 21 36 80 162 290), lower := (rows 35 74 196 265 21 36 80 128 256), losses := [] }

theorem u6327 : Upper (D 6) (R 6) [34,72,192,257,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6327 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6328 : PairBound 9 := { available := 18, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 35 74 196 265 21 36 96 146 274), lower := (rows 35 74 196 265 21 36 96 128 256), losses := [{ target := 0, region := (rows 0 10 132 8 16 180 245 128 256), good := (rows 98 74 228 330 116 100 96 228 256) }] }

theorem u6328 : Upper (D 6) (R 6) [34,72,192,257,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6329 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 180, targets := 1 },{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 35 74 196 265 22 36 65 176 304), lower := (rows 35 74 196 265 22 36 65 128 256), losses := [] }

theorem u6329 : Upper (D 6) (R 6) [34,72,192,257,6,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6330 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 264, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 74 196 265 22 36 80 161 289), lower := (rows 35 74 196 265 22 36 80 128 256), losses := [] }

theorem u6330 : Upper (D 6) (R 6) [34,72,192,257,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6330 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6331 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 297, targets := 64 },{ cop := 7, region := 100, targets := 1 }], pairs := [(0,6),(2,0),(3,6)], upper := (rows 35 74 196 265 22 36 96 145 273), lower := (rows 35 74 196 265 22 36 96 128 256), losses := [] }

theorem u6331 : Upper (D 6) (R 6) [34,72,192,257,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6332 : Route 9 := (fun mask => (mask,id))

def c6332 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6332 : Upper (D 6) (R 6) [34,72,192,258,5,4,1] 13 := by
  apply FastRouting.sound _ _ [34,72,192,258,5,4,1] 13 (by decide) (choices 1) [16,32] r6332 c6332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u461
  · exact u462

def b6333 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 212, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 196 266 21 36 80 161 289), lower := (rows 35 74 196 266 21 36 80 128 256), losses := [] }

theorem u6333 : Upper (D 6) (R 6) [34,72,192,258,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6333 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6334 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 7, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 74 196 266 21 36 96 145 273), lower := (rows 35 74 196 266 21 36 96 128 256), losses := [] }

theorem u6334 : Upper (D 6) (R 6) [34,72,192,258,5,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6335 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 66, targets := 33 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 74 196 268 21 33 66 176 304), lower := (rows 35 74 196 268 21 33 66 128 256), losses := [] }

theorem u6335 : Upper (D 6) (R 6) [34,72,192,260,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6336 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 74 196 268 21 33 80 162 290), lower := (rows 35 74 196 268 21 33 80 128 256), losses := [] }

theorem u6336 : Upper (D 6) (R 6) [34,72,192,260,5,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6336 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6337 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 74 196 268 21 33 96 146 274), lower := (rows 35 74 196 268 21 33 96 128 256), losses := [] }

theorem u6337 : Upper (D 6) (R 6) [34,72,192,260,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6338 : PairBound 9 := { available := 34, camps := [], pairs := [(1,0),(2,0)], upper := (rows 35 74 196 268 21 48 65 162 290), lower := (rows 35 74 196 268 21 48 65 128 256), losses := [{ target := 0, region := (rows 0 70 68 88 16 48 64 145 273), good := (rows 418 78 206 270 446 440 462 128 256) }] }

theorem u6338 : Upper (D 6) (R 6) [34,72,192,260,5,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6338 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6339 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 74 196 268 21 48 66 161 289), lower := (rows 35 74 196 268 21 48 66 128 256), losses := [] }

theorem u6339 : Upper (D 6) (R 6) [34,72,192,260,5,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6339 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6340 : PairBound 9 := { available := 3, camps := [], pairs := [(3,5),(3,6)], upper := (rows 35 74 196 268 21 48 96 131 259), lower := (rows 35 74 196 268 21 48 96 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 64 129 257), good := (rows 387 74 196 268 413 24 64 128 256) },{ target := 6, region := (rows 1 2 4 24 16 48 0 129 257), good := (rows 419 10 132 268 445 56 32 128 256) }] }

theorem u6340 : Upper (D 6) (R 6) [34,72,192,260,5,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6340 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6341 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 74 196 268 52 33 65 146 274), lower := (rows 35 74 196 268 52 33 65 128 256), losses := [] }

theorem u6341 : Upper (D 6) (R 6) [34,72,192,260,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6342 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 66, targets := 33 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 74 196 268 52 33 66 145 273), lower := (rows 35 74 196 268 52 33 66 128 256), losses := [] }

theorem u6342 : Upper (D 6) (R 6) [34,72,192,260,36,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6343 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 74 196 268 52 33 80 131 259), lower := (rows 35 74 196 268 52 33 80 128 256), losses := [] }

theorem u6343 : Upper (D 6) (R 6) [34,72,192,260,36,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6343 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6344 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 3, region := 67, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 196 296 21 36 65 146 274), lower := (rows 35 74 196 296 21 36 65 128 256), losses := [] }

theorem u6344 : Upper (D 6) (R 6) [34,72,192,288,5,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6345 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 35 74 196 296 21 36 66 145 273), lower := (rows 35 74 196 296 21 36 66 128 256), losses := [] }

theorem u6345 : Upper (D 6) (R 6) [34,72,192,288,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6346 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 264, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 35 74 196 296 21 36 80 131 259), lower := (rows 35 74 196 296 21 36 80 128 256), losses := [] }

theorem u6346 : Upper (D 6) (R 6) [34,72,192,288,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6346 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6347 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(4,0)], upper := (rows 35 131 44 25 84 288 66 196 324), lower := (rows 35 131 44 25 84 288 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 316 67 152 280), good := (rows 98 194 444 508 500 288 66 128 288) }] }

theorem u6347 : Upper (D 6) (R 6) [34,129,40,17,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6347 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6348 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 44 25 84 288 68 194 322), lower := (rows 35 131 44 25 84 288 68 128 256), losses := [] }

theorem u6348 : Upper (D 6) (R 6) [34,129,40,17,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6348 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6349 : Route 9 := (fun mask => (mask,id))

def c6349 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6349 : Upper (D 6) (R 6) [34,129,40,17,258,64,4] 13 := by
  apply FastRouting.sound _ _ [34,129,40,17,258,64,4] 13 (by decide) (choices 1) [4,64] r6349 c6349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u463
  · exact u464

def b6350 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 44 25 276 96 66 196 324), lower := (rows 35 131 44 25 276 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 28 107 67 136 264), good := (rows 98 226 444 508 276 96 98 128 256) }] }

theorem u6350 : Upper (D 6) (R 6) [34,129,40,17,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6351 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 5, region := 131, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 44 25 276 96 68 194 322), lower := (rows 35 131 44 25 276 96 68 128 256), losses := [] }

theorem u6351 : Upper (D 6) (R 6) [34,129,40,17,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6352 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 26 84 288 65 196 324), lower := (rows 35 131 44 26 84 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 312 64 144 272), good := (rows 34 130 44 446 500 288 64 128 288) },{ target := 1, region := (rows 1 0 12 8 24 316 67 152 280), good := (rows 97 193 444 508 500 288 65 128 288) }] }

theorem u6352 : Upper (D 6) (R 6) [34,129,40,18,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6352 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6353 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 92, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 131 44 26 84 288 68 193 321), lower := (rows 35 131 44 26 84 288 68 128 256), losses := [] }

theorem u6353 : Upper (D 6) (R 6) [34,129,40,18,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6353 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6354 : Route 9 := (fun mask => (mask,id))

def c6354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6354 : Upper (D 6) (R 6) [34,129,40,18,257,64,4] 13 := by
  apply FastRouting.sound _ _ [34,129,40,18,257,64,4] 13 (by decide) (choices 1) [4,64] r6354 c6354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u465
  · exact u466

def b6355 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 44 26 276 96 65 196 324), lower := (rows 35 131 44 26 276 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 69 11 117 96 64 224 352), good := (rows 446 158 444 26 276 500 508 128 256) }] }

theorem u6355 : Upper (D 6) (R 6) [34,129,40,18,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6355 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6356 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 100, targets := 3 },{ cop := 5, region := 131, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 44 26 276 96 68 193 321), lower := (rows 35 131 44 26 276 96 68 128 256), losses := [] }

theorem u6356 : Upper (D 6) (R 6) [34,129,40,18,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6357 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 28 81 288 66 196 324), lower := (rows 35 131 44 28 81 288 66 128 256), losses := [] }

theorem u6357 : Upper (D 6) (R 6) [34,129,40,20,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6357 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6358 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 131 44 28 81 288 68 194 322), lower := (rows 35 131 44 28 81 288 68 128 256), losses := [] }

theorem u6358 : Upper (D 6) (R 6) [34,129,40,20,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6358 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6359 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 44 28 82 288 65 196 324), lower := (rows 35 131 44 28 82 288 65 128 256), losses := [] }

theorem u6359 : Upper (D 6) (R 6) [34,129,40,20,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6359 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u6359
end Delivery.IrregularNine14.P06
