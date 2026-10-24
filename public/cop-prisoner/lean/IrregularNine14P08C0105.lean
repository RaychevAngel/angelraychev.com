import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0013

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6300 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 56 146 96 225 161 417), lower := (rows 289 7 76 56 146 96 64 128 256), losses := [] }

theorem u6300 : Upper (D 8) (R 8) [288,5,72,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6300 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6301 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 56 146 160 97 225 353), lower := (rows 289 7 76 56 146 160 64 128 256), losses := [] }

theorem u6301 : Upper (D 8) (R 8) [288,5,72,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6302 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 76 152 50 33 224 224 480), lower := (rows 289 7 76 152 50 33 64 128 256), losses := [] }

theorem u6302 : Upper (D 8) (R 8) [288,5,72,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6303 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 152 50 96 225 161 417), lower := (rows 289 7 76 152 50 96 64 128 256), losses := [] }

theorem u6303 : Upper (D 8) (R 8) [288,5,72,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6303 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6304 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 152 50 160 97 225 353), lower := (rows 289 7 76 152 50 160 64 128 256), losses := [] }

theorem u6304 : Upper (D 8) (R 8) [288,5,72,144,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6304 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6305 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 76 168 50 33 208 208 464), lower := (rows 289 7 76 168 50 33 64 128 256), losses := [] }

theorem u6305 : Upper (D 8) (R 8) [288,5,72,160,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6305 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6306 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 7 76 168 50 48 193 193 449), lower := (rows 289 7 76 168 50 48 64 128 256), losses := [] }

theorem u6306 : Upper (D 8) (R 8) [288,5,72,160,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6306 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6307 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 168 50 96 209 145 401), lower := (rows 289 7 76 168 50 96 64 128 256), losses := [] }

theorem u6307 : Upper (D 8) (R 8) [288,5,72,160,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6307 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6308 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 168 50 160 81 209 337), lower := (rows 289 7 76 168 50 160 64 128 256), losses := [] }

theorem u6308 : Upper (D 8) (R 8) [288,5,72,160,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6309 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 289 7 76 168 81 34 240 176 432), lower := (rows 289 7 76 168 81 34 64 128 256), losses := [] }

theorem u6309 : Upper (D 8) (R 8) [288,5,72,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6309 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6310 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 289 7 76 168 81 48 226 162 418), lower := (rows 289 7 76 168 81 48 64 128 256), losses := [] }

theorem u6310 : Upper (D 8) (R 8) [288,5,72,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6310 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6311 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 168 81 160 114 178 306), lower := (rows 289 7 76 168 81 160 64 128 256), losses := [] }

theorem u6311 : Upper (D 8) (R 8) [288,5,72,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6311 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6312 : PairBound 9 := { available := 146, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 168 112 33 210 146 402), lower := (rows 289 7 76 168 112 33 64 128 256), losses := [] }

theorem u6312 : Upper (D 8) (R 8) [288,5,72,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6312 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6313 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 289 7 76 168 112 34 209 145 401), lower := (rows 289 7 76 168 112 34 64 128 256), losses := [] }

theorem u6313 : Upper (D 8) (R 8) [288,5,72,160,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6313 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6314 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 289 7 76 168 112 48 195 131 387), lower := (rows 289 7 76 168 112 48 64 128 256), losses := [] }

theorem u6314 : Upper (D 8) (R 8) [288,5,72,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6314 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6315 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 168 112 160 83 147 275), lower := (rows 289 7 76 168 112 160 64 128 256), losses := [] }

theorem u6315 : Upper (D 8) (R 8) [288,5,72,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6315 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6316 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 289 7 76 168 145 34 112 240 368), lower := (rows 289 7 76 168 145 34 64 128 256), losses := [] }

theorem u6316 : Upper (D 8) (R 8) [288,5,72,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6316 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6317 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 289 7 76 168 145 48 98 226 354), lower := (rows 289 7 76 168 145 48 64 128 256), losses := [] }

theorem u6317 : Upper (D 8) (R 8) [288,5,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6317 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6318 : Route 9 := (fun mask => (mask,id))

def c6318 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6318 : Upper (D 8) (R 8) [288,5,72,160,129,64] 13 := by
  apply FastRouting.sound _ _ [288,5,72,160,129,64] 13 (by decide) (choices 1) [2,16,32] r6318 c6318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u795
  · exact u796
  · exact u797

def b6319 : PairBound 9 := { available := 50, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 168 208 33 114 178 306), lower := (rows 289 7 76 168 208 33 64 128 256), losses := [] }

theorem u6319 : Upper (D 8) (R 8) [288,5,72,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6320 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 289 7 76 168 208 34 113 177 305), lower := (rows 289 7 76 168 208 34 64 128 256), losses := [] }

theorem u6320 : Upper (D 8) (R 8) [288,5,72,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6320 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6321 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 289 7 76 168 208 48 99 163 291), lower := (rows 289 7 76 168 208 48 64 128 256), losses := [] }

theorem u6321 : Upper (D 8) (R 8) [288,5,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6321 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6322 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 289 7 100 25 176 34 200 200 456), lower := (rows 289 7 100 25 176 34 64 128 256), losses := [] }

theorem u6322 : Upper (D 8) (R 8) [288,5,96,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6322 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6323 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 25 176 96 202 138 394), lower := (rows 289 7 100 25 176 96 64 128 256), losses := [] }

theorem u6323 : Upper (D 8) (R 8) [288,5,96,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6323 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6324 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 289 7 100 25 208 34 232 168 424), lower := (rows 289 7 100 25 208 34 64 128 256), losses := [] }

theorem u6324 : Upper (D 8) (R 8) [288,5,96,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6324 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6325 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 289 7 100 25 208 40 226 162 418), lower := (rows 289 7 100 25 208 40 64 128 256), losses := [] }

theorem u6325 : Upper (D 8) (R 8) [288,5,96,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6325 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6326 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 100 25 208 160 106 170 298), lower := (rows 289 7 100 25 208 160 64 128 256), losses := [] }

theorem u6326 : Upper (D 8) (R 8) [288,5,96,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6327 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 100 26 56 33 192 192 448), lower := (rows 289 7 100 26 56 33 64 128 256), losses := [] }

theorem u6327 : Upper (D 8) (R 8) [288,5,96,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6327 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6328 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 26 56 96 193 129 385), lower := (rows 289 7 100 26 56 96 64 128 256), losses := [] }

theorem u6328 : Upper (D 8) (R 8) [288,5,96,18,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6328 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6329 : Route 9 := (fun mask => (mask,id))

def c6329 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6329 : Upper (D 8) (R 8) [288,5,96,18,40,128] 13 := by
  apply FastRouting.sound _ _ [288,5,96,18,40,128] 13 (by decide) (choices 1) [1,128] r6329 c6329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u798
  · exact u799

def b6330 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 26 152 33 224 224 480), lower := (rows 289 7 100 26 152 33 64 128 256), losses := [] }

theorem u6330 : Upper (D 8) (R 8) [288,5,96,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6331 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 26 152 96 225 161 417), lower := (rows 289 7 100 26 152 96 64 128 256), losses := [] }

theorem u6331 : Upper (D 8) (R 8) [288,5,96,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6331 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6332 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 100 26 152 160 97 225 353), lower := (rows 289 7 100 26 152 160 64 128 256), losses := [] }

theorem u6332 : Upper (D 8) (R 8) [288,5,96,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6333 : PairBound 9 := { available := 200, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 26 176 33 200 200 456), lower := (rows 289 7 100 26 176 33 64 128 256), losses := [] }

theorem u6333 : Upper (D 8) (R 8) [288,5,96,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6333 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6334 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 7 100 26 176 40 193 193 449), lower := (rows 289 7 100 26 176 40 64 128 256), losses := [] }

theorem u6334 : Upper (D 8) (R 8) [288,5,96,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6334 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6335 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 26 176 96 201 137 393), lower := (rows 289 7 100 26 176 96 64 128 256), losses := [] }

theorem u6335 : Upper (D 8) (R 8) [288,5,96,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6336 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 100 26 176 160 73 201 329), lower := (rows 289 7 100 26 176 160 64 128 256), losses := [] }

theorem u6336 : Upper (D 8) (R 8) [288,5,96,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6336 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6337 : PairBound 9 := { available := 144, camps := [], pairs := [], upper := (rows 289 7 100 42 81 40 208 144 400), lower := (rows 289 7 100 42 81 40 64 128 256), losses := [] }

theorem u6337 : Upper (D 8) (R 8) [288,5,96,34,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6337 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6338 : PairBound 9 := { available := 136, camps := [], pairs := [], upper := (rows 289 7 100 42 81 48 200 136 392), lower := (rows 289 7 100 42 81 48 64 128 256), losses := [] }

theorem u6338 : Upper (D 8) (R 8) [288,5,96,34,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6338 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6339 : Route 9 := (fun mask => (mask,id))

def c6339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6339 : Upper (D 8) (R 8) [288,5,96,34,65,128] 13 := by
  apply FastRouting.sound _ _ [288,5,96,34,65,128] 13 (by decide) (choices 1) [8,16,128] r6339 c6339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u800
  · exact u801
  · exact u802

def b6340 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 289 7 100 42 145 40 208 208 464), lower := (rows 289 7 100 42 145 40 64 128 256), losses := [] }

theorem u6340 : Upper (D 8) (R 8) [288,5,96,34,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6340 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6341 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 289 7 100 42 145 48 200 200 456), lower := (rows 289 7 100 42 145 48 64 128 256), losses := [] }

theorem u6341 : Upper (D 8) (R 8) [288,5,96,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6341 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6342 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 42 145 96 216 152 408), lower := (rows 289 7 100 42 145 96 64 128 256), losses := [] }

theorem u6342 : Upper (D 8) (R 8) [288,5,96,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6342 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6343 : Route 9 := (fun mask => (mask,id))

def c6343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6343 : Upper (D 8) (R 8) [288,5,96,34,129,128] 13 := by
  apply FastRouting.sound _ _ [288,5,96,34,129,128] 13 (by decide) (choices 1) [8,16] r6343 c6343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u803
  · exact u804

def b6344 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 100 42 152 33 208 208 464), lower := (rows 289 7 100 42 152 33 64 128 256), losses := [] }

theorem u6344 : Upper (D 8) (R 8) [288,5,96,34,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6344 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6345 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 7 100 42 152 48 193 193 449), lower := (rows 289 7 100 42 152 48 64 128 256), losses := [] }

theorem u6345 : Upper (D 8) (R 8) [288,5,96,34,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6345 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6346 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 42 152 96 209 145 401), lower := (rows 289 7 100 42 152 96 64 128 256), losses := [] }

theorem u6346 : Upper (D 8) (R 8) [288,5,96,34,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6347 : Route 9 := (fun mask => (mask,id))

def c6347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6347 : Upper (D 8) (R 8) [288,5,96,34,136,128] 13 := by
  apply FastRouting.sound _ _ [288,5,96,34,136,128] 13 (by decide) (choices 1) [1,16] r6347 c6347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u805
  · exact u806

def b6348 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 100 42 208 33 216 152 408), lower := (rows 289 7 100 42 208 33 64 128 256), losses := [] }

theorem u6348 : Upper (D 8) (R 8) [288,5,96,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6349 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 289 7 100 42 208 40 209 145 401), lower := (rows 289 7 100 42 208 40 64 128 256), losses := [] }

theorem u6349 : Upper (D 8) (R 8) [288,5,96,34,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6349 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6350 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 289 7 100 42 208 48 201 137 393), lower := (rows 289 7 100 42 208 48 64 128 256), losses := [] }

theorem u6350 : Upper (D 8) (R 8) [288,5,96,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6350 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6351 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 100 42 208 160 89 153 281), lower := (rows 289 7 100 42 208 160 64 128 256), losses := [] }

theorem u6351 : Upper (D 8) (R 8) [288,5,96,34,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6351 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6352 : PairBound 9 := { available := 136, camps := [], pairs := [], upper := (rows 289 7 100 56 81 34 200 136 392), lower := (rows 289 7 100 56 81 34 64 128 256), losses := [] }

theorem u6352 : Upper (D 8) (R 8) [288,5,96,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6352 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6353 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 289 7 100 56 81 40 194 130 386), lower := (rows 289 7 100 56 81 40 64 128 256), losses := [] }

theorem u6353 : Upper (D 8) (R 8) [288,5,96,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6353 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6354 : Route 9 := (fun mask => (mask,id))

def c6354 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6354 : Upper (D 8) (R 8) [288,5,96,48,65,128] 13 := by
  apply FastRouting.sound _ _ [288,5,96,48,65,128] 13 (by decide) (choices 1) [2,8,128] r6354 c6354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u807
  · exact u808
  · exact u809

def b6355 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 289 7 100 56 145 34 200 200 456), lower := (rows 289 7 100 56 145 34 64 128 256), losses := [] }

theorem u6355 : Upper (D 8) (R 8) [288,5,96,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6355 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6356 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 289 7 100 56 145 40 194 194 450), lower := (rows 289 7 100 56 145 40 64 128 256), losses := [] }

theorem u6356 : Upper (D 8) (R 8) [288,5,96,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6356 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6357 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 56 145 96 202 138 394), lower := (rows 289 7 100 56 145 96 64 128 256), losses := [] }

theorem u6357 : Upper (D 8) (R 8) [288,5,96,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6358 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 100 56 145 160 74 202 330), lower := (rows 289 7 100 56 145 160 64 128 256), losses := [] }

theorem u6358 : Upper (D 8) (R 8) [288,5,96,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6358 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6359 : PairBound 9 := { available := 200, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 100 56 146 33 200 200 456), lower := (rows 289 7 100 56 146 33 64 128 256), losses := [] }

theorem u6359 : Upper (D 8) (R 8) [288,5,96,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u6359
end Delivery.IrregularNine14.P08
