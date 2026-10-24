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

def b6240 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 28 42 112 33 192 192 448), lower := (rows 289 7 28 42 112 33 64 128 256), losses := [] }

theorem u6240 : Upper (D 8) (R 8) [288,5,24,34,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6240 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6241 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 42 112 96 193 129 385), lower := (rows 289 7 28 42 112 96 64 128 256), losses := [] }

theorem u6241 : Upper (D 8) (R 8) [288,5,24,34,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6242 : Route 9 := (fun mask => (mask,id))

def c6242 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6242 : Upper (D 8) (R 8) [288,5,24,34,96,128] 13 := by
  apply FastRouting.sound _ _ [288,5,24,34,96,128] 13 (by decide) (choices 1) [1,128] r6242 c6242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u784
  · exact u785

def b6243 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 28 42 208 33 224 224 480), lower := (rows 289 7 28 42 208 33 64 128 256), losses := [] }

theorem u6243 : Upper (D 8) (R 8) [288,5,24,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6244 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 42 208 96 225 161 417), lower := (rows 289 7 28 42 208 96 64 128 256), losses := [] }

theorem u6244 : Upper (D 8) (R 8) [288,5,24,34,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6245 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 74 176 33 224 224 480), lower := (rows 289 7 28 74 176 33 64 128 256), losses := [] }

theorem u6245 : Upper (D 8) (R 8) [288,5,24,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6245 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6246 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 74 176 96 225 161 417), lower := (rows 289 7 28 74 176 96 64 128 256), losses := [] }

theorem u6246 : Upper (D 8) (R 8) [288,5,24,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6246 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6247 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 28 74 176 160 97 225 353), lower := (rows 289 7 28 74 176 160 64 128 256), losses := [] }

theorem u6247 : Upper (D 8) (R 8) [288,5,24,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6248 : PairBound 9 := { available := 194, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 104 176 33 194 194 450), lower := (rows 289 7 28 104 176 33 64 128 256), losses := [] }

theorem u6248 : Upper (D 8) (R 8) [288,5,24,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6249 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 7 28 104 176 34 193 193 449), lower := (rows 289 7 28 104 176 34 64 128 256), losses := [] }

theorem u6249 : Upper (D 8) (R 8) [288,5,24,96,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6249 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6250 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 104 176 96 195 131 387), lower := (rows 289 7 28 104 176 96 64 128 256), losses := [] }

theorem u6250 : Upper (D 8) (R 8) [288,5,24,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6250 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6251 : PairBound 9 := { available := 192, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 26 112 33 192 192 448), lower := (rows 289 7 44 26 112 33 64 128 256), losses := [] }

theorem u6251 : Upper (D 8) (R 8) [288,5,40,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6251 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6252 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 26 112 96 193 129 385), lower := (rows 289 7 44 26 112 96 64 128 256), losses := [] }

theorem u6252 : Upper (D 8) (R 8) [288,5,40,18,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6253 : Route 9 := (fun mask => (mask,id))

def c6253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6253 : Upper (D 8) (R 8) [288,5,40,18,96,128] 13 := by
  apply FastRouting.sound _ _ [288,5,40,18,96,128] 13 (by decide) (choices 1) [1,128] r6253 c6253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u786
  · exact u787

def b6254 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 26 208 33 224 224 480), lower := (rows 289 7 44 26 208 33 64 128 256), losses := [] }

theorem u6254 : Upper (D 8) (R 8) [288,5,40,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6254 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6255 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 26 208 96 225 161 417), lower := (rows 289 7 44 26 208 96 64 128 256), losses := [] }

theorem u6255 : Upper (D 8) (R 8) [288,5,40,18,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6255 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6256 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 289 7 44 74 145 48 224 224 480), lower := (rows 289 7 44 74 145 48 64 128 256), losses := [] }

theorem u6256 : Upper (D 8) (R 8) [288,5,40,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6256 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6257 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 74 145 96 240 176 432), lower := (rows 289 7 44 74 145 96 64 128 256), losses := [] }

theorem u6257 : Upper (D 8) (R 8) [288,5,40,66,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6258 : Route 9 := (fun mask => (mask,id))

def c6258 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6258 : Upper (D 8) (R 8) [288,5,40,66,129,128] 13 := by
  apply FastRouting.sound _ _ [288,5,40,66,129,128] 13 (by decide) (choices 1) [16,32] r6258 c6258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u788
  · exact u789

def b6259 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 74 176 33 208 208 464), lower := (rows 289 7 44 74 176 33 64 128 256), losses := [] }

theorem u6259 : Upper (D 8) (R 8) [288,5,40,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6259 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6260 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 7 44 74 176 48 193 193 449), lower := (rows 289 7 44 74 176 48 64 128 256), losses := [] }

theorem u6260 : Upper (D 8) (R 8) [288,5,40,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6260 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6261 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 74 176 96 209 145 401), lower := (rows 289 7 44 74 176 96 64 128 256), losses := [] }

theorem u6261 : Upper (D 8) (R 8) [288,5,40,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6261 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6262 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 44 74 176 160 81 209 337), lower := (rows 289 7 44 74 176 160 64 128 256), losses := [] }

theorem u6262 : Upper (D 8) (R 8) [288,5,40,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6262 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6263 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 289 7 44 88 145 34 224 224 480), lower := (rows 289 7 44 88 145 34 64 128 256), losses := [] }

theorem u6263 : Upper (D 8) (R 8) [288,5,40,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6263 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6264 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 88 145 96 226 162 418), lower := (rows 289 7 44 88 145 96 64 128 256), losses := [] }

theorem u6264 : Upper (D 8) (R 8) [288,5,40,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6265 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 44 88 145 160 98 226 354), lower := (rows 289 7 44 88 145 160 64 128 256), losses := [] }

theorem u6265 : Upper (D 8) (R 8) [288,5,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6265 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6266 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 88 146 33 224 224 480), lower := (rows 289 7 44 88 146 33 64 128 256), losses := [] }

theorem u6266 : Upper (D 8) (R 8) [288,5,40,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6266 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6267 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 88 146 96 225 161 417), lower := (rows 289 7 44 88 146 96 64 128 256), losses := [] }

theorem u6267 : Upper (D 8) (R 8) [288,5,40,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6268 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 44 88 146 160 97 225 353), lower := (rows 289 7 44 88 146 160 64 128 256), losses := [] }

theorem u6268 : Upper (D 8) (R 8) [288,5,40,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6268 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6269 : PairBound 9 := { available := 194, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 88 176 33 194 194 450), lower := (rows 289 7 44 88 176 33 64 128 256), losses := [] }

theorem u6269 : Upper (D 8) (R 8) [288,5,40,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6269 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6270 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 7 44 88 176 34 193 193 449), lower := (rows 289 7 44 88 176 34 64 128 256), losses := [] }

theorem u6270 : Upper (D 8) (R 8) [288,5,40,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6270 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6271 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 88 176 96 195 131 387), lower := (rows 289 7 44 88 176 96 64 128 256), losses := [] }

theorem u6271 : Upper (D 8) (R 8) [288,5,40,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6271 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6272 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 44 88 176 160 67 195 323), lower := (rows 289 7 44 88 176 160 64 128 256), losses := [] }

theorem u6272 : Upper (D 8) (R 8) [288,5,40,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6273 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 289 7 44 200 50 33 208 208 464), lower := (rows 289 7 44 200 50 33 64 128 256), losses := [] }

theorem u6273 : Upper (D 8) (R 8) [288,5,40,192,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6273 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6274 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 7 44 200 50 48 193 193 449), lower := (rows 289 7 44 200 50 48 64 128 256), losses := [] }

theorem u6274 : Upper (D 8) (R 8) [288,5,40,192,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6274 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6275 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 200 50 96 209 145 401), lower := (rows 289 7 44 200 50 96 64 128 256), losses := [] }

theorem u6275 : Upper (D 8) (R 8) [288,5,40,192,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6276 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 289 7 44 200 81 34 240 176 432), lower := (rows 289 7 44 200 81 34 64 128 256), losses := [] }

theorem u6276 : Upper (D 8) (R 8) [288,5,40,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6276 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6277 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 289 7 44 200 81 48 226 162 418), lower := (rows 289 7 44 200 81 48 64 128 256), losses := [] }

theorem u6277 : Upper (D 8) (R 8) [288,5,40,192,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6277 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6278 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 44 200 81 160 114 178 306), lower := (rows 289 7 44 200 81 160 64 128 256), losses := [] }

theorem u6278 : Upper (D 8) (R 8) [288,5,40,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6278 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6279 : PairBound 9 := { available := 146, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 44 200 112 33 210 146 402), lower := (rows 289 7 44 200 112 33 64 128 256), losses := [] }

theorem u6279 : Upper (D 8) (R 8) [288,5,40,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6280 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 289 7 44 200 112 34 209 145 401), lower := (rows 289 7 44 200 112 34 64 128 256), losses := [] }

theorem u6280 : Upper (D 8) (R 8) [288,5,40,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6280 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6281 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 289 7 44 200 112 48 195 131 387), lower := (rows 289 7 44 200 112 48 64 128 256), losses := [] }

theorem u6281 : Upper (D 8) (R 8) [288,5,40,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6281 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6282 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 44 200 112 160 83 147 275), lower := (rows 289 7 44 200 112 160 64 128 256), losses := [] }

theorem u6282 : Upper (D 8) (R 8) [288,5,40,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6282 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6283 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 70 56 152 33 224 224 480), lower := (rows 289 7 70 56 152 33 64 128 256), losses := [] }

theorem u6283 : Upper (D 8) (R 8) [288,5,66,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6283 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6284 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 56 152 96 225 161 417), lower := (rows 289 7 70 56 152 96 64 128 256), losses := [] }

theorem u6284 : Upper (D 8) (R 8) [288,5,66,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6284 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6285 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 70 56 152 160 97 225 353), lower := (rows 289 7 70 56 152 160 64 128 256), losses := [] }

theorem u6285 : Upper (D 8) (R 8) [288,5,66,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6285 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6286 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 26 176 33 224 224 480), lower := (rows 289 7 76 26 176 33 64 128 256), losses := [] }

theorem u6286 : Upper (D 8) (R 8) [288,5,72,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6286 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6287 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 26 176 96 225 161 417), lower := (rows 289 7 76 26 176 96 64 128 256), losses := [] }

theorem u6287 : Upper (D 8) (R 8) [288,5,72,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6288 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 26 176 160 97 225 353), lower := (rows 289 7 76 26 176 160 64 128 256), losses := [] }

theorem u6288 : Upper (D 8) (R 8) [288,5,72,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6289 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 289 7 76 42 145 48 224 224 480), lower := (rows 289 7 76 42 145 48 64 128 256), losses := [] }

theorem u6289 : Upper (D 8) (R 8) [288,5,72,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6289 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6290 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 42 145 96 240 176 432), lower := (rows 289 7 76 42 145 96 64 128 256), losses := [] }

theorem u6290 : Upper (D 8) (R 8) [288,5,72,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6290 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6291 : Route 9 := (fun mask => (mask,id))

def c6291 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6291 : Upper (D 8) (R 8) [288,5,72,34,129,128] 13 := by
  apply FastRouting.sound _ _ [288,5,72,34,129,128] 13 (by decide) (choices 1) [16,32] r6291 c6291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u790
  · exact u791

def b6292 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 76 42 176 33 208 208 464), lower := (rows 289 7 76 42 176 33 64 128 256), losses := [] }

theorem u6292 : Upper (D 8) (R 8) [288,5,72,34,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6292 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6293 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 7 76 42 176 48 193 193 449), lower := (rows 289 7 76 42 176 48 64 128 256), losses := [] }

theorem u6293 : Upper (D 8) (R 8) [288,5,72,34,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6293 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6294 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 42 176 96 209 145 401), lower := (rows 289 7 76 42 176 96 64 128 256), losses := [] }

theorem u6294 : Upper (D 8) (R 8) [288,5,72,34,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6294 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6295 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 42 176 160 81 209 337), lower := (rows 289 7 76 42 176 160 64 128 256), losses := [] }

theorem u6295 : Upper (D 8) (R 8) [288,5,72,34,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6296 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 289 7 76 56 145 34 224 224 480), lower := (rows 289 7 76 56 145 34 64 128 256), losses := [] }

theorem u6296 : Upper (D 8) (R 8) [288,5,72,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6296 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r6297 : Route 9 := (fun mask => (mask,id))

def c6297 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u6297 : Upper (D 8) (R 8) [288,5,72,48,129,64] 13 := by
  apply FastRouting.sound _ _ [288,5,72,48,129,64] 13 (by decide) (choices 1) [2,32,128] r6297 c6297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u792
  · exact u793
  · exact u794

def b6298 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 56 145 160 98 226 354), lower := (rows 289 7 76 56 145 160 64 128 256), losses := [] }

theorem u6298 : Upper (D 8) (R 8) [288,5,72,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6299 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 56 146 33 224 224 480), lower := (rows 289 7 76 56 146 33 64 128 256), losses := [] }

theorem u6299 : Upper (D 8) (R 8) [288,5,72,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6299 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u6299
end Delivery.IrregularNine14.P08
