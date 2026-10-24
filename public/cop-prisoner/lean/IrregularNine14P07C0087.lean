import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0006

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5220 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(1,0),(3,5),(4,1),(4,5)], upper := (rows 35 70 44 265 81 160 192 146 274), lower := (rows 35 70 44 265 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 224 224 128 256), good := (rows 98 102 110 264 112 224 224 224 256) },{ target := 1, region := (rows 1 0 4 8 17 224 224 128 256), good := (rows 113 100 108 281 113 224 224 224 256) }] }

theorem u5220 : Upper (D 7) (R 7) [34,68,40,257,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5221 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 66, targets := 33 }], pairs := [(1,0),(1,5),(3,5),(4,5)], upper := (rows 35 70 44 265 145 160 66 208 336), lower := (rows 35 70 44 265 145 160 66 128 256), losses := [] }

theorem u5221 : Upper (D 7) (R 7) [34,68,40,257,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5222 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 35 70 44 265 145 160 80 194 322), lower := (rows 35 70 44 265 145 160 80 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 179 80 130 258), good := (rows 418 486 44 300 240 160 112 160 256) }] }

theorem u5222 : Upper (D 7) (R 7) [34,68,40,257,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5222 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5223 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 44 265 208 160 65 146 274), lower := (rows 35 70 44 265 208 160 65 128 256), losses := [] }

theorem u5223 : Upper (D 7) (R 7) [34,68,40,257,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5224 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 66, targets := 33 }], pairs := [(1,0),(1,5),(3,5),(4,5)], upper := (rows 35 70 44 265 208 160 66 145 273), lower := (rows 35 70 44 265 208 160 66 128 256), losses := [] }

theorem u5224 : Upper (D 7) (R 7) [34,68,40,257,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5225 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 44 265 208 160 80 131 259), lower := (rows 35 70 44 265 208 160 80 128 256), losses := [] }

theorem u5225 : Upper (D 7) (R 7) [34,68,40,257,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5225 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5226 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 83, targets := 128 },{ cop := 4, region := 430, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 35 70 44 266 81 160 65 144 400), lower := (rows 35 70 44 266 81 160 65 128 256), losses := [] }

theorem u5226 : Upper (D 7) (R 7) [34,68,40,258,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5227 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 44 266 81 160 80 129 385), lower := (rows 35 70 44 266 81 160 80 128 256), losses := [] }

theorem u5227 : Upper (D 7) (R 7) [34,68,40,258,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5227 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5228 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(3,5),(4,1),(4,5)], upper := (rows 35 70 44 266 81 160 192 145 273), lower := (rows 35 70 44 266 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 224 224 128 256), good := (rows 98 102 110 266 112 224 224 224 256) }] }

theorem u5228 : Upper (D 7) (R 7) [34,68,40,258,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5229 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 44 266 145 160 65 208 336), lower := (rows 35 70 44 266 145 160 65 128 256), losses := [] }

theorem u5229 : Upper (D 7) (R 7) [34,68,40,258,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5230 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 35 70 44 266 145 160 80 193 321), lower := (rows 35 70 44 266 145 160 80 128 256), losses := [] }

theorem u5230 : Upper (D 7) (R 7) [34,68,40,258,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5230 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5231 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 44 266 208 160 65 145 273), lower := (rows 35 70 44 266 208 160 65 128 256), losses := [] }

theorem u5231 : Upper (D 7) (R 7) [34,68,40,258,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5232 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 44 266 208 160 80 129 257), lower := (rows 35 70 44 266 208 160 80 128 256), losses := [] }

theorem u5232 : Upper (D 7) (R 7) [34,68,40,258,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5232 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5233 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 70 133 25 112 288 66 136 392), lower := (rows 35 70 133 25 112 288 66 128 256), losses := [] }

theorem u5233 : Upper (D 7) (R 7) [34,68,129,17,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5233 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5234 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7)], upper := (rows 35 70 133 25 112 288 72 130 386), lower := (rows 35 70 133 25 112 288 72 128 256), losses := [] }

theorem u5234 : Upper (D 7) (R 7) [34,68,129,17,96,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5234 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5235 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 313, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 70 133 25 112 288 192 138 266), lower := (rows 35 70 133 25 112 288 192 128 256), losses := [] }

theorem u5235 : Upper (D 7) (R 7) [34,68,129,17,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5235 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5236 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 70 133 25 176 288 66 200 328), lower := (rows 35 70 133 25 176 288 66 128 256), losses := [] }

theorem u5236 : Upper (D 7) (R 7) [34,68,129,17,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5236 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5237 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 25 176 288 72 194 322), lower := (rows 35 70 133 25 176 288 72 128 256), losses := [] }

theorem u5237 : Upper (D 7) (R 7) [34,68,129,17,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5237 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5238 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 90, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 70 133 25 208 288 66 168 296), lower := (rows 35 70 133 25 208 288 66 128 256), losses := [] }

theorem u5238 : Upper (D 7) (R 7) [34,68,129,17,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5238 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5239 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 90, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 70 133 25 208 288 72 162 290), lower := (rows 35 70 133 25 208 288 72 128 256), losses := [] }

theorem u5239 : Upper (D 7) (R 7) [34,68,129,17,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5239 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5240 : PairBound 9 := { available := 10, camps := [], pairs := [(1,0),(3,1),(4,0)], upper := (rows 35 70 133 25 208 288 96 138 266), lower := (rows 35 70 133 25 208 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 20 288 353 128 256), good := (rows 98 86 214 88 208 352 96 128 352) },{ target := 1, region := (rows 1 0 4 12 20 288 353 128 256), good := (rows 97 92 221 89 208 352 96 128 352) }] }

theorem u5240 : Upper (D 7) (R 7) [34,68,129,17,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5240 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5241 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 90, targets := 160 }], pairs := [(1,5),(1,7)], upper := (rows 35 70 133 26 81 288 72 160 416), lower := (rows 35 70 133 26 81 288 72 128 256), losses := [] }

theorem u5241 : Upper (D 7) (R 7) [34,68,129,18,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5241 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5242 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 142, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 133 26 81 288 96 136 392), lower := (rows 35 70 133 26 81 288 96 128 256), losses := [] }

theorem u5242 : Upper (D 7) (R 7) [34,68,129,18,65,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5242 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5243 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 313, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 70 133 26 81 288 192 168 296), lower := (rows 35 70 133 26 81 288 192 128 256), losses := [] }

theorem u5243 : Upper (D 7) (R 7) [34,68,129,18,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5243 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5244 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 88, targets := 128 },{ cop := 1, region := 440, targets := 1 }], pairs := [(3,0),(3,7),(4,7)], upper := (rows 35 70 133 26 112 288 65 136 392), lower := (rows 35 70 133 26 112 288 65 128 256), losses := [] }

theorem u5244 : Upper (D 7) (R 7) [34,68,129,18,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5244 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5245 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 88, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 70 133 26 112 288 72 129 385), lower := (rows 35 70 133 26 112 288 72 128 256), losses := [] }

theorem u5245 : Upper (D 7) (R 7) [34,68,129,18,96,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5245 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5246 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 313, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 70 133 26 112 288 192 137 265), lower := (rows 35 70 133 26 112 288 192 128 256), losses := [] }

theorem u5246 : Upper (D 7) (R 7) [34,68,129,18,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5246 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5247 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 70 133 26 176 288 65 200 328), lower := (rows 35 70 133 26 176 288 65 128 256), losses := [] }

theorem u5247 : Upper (D 7) (R 7) [34,68,129,18,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5247 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5248 : Route 9 := (fun mask => (mask,id))

def c5248 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5248 : Upper (D 7) (R 7) [34,68,129,18,160,256,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,160,256,8] 13 (by decide) (choices 1) [1,64] r5248 c5248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u394
  · exact u395

def b5249 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 82, targets := 160 }], pairs := [(1,5),(1,7),(4,5)], upper := (rows 35 70 133 56 81 288 66 136 392), lower := (rows 35 70 133 56 81 288 66 128 256), losses := [] }

theorem u5249 : Upper (D 7) (R 7) [34,68,129,48,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5249 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5250 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7)], upper := (rows 35 70 133 56 81 288 72 130 386), lower := (rows 35 70 133 56 81 288 72 128 256), losses := [] }

theorem u5250 : Upper (D 7) (R 7) [34,68,129,48,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5250 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5251 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 313, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 70 133 56 81 288 192 138 266), lower := (rows 35 70 133 56 81 288 192 128 256), losses := [] }

theorem u5251 : Upper (D 7) (R 7) [34,68,129,48,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5251 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5252 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 70 133 56 146 288 65 200 328), lower := (rows 35 70 133 56 146 288 65 128 256), losses := [] }

theorem u5252 : Upper (D 7) (R 7) [34,68,129,48,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5252 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5253 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 35 70 133 56 146 288 72 193 321), lower := (rows 35 70 133 56 146 288 72 128 256), losses := [] }

theorem u5253 : Upper (D 7) (R 7) [34,68,129,48,130,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5253 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5254 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 70 133 56 208 288 65 138 266), lower := (rows 35 70 133 56 208 288 65 128 256), losses := [] }

theorem u5254 : Upper (D 7) (R 7) [34,68,129,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5254 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5255 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 133 56 208 288 66 137 265), lower := (rows 35 70 133 56 208 288 66 128 256), losses := [] }

theorem u5255 : Upper (D 7) (R 7) [34,68,129,48,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5255 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5256 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 133 56 208 288 72 131 259), lower := (rows 35 70 133 56 208 288 72 128 256), losses := [] }

theorem u5256 : Upper (D 7) (R 7) [34,68,129,48,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5256 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5257 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 35 70 133 73 146 288 72 176 304), lower := (rows 35 70 133 73 146 288 72 128 256), losses := [] }

theorem u5257 : Upper (D 7) (R 7) [34,68,129,65,130,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5257 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5258 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 90, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 70 133 73 146 288 80 168 296), lower := (rows 35 70 133 73 146 288 80 128 256), losses := [] }

theorem u5258 : Upper (D 7) (R 7) [34,68,129,65,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5258 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5259 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 150, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 133 73 146 288 96 152 280), lower := (rows 35 70 133 73 146 288 96 128 256), losses := [] }

theorem u5259 : Upper (D 7) (R 7) [34,68,129,65,130,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5259 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5260 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 70 133 73 152 288 66 176 304), lower := (rows 35 70 133 73 152 288 66 128 256), losses := [] }

theorem u5260 : Upper (D 7) (R 7) [34,68,129,65,136,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5260 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5261 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 90, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 70 133 73 152 288 80 162 290), lower := (rows 35 70 133 73 152 288 80 128 256), losses := [] }

theorem u5261 : Upper (D 7) (R 7) [34,68,129,65,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5261 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5262 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 150, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 133 73 152 288 96 146 274), lower := (rows 35 70 133 73 152 288 96 128 256), losses := [] }

theorem u5262 : Upper (D 7) (R 7) [34,68,129,65,136,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5262 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5263 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 74, targets := 160 }], pairs := [(1,5),(1,7),(3,5)], upper := (rows 35 70 133 73 176 288 66 152 280), lower := (rows 35 70 133 73 176 288 66 128 256), losses := [] }

theorem u5263 : Upper (D 7) (R 7) [34,68,129,65,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5263 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5264 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 74, targets := 160 }], pairs := [(1,5),(1,7)], upper := (rows 35 70 133 73 176 288 72 146 274), lower := (rows 35 70 133 73 176 288 72 128 256), losses := [] }

theorem u5264 : Upper (D 7) (R 7) [34,68,129,65,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5264 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5265 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 297, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 35 70 133 73 176 288 80 138 266), lower := (rows 35 70 133 73 176 288 80 128 256), losses := [] }

theorem u5265 : Upper (D 7) (R 7) [34,68,129,65,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5265 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5266 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 74, targets := 160 }], pairs := [(1,5),(1,7),(3,5)], upper := (rows 35 70 133 73 400 48 66 168 296), lower := (rows 35 70 133 73 400 48 66 128 256), losses := [] }

theorem u5266 : Upper (D 7) (R 7) [34,68,129,65,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5266 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5267 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 74, targets := 160 }], pairs := [(1,5),(1,7)], upper := (rows 35 70 133 73 400 48 72 162 290), lower := (rows 35 70 133 73 400 48 72 128 256), losses := [] }

theorem u5267 : Upper (D 7) (R 7) [34,68,129,65,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5267 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5268 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 133 73 400 48 96 138 266), lower := (rows 35 70 133 73 400 48 96 128 256), losses := [] }

theorem u5268 : Upper (D 7) (R 7) [34,68,129,65,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5268 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5269 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 90, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 70 133 88 146 288 65 168 296), lower := (rows 35 70 133 88 146 288 65 128 256), losses := [] }

theorem u5269 : Upper (D 7) (R 7) [34,68,129,80,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5269 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5270 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 90, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 133 88 146 288 72 161 289), lower := (rows 35 70 133 88 146 288 72 128 256), losses := [] }

theorem u5270 : Upper (D 7) (R 7) [34,68,129,80,130,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5270 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5271 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(1,0),(3,7)], upper := (rows 35 70 133 88 146 288 96 137 265), lower := (rows 35 70 133 88 146 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 14 20 288 353 128 256), good := (rows 106 94 222 88 154 352 96 128 352) }] }

theorem u5271 : Upper (D 7) (R 7) [34,68,129,80,130,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5271 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5272 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 70 133 88 176 288 65 138 266), lower := (rows 35 70 133 88 176 288 65 128 256), losses := [] }

theorem u5272 : Upper (D 7) (R 7) [34,68,129,80,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5272 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5273 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 70 133 88 176 288 66 137 265), lower := (rows 35 70 133 88 176 288 66 128 256), losses := [] }

theorem u5273 : Upper (D 7) (R 7) [34,68,129,80,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5273 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5274 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 133 88 176 288 72 131 259), lower := (rows 35 70 133 88 176 288 72 128 256), losses := [] }

theorem u5274 : Upper (D 7) (R 7) [34,68,129,80,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5274 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5275 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 1, region := 440, targets := 1 }], pairs := [(3,0),(3,1),(3,7)], upper := (rows 35 70 133 104 146 288 65 152 280), lower := (rows 35 70 133 104 146 288 65 128 256), losses := [] }

theorem u5275 : Upper (D 7) (R 7) [34,68,129,96,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5275 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5276 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 133 104 146 288 72 145 273), lower := (rows 35 70 133 104 146 288 72 128 256), losses := [] }

theorem u5276 : Upper (D 7) (R 7) [34,68,129,96,130,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5276 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5277 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 133 104 146 288 80 137 265), lower := (rows 35 70 133 104 146 288 80 128 256), losses := [] }

theorem u5277 : Upper (D 7) (R 7) [34,68,129,96,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5277 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5278 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 1, region := 440, targets := 1 }], pairs := [(3,0),(3,1),(3,7)], upper := (rows 35 70 133 104 152 288 65 146 274), lower := (rows 35 70 133 104 152 288 65 128 256), losses := [] }

theorem u5278 : Upper (D 7) (R 7) [34,68,129,96,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5278 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5279 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 70 133 104 152 288 66 145 273), lower := (rows 35 70 133 104 152 288 66 128 256), losses := [] }

theorem u5279 : Upper (D 7) (R 7) [34,68,129,96,136,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5279 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5279
end Delivery.IrregularNine14.P07
