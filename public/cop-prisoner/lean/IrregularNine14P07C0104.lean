import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0007

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6240 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 70 25 208 40 192 161 289), lower := (rows 35 262 70 25 208 40 192 128 256), losses := [] }

theorem u6240 : Upper (D 7) (R 7) [34,260,66,17,192,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6240 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6241 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 68, targets := 160 }], pairs := [(2,5),(2,7),(3,1),(4,1)], upper := (rows 35 262 70 25 208 160 65 168 296), lower := (rows 35 262 70 25 208 160 65 128 256), losses := [] }

theorem u6241 : Upper (D 7) (R 7) [34,260,66,17,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6242 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 262 70 25 208 160 72 161 289), lower := (rows 35 262 70 25 208 160 72 128 256), losses := [] }

theorem u6242 : Upper (D 7) (R 7) [34,260,66,17,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6242 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6243 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 128 }], pairs := [(2,0),(2,7),(3,1),(4,1)], upper := (rows 35 262 70 25 208 160 96 137 265), lower := (rows 35 262 70 25 208 160 96 128 256), losses := [] }

theorem u6243 : Upper (D 7) (R 7) [34,260,66,17,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6244 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 262 70 56 81 160 65 136 392), lower := (rows 35 262 70 56 81 160 65 128 256), losses := [] }

theorem u6244 : Upper (D 7) (R 7) [34,260,66,48,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6245 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 262 70 56 81 160 72 129 385), lower := (rows 35 262 70 56 81 160 72 128 256), losses := [] }

theorem u6245 : Upper (D 7) (R 7) [34,260,66,48,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6245 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6246 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 4, region := 168, targets := 64 }], pairs := [(2,0),(3,1),(3,6),(4,1)], upper := (rows 35 262 70 56 81 160 192 137 265), lower := (rows 35 262 70 56 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 5 24 16 224 224 128 256), good := (rows 102 262 102 120 124 224 224 224 256) }] }

theorem u6246 : Upper (D 7) (R 7) [34,260,66,48,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6247 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 262 70 73 145 160 72 176 304), lower := (rows 35 262 70 73 145 160 72 128 256), losses := [] }

theorem u6247 : Upper (D 7) (R 7) [34,260,66,65,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6247 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6248 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 422, targets := 1 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 35 262 70 73 145 160 80 168 296), lower := (rows 35 262 70 73 145 160 80 128 256), losses := [] }

theorem u6248 : Upper (D 7) (R 7) [34,260,66,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6248 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6249 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 262 70 73 145 160 96 152 280), lower := (rows 35 262 70 73 145 160 96 128 256), losses := [] }

theorem u6249 : Upper (D 7) (R 7) [34,260,66,65,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6250 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 262 70 73 152 160 65 176 304), lower := (rows 35 262 70 73 152 160 65 128 256), losses := [] }

theorem u6250 : Upper (D 7) (R 7) [34,260,66,65,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6251 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 262 70 73 152 160 80 161 289), lower := (rows 35 262 70 73 152 160 80 128 256), losses := [] }

theorem u6251 : Upper (D 7) (R 7) [34,260,66,65,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6251 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6252 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 262 70 73 152 160 96 145 273), lower := (rows 35 262 70 73 152 160 96 128 256), losses := [] }

theorem u6252 : Upper (D 7) (R 7) [34,260,66,65,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6253 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 68, targets := 160 }], pairs := [(2,5),(2,7),(3,1),(4,1)], upper := (rows 35 262 70 88 145 160 65 168 296), lower := (rows 35 262 70 88 145 160 65 128 256), losses := [] }

theorem u6253 : Upper (D 7) (R 7) [34,260,66,80,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6254 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 262 70 88 145 160 72 161 289), lower := (rows 35 262 70 88 145 160 72 128 256), losses := [] }

theorem u6254 : Upper (D 7) (R 7) [34,260,66,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6254 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6255 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 68, targets := 1 },{ cop := 0, region := 68, targets := 128 }], pairs := [(2,0),(2,7),(3,1),(4,1)], upper := (rows 35 262 70 88 145 160 96 137 265), lower := (rows 35 262 70 88 145 160 96 128 256), losses := [] }

theorem u6255 : Upper (D 7) (R 7) [34,260,66,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6256 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 262 70 104 145 48 65 136 392), lower := (rows 35 262 70 104 145 48 65 128 256), losses := [] }

theorem u6256 : Upper (D 7) (R 7) [34,260,66,96,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6256 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6257 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 262 70 104 145 48 72 129 385), lower := (rows 35 262 70 104 145 48 72 128 256), losses := [] }

theorem u6257 : Upper (D 7) (R 7) [34,260,66,96,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6257 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6258 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 70 104 145 48 192 137 265), lower := (rows 35 262 70 104 145 48 192 128 256), losses := [] }

theorem u6258 : Upper (D 7) (R 7) [34,260,66,96,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6258 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6259 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 76, targets := 128 }], pairs := [(2,7),(3,1),(3,7),(4,1)], upper := (rows 35 262 70 104 145 160 65 152 280), lower := (rows 35 262 70 104 145 160 65 128 256), losses := [] }

theorem u6259 : Upper (D 7) (R 7) [34,260,66,96,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6260 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 262 70 104 145 160 72 145 273), lower := (rows 35 262 70 104 145 160 72 128 256), losses := [] }

theorem u6260 : Upper (D 7) (R 7) [34,260,66,96,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6260 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6261 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 70 104 145 160 80 137 265), lower := (rows 35 262 70 104 145 160 80 128 256), losses := [] }

theorem u6261 : Upper (D 7) (R 7) [34,260,66,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6261 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6262 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 76, targets := 128 }], pairs := [(2,7),(3,1),(3,7),(4,1)], upper := (rows 35 262 70 104 152 160 65 145 273), lower := (rows 35 262 70 104 152 160 65 128 256), losses := [] }

theorem u6262 : Upper (D 7) (R 7) [34,260,66,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6263 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 262 70 104 152 160 80 129 257), lower := (rows 35 262 70 104 152 160 80 128 256), losses := [] }

theorem u6263 : Upper (D 7) (R 7) [34,260,66,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6263 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6264 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 35 262 70 137 208 40 65 176 304), lower := (rows 35 262 70 137 208 40 65 128 256), losses := [] }

theorem u6264 : Upper (D 7) (R 7) [34,260,66,129,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6264 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6265 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 262 70 137 208 40 80 161 289), lower := (rows 35 262 70 137 208 40 80 128 256), losses := [] }

theorem u6265 : Upper (D 7) (R 7) [34,260,66,129,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6265 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6266 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(3,1),(4,1)], upper := (rows 35 262 70 137 208 40 96 145 273), lower := (rows 35 262 70 137 208 40 96 128 256), losses := [] }

theorem u6266 : Upper (D 7) (R 7) [34,260,66,129,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6266 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6267 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 262 76 26 112 160 65 129 385), lower := (rows 35 262 76 26 112 160 65 128 256), losses := [] }

theorem u6267 : Upper (D 7) (R 7) [34,260,72,18,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6268 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 76 26 112 160 192 129 257), lower := (rows 35 262 76 26 112 160 192 128 256), losses := [] }

theorem u6268 : Upper (D 7) (R 7) [34,260,72,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6269 : Route 9 := (fun mask => (mask,id))

def c6269 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6269 : Upper (D 7) (R 7) [34,260,72,18,192,128,1] 13 := by
  apply FastRouting.sound _ _ [34,260,72,18,192,128,1] 13 (by decide) (choices 1) [1,32] r6269 c6269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u462
  · exact u463

def b6270 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 5, region := 80, targets := 3 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 35 262 76 26 208 160 96 129 257), lower := (rows 35 262 76 26 208 160 96 128 256), losses := [] }

theorem u6270 : Upper (D 7) (R 7) [34,260,72,18,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6271 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 172, targets := 2 },{ cop := 0, region := 80, targets := 32 },{ cop := 0, region := 80, targets := 128 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 35 262 76 137 81 160 66 176 304), lower := (rows 35 262 76 137 81 160 66 128 256), losses := [] }

theorem u6271 : Upper (D 7) (R 7) [34,260,72,129,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6272 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 84, targets := 160 }], pairs := [(2,5),(2,7),(4,5)], upper := (rows 35 262 76 137 81 160 80 162 290), lower := (rows 35 262 76 137 81 160 80 128 256), losses := [] }

theorem u6272 : Upper (D 7) (R 7) [34,260,72,129,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6272 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6273 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 3, region := 100, targets := 2 }], pairs := [(1,5),(2,1),(2,5),(3,5)], upper := (rows 35 262 76 137 81 160 96 146 274), lower := (rows 35 262 76 137 81 160 96 128 256), losses := [] }

theorem u6273 : Upper (D 7) (R 7) [34,260,72,129,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6274 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 2, region := 434, targets := 1 }], pairs := [(1,0),(3,6),(4,0),(4,6)], upper := (rows 35 262 76 137 146 96 65 176 304), lower := (rows 35 262 76 137 146 96 65 128 256), losses := [] }

theorem u6274 : Upper (D 7) (R 7) [34,260,72,129,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6275 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(3,6),(4,6)], upper := (rows 35 262 76 137 146 96 80 161 289), lower := (rows 35 262 76 137 146 96 80 128 256), losses := [] }

theorem u6275 : Upper (D 7) (R 7) [34,260,72,129,130,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6275 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6276 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 262 76 137 146 96 96 145 273), lower := (rows 35 262 76 137 146 96 96 128 256), losses := [] }

theorem u6276 : Upper (D 7) (R 7) [34,260,72,129,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6277 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 2, region := 434, targets := 1 }], pairs := [(1,0),(3,6),(4,0),(4,6)], upper := (rows 35 262 76 137 176 96 65 146 274), lower := (rows 35 262 76 137 176 96 65 128 256), losses := [] }

theorem u6277 : Upper (D 7) (R 7) [34,260,72,129,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6278 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 35 262 76 137 176 96 66 145 273), lower := (rows 35 262 76 137 176 96 66 128 256), losses := [] }

theorem u6278 : Upper (D 7) (R 7) [34,260,72,129,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6279 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 262 76 137 176 96 80 131 259), lower := (rows 35 262 76 137 176 96 80 128 256), losses := [] }

theorem u6279 : Upper (D 7) (R 7) [34,260,72,129,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6279 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6280 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 430, targets := 1 },{ cop := 6, region := 16, targets := 32 }], pairs := [(1,0),(2,0),(3,0),(4,5)], upper := (rows 35 262 76 138 81 160 65 176 304), lower := (rows 35 262 76 138 81 160 65 128 256), losses := [] }

theorem u6280 : Upper (D 7) (R 7) [34,260,72,130,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6281 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 262 76 138 81 160 80 161 289), lower := (rows 35 262 76 138 81 160 80 128 256), losses := [] }

theorem u6281 : Upper (D 7) (R 7) [34,260,72,130,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6281 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6282 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 3, region := 100, targets := 1 }], pairs := [(1,5),(2,0),(2,5),(3,5)], upper := (rows 35 262 76 138 81 160 96 145 273), lower := (rows 35 262 76 138 81 160 96 128 256), losses := [] }

theorem u6282 : Upper (D 7) (R 7) [34,260,72,130,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6283 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(4,1)], upper := (rows 35 262 76 138 208 33 65 176 304), lower := (rows 35 262 76 138 208 33 65 128 256), losses := [] }

theorem u6283 : Upper (D 7) (R 7) [34,260,72,130,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6284 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 84, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 262 76 138 208 33 80 161 289), lower := (rows 35 262 76 138 208 33 80 128 256), losses := [] }

theorem u6284 : Upper (D 7) (R 7) [34,260,72,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6284 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6285 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(4,1)], upper := (rows 35 262 76 138 208 33 96 145 273), lower := (rows 35 262 76 138 208 33 96 128 256), losses := [] }

theorem u6285 : Upper (D 7) (R 7) [34,260,72,130,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6286 : Route 9 := (fun mask => (mask,id))

def c6286 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6286 : Upper (D 7) (R 7) [34,260,72,130,192,16,1] 13 := by
  apply FastRouting.sound _ _ [34,260,72,130,192,16,1] 13 (by decide) (choices 1) [1,32] r6286 c6286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u464
  · exact u465

def b6287 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 262 76 138 208 48 96 129 257), lower := (rows 35 262 76 138 208 48 96 128 256), losses := [] }

theorem u6287 : Upper (D 7) (R 7) [34,260,72,130,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6287 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6288 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 398, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 262 76 152 112 33 65 130 386), lower := (rows 35 262 76 152 112 33 65 128 256), losses := [] }

theorem u6288 : Upper (D 7) (R 7) [34,260,72,144,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6289 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 113, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(0,7),(1,6),(4,7)], upper := (rows 35 262 76 152 112 33 66 129 385), lower := (rows 35 262 76 152 112 33 66 128 256), losses := [] }

theorem u6289 : Upper (D 7) (R 7) [34,260,72,144,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6290 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 262 76 152 112 33 192 131 259), lower := (rows 35 262 76 152 112 33 192 128 256), losses := [] }

theorem u6290 : Upper (D 7) (R 7) [34,260,72,144,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6291 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 386, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 35 262 76 168 81 48 65 130 386), lower := (rows 35 262 76 168 81 48 65 128 256), losses := [] }

theorem u6291 : Upper (D 7) (R 7) [34,260,72,160,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6291 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6292 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 136, targets := 66 },{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7),(3,1),(3,6)], upper := (rows 35 262 76 168 81 48 66 129 385), lower := (rows 35 262 76 168 81 48 66 128 256), losses := [] }

theorem u6292 : Upper (D 7) (R 7) [34,260,72,160,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6292 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6293 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 35 262 76 168 81 48 192 131 259), lower := (rows 35 262 76 168 81 48 192 128 256), losses := [] }

theorem u6293 : Upper (D 7) (R 7) [34,260,72,160,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6293 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6294 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 262 76 168 208 33 65 146 274), lower := (rows 35 262 76 168 208 33 65 128 256), losses := [] }

theorem u6294 : Upper (D 7) (R 7) [34,260,72,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6295 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 208, targets := 32 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(4,5)], upper := (rows 35 262 76 168 208 33 66 145 273), lower := (rows 35 262 76 168 208 33 66 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 57 0 79 161 289), good := (rows 467 326 94 478 208 465 66 128 256) }] }

theorem u6295 : Upper (D 7) (R 7) [34,260,72,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6296 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 84, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 262 76 168 208 33 80 131 259), lower := (rows 35 262 76 168 208 33 80 128 256), losses := [] }

theorem u6296 : Upper (D 7) (R 7) [34,260,72,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6296 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6297 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 262 100 26 81 160 65 136 392), lower := (rows 35 262 100 26 81 160 65 128 256), losses := [] }

theorem u6297 : Upper (D 7) (R 7) [34,260,96,18,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6298 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 262 100 26 81 160 72 129 385), lower := (rows 35 262 100 26 81 160 72 128 256), losses := [] }

theorem u6298 : Upper (D 7) (R 7) [34,260,96,18,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6298 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6299 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 262 100 26 81 160 192 137 265), lower := (rows 35 262 100 26 81 160 192 128 256), losses := [] }

theorem u6299 : Upper (D 7) (R 7) [34,260,96,18,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u6299
end Delivery.IrregularNine14.P07
