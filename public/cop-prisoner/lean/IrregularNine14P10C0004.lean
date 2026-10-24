import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0000

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b240 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 168 276 288 80 161 289), lower := (rows 35 194 76 168 276 288 80 128 256), losses := [] }

theorem u240 : Upper (D 10) (R 10) [34,192,72,160,260,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b240 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b241 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 67, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 76 168 276 288 96 145 273), lower := (rows 35 194 76 168 276 288 96 128 256), losses := [] }

theorem u241 : Upper (D 10) (R 10) [34,192,72,160,260,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b241 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b242 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 265 176 288 68 176 304), lower := (rows 35 194 76 265 176 288 68 128 256), losses := [] }

theorem u242 : Upper (D 10) (R 10) [34,192,72,257,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b242 [(6,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b243 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 76 265 176 288 80 164 292), lower := (rows 35 194 76 265 176 288 80 128 256), losses := [] }

theorem u243 : Upper (D 10) (R 10) [34,192,72,257,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b243 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b244 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 67, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 76 265 176 288 96 148 276), lower := (rows 35 194 76 265 176 288 96 128 256), losses := [] }

theorem u244 : Upper (D 10) (R 10) [34,192,72,257,160,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b244 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b245 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 76 280 176 288 65 164 292), lower := (rows 35 194 76 280 176 288 65 128 256), losses := [] }

theorem u245 : Upper (D 10) (R 10) [34,192,72,272,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b245 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b246 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 280 176 288 68 161 289), lower := (rows 35 194 76 280 176 288 68 128 256), losses := [] }

theorem u246 : Upper (D 10) (R 10) [34,192,72,272,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b246 [(6,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b247 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 67, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 76 280 176 288 96 133 261), lower := (rows 35 194 76 280 176 288 96 128 256), losses := [] }

theorem u247 : Upper (D 10) (R 10) [34,192,72,272,160,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b247 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b248 : PairBound 9 := { available := 32, camps := [], pairs := [], upper := (rows 35 194 76 392 273 48 68 160 288), lower := (rows 35 194 76 392 273 48 68 128 256), losses := [] }

theorem u248 : Upper (D 10) (R 10) [34,192,72,384,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b248 [(5,4),(6,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r249 : Route 9 := (fun mask => (mask,id))

def c249 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u249 : Upper (D 10) (R 10) [34,192,72,384,257,16,32] 13 := by
  apply FastRouting.sound _ _ [34,192,72,384,257,16,32] 13 (by decide) (choices 1) [4,32] r249 c249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6
  · exact u7

def b250 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 100 168 273 288 68 152 280), lower := (rows 35 194 100 168 273 288 68 128 256), losses := [] }

theorem u250 : Upper (D 10) (R 10) [34,192,96,160,257,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b250 [(6,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b251 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 100 168 273 288 72 148 276), lower := (rows 35 194 100 168 273 288 72 128 256), losses := [] }

theorem u251 : Upper (D 10) (R 10) [34,192,96,160,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b251 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b252 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 139, targets := 256 }], pairs := [(0,8)], upper := (rows 35 194 100 168 273 288 80 140 268), lower := (rows 35 194 100 168 273 288 80 128 256), losses := [] }

theorem u252 : Upper (D 10) (R 10) [34,192,96,160,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b252 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b253 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 67, targets := 256 }], pairs := [(0,8)], upper := (rows 35 194 100 168 276 288 65 152 280), lower := (rows 35 194 100 168 276 288 65 128 256), losses := [] }

theorem u253 : Upper (D 10) (R 10) [34,192,96,160,260,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b253 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b254 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 100 168 276 288 72 145 273), lower := (rows 35 194 100 168 276 288 72 128 256), losses := [] }

theorem u254 : Upper (D 10) (R 10) [34,192,96,160,260,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b254 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b255 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 139, targets := 256 }], pairs := [(0,8)], upper := (rows 35 194 100 168 276 288 80 137 265), lower := (rows 35 194 100 168 276 288 80 128 256), losses := [] }

theorem u255 : Upper (D 10) (R 10) [34,192,96,160,260,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b255 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b256 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 67 134 268 104 176 288 65 176 304), lower := (rows 67 134 268 104 176 288 65 128 256), losses := [] }

theorem u256 : Upper (D 10) (R 10) [66,132,264,96,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b256 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b257 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 300, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 268 104 176 288 80 161 289), lower := (rows 67 134 268 104 176 288 80 128 256), losses := [] }

theorem u257 : Upper (D 10) (R 10) [66,132,264,96,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b257 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b258 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 72, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 67 134 268 104 176 288 96 145 273), lower := (rows 67 134 268 104 176 288 96 128 256), losses := [] }

theorem u258 : Upper (D 10) (R 10) [66,132,264,96,160,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b258 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b259 : PairBound 9 := { available := 288, camps := [], pairs := [], upper := (rows 67 134 292 88 176 40 65 416 288), lower := (rows 67 134 292 88 176 40 65 128 256), losses := [] }

theorem u259 : Upper (D 10) (R 10) [66,132,288,80,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b259 [(5,3),(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b260 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 121, targets := 256 }], pairs := [(0,8)], upper := (rows 67 134 292 88 176 40 96 385 257), lower := (rows 67 134 292 88 176 40 96 128 256), losses := [] }

theorem u260 : Upper (D 10) (R 10) [66,132,288,80,160,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b260 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b261 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 184, targets := 256 }], pairs := [(3,8)], upper := (rows 67 134 292 88 176 40 320 161 289), lower := (rows 67 134 292 88 176 40 320 128 256), losses := [] }

theorem u261 : Upper (D 10) (R 10) [66,132,288,80,160,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b261 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b262 : PairBound 9 := { available := 32, camps := [], pairs := [], upper := (rows 67 134 292 88 400 33 72 160 288), lower := (rows 67 134 292 88 400 33 72 128 256), losses := [] }

theorem u262 : Upper (D 10) (R 10) [66,132,288,80,384,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b262 [(5,0),(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b263 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 292 88 400 33 96 168 296), lower := (rows 67 134 292 88 400 33 96 128 256), losses := [] }

theorem u263 : Upper (D 10) (R 10) [66,132,288,80,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b263 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b264 : PairBound 9 := { available := 288, camps := [], pairs := [], upper := (rows 67 134 292 104 152 48 65 416 288), lower := (rows 67 134 292 104 152 48 65 128 256), losses := [] }

theorem u264 : Upper (D 10) (R 10) [66,132,288,96,136,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b264 [(5,4),(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b265 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 121, targets := 256 }], pairs := [(0,8)], upper := (rows 67 134 292 104 152 48 96 385 257), lower := (rows 67 134 292 104 152 48 96 128 256), losses := [] }

theorem u265 : Upper (D 10) (R 10) [66,132,288,96,136,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b265 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b266 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 184, targets := 256 }], pairs := [(3,8)], upper := (rows 67 134 292 104 152 48 320 161 289), lower := (rows 67 134 292 104 152 48 320 128 256), losses := [] }

theorem u266 : Upper (D 10) (R 10) [66,132,288,96,136,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b266 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b267 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 104 280 160 65 176 304), lower := (rows 67 134 292 104 280 160 65 128 256), losses := [] }

theorem u267 : Upper (D 10) (R 10) [66,132,288,96,264,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b267 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b268 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 104 280 160 80 161 289), lower := (rows 67 134 292 104 280 160 80 128 256), losses := [] }

theorem u268 : Upper (D 10) (R 10) [66,132,288,96,264,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b268 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b269 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 105, targets := 256 }], pairs := [(0,8),(3,8)], upper := (rows 67 134 292 104 280 160 96 145 273), lower := (rows 67 134 292 104 280 160 96 128 256), losses := [] }

theorem u269 : Upper (D 10) (R 10) [66,132,288,96,264,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b269 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b270 : PairBound 9 := { available := 32, camps := [], pairs := [], upper := (rows 67 134 292 152 336 33 72 160 288), lower := (rows 67 134 292 152 336 33 72 128 256), losses := [] }

theorem u270 : Upper (D 10) (R 10) [66,132,288,144,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b270 [(5,0),(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b271 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 292 152 336 33 96 168 296), lower := (rows 67 134 292 152 336 33 96 128 256), losses := [] }

theorem u271 : Upper (D 10) (R 10) [66,132,288,144,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b271 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b272 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 292 168 280 96 65 176 304), lower := (rows 67 134 292 168 280 96 65 128 256), losses := [] }

theorem u272 : Upper (D 10) (R 10) [66,132,288,160,264,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b272 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b273 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 292, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 292 168 280 96 80 161 289), lower := (rows 67 134 292 168 280 96 80 128 256), losses := [] }

theorem u273 : Upper (D 10) (R 10) [66,132,288,160,264,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b273 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b274 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 105, targets := 256 }], pairs := [(0,8),(3,8)], upper := (rows 67 134 292 168 280 96 96 145 273), lower := (rows 67 134 292 168 280 96 96 128 256), losses := [] }

theorem u274 : Upper (D 10) (R 10) [66,132,288,160,264,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b274 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b275 : PairBound 9 := { available := 32, camps := [], pairs := [], upper := (rows 67 134 292 200 280 33 80 160 288), lower := (rows 67 134 292 200 280 33 80 128 256), losses := [] }

theorem u275 : Upper (D 10) (R 10) [66,132,288,192,264,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b275 [(5,0),(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b276 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 97, targets := 256 }], pairs := [(0,8)], upper := (rows 67 134 292 200 280 33 96 176 304), lower := (rows 67 134 292 200 280 33 96 128 256), losses := [] }

theorem u276 : Upper (D 10) (R 10) [66,132,288,192,264,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b276 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b277 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 67 162 76 296 400 33 68 176 304), lower := (rows 67 162 76 296 400 33 68 128 256), losses := [] }

theorem u277 : Upper (D 10) (R 10) [66,160,72,288,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b277 [(5,0),(6,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b278 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 67 162 76 296 400 33 80 164 292), lower := (rows 67 162 76 296 400 33 80 128 256), losses := [] }

theorem u278 : Upper (D 10) (R 10) [66,160,72,288,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b278 [(5,0),(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b279 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 76 296 400 33 96 148 276), lower := (rows 67 162 76 296 400 33 96 128 256), losses := [] }

theorem u279 : Upper (D 10) (R 10) [66,160,72,288,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b279 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b280 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 67 162 76 392 304 33 68 176 304), lower := (rows 67 162 76 392 304 33 68 128 256), losses := [] }

theorem u280 : Upper (D 10) (R 10) [66,160,72,384,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b280 [(5,0),(6,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b281 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 67 162 76 392 304 33 80 164 292), lower := (rows 67 162 76 392 304 33 80 128 256), losses := [] }

theorem u281 : Upper (D 10) (R 10) [66,160,72,384,288,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b281 [(5,0),(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b282 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 99, targets := 256 }], pairs := [(0,8)], upper := (rows 67 162 76 392 304 33 96 148 276), lower := (rows 67 162 76 392 304 33 96 128 256), losses := [] }

theorem u282 : Upper (D 10) (R 10) [66,160,72,384,288,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b282 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b283 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 67 162 100 268 400 40 65 176 304), lower := (rows 67 162 100 268 400 40 65 128 256), losses := [] }

theorem u283 : Upper (D 10) (R 10) [66,160,96,260,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b283 [(5,3),(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b284 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 100 268 400 40 80 161 289), lower := (rows 67 162 100 268 400 40 80 128 256), losses := [] }

theorem u284 : Upper (D 10) (R 10) [66,160,96,260,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b284 [(5,3),(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b285 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 100 268 400 40 96 145 273), lower := (rows 67 162 100 268 400 40 96 128 256), losses := [] }

theorem u285 : Upper (D 10) (R 10) [66,160,96,260,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b285 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b286 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 67 162 140 328 304 33 68 176 304), lower := (rows 67 162 140 328 304 33 68 128 256), losses := [] }

theorem u286 : Upper (D 10) (R 10) [66,160,136,320,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b286 [(5,0),(6,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b287 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 67 162 140 328 304 33 80 164 292), lower := (rows 67 162 140 328 304 33 80 128 256), losses := [] }

theorem u287 : Upper (D 10) (R 10) [66,160,136,320,288,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b287 [(5,0),(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b288 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 140 328 304 33 96 148 276), lower := (rows 67 162 140 328 304 33 96 128 256), losses := [] }

theorem u288 : Upper (D 10) (R 10) [66,160,136,320,288,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b288 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b289 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 11 52 104 208 160 352 416 288), lower := (rows 7 11 52 104 208 160 64 128 256), losses := [] }

theorem u289 : Upper (D 10) (R 10) [6,9,48,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b289 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r290 : Route 9 := (fun mask => (mask,id))

def c290 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u290 : Upper (D 10) (R 10) [6,9,48,96,192,256] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,192,256] 13 (by decide) (choices 1) [32,128,256] r290 c290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8
  · exact u9
  · exact u10

def b291 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 52 104 400 96 480 416 416), lower := (rows 7 11 52 104 400 96 64 128 256), losses := [] }

theorem u291 : Upper (D 10) (R 10) [6,9,48,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b291 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b292 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 11 52 104 400 160 352 480 352), lower := (rows 7 11 52 104 400 160 64 128 256), losses := [] }

theorem u292 : Upper (D 10) (R 10) [6,9,48,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b292 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b293 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 340, targets := 128 }], pairs := [(2,7),(4,7)], upper := (rows 7 11 52 200 336 160 352 416 288), lower := (rows 7 11 52 200 336 160 64 128 256), losses := [] }

theorem u293 : Upper (D 10) (R 10) [6,9,48,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b293 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b294 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 203, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 11 52 200 336 288 224 160 416), lower := (rows 7 11 52 200 336 288 64 128 256), losses := [] }

theorem u294 : Upper (D 10) (R 10) [6,9,48,192,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b294 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b295 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 11 84 104 176 160 352 416 288), lower := (rows 7 11 84 104 176 160 64 128 256), losses := [] }

theorem u295 : Upper (D 10) (R 10) [6,9,80,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b295 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r296 : Route 9 := (fun mask => (mask,id))

def c296 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u296 : Upper (D 10) (R 10) [6,9,80,96,160,256] 13 := by
  apply FastRouting.sound _ _ [6,9,80,96,160,256] 13 (by decide) (choices 1) [32,128,256] r296 c296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11
  · exact u12
  · exact u13

def b297 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 5, region := 328, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 7 11 84 104 400 160 352 416 288), lower := (rows 7 11 84 104 400 160 64 128 256), losses := [] }

theorem u297 : Upper (D 10) (R 10) [6,9,80,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b297 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b298 : PairBound 9 := { available := 416, camps := [{ cop := 5, region := 408, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 11 84 168 304 96 480 416 416), lower := (rows 7 11 84 168 304 96 64 128 256), losses := [] }

theorem u298 : Upper (D 10) (R 10) [6,9,80,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b298 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b299 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 11 84 168 304 160 352 480 352), lower := (rows 7 11 84 168 304 160 64 128 256), losses := [] }

theorem u299 : Upper (D 10) (R 10) [6,9,80,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b299 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u299
end Delivery.IrregularNine14.P10
