import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0029
import IrregularNine14P07C0030

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13260 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 42 100 137 273 96 210 146 402), lower := (rows 7 42 100 137 273 96 64 128 256), losses := [] }

theorem u13260 : Upper (D 7) (R 7) [6,40,96,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13261 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 100 137 273 160 82 210 338), lower := (rows 7 42 100 137 273 160 64 128 256), losses := [] }

theorem u13261 : Upper (D 7) (R 7) [6,40,96,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13262 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 100 137 274 33 208 208 464), lower := (rows 7 42 100 137 274 33 64 128 256), losses := [] }

theorem u13262 : Upper (D 7) (R 7) [6,40,96,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13263 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 42 100 137 274 48 193 193 449), lower := (rows 7 42 100 137 274 48 64 128 256), losses := [] }

theorem u13263 : Upper (D 7) (R 7) [6,40,96,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13263 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13264 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 42 100 137 274 96 209 145 401), lower := (rows 7 42 100 137 274 96 64 128 256), losses := [] }

theorem u13264 : Upper (D 7) (R 7) [6,40,96,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13265 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 100 137 274 160 81 209 337), lower := (rows 7 42 100 137 274 160 64 128 256), losses := [] }

theorem u13265 : Upper (D 7) (R 7) [6,40,96,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13266 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 100 137 336 33 210 146 402), lower := (rows 7 42 100 137 336 33 64 128 256), losses := [] }

theorem u13266 : Upper (D 7) (R 7) [6,40,96,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13267 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 137 336 34 209 145 401), lower := (rows 7 42 100 137 336 34 64 128 256), losses := [] }

theorem u13267 : Upper (D 7) (R 7) [6,40,96,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13268 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 137 336 48 195 131 387), lower := (rows 7 42 100 137 336 48 64 128 256), losses := [] }

theorem u13268 : Upper (D 7) (R 7) [6,40,96,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13268 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13269 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 100 137 336 160 83 147 275), lower := (rows 7 42 100 137 336 160 64 128 256), losses := [] }

theorem u13269 : Upper (D 7) (R 7) [6,40,96,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13270 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 100 137 400 33 82 210 338), lower := (rows 7 42 100 137 400 33 64 128 256), losses := [] }

theorem u13270 : Upper (D 7) (R 7) [6,40,96,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13271 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 137 400 34 81 209 337), lower := (rows 7 42 100 137 400 34 64 128 256), losses := [] }

theorem u13271 : Upper (D 7) (R 7) [6,40,96,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13272 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 42 100 137 400 48 67 195 323), lower := (rows 7 42 100 137 400 48 64 128 256), losses := [] }

theorem u13272 : Upper (D 7) (R 7) [6,40,96,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13272 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13273 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 42 100 137 400 96 83 147 275), lower := (rows 7 42 100 137 400 96 64 128 256), losses := [] }

theorem u13273 : Upper (D 7) (R 7) [6,40,96,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13274 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 152 82 33 449 385 385), lower := (rows 7 42 100 152 82 33 64 128 256), losses := [] }

theorem u13274 : Upper (D 7) (R 7) [6,40,96,144,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13275 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 100 152 82 160 321 385 257), lower := (rows 7 42 100 152 82 160 64 128 256), losses := [] }

theorem u13275 : Upper (D 7) (R 7) [6,40,96,144,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13276 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 42 100 152 82 288 193 129 385), lower := (rows 7 42 100 152 82 288 64 128 256), losses := [] }

theorem u13276 : Upper (D 7) (R 7) [6,40,96,144,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13276 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13277 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(4,5)], upper := (rows 7 42 100 152 273 33 194 194 450), lower := (rows 7 42 100 152 273 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 38 24 16 32 67 131 259), good := (rows 454 494 100 152 472 484 64 128 256) }] }

theorem u13277 : Upper (D 7) (R 7) [6,40,96,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13278 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 152 273 34 193 193 449), lower := (rows 7 42 100 152 273 34 64 128 256), losses := [] }

theorem u13278 : Upper (D 7) (R 7) [6,40,96,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13279 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 42 100 152 273 96 195 131 387), lower := (rows 7 42 100 152 273 96 64 128 256), losses := [] }

theorem u13279 : Upper (D 7) (R 7) [6,40,96,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13280 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 100 152 273 160 67 195 323), lower := (rows 7 42 100 152 273 160 64 128 256), losses := [] }

theorem u13280 : Upper (D 7) (R 7) [6,40,96,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13281 : Route 9 := (fun mask => (mask,id))

def c13281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13281 : Upper (D 7) (R 7) [6,40,96,144,258,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,258,1] 13 (by decide) (choices 1) [1,128] r13281 c13281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1794
  · exact u1795

def b13282 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 42 100 152 274 96 193 129 385), lower := (rows 7 42 100 152 274 96 64 128 256), losses := [] }

theorem u13282 : Upper (D 7) (R 7) [6,40,96,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13283 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 100 152 274 160 65 193 321), lower := (rows 7 42 100 152 274 160 64 128 256), losses := [] }

theorem u13283 : Upper (D 7) (R 7) [6,40,96,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13284 : Route 9 := (fun mask => (mask,id))

def c13284 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13284 : Upper (D 7) (R 7) [6,40,96,144,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,320,1] 13 (by decide) (choices 1) [1,2,128] r13284 c13284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1796
  · exact u1797
  · exact u1798

def b13285 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 152 336 34 193 129 385), lower := (rows 7 42 100 152 336 34 64 128 256), losses := [] }

theorem u13285 : Upper (D 7) (R 7) [6,40,96,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13286 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 100 152 336 160 67 131 259), lower := (rows 7 42 100 152 336 160 64 128 256), losses := [] }

theorem u13286 : Upper (D 7) (R 7) [6,40,96,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13286 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13287 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 42 100 200 145 33 338 402 274), lower := (rows 7 42 100 200 145 33 64 128 256), losses := [] }

theorem u13287 : Upper (D 7) (R 7) [6,40,96,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13288 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 200 145 34 337 401 273), lower := (rows 7 42 100 200 145 34 64 128 256), losses := [] }

theorem u13288 : Upper (D 7) (R 7) [6,40,96,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13289 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 42 100 200 145 48 323 387 259), lower := (rows 7 42 100 200 145 48 64 128 256), losses := [] }

theorem u13289 : Upper (D 7) (R 7) [6,40,96,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13289 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13290 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 7 42 100 200 145 288 83 147 275), lower := (rows 7 42 100 200 145 288 64 128 256), losses := [] }

theorem u13290 : Upper (D 7) (R 7) [6,40,96,192,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13290 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13291 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 42 100 200 273 33 210 146 402), lower := (rows 7 42 100 200 273 33 64 128 256), losses := [] }

theorem u13291 : Upper (D 7) (R 7) [6,40,96,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13292 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 200 273 34 209 145 401), lower := (rows 7 42 100 200 273 34 64 128 256), losses := [] }

theorem u13292 : Upper (D 7) (R 7) [6,40,96,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13293 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 7 42 100 200 273 48 195 131 387), lower := (rows 7 42 100 200 273 48 64 128 256), losses := [] }

theorem u13293 : Upper (D 7) (R 7) [6,40,96,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13293 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13294 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 100 200 273 160 83 147 275), lower := (rows 7 42 100 200 273 160 64 128 256), losses := [] }

theorem u13294 : Upper (D 7) (R 7) [6,40,96,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13295 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 42 100 200 274 33 209 145 401), lower := (rows 7 42 100 200 274 33 64 128 256), losses := [] }

theorem u13295 : Upper (D 7) (R 7) [6,40,96,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13296 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 42 100 200 274 48 193 129 385), lower := (rows 7 42 100 200 274 48 64 128 256), losses := [] }

theorem u13296 : Upper (D 7) (R 7) [6,40,96,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13296 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13297 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 100 200 274 160 81 145 273), lower := (rows 7 42 100 200 274 160 64 128 256), losses := [] }

theorem u13297 : Upper (D 7) (R 7) [6,40,96,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13298 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 42 100 200 400 33 83 147 275), lower := (rows 7 42 100 200 400 33 64 128 256), losses := [] }

theorem u13298 : Upper (D 7) (R 7) [6,40,96,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13299 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 200 400 34 81 145 273), lower := (rows 7 42 100 200 400 34 64 128 256), losses := [] }

theorem u13299 : Upper (D 7) (R 7) [6,40,96,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13300 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 42 100 200 400 48 67 131 259), lower := (rows 7 42 100 200 400 48 64 128 256), losses := [] }

theorem u13300 : Upper (D 7) (R 7) [6,40,96,192,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13300 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13301 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 100 265 82 33 208 144 400), lower := (rows 7 42 100 265 82 33 64 128 256), losses := [] }

theorem u13301 : Upper (D 7) (R 7) [6,40,96,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13302 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 265 82 48 193 129 385), lower := (rows 7 42 100 265 82 48 64 128 256), losses := [] }

theorem u13302 : Upper (D 7) (R 7) [6,40,96,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13302 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13303 : Route 9 := (fun mask => (mask,id))

def c13303 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13303 : Upper (D 7) (R 7) [6,40,96,257,66,128] 13 := by
  apply FastRouting.sound _ _ [6,40,96,257,66,128] 13 (by decide) (choices 1) [1,16,128] r13303 c13303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1799
  · exact u1800
  · exact u1801

def b13304 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 265 145 34 208 208 464), lower := (rows 7 42 100 265 145 34 64 128 256), losses := [] }

theorem u13304 : Upper (D 7) (R 7) [6,40,96,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13305 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 100 265 145 48 194 194 450), lower := (rows 7 42 100 265 145 48 64 128 256), losses := [] }

theorem u13305 : Upper (D 7) (R 7) [6,40,96,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13305 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13306 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 42 100 265 145 96 210 146 402), lower := (rows 7 42 100 265 145 96 64 128 256), losses := [] }

theorem u13306 : Upper (D 7) (R 7) [6,40,96,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13307 : Route 9 := (fun mask => (mask,id))

def c13307 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13307 : Upper (D 7) (R 7) [6,40,96,257,129,128] 13 := by
  apply FastRouting.sound _ _ [6,40,96,257,129,128] 13 (by decide) (choices 1) [2,16] r13307 c13307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1802
  · exact u1803

def b13308 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 100 265 146 33 208 208 464), lower := (rows 7 42 100 265 146 33 64 128 256), losses := [] }

theorem u13308 : Upper (D 7) (R 7) [6,40,96,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13309 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 42 100 265 146 48 193 193 449), lower := (rows 7 42 100 265 146 48 64 128 256), losses := [] }

theorem u13309 : Upper (D 7) (R 7) [6,40,96,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13309 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13310 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 42 100 265 146 96 209 145 401), lower := (rows 7 42 100 265 146 96 64 128 256), losses := [] }

theorem u13310 : Upper (D 7) (R 7) [6,40,96,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13311 : Route 9 := (fun mask => (mask,id))

def c13311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13311 : Upper (D 7) (R 7) [6,40,96,257,130,128] 13 := by
  apply FastRouting.sound _ _ [6,40,96,257,130,128] 13 (by decide) (choices 1) [1,16] r13311 c13311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1804
  · exact u1805

def b13312 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 100 265 208 33 210 146 402), lower := (rows 7 42 100 265 208 33 64 128 256), losses := [] }

theorem u13312 : Upper (D 7) (R 7) [6,40,96,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13313 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 265 208 34 209 145 401), lower := (rows 7 42 100 265 208 34 64 128 256), losses := [] }

theorem u13313 : Upper (D 7) (R 7) [6,40,96,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13314 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 265 208 48 195 131 387), lower := (rows 7 42 100 265 208 48 64 128 256), losses := [] }

theorem u13314 : Upper (D 7) (R 7) [6,40,96,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13314 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13315 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,5),(4,5)], upper := (rows 7 42 100 265 208 160 83 147 275), lower := (rows 7 42 100 265 208 160 64 128 256), losses := [] }

theorem u13315 : Upper (D 7) (R 7) [6,40,96,257,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13316 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 280 82 33 193 129 385), lower := (rows 7 42 100 280 82 33 64 128 256), losses := [] }

theorem u13316 : Upper (D 7) (R 7) [6,40,96,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13317 : Route 9 := (fun mask => (mask,id))

def c13317 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13317 : Upper (D 7) (R 7) [6,40,96,272,66,128] 13 := by
  apply FastRouting.sound _ _ [6,40,96,272,66,128] 13 (by decide) (choices 1) [1,128] r13317 c13317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1806
  · exact u1807

def b13318 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(4,5)], upper := (rows 7 42 100 280 145 33 194 194 450), lower := (rows 7 42 100 280 145 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 38 24 16 32 67 131 259), good := (rows 454 494 100 280 472 484 64 128 256) }] }

theorem u13318 : Upper (D 7) (R 7) [6,40,96,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13319 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 100 280 145 34 193 193 449), lower := (rows 7 42 100 280 145 34 64 128 256), losses := [] }

theorem u13319 : Upper (D 7) (R 7) [6,40,96,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u13319
end Delivery.IrregularNine14.P07
