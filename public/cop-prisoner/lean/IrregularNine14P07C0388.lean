import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0122
import IrregularNine14P07C0123

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23280 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 228, targets := 1 },{ cop := 4, region := 488, targets := 2 }], pairs := [(0,1),(0,7),(2,0),(3,1)], upper := (rows 37 74 134 265 19 96 240 176 432), lower := (rows 37 74 134 265 19 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 24 16 114 80 144 272), good := (rows 37 104 165 265 505 96 96 128 256) },{ target := 7, region := (rows 5 2 4 8 20 98 64 0 256), good := (rows 53 106 55 265 51 96 96 0 256) }] }

theorem u23280 : Upper (D 7) (R 7) [36,72,130,257,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23281 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 74 134 265 19 160 112 240 368), lower := (rows 37 74 134 265 19 160 64 128 256), losses := [] }

theorem u23281 : Upper (D 7) (R 7) [36,72,130,257,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23282 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 74 134 265 50 33 208 208 464), lower := (rows 37 74 134 265 50 33 64 128 256), losses := [] }

theorem u23282 : Upper (D 7) (R 7) [36,72,130,257,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23283 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 74 134 265 50 48 193 193 449), lower := (rows 37 74 134 265 50 48 64 128 256), losses := [] }

theorem u23283 : Upper (D 7) (R 7) [36,72,130,257,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23283 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23284 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 74 134 265 50 96 209 145 401), lower := (rows 37 74 134 265 50 96 64 128 256), losses := [] }

theorem u23284 : Upper (D 7) (R 7) [36,72,130,257,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23285 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 74 134 265 50 160 81 209 337), lower := (rows 37 74 134 265 50 160 64 128 256), losses := [] }

theorem u23285 : Upper (D 7) (R 7) [36,72,130,257,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23286 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 74 134 265 81 34 240 176 432), lower := (rows 37 74 134 265 81 34 64 128 256), losses := [] }

theorem u23286 : Upper (D 7) (R 7) [36,72,130,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23286 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23287 : Route 9 := (fun mask => (mask,id))

def c23287 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u23287 : Upper (D 7) (R 7) [36,72,130,257,65,16] 13 := by
  apply FastRouting.sound _ _ [36,72,130,257,65,16] 13 (by decide) (choices 1) [2,32,128] r23287 c23287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7370
  · exact u7371
  · exact u7372

def b23288 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 134 265 81 160 114 178 306), lower := (rows 37 74 134 265 81 160 64 128 256), losses := [] }

theorem u23288 : Upper (D 7) (R 7) [36,72,130,257,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23289 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 74 134 265 112 33 210 146 402), lower := (rows 37 74 134 265 112 33 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 18 45 64 128 256), good := (rows 37 120 181 297 112 33 64 128 256) }] }

theorem u23289 : Upper (D 7) (R 7) [36,72,130,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23290 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 48, targets := 129 }], pairs := [(3,1),(4,0),(4,1),(4,7)], upper := (rows 37 74 134 265 112 34 209 145 401), lower := (rows 37 74 134 265 112 34 64 128 256), losses := [] }

theorem u23290 : Upper (D 7) (R 7) [36,72,130,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23291 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 134 265 112 48 195 131 387), lower := (rows 37 74 134 265 112 48 64 128 256), losses := [] }

theorem u23291 : Upper (D 7) (R 7) [36,72,130,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23291 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23292 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 134 265 112 160 83 147 275), lower := (rows 37 74 134 265 112 160 64 128 256), losses := [] }

theorem u23292 : Upper (D 7) (R 7) [36,72,130,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23293 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 49, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 74 134 265 145 34 112 240 368), lower := (rows 37 74 134 265 145 34 64 128 256), losses := [] }

theorem u23293 : Upper (D 7) (R 7) [36,72,130,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23294 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 74 134 265 145 48 98 226 354), lower := (rows 37 74 134 265 145 48 64 128 256), losses := [] }

theorem u23294 : Upper (D 7) (R 7) [36,72,130,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23294 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23295 : PairBound 9 := { available := 50, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(0,1),(1,7),(3,7),(4,1)], upper := (rows 37 74 134 265 145 96 114 178 306), lower := (rows 37 74 134 265 145 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 20 98 64 128 256), good := (rows 53 104 181 265 145 96 96 128 256) }] }

theorem u23295 : Upper (D 7) (R 7) [36,72,130,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23296 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 74 134 265 176 33 82 210 338), lower := (rows 37 74 134 265 176 33 64 128 256), losses := [] }

theorem u23296 : Upper (D 7) (R 7) [36,72,130,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23297 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 49, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 74 134 265 176 34 81 209 337), lower := (rows 37 74 134 265 176 34 64 128 256), losses := [] }

theorem u23297 : Upper (D 7) (R 7) [36,72,130,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23298 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 74 134 265 176 48 67 195 323), lower := (rows 37 74 134 265 176 48 64 128 256), losses := [] }

theorem u23298 : Upper (D 7) (R 7) [36,72,130,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23298 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23299 : PairBound 9 := { available := 19, camps := [], pairs := [(0,1),(0,7),(4,0),(4,1)], upper := (rows 37 74 134 265 176 96 83 147 275), lower := (rows 37 74 134 265 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 98 64 128 256), good := (rows 52 106 182 264 176 96 96 128 256) },{ target := 1, region := (rows 5 0 4 8 20 98 64 128 256), good := (rows 53 104 181 265 176 96 96 128 256) },{ target := 7, region := (rows 5 2 4 8 16 98 64 0 256), good := (rows 37 106 39 265 48 96 96 0 256) }] }

theorem u23299 : Upper (D 7) (R 7) [36,72,130,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23300 : Route 9 := (fun mask => (mask,id))

def c23300 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23300 : Upper (D 7) (R 7) [36,72,130,257,192,1] 13 := by
  apply FastRouting.sound _ _ [36,72,130,257,192,1] 13 (by decide) (choices 1) [2,16,32] r23300 c23300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7373
  · exact u7374
  · exact u7375

def b23301 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 74 134 265 208 34 113 177 305), lower := (rows 37 74 134 265 208 34 64 128 256), losses := [] }

theorem u23301 : Upper (D 7) (R 7) [36,72,130,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23302 : Route 9 := (fun mask => (mask,id))

def c23302 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23302 : Upper (D 7) (R 7) [36,72,130,257,192,16] 13 := by
  apply FastRouting.sound _ _ [36,72,130,257,192,16] 13 (by decide) (choices 1) [1,2,32] r23302 c23302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7376
  · exact u7377
  · exact u7378

def b23303 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 74 134 266 81 33 240 176 432), lower := (rows 37 74 134 266 81 33 64 128 256), losses := [] }

theorem u23303 : Upper (D 7) (R 7) [36,72,130,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23304 : Route 9 := (fun mask => (mask,id))

def c23304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u23304 : Upper (D 7) (R 7) [36,72,130,258,65,16] 13 := by
  apply FastRouting.sound _ _ [36,72,130,258,65,16] 13 (by decide) (choices 1) [1,32,128] r23304 c23304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7379
  · exact u7380
  · exact u7381

def b23305 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 134 266 81 160 113 177 305), lower := (rows 37 74 134 266 81 160 64 128 256), losses := [] }

theorem u23305 : Upper (D 7) (R 7) [36,72,130,258,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23305 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23306 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 74 134 266 112 33 209 145 401), lower := (rows 37 74 134 266 112 33 64 128 256), losses := [] }

theorem u23306 : Upper (D 7) (R 7) [36,72,130,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23307 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 134 266 112 48 193 129 385), lower := (rows 37 74 134 266 112 48 64 128 256), losses := [] }

theorem u23307 : Upper (D 7) (R 7) [36,72,130,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23307 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23308 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 134 266 112 160 81 145 273), lower := (rows 37 74 134 266 112 160 64 128 256), losses := [] }

theorem u23308 : Upper (D 7) (R 7) [36,72,130,258,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23309 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 49, targets := 2 },{ cop := 2, region := 49, targets := 64 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 74 134 266 176 33 81 209 337), lower := (rows 37 74 134 266 176 33 64 128 256), losses := [] }

theorem u23309 : Upper (D 7) (R 7) [36,72,130,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23310 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 134 266 176 48 65 193 321), lower := (rows 37 74 134 266 176 48 64 128 256), losses := [] }

theorem u23310 : Upper (D 7) (R 7) [36,72,130,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23310 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23311 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,1),(4,0),(4,1),(4,6)], upper := (rows 37 74 134 266 176 96 81 145 273), lower := (rows 37 74 134 266 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 98 64 128 256), good := (rows 52 106 182 298 176 96 96 128 256) }] }

theorem u23311 : Upper (D 7) (R 7) [36,72,130,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23312 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 113, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 74 134 266 208 33 113 177 305), lower := (rows 37 74 134 266 208 33 64 128 256), losses := [] }

theorem u23312 : Upper (D 7) (R 7) [36,72,130,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23313 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 113, targets := 2 }], pairs := [(0,1),(1,7),(3,7)], upper := (rows 37 74 134 266 208 48 97 161 289), lower := (rows 37 74 134 266 208 48 64 128 256), losses := [] }

theorem u23313 : Upper (D 7) (R 7) [36,72,130,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23313 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23314 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 74 134 280 19 33 224 224 480), lower := (rows 37 74 134 280 19 33 64 128 256), losses := [] }

theorem u23314 : Upper (D 7) (R 7) [36,72,130,272,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23315 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 97, targets := 2 },{ cop := 4, region := 488, targets := 2 }], pairs := [(0,1),(2,6),(3,1),(3,6)], upper := (rows 37 74 134 280 19 96 225 161 417), lower := (rows 37 74 134 280 19 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 32 0 129 257), good := (rows 421 10 134 284 415 32 0 128 256) }] }

theorem u23315 : Upper (D 7) (R 7) [36,72,130,272,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23316 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 74 134 280 19 160 97 225 353), lower := (rows 37 74 134 280 19 160 64 128 256), losses := [] }

theorem u23316 : Upper (D 7) (R 7) [36,72,130,272,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23317 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 74 134 280 50 33 193 193 449), lower := (rows 37 74 134 280 50 33 64 128 256), losses := [] }

theorem u23317 : Upper (D 7) (R 7) [36,72,130,272,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23318 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 74 134 280 50 96 193 129 385), lower := (rows 37 74 134 280 50 96 64 128 256), losses := [] }

theorem u23318 : Upper (D 7) (R 7) [36,72,130,272,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23319 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 74 134 280 50 160 65 193 321), lower := (rows 37 74 134 280 50 160 64 128 256), losses := [] }

theorem u23319 : Upper (D 7) (R 7) [36,72,130,272,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23320 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 2, region := 33, targets := 130 }], pairs := [(0,1),(0,6),(0,7),(2,6)], upper := (rows 37 74 134 280 81 33 226 162 418), lower := (rows 37 74 134 280 81 33 64 128 256), losses := [] }

theorem u23320 : Upper (D 7) (R 7) [36,72,130,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23321 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,1),(4,1)], upper := (rows 37 74 134 280 81 34 225 161 417), lower := (rows 37 74 134 280 81 34 64 128 256), losses := [] }

theorem u23321 : Upper (D 7) (R 7) [36,72,130,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23322 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 74 134 280 81 160 99 163 291), lower := (rows 37 74 134 280 81 160 64 128 256), losses := [] }

theorem u23322 : Upper (D 7) (R 7) [36,72,130,272,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23323 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 2, region := 33, targets := 130 }], pairs := [(0,1),(0,6),(0,7),(2,6)], upper := (rows 37 74 134 280 112 33 195 131 387), lower := (rows 37 74 134 280 112 33 64 128 256), losses := [] }

theorem u23323 : Upper (D 7) (R 7) [36,72,130,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23324 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 48, targets := 129 }], pairs := [(3,1),(4,0),(4,1),(4,7)], upper := (rows 37 74 134 280 112 34 193 129 385), lower := (rows 37 74 134 280 112 34 64 128 256), losses := [] }

theorem u23324 : Upper (D 7) (R 7) [36,72,130,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23325 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 74 134 280 112 160 67 131 259), lower := (rows 37 74 134 280 112 160 64 128 256), losses := [] }

theorem u23325 : Upper (D 7) (R 7) [36,72,130,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23326 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 74 134 280 145 33 98 226 354), lower := (rows 37 74 134 280 145 33 64 128 256), losses := [] }

theorem u23326 : Upper (D 7) (R 7) [36,72,130,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23327 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 49, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 74 134 280 145 34 97 225 353), lower := (rows 37 74 134 280 145 34 64 128 256), losses := [] }

theorem u23327 : Upper (D 7) (R 7) [36,72,130,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23328 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(3,7)], upper := (rows 37 74 134 280 145 96 99 163 291), lower := (rows 37 74 134 280 145 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 20 98 64 128 256), good := (rows 53 104 181 280 145 96 96 128 256) }] }

theorem u23328 : Upper (D 7) (R 7) [36,72,130,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23329 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 74 134 280 176 33 67 195 323), lower := (rows 37 74 134 280 176 33 64 128 256), losses := [] }

theorem u23329 : Upper (D 7) (R 7) [36,72,130,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23330 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 49, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 74 134 280 176 34 65 193 321), lower := (rows 37 74 134 280 176 34 64 128 256), losses := [] }

theorem u23330 : Upper (D 7) (R 7) [36,72,130,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23331 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(4,0),(4,1)], upper := (rows 37 74 134 280 176 96 67 131 259), lower := (rows 37 74 134 280 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 98 64 128 256), good := (rows 52 106 182 280 176 96 96 128 256) },{ target := 1, region := (rows 5 0 4 8 20 98 64 128 256), good := (rows 53 104 181 280 176 96 96 128 256) }] }

theorem u23331 : Upper (D 7) (R 7) [36,72,130,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23332 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 2, region := 33, targets := 2 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,6)], upper := (rows 37 74 134 280 208 33 99 163 291), lower := (rows 37 74 134 280 208 33 64 128 256), losses := [] }

theorem u23332 : Upper (D 7) (R 7) [36,72,130,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23333 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,1),(4,1)], upper := (rows 37 74 134 280 208 34 97 161 289), lower := (rows 37 74 134 280 208 34 64 128 256), losses := [] }

theorem u23333 : Upper (D 7) (R 7) [36,72,130,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23334 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 37 74 134 296 19 33 208 208 464), lower := (rows 37 74 134 296 19 33 64 128 256), losses := [] }

theorem u23334 : Upper (D 7) (R 7) [36,72,130,288,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23335 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 74 134 296 19 48 193 193 449), lower := (rows 37 74 134 296 19 48 64 128 256), losses := [] }

theorem u23335 : Upper (D 7) (R 7) [36,72,130,288,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23335 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23336 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 488, targets := 2 },{ cop := 4, region := 132, targets := 32 },{ cop := 4, region := 132, targets := 64 }], pairs := [(0,1),(2,5),(2,6),(3,1)], upper := (rows 37 74 134 296 19 96 209 145 401), lower := (rows 37 74 134 296 19 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 24 16 114 80 144 272), good := (rows 37 104 165 296 505 96 96 128 256) }] }

theorem u23336 : Upper (D 7) (R 7) [36,72,130,288,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23337 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 74 134 296 19 160 81 209 337), lower := (rows 37 74 134 296 19 160 64 128 256), losses := [] }

theorem u23337 : Upper (D 7) (R 7) [36,72,130,288,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23338 : Route 9 := (fun mask => (mask,id))

def c23338 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23338 : Upper (D 7) (R 7) [36,72,130,288,65,1] 13 := by
  apply FastRouting.sound _ _ [36,72,130,288,65,1] 13 (by decide) (choices 1) [2,16,128] r23338 c23338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7382
  · exact u7383
  · exact u7384

def b23339 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 74 134 296 81 34 209 145 401), lower := (rows 37 74 134 296 81 34 64 128 256), losses := [] }

theorem u23339 : Upper (D 7) (R 7) [36,72,130,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u23339
end Delivery.IrregularNine14.P07
