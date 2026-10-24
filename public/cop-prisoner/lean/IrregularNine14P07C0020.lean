import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0000

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1200 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 84, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 138 208 288 80 161 289), lower := (rows 7 35 76 138 208 288 80 128 256), losses := [] }

theorem u1200 : Upper (D 7) (R 7) [6,33,72,130,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1200 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1201 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 496, targets := 2 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 7 35 76 138 208 288 96 145 273), lower := (rows 7 35 76 138 208 288 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 288 354 128 256), good := (rows 70 98 92 222 208 352 96 128 352) }] }

theorem u1201 : Upper (D 7) (R 7) [6,33,72,130,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1201 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1202 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 1, region := 80, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 7 35 76 152 112 288 65 130 386), lower := (rows 7 35 76 152 112 288 65 128 256), losses := [] }

theorem u1202 : Upper (D 7) (R 7) [6,33,72,144,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1202 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1203 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 129 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(4,0),(4,7)], upper := (rows 7 35 76 152 112 288 66 129 385), lower := (rows 7 35 76 152 112 288 66 128 256), losses := [] }

theorem u1203 : Upper (D 7) (R 7) [6,33,72,144,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1203 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1204 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 35 76 152 112 288 192 131 259), lower := (rows 7 35 76 152 112 288 192 128 256), losses := [] }

theorem u1204 : Upper (D 7) (R 7) [6,33,72,144,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1204 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1205 : Route 9 := (fun mask => (mask,id))

def c1205 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1205 : Upper (D 7) (R 7) [6,33,72,144,288,128,1] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,288,128,1] 13 (by decide) (choices 1) [2,64] r1205 c1205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u28
  · exact u29

def r1206 : Route 9 := (fun mask => (mask,id))

def c1206 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1206 : Upper (D 7) (R 7) [6,33,72,144,288,128,2] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,288,128,2] 13 (by decide) (choices 1) [1,64] r1206 c1206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u30
  · exact u31

def b1207 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(1,6),(2,0),(4,7)], upper := (rows 7 35 76 152 336 160 65 162 290), lower := (rows 7 35 76 152 336 160 65 128 256), losses := [{ target := 0, region := (rows 0 2 84 72 80 235 64 131 259), good := (rows 422 418 124 188 380 160 508 160 256) }] }

theorem u1207 : Upper (D 7) (R 7) [6,33,72,144,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1208 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(1,6),(2,1),(4,7)], upper := (rows 7 35 76 152 336 160 66 161 289), lower := (rows 7 35 76 152 336 160 66 128 256), losses := [{ target := 1, region := (rows 1 0 84 72 80 235 64 131 259), good := (rows 421 417 124 188 380 160 508 160 256) }] }

theorem u1208 : Upper (D 7) (R 7) [6,33,72,144,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1209 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 3, region := 100, targets := 3 }], pairs := [(0,6),(1,6),(2,0),(2,1)], upper := (rows 7 35 76 152 336 160 96 131 259), lower := (rows 7 35 76 152 336 160 96 128 256), losses := [] }

theorem u1209 : Upper (D 7) (R 7) [6,33,72,144,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1210 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 76 168 82 288 65 144 400), lower := (rows 7 35 76 168 82 288 65 128 256), losses := [] }

theorem u1210 : Upper (D 7) (R 7) [6,33,72,160,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1210 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1211 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 76 168 82 288 80 129 385), lower := (rows 7 35 76 168 82 288 80 128 256), losses := [] }

theorem u1211 : Upper (D 7) (R 7) [6,33,72,160,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1211 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1212 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 35 76 168 82 288 192 145 273), lower := (rows 7 35 76 168 82 288 192 128 256), losses := [] }

theorem u1212 : Upper (D 7) (R 7) [6,33,72,160,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1212 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1213 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 76 168 145 288 66 208 336), lower := (rows 7 35 76 168 145 288 66 128 256), losses := [] }

theorem u1213 : Upper (D 7) (R 7) [6,33,72,160,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1213 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1214 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 76 168 145 288 80 194 322), lower := (rows 7 35 76 168 145 288 80 128 256), losses := [] }

theorem u1214 : Upper (D 7) (R 7) [6,33,72,160,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1214 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1215 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 76 168 146 288 65 208 336), lower := (rows 7 35 76 168 146 288 65 128 256), losses := [] }

theorem u1215 : Upper (D 7) (R 7) [6,33,72,160,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1215 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1216 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 76 168 146 288 80 193 321), lower := (rows 7 35 76 168 146 288 80 128 256), losses := [] }

theorem u1216 : Upper (D 7) (R 7) [6,33,72,160,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1216 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1217 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 76 168 208 288 65 146 274), lower := (rows 7 35 76 168 208 288 65 128 256), losses := [] }

theorem u1217 : Upper (D 7) (R 7) [6,33,72,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1217 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1218 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 76 168 208 288 66 145 273), lower := (rows 7 35 76 168 208 288 66 128 256), losses := [] }

theorem u1218 : Upper (D 7) (R 7) [6,33,72,160,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1218 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1219 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 84, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 168 208 288 80 131 259), lower := (rows 7 35 76 168 208 288 80 128 256), losses := [] }

theorem u1219 : Upper (D 7) (R 7) [6,33,72,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1219 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1220 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 76 168 336 48 65 130 386), lower := (rows 7 35 76 168 336 48 65 128 256), losses := [] }

theorem u1220 : Upper (D 7) (R 7) [6,33,72,160,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1220 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1221 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 76 168 336 48 66 129 385), lower := (rows 7 35 76 168 336 48 66 128 256), losses := [] }

theorem u1221 : Upper (D 7) (R 7) [6,33,72,160,320,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1221 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1222 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 35 76 168 336 48 192 131 259), lower := (rows 7 35 76 168 336 48 192 128 256), losses := [] }

theorem u1222 : Upper (D 7) (R 7) [6,33,72,160,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1222 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1223 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 76 265 82 160 80 160 416), lower := (rows 7 35 76 265 82 160 80 128 256), losses := [] }

theorem u1223 : Upper (D 7) (R 7) [6,33,72,257,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1223 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1224 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 0, region := 240, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 35 76 265 82 160 96 144 400), lower := (rows 7 35 76 265 82 160 96 128 256), losses := [] }

theorem u1224 : Upper (D 7) (R 7) [6,33,72,257,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1225 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 240, targets := 1 }], pairs := [(0,6),(2,0),(4,0),(4,5)], upper := (rows 7 35 76 265 82 160 192 176 304), lower := (rows 7 35 76 265 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 255 255 155 283), good := (rows 502 498 492 508 498 224 224 224 256) },{ target := 5, region := (rows 1 2 4 8 18 0 224 128 256), good := (rows 23 83 76 265 82 192 192 192 256) },{ target := 6, region := (rows 5 6 4 8 16 240 0 144 272), good := (rows 7 35 47 265 434 160 160 160 256) }] }

theorem u1225 : Upper (D 7) (R 7) [6,33,72,257,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1225 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1226 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 176, targets := 3 },{ cop := 1, region := 80, targets := 128 }], pairs := [(2,0),(4,0),(4,1),(4,7)], upper := (rows 7 35 76 265 112 160 66 144 400), lower := (rows 7 35 76 265 112 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 95 255 67 223 351), good := (rows 502 498 508 508 496 160 498 160 256) }] }

theorem u1226 : Upper (D 7) (R 7) [6,33,72,257,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1227 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 76 265 112 160 80 130 386), lower := (rows 7 35 76 265 112 160 80 128 256), losses := [] }

theorem u1227 : Upper (D 7) (R 7) [6,33,72,257,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1227 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1228 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 76 265 112 160 192 146 274), lower := (rows 7 35 76 265 112 160 192 128 256), losses := [] }

theorem u1228 : Upper (D 7) (R 7) [6,33,72,257,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1229 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 240, targets := 1 }], pairs := [(2,0),(3,1),(4,0)], upper := (rows 7 35 76 265 146 160 80 224 352), lower := (rows 7 35 76 265 146 160 80 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 255 91 223 351), good := (rows 502 498 492 508 498 160 496 160 256) },{ target := 1, region := (rows 1 0 4 9 16 245 80 212 340), good := (rows 429 41 492 297 496 160 496 160 256) }] }

theorem u1229 : Upper (D 7) (R 7) [6,33,72,257,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1229 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1230 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 240, targets := 1 }], pairs := [(0,7),(2,0),(2,7),(4,0)], upper := (rows 7 35 76 265 146 160 96 208 336), lower := (rows 7 35 76 265 146 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 191 255 155 283), good := (rows 502 498 492 508 498 224 96 224 256) },{ target := 7, region := (rows 17 2 20 24 16 32 98 0 272), good := (rows 71 99 76 265 351 96 96 0 256) }] }

theorem u1230 : Upper (D 7) (R 7) [6,33,72,257,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1231 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 176, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 76 265 208 160 66 176 304), lower := (rows 7 35 76 265 208 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 95 255 67 223 351), good := (rows 502 498 508 508 496 160 498 160 256) },{ target := 1, region := (rows 1 0 68 11 84 255 64 213 341), good := (rows 445 425 508 425 500 160 508 160 256) }] }

theorem u1231 : Upper (D 7) (R 7) [6,33,72,257,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1232 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 76 265 208 160 80 162 290), lower := (rows 7 35 76 265 208 160 80 128 256), losses := [] }

theorem u1232 : Upper (D 7) (R 7) [6,33,72,257,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1232 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1233 : Route 9 := (fun mask => (mask,id))

def c1233 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1233 : Upper (D 7) (R 7) [6,33,72,257,192,128,32] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257,192,128,32] 13 (by decide) (choices 1) [2,16] r1233 c1233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u32
  · exact u33

def b1234 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 76 266 112 160 65 144 400), lower := (rows 7 35 76 266 112 160 65 128 256), losses := [] }

theorem u1234 : Upper (D 7) (R 7) [6,33,72,258,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1235 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 76 266 112 160 80 129 385), lower := (rows 7 35 76 266 112 160 80 128 256), losses := [] }

theorem u1235 : Upper (D 7) (R 7) [6,33,72,258,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1235 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1236 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 76 266 112 160 192 145 273), lower := (rows 7 35 76 266 112 160 192 128 256), losses := [] }

theorem u1236 : Upper (D 7) (R 7) [6,33,72,258,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1237 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(4,1)], upper := (rows 7 35 76 266 145 160 80 224 352), lower := (rows 7 35 76 266 145 160 80 128 256), losses := [{ target := 0, region := (rows 0 2 20 9 16 245 80 212 340), good := (rows 430 42 492 266 508 160 500 160 256) }] }

theorem u1237 : Upper (D 7) (R 7) [6,33,72,258,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1237 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1238 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(2,1),(4,1)], upper := (rows 7 35 76 266 145 160 96 208 336), lower := (rows 7 35 76 266 145 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 242 144 272), good := (rows 70 98 76 334 496 224 96 224 256) },{ target := 1, region := (rows 1 0 12 8 19 191 255 155 283), good := (rows 501 497 492 508 497 224 96 224 256) }] }

theorem u1238 : Upper (D 7) (R 7) [6,33,72,258,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1239 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 76 266 208 160 65 176 304), lower := (rows 7 35 76 266 208 160 65 128 256), losses := [] }

theorem u1239 : Upper (D 7) (R 7) [6,33,72,258,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1240 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 76 266 208 160 80 161 289), lower := (rows 7 35 76 266 208 160 80 128 256), losses := [] }

theorem u1240 : Upper (D 7) (R 7) [6,33,72,258,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1240 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1241 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 80, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 76 266 208 160 96 145 273), lower := (rows 7 35 76 266 208 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 176 176 242 128 256), good := (rows 70 114 76 334 240 240 112 240 256) },{ target := 1, region := (rows 1 0 12 8 187 187 255 131 259), good := (rows 501 497 124 508 240 240 112 240 256) }] }

theorem u1241 : Upper (D 7) (R 7) [6,33,72,258,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1242 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 1, region := 80, targets := 2 },{ cop := 1, region := 80, targets := 128 }], pairs := [(0,6),(1,6),(4,1),(4,7)], upper := (rows 7 35 76 280 112 160 65 130 386), lower := (rows 7 35 76 280 112 160 65 128 256), losses := [] }

theorem u1242 : Upper (D 7) (R 7) [6,33,72,272,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1243 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 129 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(4,0),(4,7)], upper := (rows 7 35 76 280 112 160 66 129 385), lower := (rows 7 35 76 280 112 160 66 128 256), losses := [] }

theorem u1243 : Upper (D 7) (R 7) [6,33,72,272,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1244 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 76 280 112 160 192 131 259), lower := (rows 7 35 76 280 112 160 192 128 256), losses := [] }

theorem u1244 : Upper (D 7) (R 7) [6,33,72,272,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1245 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(3,1)], upper := (rows 7 35 76 280 145 160 66 224 352), lower := (rows 7 35 76 280 145 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 255 67 215 343), good := (rows 486 482 492 444 508 160 482 160 256) },{ target := 1, region := (rows 1 0 4 9 17 245 64 196 324), good := (rows 445 57 492 312 185 160 480 160 256) }] }

theorem u1245 : Upper (D 7) (R 7) [6,33,72,272,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1246 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(2,1),(3,0)], upper := (rows 7 35 76 280 145 160 96 194 322), lower := (rows 7 35 76 280 145 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 16 179 251 131 259), good := (rows 486 482 76 380 508 224 96 224 256) },{ target := 1, region := (rows 1 0 12 8 16 176 250 128 256), good := (rows 69 97 76 380 241 224 96 224 256) }] }

theorem u1246 : Upper (D 7) (R 7) [6,33,72,272,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1247 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(2,0),(3,0)], upper := (rows 7 35 76 280 208 160 65 162 290), lower := (rows 7 35 76 280 208 160 65 128 256), losses := [{ target := 0, region := (rows 0 2 84 72 80 243 64 131 259), good := (rows 422 418 124 316 252 160 508 160 256) }] }

theorem u1247 : Upper (D 7) (R 7) [6,33,72,272,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1248 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(2,1),(3,1)], upper := (rows 7 35 76 280 208 160 66 161 289), lower := (rows 7 35 76 280 208 160 66 128 256), losses := [{ target := 1, region := (rows 1 0 84 72 80 243 64 131 259), good := (rows 421 417 124 316 252 160 508 160 256) }] }

theorem u1248 : Upper (D 7) (R 7) [6,33,72,272,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1249 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 5, region := 80, targets := 3 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 7 35 76 280 208 160 96 131 259), lower := (rows 7 35 76 280 208 160 96 128 256), losses := [] }

theorem u1249 : Upper (D 7) (R 7) [6,33,72,272,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1250 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 35 76 296 81 160 66 144 400), lower := (rows 7 35 76 296 81 160 66 128 256), losses := [] }

theorem u1250 : Upper (D 7) (R 7) [6,33,72,288,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1251 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 76 296 81 160 80 130 386), lower := (rows 7 35 76 296 81 160 80 128 256), losses := [] }

theorem u1251 : Upper (D 7) (R 7) [6,33,72,288,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1251 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1252 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,6),(2,0),(3,6),(4,5)], upper := (rows 7 35 76 296 81 160 192 146 274), lower := (rows 7 35 76 296 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 224 224 128 256), good := (rows 6 98 108 364 112 224 224 224 256) }] }

theorem u1252 : Upper (D 7) (R 7) [6,33,72,288,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1253 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 35 76 296 82 160 65 144 400), lower := (rows 7 35 76 296 82 160 65 128 256), losses := [] }

theorem u1253 : Upper (D 7) (R 7) [6,33,72,288,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1254 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 76 296 82 160 80 129 385), lower := (rows 7 35 76 296 82 160 80 128 256), losses := [] }

theorem u1254 : Upper (D 7) (R 7) [6,33,72,288,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1254 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1255 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(2,0),(2,1),(4,0),(4,5)], upper := (rows 7 35 76 296 82 160 192 145 273), lower := (rows 7 35 76 296 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 18 224 224 128 256), good := (rows 22 114 108 364 114 224 224 224 256) },{ target := 1, region := (rows 1 0 12 8 16 224 224 128 256), good := (rows 5 97 108 364 112 224 224 224 256) }] }

theorem u1255 : Upper (D 7) (R 7) [6,33,72,288,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1256 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(4,5)], upper := (rows 7 35 76 296 145 160 66 208 336), lower := (rows 7 35 76 296 145 160 66 128 256), losses := [] }

theorem u1256 : Upper (D 7) (R 7) [6,33,72,288,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1257 : Route 9 := (fun mask => (mask,id))

def c1257 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1257 : Upper (D 7) (R 7) [6,33,72,288,129,128,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,129,128,16] 13 (by decide) (choices 1) [2,64] r1257 c1257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u34
  · exact u35

def b1258 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(4,5)], upper := (rows 7 35 76 296 146 160 65 208 336), lower := (rows 7 35 76 296 146 160 65 128 256), losses := [] }

theorem u1258 : Upper (D 7) (R 7) [6,33,72,288,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1259 : Route 9 := (fun mask => (mask,id))

def c1259 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1259 : Upper (D 7) (R 7) [6,33,72,288,130,128,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,130,128,16] 13 (by decide) (choices 1) [1,64] r1259 c1259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u36
  · exact u37

#print axioms u1259
end Delivery.IrregularNine14.P07
