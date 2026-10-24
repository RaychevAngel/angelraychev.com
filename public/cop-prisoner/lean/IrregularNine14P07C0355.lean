import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0103
import IrregularNine14P07C0104

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21300 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 69 104 152 33 210 146 402), lower := (rows 35 262 69 104 152 33 64 128 256), losses := [] }

theorem u21300 : Upper (D 7) (R 7) [34,260,65,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21301 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 69 104 152 34 209 145 401), lower := (rows 35 262 69 104 152 34 64 128 256), losses := [] }

theorem u21301 : Upper (D 7) (R 7) [34,260,65,96,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21302 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 262 69 104 152 48 195 131 387), lower := (rows 35 262 69 104 152 48 64 128 256), losses := [] }

theorem u21302 : Upper (D 7) (R 7) [34,260,65,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21302 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21303 : Route 9 := (fun mask => (mask,id))

def c21303 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21303 : Upper (D 7) (R 7) [34,260,65,96,136,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96,136,128] 13 (by decide) (choices 1) [1,2,16] r21303 c21303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6226
  · exact u6227
  · exact u6228

def b21304 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 0, region := 208, targets := 1 }], pairs := [(0,6),(3,6),(4,0)], upper := (rows 35 262 69 137 146 40 112 240 368), lower := (rows 35 262 69 137 146 40 64 128 256), losses := [] }

theorem u21304 : Upper (D 7) (R 7) [34,260,65,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21304 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21305 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 262 69 137 146 48 104 232 360), lower := (rows 35 262 69 137 146 48 64 128 256), losses := [] }

theorem u21305 : Upper (D 7) (R 7) [34,260,65,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21305 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21306 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 35 262 69 137 146 96 120 184 312), lower := (rows 35 262 69 137 146 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 13 21 32 0 129 257), good := (rows 443 286 415 409 146 32 0 128 256) },{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 295 101 9 19 96 96 0 256) }] }

theorem u21306 : Upper (D 7) (R 7) [34,260,65,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21307 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 69 137 176 34 88 216 344), lower := (rows 35 262 69 137 176 34 64 128 256), losses := [] }

theorem u21307 : Upper (D 7) (R 7) [34,260,65,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21308 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 262 69 137 176 40 82 210 338), lower := (rows 35 262 69 137 176 40 64 128 256), losses := [] }

theorem u21308 : Upper (D 7) (R 7) [34,260,65,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21308 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21309 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 69 137 176 48 74 202 330), lower := (rows 35 262 69 137 176 48 64 128 256), losses := [] }

theorem u21309 : Upper (D 7) (R 7) [34,260,65,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21309 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21310 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 35 262 69 137 176 96 90 154 282), lower := (rows 35 262 69 137 176 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 13 17 32 0 133 261), good := (rows 443 398 415 409 176 32 0 128 256) },{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 295 101 9 48 96 96 0 256) }] }

theorem u21310 : Upper (D 7) (R 7) [34,260,65,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21311 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 69 137 208 34 120 184 312), lower := (rows 35 262 69 137 208 34 64 128 256), losses := [] }

theorem u21311 : Upper (D 7) (R 7) [34,260,65,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21312 : Route 9 := (fun mask => (mask,id))

def c21312 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21312 : Upper (D 7) (R 7) [34,260,65,129,192,8] 13 := by
  apply FastRouting.sound _ _ [34,260,65,129,192,8] 13 (by decide) (choices 1) [2,16,32] r21312 c21312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6229
  · exact u6230
  · exact u6231

def r21313 : Route 9 := (fun mask => (mask,id))

def c21313 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21313 : Upper (D 7) (R 7) [34,260,65,129,192,16] 13 := by
  apply FastRouting.sound _ _ [34,260,65,129,192,16] 13 (by decide) (choices 1) [2,8,32] r21313 c21313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6232
  · exact u6233
  · exact u6234

def b21314 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 69 138 176 33 88 216 344), lower := (rows 35 262 69 138 176 33 64 128 256), losses := [] }

theorem u21314 : Upper (D 7) (R 7) [34,260,65,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21315 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 69 138 176 40 81 209 337), lower := (rows 35 262 69 138 176 40 64 128 256), losses := [] }

theorem u21315 : Upper (D 7) (R 7) [34,260,65,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21315 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21316 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 69 138 176 48 73 201 329), lower := (rows 35 262 69 138 176 48 64 128 256), losses := [] }

theorem u21316 : Upper (D 7) (R 7) [34,260,65,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21316 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21317 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 35 262 69 138 176 96 89 153 281), lower := (rows 35 262 69 138 176 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 15 17 32 0 133 261), good := (rows 443 398 415 138 176 32 0 128 256) },{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 295 101 11 48 96 96 0 256) }] }

theorem u21317 : Upper (D 7) (R 7) [34,260,65,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21318 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 69 138 208 33 120 184 312), lower := (rows 35 262 69 138 208 33 64 128 256), losses := [] }

theorem u21318 : Upper (D 7) (R 7) [34,260,65,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21319 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 262 69 138 208 40 113 177 305), lower := (rows 35 262 69 138 208 40 64 128 256), losses := [] }

theorem u21319 : Upper (D 7) (R 7) [34,260,65,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21319 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21320 : Route 9 := (fun mask => (mask,id))

def c21320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21320 : Upper (D 7) (R 7) [34,260,65,130,192,16] 13 := by
  apply FastRouting.sound _ _ [34,260,65,130,192,16] 13 (by decide) (choices 1) [1,8,32] r21320 c21320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6235
  · exact u6236
  · exact u6237

def b21321 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 69 168 208 33 90 154 282), lower := (rows 35 262 69 168 208 33 64 128 256), losses := [] }

theorem u21321 : Upper (D 7) (R 7) [34,260,65,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21322 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 69 168 208 34 89 153 281), lower := (rows 35 262 69 168 208 34 64 128 256), losses := [] }

theorem u21322 : Upper (D 7) (R 7) [34,260,65,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21323 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 262 69 168 208 40 83 147 275), lower := (rows 35 262 69 168 208 40 64 128 256), losses := [] }

theorem u21323 : Upper (D 7) (R 7) [34,260,65,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21323 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21324 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 69 168 208 48 75 139 267), lower := (rows 35 262 69 168 208 48 64 128 256), losses := [] }

theorem u21324 : Upper (D 7) (R 7) [34,260,65,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21324 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21325 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 0, region := 216, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,1)], upper := (rows 35 262 70 25 152 33 224 224 480), lower := (rows 35 262 70 25 152 33 64 128 256), losses := [] }

theorem u21325 : Upper (D 7) (R 7) [34,260,66,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21326 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 152, targets := 2 },{ cop := 0, region := 152, targets := 64 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 35 262 70 25 152 96 225 161 417), lower := (rows 35 262 70 25 152 96 64 128 256), losses := [] }

theorem u21326 : Upper (D 7) (R 7) [34,260,66,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21327 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 216, targets := 2 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 35 262 70 25 152 160 97 225 353), lower := (rows 35 262 70 25 152 160 64 128 256), losses := [] }

theorem u21327 : Upper (D 7) (R 7) [34,260,66,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21328 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 70 25 208 33 232 168 424), lower := (rows 35 262 70 25 208 33 64 128 256), losses := [] }

theorem u21328 : Upper (D 7) (R 7) [34,260,66,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21329 : Route 9 := (fun mask => (mask,id))

def c21329 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21329 : Upper (D 7) (R 7) [34,260,66,17,192,8] 13 := by
  apply FastRouting.sound _ _ [34,260,66,17,192,8] 13 (by decide) (choices 1) [1,32,128] r21329 c21329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6238
  · exact u6239
  · exact u6240

def r21330 : Route 9 := (fun mask => (mask,id))

def c21330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21330 : Upper (D 7) (R 7) [34,260,66,17,192,128] 13 := by
  apply FastRouting.sound _ _ [34,260,66,17,192,128] 13 (by decide) (choices 1) [1,8,32] r21330 c21330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6241
  · exact u6242
  · exact u6243

def b21331 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 262 70 56 81 33 200 136 392), lower := (rows 35 262 70 56 81 33 64 128 256), losses := [] }

theorem u21331 : Upper (D 7) (R 7) [34,260,66,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21332 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 262 70 56 81 40 193 129 385), lower := (rows 35 262 70 56 81 40 64 128 256), losses := [] }

theorem u21332 : Upper (D 7) (R 7) [34,260,66,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21332 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21333 : Route 9 := (fun mask => (mask,id))

def c21333 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21333 : Upper (D 7) (R 7) [34,260,66,48,65,128] 13 := by
  apply FastRouting.sound _ _ [34,260,66,48,65,128] 13 (by decide) (choices 1) [1,8,128] r21333 c21333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6244
  · exact u6245
  · exact u6246

def b21334 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 262 70 56 145 33 200 200 456), lower := (rows 35 262 70 56 145 33 64 128 256), losses := [] }

theorem u21334 : Upper (D 7) (R 7) [34,260,66,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21335 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 262 70 56 145 40 193 193 449), lower := (rows 35 262 70 56 145 40 64 128 256), losses := [] }

theorem u21335 : Upper (D 7) (R 7) [34,260,66,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21335 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21336 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 152, targets := 2 },{ cop := 0, region := 152, targets := 64 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 35 262 70 56 145 96 201 137 393), lower := (rows 35 262 70 56 145 96 64 128 256), losses := [] }

theorem u21336 : Upper (D 7) (R 7) [34,260,66,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21337 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 0, region := 216, targets := 2 }], pairs := [(0,7),(1,7),(2,7),(3,1)], upper := (rows 35 262 70 56 145 160 73 201 329), lower := (rows 35 262 70 56 145 160 64 128 256), losses := [] }

theorem u21337 : Upper (D 7) (R 7) [34,260,66,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21338 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 70 56 208 33 201 137 393), lower := (rows 35 262 70 56 208 33 64 128 256), losses := [] }

theorem u21338 : Upper (D 7) (R 7) [34,260,66,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21339 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 262 70 56 208 40 193 129 385), lower := (rows 35 262 70 56 208 40 64 128 256), losses := [] }

theorem u21339 : Upper (D 7) (R 7) [34,260,66,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21339 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21340 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 262 70 56 208 160 73 137 265), lower := (rows 35 262 70 56 208 160 64 128 256), losses := [] }

theorem u21340 : Upper (D 7) (R 7) [34,260,66,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21341 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(4,1)], upper := (rows 35 262 70 73 145 40 240 176 432), lower := (rows 35 262 70 73 145 40 64 128 256), losses := [] }

theorem u21341 : Upper (D 7) (R 7) [34,260,66,65,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21341 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21342 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 176, targets := 64 }], pairs := [(3,1),(4,1),(4,6)], upper := (rows 35 262 70 73 145 48 232 168 424), lower := (rows 35 262 70 73 145 48 64 128 256), losses := [] }

theorem u21342 : Upper (D 7) (R 7) [34,260,66,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21342 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21343 : Route 9 := (fun mask => (mask,id))

def c21343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21343 : Upper (D 7) (R 7) [34,260,66,65,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,66,65,129,128] 13 (by decide) (choices 1) [8,16,32] r21343 c21343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6247
  · exact u6248
  · exact u6249

def b21344 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 70 73 152 33 240 176 432), lower := (rows 35 262 70 73 152 33 64 128 256), losses := [] }

theorem u21344 : Upper (D 7) (R 7) [34,260,66,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21345 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 176, targets := 64 }], pairs := [(3,1),(4,1),(4,6)], upper := (rows 35 262 70 73 152 48 225 161 417), lower := (rows 35 262 70 73 152 48 64 128 256), losses := [] }

theorem u21345 : Upper (D 7) (R 7) [34,260,66,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21345 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21346 : Route 9 := (fun mask => (mask,id))

def c21346 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21346 : Upper (D 7) (R 7) [34,260,66,65,136,128] 13 := by
  apply FastRouting.sound _ _ [34,260,66,65,136,128] 13 (by decide) (choices 1) [1,16,32] r21346 c21346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6250
  · exact u6251
  · exact u6252

def b21347 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 70 73 176 33 216 152 408), lower := (rows 35 262 70 73 176 33 64 128 256), losses := [] }

theorem u21347 : Upper (D 7) (R 7) [34,260,66,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21348 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 41, targets := 128 }], pairs := [(0,7),(3,1),(4,1)], upper := (rows 35 262 70 73 176 40 209 145 401), lower := (rows 35 262 70 73 176 40 64 128 256), losses := [] }

theorem u21348 : Upper (D 7) (R 7) [34,260,66,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21348 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21349 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 70 73 176 48 201 137 393), lower := (rows 35 262 70 73 176 48 64 128 256), losses := [] }

theorem u21349 : Upper (D 7) (R 7) [34,260,66,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21349 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21350 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 70 73 176 160 89 153 281), lower := (rows 35 262 70 73 176 160 64 128 256), losses := [] }

theorem u21350 : Upper (D 7) (R 7) [34,260,66,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21351 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 70 88 145 33 232 168 424), lower := (rows 35 262 70 88 145 33 64 128 256), losses := [] }

theorem u21351 : Upper (D 7) (R 7) [34,260,66,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21352 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(3,1),(4,1),(4,6)], upper := (rows 35 262 70 88 145 40 225 161 417), lower := (rows 35 262 70 88 145 40 64 128 256), losses := [] }

theorem u21352 : Upper (D 7) (R 7) [34,260,66,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21352 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21353 : Route 9 := (fun mask => (mask,id))

def c21353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21353 : Upper (D 7) (R 7) [34,260,66,80,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,66,80,129,128] 13 (by decide) (choices 1) [1,8,32] r21353 c21353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6253
  · exact u6254
  · exact u6255

def b21354 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 70 88 176 33 201 137 393), lower := (rows 35 262 70 88 176 33 64 128 256), losses := [] }

theorem u21354 : Upper (D 7) (R 7) [34,260,66,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21355 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 262 70 88 176 40 193 129 385), lower := (rows 35 262 70 88 176 40 64 128 256), losses := [] }

theorem u21355 : Upper (D 7) (R 7) [34,260,66,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21355 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21356 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 70 88 176 160 73 137 265), lower := (rows 35 262 70 88 176 160 64 128 256), losses := [] }

theorem u21356 : Upper (D 7) (R 7) [34,260,66,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21357 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 70 104 145 33 216 152 408), lower := (rows 35 262 70 104 145 33 64 128 256), losses := [] }

theorem u21357 : Upper (D 7) (R 7) [34,260,66,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21358 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 262 70 104 145 40 209 145 401), lower := (rows 35 262 70 104 145 40 64 128 256), losses := [] }

theorem u21358 : Upper (D 7) (R 7) [34,260,66,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21358 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21359 : Route 9 := (fun mask => (mask,id))

def c21359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21359 : Upper (D 7) (R 7) [34,260,66,96,129,16] 13 := by
  apply FastRouting.sound _ _ [34,260,66,96,129,16] 13 (by decide) (choices 1) [1,8,128] r21359 c21359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6256
  · exact u6257
  · exact u6258

#print axioms u21359
end Delivery.IrregularNine14.P07
