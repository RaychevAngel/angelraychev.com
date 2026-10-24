import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0103

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21240 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 69 26 152 33 224 224 480), lower := (rows 35 262 69 26 152 33 64 128 256), losses := [] }

theorem u21240 : Upper (D 7) (R 7) [34,260,65,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21241 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,6),(2,1),(3,6),(4,6)], upper := (rows 35 262 69 26 152 96 225 161 417), lower := (rows 35 262 69 26 152 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 15 21 32 0 129 257), good := (rows 443 286 415 26 152 32 0 128 256) }] }

theorem u21241 : Upper (D 7) (R 7) [34,260,65,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21242 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 68, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(2,7)], upper := (rows 35 262 69 26 152 160 97 225 353), lower := (rows 35 262 69 26 152 160 64 128 256), losses := [] }

theorem u21242 : Upper (D 7) (R 7) [34,260,65,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21243 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 69 26 176 33 200 200 456), lower := (rows 35 262 69 26 176 33 64 128 256), losses := [] }

theorem u21243 : Upper (D 7) (R 7) [34,260,65,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21244 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 262 69 26 176 40 193 193 449), lower := (rows 35 262 69 26 176 40 64 128 256), losses := [] }

theorem u21244 : Upper (D 7) (R 7) [34,260,65,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21244 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21245 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 35 262 69 26 176 96 201 137 393), lower := (rows 35 262 69 26 176 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 13 17 32 0 133 261), good := (rows 443 398 415 26 176 32 0 128 256) },{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 295 101 27 48 96 96 0 256) }] }

theorem u21245 : Upper (D 7) (R 7) [34,260,65,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21246 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 69 26 176 160 73 201 329), lower := (rows 35 262 69 26 176 160 64 128 256), losses := [] }

theorem u21246 : Upper (D 7) (R 7) [34,260,65,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21247 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 69 26 208 33 232 168 424), lower := (rows 35 262 69 26 208 33 64 128 256), losses := [] }

theorem u21247 : Upper (D 7) (R 7) [34,260,65,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21248 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 262 69 26 208 40 225 161 417), lower := (rows 35 262 69 26 208 40 64 128 256), losses := [] }

theorem u21248 : Upper (D 7) (R 7) [34,260,65,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21248 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21249 : Route 9 := (fun mask => (mask,id))

def c21249 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21249 : Upper (D 7) (R 7) [34,260,65,18,192,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,18,192,128] 13 (by decide) (choices 1) [1,8,32] r21249 c21249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6199
  · exact u6200
  · exact u6201

def b21250 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 0, region := 216, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(3,7)], upper := (rows 35 262 69 56 82 33 200 136 392), lower := (rows 35 262 69 56 82 33 64 128 256), losses := [] }

theorem u21250 : Upper (D 7) (R 7) [34,260,65,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21251 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 262 69 56 82 40 193 129 385), lower := (rows 35 262 69 56 82 40 64 128 256), losses := [] }

theorem u21251 : Upper (D 7) (R 7) [34,260,65,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21251 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21252 : Route 9 := (fun mask => (mask,id))

def c21252 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21252 : Upper (D 7) (R 7) [34,260,65,48,66,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,48,66,128] 13 (by decide) (choices 1) [1,8,128] r21252 c21252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6202
  · exact u6203
  · exact u6204

def b21253 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 69 56 145 34 200 200 456), lower := (rows 35 262 69 56 145 34 64 128 256), losses := [] }

theorem u21253 : Upper (D 7) (R 7) [34,260,65,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21254 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 262 69 56 145 40 194 194 450), lower := (rows 35 262 69 56 145 40 64 128 256), losses := [] }

theorem u21254 : Upper (D 7) (R 7) [34,260,65,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21254 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21255 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 35 262 69 56 145 96 202 138 394), lower := (rows 35 262 69 56 145 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 9 21 32 0 133 261), good := (rows 443 406 415 56 409 32 0 128 256) },{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 295 101 56 17 96 96 0 256) }] }

theorem u21255 : Upper (D 7) (R 7) [34,260,65,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21256 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 262 69 56 145 160 74 202 330), lower := (rows 35 262 69 56 145 160 64 128 256), losses := [] }

theorem u21256 : Upper (D 7) (R 7) [34,260,65,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21257 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 69 56 146 33 200 200 456), lower := (rows 35 262 69 56 146 33 64 128 256), losses := [] }

theorem u21257 : Upper (D 7) (R 7) [34,260,65,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21258 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 262 69 56 146 40 193 193 449), lower := (rows 35 262 69 56 146 40 64 128 256), losses := [] }

theorem u21258 : Upper (D 7) (R 7) [34,260,65,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21258 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21259 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 35 262 69 56 146 96 201 137 393), lower := (rows 35 262 69 56 146 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 9 23 32 0 133 261), good := (rows 443 406 415 56 146 32 0 128 256) },{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 295 101 56 19 96 96 0 256) }] }

theorem u21259 : Upper (D 7) (R 7) [34,260,65,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21260 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 262 69 56 146 160 73 201 329), lower := (rows 35 262 69 56 146 160 64 128 256), losses := [] }

theorem u21260 : Upper (D 7) (R 7) [34,260,65,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21261 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,0),(4,0)], upper := (rows 35 262 69 56 152 33 194 194 450), lower := (rows 35 262 69 56 152 33 64 128 256), losses := [] }

theorem u21261 : Upper (D 7) (R 7) [34,260,65,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21262 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 262 69 56 152 34 193 193 449), lower := (rows 35 262 69 56 152 34 64 128 256), losses := [] }

theorem u21262 : Upper (D 7) (R 7) [34,260,65,48,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21263 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 152, targets := 64 }], pairs := [(1,5),(2,5),(3,6),(4,6)], upper := (rows 35 262 69 56 152 96 195 131 387), lower := (rows 35 262 69 56 152 96 64 128 256), losses := [] }

theorem u21263 : Upper (D 7) (R 7) [34,260,65,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21264 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6),(4,0)], upper := (rows 35 262 69 56 152 160 67 195 323), lower := (rows 35 262 69 56 152 160 64 128 256), losses := [] }

theorem u21264 : Upper (D 7) (R 7) [34,260,65,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21265 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 69 56 208 33 202 138 394), lower := (rows 35 262 69 56 208 33 64 128 256), losses := [] }

theorem u21265 : Upper (D 7) (R 7) [34,260,65,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21266 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 69 56 208 34 201 137 393), lower := (rows 35 262 69 56 208 34 64 128 256), losses := [] }

theorem u21266 : Upper (D 7) (R 7) [34,260,65,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21267 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 262 69 56 208 40 195 131 387), lower := (rows 35 262 69 56 208 40 64 128 256), losses := [] }

theorem u21267 : Upper (D 7) (R 7) [34,260,65,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21267 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21268 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 262 69 56 208 160 75 139 267), lower := (rows 35 262 69 56 208 160 64 128 256), losses := [] }

theorem u21268 : Upper (D 7) (R 7) [34,260,65,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21269 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 262 69 74 145 40 240 176 432), lower := (rows 35 262 69 74 145 40 64 128 256), losses := [] }

theorem u21269 : Upper (D 7) (R 7) [34,260,65,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21269 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21270 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 177, targets := 64 },{ cop := 0, region := 200, targets := 1 }], pairs := [(0,6),(3,0),(4,6)], upper := (rows 35 262 69 74 145 48 232 168 424), lower := (rows 35 262 69 74 145 48 64 128 256), losses := [] }

theorem u21270 : Upper (D 7) (R 7) [34,260,65,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21270 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21271 : Route 9 := (fun mask => (mask,id))

def c21271 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21271 : Upper (D 7) (R 7) [34,260,65,66,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,66,129,128] 13 (by decide) (choices 1) [8,16,32] r21271 c21271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6205
  · exact u6206
  · exact u6207

def b21272 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 69 74 152 33 240 176 432), lower := (rows 35 262 69 74 152 33 64 128 256), losses := [] }

theorem u21272 : Upper (D 7) (R 7) [34,260,65,66,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21273 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 177, targets := 64 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,6),(2,1),(4,6)], upper := (rows 35 262 69 74 152 48 225 161 417), lower := (rows 35 262 69 74 152 48 64 128 256), losses := [] }

theorem u21273 : Upper (D 7) (R 7) [34,260,65,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21273 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21274 : Route 9 := (fun mask => (mask,id))

def c21274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21274 : Upper (D 7) (R 7) [34,260,65,66,136,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,66,136,128] 13 (by decide) (choices 1) [1,16,32] r21274 c21274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6208
  · exact u6209
  · exact u6210

def b21275 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 69 74 176 33 216 152 408), lower := (rows 35 262 69 74 176 33 64 128 256), losses := [] }

theorem u21275 : Upper (D 7) (R 7) [34,260,65,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21276 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 262 69 74 176 40 209 145 401), lower := (rows 35 262 69 74 176 40 64 128 256), losses := [] }

theorem u21276 : Upper (D 7) (R 7) [34,260,65,66,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21276 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21277 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 69 74 176 48 201 137 393), lower := (rows 35 262 69 74 176 48 64 128 256), losses := [] }

theorem u21277 : Upper (D 7) (R 7) [34,260,65,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21277 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21278 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 69 74 176 160 89 153 281), lower := (rows 35 262 69 74 176 160 64 128 256), losses := [] }

theorem u21278 : Upper (D 7) (R 7) [34,260,65,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21279 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 69 88 145 34 232 168 424), lower := (rows 35 262 69 88 145 34 64 128 256), losses := [] }

theorem u21279 : Upper (D 7) (R 7) [34,260,65,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21280 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(1,0),(3,0),(4,6)], upper := (rows 35 262 69 88 145 40 226 162 418), lower := (rows 35 262 69 88 145 40 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 56 65 129 257), good := (rows 482 262 454 120 504 40 64 128 256) }] }

theorem u21280 : Upper (D 7) (R 7) [34,260,65,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21280 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21281 : Route 9 := (fun mask => (mask,id))

def c21281 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21281 : Upper (D 7) (R 7) [34,260,65,80,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,80,129,128] 13 (by decide) (choices 1) [2,8,32] r21281 c21281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6211
  · exact u6212
  · exact u6213

def b21282 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 69 88 146 33 232 168 424), lower := (rows 35 262 69 88 146 33 64 128 256), losses := [] }

theorem u21282 : Upper (D 7) (R 7) [34,260,65,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21283 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 196, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 35 262 69 88 146 40 225 161 417), lower := (rows 35 262 69 88 146 40 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 21 40 0 129 257), good := (rows 435 278 407 56 146 40 0 128 256) }] }

theorem u21283 : Upper (D 7) (R 7) [34,260,65,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21283 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21284 : Route 9 := (fun mask => (mask,id))

def c21284 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21284 : Upper (D 7) (R 7) [34,260,65,80,130,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,80,130,128] 13 (by decide) (choices 1) [1,8,32] r21284 c21284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6214
  · exact u6215
  · exact u6216

def b21285 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(3,0),(4,0)], upper := (rows 35 262 69 88 152 33 226 162 418), lower := (rows 35 262 69 88 152 33 64 128 256), losses := [] }

theorem u21285 : Upper (D 7) (R 7) [34,260,65,80,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21286 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 69 88 152 34 225 161 417), lower := (rows 35 262 69 88 152 34 64 128 256), losses := [] }

theorem u21286 : Upper (D 7) (R 7) [34,260,65,80,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21286 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21287 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 35 262 69 88 152 160 99 163 291), lower := (rows 35 262 69 88 152 160 64 128 256), losses := [] }

theorem u21287 : Upper (D 7) (R 7) [34,260,65,80,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21288 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 69 88 176 33 202 138 394), lower := (rows 35 262 69 88 176 33 64 128 256), losses := [] }

theorem u21288 : Upper (D 7) (R 7) [34,260,65,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21289 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 69 88 176 34 201 137 393), lower := (rows 35 262 69 88 176 34 64 128 256), losses := [] }

theorem u21289 : Upper (D 7) (R 7) [34,260,65,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21290 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(1,5),(2,5),(4,6)], upper := (rows 35 262 69 88 176 40 195 131 387), lower := (rows 35 262 69 88 176 40 64 128 256), losses := [] }

theorem u21290 : Upper (D 7) (R 7) [34,260,65,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21290 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21291 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 69 88 176 160 75 139 267), lower := (rows 35 262 69 88 176 160 64 128 256), losses := [] }

theorem u21291 : Upper (D 7) (R 7) [34,260,65,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21292 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 69 104 145 34 216 152 408), lower := (rows 35 262 69 104 145 34 64 128 256), losses := [] }

theorem u21292 : Upper (D 7) (R 7) [34,260,65,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21293 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 262 69 104 145 40 210 146 402), lower := (rows 35 262 69 104 145 40 64 128 256), losses := [] }

theorem u21293 : Upper (D 7) (R 7) [34,260,65,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21293 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21294 : Route 9 := (fun mask => (mask,id))

def c21294 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21294 : Upper (D 7) (R 7) [34,260,65,96,129,16] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96,129,16] 13 (by decide) (choices 1) [2,8,128] r21294 c21294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6217
  · exact u6218
  · exact u6219

def r21295 : Route 9 := (fun mask => (mask,id))

def c21295 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21295 : Upper (D 7) (R 7) [34,260,65,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96,129,128] 13 (by decide) (choices 1) [2,8,16] r21295 c21295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6220
  · exact u6221
  · exact u6222

def b21296 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 262 69 104 146 33 216 152 408), lower := (rows 35 262 69 104 146 33 64 128 256), losses := [] }

theorem u21296 : Upper (D 7) (R 7) [34,260,65,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21297 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 262 69 104 146 40 209 145 401), lower := (rows 35 262 69 104 146 40 64 128 256), losses := [] }

theorem u21297 : Upper (D 7) (R 7) [34,260,65,96,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21297 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21298 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 262 69 104 146 48 201 137 393), lower := (rows 35 262 69 104 146 48 64 128 256), losses := [] }

theorem u21298 : Upper (D 7) (R 7) [34,260,65,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21298 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21299 : Route 9 := (fun mask => (mask,id))

def c21299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21299 : Upper (D 7) (R 7) [34,260,65,96,130,128] 13 := by
  apply FastRouting.sound _ _ [34,260,65,96,130,128] 13 (by decide) (choices 1) [1,8,16] r21299 c21299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6223
  · exact u6224
  · exact u6225

#print axioms u21299
end Delivery.IrregularNine14.P07
