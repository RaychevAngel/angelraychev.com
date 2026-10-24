import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0518
import IrregularNine14P07C0519
import IrregularNine14P07C0520
import IrregularNine14P07C0521
import IrregularNine14P07C0522

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r41280 : Route 9 := (fun mask => (mask,id))

def c41280 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41280 : Upper (D 7) (R 7) [6,40,257,80] 13 := by
  apply FastRouting.sound _ _ [6,40,257,80] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41280 c41280
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31124
  · exact u31125
  · exact u31126
  · exact u31127
  · exact u31128
  · exact u31129
  · exact u31130
  · exact u31131
  · exact u31132
  · exact u31133

def b41281 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 261 104 211 243 211 211 467), lower := (rows 7 42 261 104 16 32 64 128 256), losses := [] }

theorem u41281 : Upper (D 7) (R 7) [6,40,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41282 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41282 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41282 : Upper (D 7) (R 7) [6,40,257,192] 13 := by
  apply FastRouting.sound _ _ [6,40,257,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41282 c41282
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31134
  · exact u31135
  · exact u31136
  · exact u31137
  · exact u31138
  · exact u31139
  · exact u31140

def b41283 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 42 276 11 241 225 225 225 481), lower := (rows 7 42 276 11 16 32 64 128 256), losses := [] }

theorem u41283 : Upper (D 7) (R 7) [6,40,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41284 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 276 41 211 227 195 195 451), lower := (rows 7 42 276 41 16 32 64 128 256), losses := [] }

theorem u41284 : Upper (D 7) (R 7) [6,40,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41285 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 276 42 209 225 193 193 449), lower := (rows 7 42 276 42 16 32 64 128 256), losses := [] }

theorem u41285 : Upper (D 7) (R 7) [6,40,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41286 : Route 9 := (fun mask => (mask,id))

def c41286 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41286 : Upper (D 7) (R 7) [6,40,272,65] 13 := by
  apply FastRouting.sound _ _ [6,40,272,65] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41286 c41286
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31141
  · exact u31142
  · exact u31143
  · exact u31144
  · exact u31145
  · exact u31146
  · exact u31147
  · exact u31148
  · exact u31149
  · exact u31150

def r41287 : Route 9 := (fun mask => (mask,id))

def c41287 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41287 : Upper (D 7) (R 7) [6,40,272,66] 13 := by
  apply FastRouting.sound _ _ [6,40,272,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41287 c41287
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31151
  · exact u31152
  · exact u31153
  · exact u31154
  · exact u31155
  · exact u31156

def b41288 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 276 104 211 227 195 195 451), lower := (rows 7 42 276 104 16 32 64 128 256), losses := [] }

theorem u41288 : Upper (D 7) (R 7) [6,40,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41289 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41289 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41289 : Upper (D 7) (R 7) [6,40,272,192] 13 := by
  apply FastRouting.sound _ _ [6,40,272,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41289 c41289
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31157
  · exact u31158
  · exact u31159
  · exact u31160
  · exact u31161
  · exact u31162
  · exact u31163

def b41290 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 11, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 42 292 11 209 241 209 209 465), lower := (rows 7 42 292 11 16 32 64 128 256), losses := [] }

theorem u41290 : Upper (D 7) (R 7) [6,40,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41291 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41291 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41291 : Upper (D 7) (R 7) [6,40,288,17] 13 := by
  apply FastRouting.sound _ _ [6,40,288,17] 13 (by decide) (choices 2) [3,65,66,192] r41291 c41291
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u31164
  · exact u31165
  · exact u31166
  · exact u31167

def b41292 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 292 26 209 225 193 193 449), lower := (rows 7 42 292 26 16 32 64 128 256), losses := [] }

theorem u41292 : Upper (D 7) (R 7) [6,40,288,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41293 : Route 9 := (fun mask => (mask,id))

def c41293 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41293 : Upper (D 7) (R 7) [6,40,288,65] 13 := by
  apply FastRouting.sound _ _ [6,40,288,65] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41293 c41293
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31168
  · exact u31169
  · exact u31170
  · exact u31171
  · exact u31172
  · exact u31173

def b41294 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 292 74 209 241 209 209 465), lower := (rows 7 42 292 74 16 32 64 128 256), losses := [] }

theorem u41294 : Upper (D 7) (R 7) [6,40,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41295 : Route 9 := (fun mask => (mask,id))

def c41295 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41295 : Upper (D 7) (R 7) [6,40,288,80] 13 := by
  apply FastRouting.sound _ _ [6,40,288,80] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41295 c41295
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31174
  · exact u31175
  · exact u31176
  · exact u31177
  · exact u31178
  · exact u31179

def r41296 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41296 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41296 : Upper (D 7) (R 7) [6,40,288,192] 13 := by
  apply FastRouting.sound _ _ [6,40,288,192] 13 (by decide) (choices 2) [3,65,66,192] r41296 c41296
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u31180
  · exact u31181
  · exact u31182
  · exact u31183

def b41297 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 42 324 11 241 241 241 241 497), lower := (rows 7 42 324 11 16 32 64 128 256), losses := [] }

theorem u41297 : Upper (D 7) (R 7) [6,40,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41298 : Route 9 := (fun mask => (mask,id))

def c41298 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41298 : Upper (D 7) (R 7) [6,40,320,17] 13 := by
  apply FastRouting.sound _ _ [6,40,320,17] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41298 c41298
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31184
  · exact u31185
  · exact u31186
  · exact u31187
  · exact u31188
  · exact u31189
  · exact u31190
  · exact u31191
  · exact u31192
  · exact u31193

def r41299 : Route 9 := (fun mask => (mask,id))

def c41299 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41299 : Upper (D 7) (R 7) [6,40,320,18] 13 := by
  apply FastRouting.sound _ _ [6,40,320,18] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41299 c41299
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31194
  · exact u31195
  · exact u31196
  · exact u31197
  · exact u31198
  · exact u31199

def b41300 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 324 41 211 243 211 211 467), lower := (rows 7 42 324 41 16 32 64 128 256), losses := [] }

theorem u41300 : Upper (D 7) (R 7) [6,40,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41301 : PairBound 9 := { available := 209, camps := [{ cop := 5, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 324 42 209 241 209 209 465), lower := (rows 7 42 324 42 16 32 64 128 256), losses := [] }

theorem u41301 : Upper (D 7) (R 7) [6,40,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41302 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 324 56 211 227 195 195 451), lower := (rows 7 42 324 56 16 32 64 128 256), losses := [] }

theorem u41302 : Upper (D 7) (R 7) [6,40,320,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41303 : Route 9 := (fun mask => (mask,id))

def c41303 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41303 : Upper (D 7) (R 7) [6,40,320,65] 13 := by
  apply FastRouting.sound _ _ [6,40,320,65] 13 (by decide) (choices 2) [3,33,34,129,130,160] r41303 c41303
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31200
  · exact u31201
  · exact u31202
  · exact u31203
  · exact u31204
  · exact u31205

def r41304 : Route 9 := (fun mask => (mask,id))

def c41304 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41304 : Upper (D 7) (R 7) [6,40,320,66] 13 := by
  apply FastRouting.sound _ _ [6,40,320,66] 13 (by decide) (choices 2) [33,129,160] r41304 c41304
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u31206
  · exact u31207
  · exact u31208

def r41305 : Route 9 := (fun mask => (mask,id))

def c41305 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41305 : Upper (D 7) (R 7) [6,40,320,80] 13 := by
  apply FastRouting.sound _ _ [6,40,320,80] 13 (by decide) (choices 2) [3,33,34,129,130,160] r41305 c41305
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31209
  · exact u31210
  · exact u31211
  · exact u31212
  · exact u31213
  · exact u31214

def b41306 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 324 104 147 179 211 147 403), lower := (rows 7 42 324 104 16 32 64 128 256), losses := [] }

theorem u41306 : Upper (D 7) (R 7) [6,40,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41307 : Route 9 := (fun mask => (mask,id))

def c41307 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41307 : Upper (D 7) (R 7) [6,40,320,129] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41307 c41307
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31215
  · exact u31216
  · exact u31217
  · exact u31218
  · exact u31219
  · exact u31220
  · exact u31221
  · exact u31222
  · exact u31223
  · exact u31224

def r41308 : Route 9 := (fun mask => (mask,id))

def c41308 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41308 : Upper (D 7) (R 7) [6,40,320,130] 13 := by
  apply FastRouting.sound _ _ [6,40,320,130] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41308 c41308
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31225
  · exact u31226
  · exact u31227
  · exact u31228
  · exact u31229
  · exact u31230

def r41309 : Route 9 := (fun mask => (mask,id))

def c41309 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41309 : Upper (D 7) (R 7) [6,40,320,144] 13 := by
  apply FastRouting.sound _ _ [6,40,320,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41309 c41309
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31231
  · exact u31232
  · exact u31233
  · exact u31234
  · exact u31235
  · exact u31236
  · exact u31237
  · exact u31238
  · exact u31239
  · exact u31240

def b41310 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 324 168 211 243 211 211 467), lower := (rows 7 42 324 168 16 32 64 128 256), losses := [] }

theorem u41310 : Upper (D 7) (R 7) [6,40,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41311 : Route 9 := (fun mask => (mask,id))

def c41311 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41311 : Upper (D 7) (R 7) [6,40,320,192] 13 := by
  apply FastRouting.sound _ _ [6,40,320,192] 13 (by decide) (choices 2) [3,33,34,129,130,160] r41311 c41311
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31241
  · exact u31242
  · exact u31243
  · exact u31244
  · exact u31245
  · exact u31246

def b41312 : PairBound 9 := { available := 496, camps := [{ cop := 1, region := 13, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 98 13 11 496 496 496 496 496), lower := (rows 7 98 13 11 16 32 64 128 256), losses := [] }

theorem u41312 : Upper (D 7) (R 7) [6,96,9,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41313 : PairBound 9 := { available := 482, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 7 98 13 25 498 482 482 482 482), lower := (rows 7 98 13 25 16 32 64 128 256), losses := [] }

theorem u41313 : Upper (D 7) (R 7) [6,96,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41314 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 98 13 26 497 481 481 481 481), lower := (rows 7 98 13 26 16 32 64 128 256), losses := [] }

theorem u41314 : Upper (D 7) (R 7) [6,96,9,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41315 : PairBound 9 := { available := 466, camps := [{ cop := 1, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 13 41 466 498 466 466 466), lower := (rows 7 98 13 41 16 32 64 128 256), losses := [] }

theorem u41315 : Upper (D 7) (R 7) [6,96,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41316 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 13 42 465 497 465 465 465), lower := (rows 7 98 13 42 16 32 64 128 256), losses := [] }

theorem u41316 : Upper (D 7) (R 7) [6,96,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41317 : Route 9 := (fun mask => (mask,id))

def c41317 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41317 : Upper (D 7) (R 7) [6,96,9,48] 13 := by
  apply FastRouting.sound _ _ [6,96,9,48] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41317 c41317
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31247
  · exact u31248
  · exact u31249
  · exact u31250
  · exact u31251
  · exact u31252
  · exact u31253
  · exact u31254
  · exact u31255
  · exact u31256

def b41318 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 13, targets := 128 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(2,7),(3,7),(4,5)], upper := (rows 7 98 13 104 403 435 467 403 403), lower := (rows 7 98 13 104 16 32 64 128 256), losses := [] }

theorem u41318 : Upper (D 7) (R 7) [6,96,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41319 : PairBound 9 := { available := 498, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 7 98 13 137 498 498 498 498 498), lower := (rows 7 98 13 137 16 32 64 128 256), losses := [] }

theorem u41319 : Upper (D 7) (R 7) [6,96,9,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41320 : PairBound 9 := { available := 497, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 98 13 138 497 497 497 497 497), lower := (rows 7 98 13 138 16 32 64 128 256), losses := [] }

theorem u41320 : Upper (D 7) (R 7) [6,96,9,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41321 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41321 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41321 : Upper (D 7) (R 7) [6,96,9,144] 13 := by
  apply FastRouting.sound _ _ [6,96,9,144] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r41321 c41321
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31257
  · exact u31258
  · exact u31259
  · exact u31260
  · exact u31261
  · exact u31262
  · exact u31263
  · exact u31264
  · exact u31265
  · exact u31266
  · exact u31267

def r41322 : Route 9 := (fun mask => (mask,id))

def c41322 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41322 : Upper (D 7) (R 7) [6,96,9,160] 13 := by
  apply FastRouting.sound _ _ [6,96,9,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41322 c41322
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31268
  · exact u31269
  · exact u31270
  · exact u31271
  · exact u31272
  · exact u31273
  · exact u31274
  · exact u31275
  · exact u31276
  · exact u31277

def b41323 : PairBound 9 := { available := 242, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 7 98 13 265 242 242 242 242 498), lower := (rows 7 98 13 265 16 32 64 128 256), losses := [] }

theorem u41323 : Upper (D 7) (R 7) [6,96,9,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41324 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 98 13 266 241 241 241 241 497), lower := (rows 7 98 13 266 16 32 64 128 256), losses := [] }

theorem u41324 : Upper (D 7) (R 7) [6,96,9,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41325 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41325 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41325 : Upper (D 7) (R 7) [6,96,9,272] 13 := by
  apply FastRouting.sound _ _ [6,96,9,272] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41325 c41325
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31278
  · exact u31279
  · exact u31280
  · exact u31281
  · exact u31282
  · exact u31283
  · exact u31284

def r41326 : Route 9 := (fun mask => (mask,id))

def c41326 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41326 : Upper (D 7) (R 7) [6,96,9,288] 13 := by
  apply FastRouting.sound _ _ [6,96,9,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41326 c41326
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31285
  · exact u31286
  · exact u31287
  · exact u31288
  · exact u31289
  · exact u31290

def r41327 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41327 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41327 : Upper (D 7) (R 7) [6,96,9,384] 13 := by
  apply FastRouting.sound _ _ [6,96,9,384] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41327 c41327
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u31291
  · exact u31292
  · exact u31293
  · exact u31294
  · exact u31295
  · exact u31296
  · exact u31297

def b41328 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 28 11 497 481 481 481 481), lower := (rows 7 98 28 11 16 32 64 128 256), losses := [] }

theorem u41328 : Upper (D 7) (R 7) [6,96,24,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41329_3 : Upper (D 7) (R 7) [6,96,24,33,3] 13 :=
  permutation_upper _ _ _ [6,96,24,3,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31298

def r41329 : Route 9 := (fun mask => (mask,id))

def c41329 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41329 : Upper (D 7) (R 7) [6,96,24,33] 13 := by
  apply FastRouting.sound _ _ [6,96,24,33] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41329 c41329
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41329_3
  · exact u31304
  · exact u31305
  · exact u31306
  · exact u31307
  · exact u31308
  · exact u31309
  · exact u31310
  · exact u31311
  · exact u31312

def b41330 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 28 42 465 481 449 449 449), lower := (rows 7 98 28 42 16 32 64 128 256), losses := [] }

theorem u41330 : Upper (D 7) (R 7) [6,96,24,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41331 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 28 104 403 419 451 387 387), lower := (rows 7 98 28 104 16 32 64 128 256), losses := [] }

theorem u41331 : Upper (D 7) (R 7) [6,96,24,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41332_3 : Upper (D 7) (R 7) [6,96,24,129,3] 13 :=
  permutation_upper _ _ _ [6,96,24,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31299

theorem m41332_33 : Upper (D 7) (R 7) [6,96,24,129,33] 13 :=
  permutation_upper _ _ _ [6,96,24,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31306

theorem m41332_34 : Upper (D 7) (R 7) [6,96,24,129,34] 13 :=
  permutation_upper _ _ _ [6,96,24,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31313

theorem m41332_96 : Upper (D 7) (R 7) [6,96,24,129,96] 13 :=
  permutation_upper _ _ _ [6,96,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31318

def r41332 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41332 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41332 : Upper (D 7) (R 7) [6,96,24,129] 13 := by
  apply FastRouting.sound _ _ [6,96,24,129] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r41332 c41332
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41332_3
  · exact m41332_33
  · exact m41332_34
  · exact m41332_96
  · exact u31323
  · exact u31324
  · exact u31325
  · exact u31326
  · exact u31327
  · exact u31328
  · exact u31329

theorem m41333_33 : Upper (D 7) (R 7) [6,96,24,130,33] 13 :=
  permutation_upper _ _ _ [6,96,24,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31307

theorem m41333_96 : Upper (D 7) (R 7) [6,96,24,130,96] 13 :=
  permutation_upper _ _ _ [6,96,24,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31319

theorem m41333_129 : Upper (D 7) (R 7) [6,96,24,130,129] 13 :=
  permutation_upper _ _ _ [6,96,24,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31324

def r41333 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41333 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41333 : Upper (D 7) (R 7) [6,96,24,130] 13 := by
  apply FastRouting.sound _ _ [6,96,24,130] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r41333 c41333
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41333_33
  · exact m41333_96
  · exact m41333_129
  · exact u31330
  · exact u31331
  · exact u31332
  · exact u31333

theorem m41334_3 : Upper (D 7) (R 7) [6,96,24,160,3] 13 :=
  permutation_upper _ _ _ [6,96,24,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31300

theorem m41334_65 : Upper (D 7) (R 7) [6,96,24,160,65] 13 :=
  permutation_upper _ _ _ [6,96,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31308

theorem m41334_66 : Upper (D 7) (R 7) [6,96,24,160,66] 13 :=
  permutation_upper _ _ _ [6,96,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31314

theorem m41334_129 : Upper (D 7) (R 7) [6,96,24,160,129] 13 :=
  permutation_upper _ _ _ [6,96,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31325

theorem m41334_130 : Upper (D 7) (R 7) [6,96,24,160,130] 13 :=
  permutation_upper _ _ _ [6,96,24,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31330

def r41334 : Route 9 := (fun mask => (mask,id))

def c41334 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41334 : Upper (D 7) (R 7) [6,96,24,160] 13 := by
  apply FastRouting.sound _ _ [6,96,24,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41334 c41334
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41334_3
  · exact m41334_65
  · exact m41334_66
  · exact m41334_129
  · exact m41334_130
  · exact u31334
  · exact u31335
  · exact u31336
  · exact u31337
  · exact u31338

theorem m41335_3 : Upper (D 7) (R 7) [6,96,24,257,3] 13 :=
  permutation_upper _ _ _ [6,96,24,3,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31301

theorem m41335_33 : Upper (D 7) (R 7) [6,96,24,257,33] 13 :=
  permutation_upper _ _ _ [6,96,24,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31309

theorem m41335_34 : Upper (D 7) (R 7) [6,96,24,257,34] 13 :=
  permutation_upper _ _ _ [6,96,24,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31315

theorem m41335_96 : Upper (D 7) (R 7) [6,96,24,257,96] 13 :=
  permutation_upper _ _ _ [6,96,24,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31320

theorem m41335_129 : Upper (D 7) (R 7) [6,96,24,257,129] 13 :=
  permutation_upper _ _ _ [6,96,24,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31326

theorem m41335_130 : Upper (D 7) (R 7) [6,96,24,257,130] 13 :=
  permutation_upper _ _ _ [6,96,24,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31331

theorem m41335_160 : Upper (D 7) (R 7) [6,96,24,257,160] 13 :=
  permutation_upper _ _ _ [6,96,24,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31335

def r41335 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41335 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41335 : Upper (D 7) (R 7) [6,96,24,257] 13 := by
  apply FastRouting.sound _ _ [6,96,24,257] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41335 c41335
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41335_3
  · exact m41335_33
  · exact m41335_34
  · exact m41335_96
  · exact m41335_129
  · exact m41335_130
  · exact m41335_160

theorem m41336_33 : Upper (D 7) (R 7) [6,96,24,258,33] 13 :=
  permutation_upper _ _ _ [6,96,24,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31310

theorem m41336_96 : Upper (D 7) (R 7) [6,96,24,258,96] 13 :=
  permutation_upper _ _ _ [6,96,24,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31321

theorem m41336_129 : Upper (D 7) (R 7) [6,96,24,258,129] 13 :=
  permutation_upper _ _ _ [6,96,24,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31327

theorem m41336_160 : Upper (D 7) (R 7) [6,96,24,258,160] 13 :=
  permutation_upper _ _ _ [6,96,24,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31336

def r41336 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41336 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41336 : Upper (D 7) (R 7) [6,96,24,258] 13 := by
  apply FastRouting.sound _ _ [6,96,24,258] 13 (by decide) (choices 2) [33,96,129,160] r41336 c41336
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m41336_33
  · exact m41336_96
  · exact m41336_129
  · exact m41336_160

theorem m41337_3 : Upper (D 7) (R 7) [6,96,24,288,3] 13 :=
  permutation_upper _ _ _ [6,96,24,3,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31302

theorem m41337_65 : Upper (D 7) (R 7) [6,96,24,288,65] 13 :=
  permutation_upper _ _ _ [6,96,24,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31311

theorem m41337_66 : Upper (D 7) (R 7) [6,96,24,288,66] 13 :=
  permutation_upper _ _ _ [6,96,24,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31316

theorem m41337_129 : Upper (D 7) (R 7) [6,96,24,288,129] 13 :=
  permutation_upper _ _ _ [6,96,24,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31328

theorem m41337_130 : Upper (D 7) (R 7) [6,96,24,288,130] 13 :=
  permutation_upper _ _ _ [6,96,24,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31332

theorem m41337_192 : Upper (D 7) (R 7) [6,96,24,288,192] 13 :=
  permutation_upper _ _ _ [6,96,24,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31337

def r41337 : Route 9 := (fun mask => (mask,id))

def c41337 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41337 : Upper (D 7) (R 7) [6,96,24,288] 13 := by
  apply FastRouting.sound _ _ [6,96,24,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41337 c41337
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41337_3
  · exact m41337_65
  · exact m41337_66
  · exact m41337_129
  · exact m41337_130
  · exact m41337_192

theorem m41338_3 : Upper (D 7) (R 7) [6,96,24,384,3] 13 :=
  permutation_upper _ _ _ [6,96,24,3,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31303

theorem m41338_33 : Upper (D 7) (R 7) [6,96,24,384,33] 13 :=
  permutation_upper _ _ _ [6,96,24,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31312

theorem m41338_34 : Upper (D 7) (R 7) [6,96,24,384,34] 13 :=
  permutation_upper _ _ _ [6,96,24,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31317

theorem m41338_96 : Upper (D 7) (R 7) [6,96,24,384,96] 13 :=
  permutation_upper _ _ _ [6,96,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31322

theorem m41338_129 : Upper (D 7) (R 7) [6,96,24,384,129] 13 :=
  permutation_upper _ _ _ [6,96,24,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31329

theorem m41338_130 : Upper (D 7) (R 7) [6,96,24,384,130] 13 :=
  permutation_upper _ _ _ [6,96,24,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31333

theorem m41338_160 : Upper (D 7) (R 7) [6,96,24,384,160] 13 :=
  permutation_upper _ _ _ [6,96,24,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31338

def r41338 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41338 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41338 : Upper (D 7) (R 7) [6,96,24,384] 13 := by
  apply FastRouting.sound _ _ [6,96,24,384] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41338 c41338
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m41338_3
  · exact m41338_33
  · exact m41338_34
  · exact m41338_96
  · exact m41338_129
  · exact m41338_130
  · exact m41338_160

def b41339 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 44 11 465 497 465 465 465), lower := (rows 7 98 44 11 16 32 64 128 256), losses := [] }

theorem u41339 : Upper (D 7) (R 7) [6,96,40,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u41339
end Delivery.IrregularNine14.P07
