import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0019
import IrregularNine14P09C0020

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4260 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 133 268 336 48 232 168 424), lower := (rows 35 67 133 268 336 48 64 128 256), losses := [] }

theorem u4260 : Upper (D 9) (R 9) [34,65,129,260,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4260 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4261 : Route 9 := (fun mask => (mask,id))

def c4261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4261 : Upper (D 9) (R 9) [34,65,129,260,320,128] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260,320,128] 13 (by decide) (choices 1) [8,16,32] r4261 c4261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1193
  · exact u1194
  · exact u1195

def r4262 : Route 9 := (fun mask => (mask,id))

def c4262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4262 : Upper (D 9) (R 9) [34,65,129,260,384,8] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260,384,8] 13 (by decide) (choices 1) [16,32] r4262 c4262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1196
  · exact u1197

def r4263 : Route 9 := (fun mask => (mask,id))

def c4263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4263 : Upper (D 9) (R 9) [34,65,129,260,384,16] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260,384,16] 13 (by decide) (choices 1) [8,32] r4263 c4263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1198
  · exact u1199

def b4264 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 133 268 400 96 120 184 312), lower := (rows 35 67 133 268 400 96 64 128 256), losses := [] }

theorem u4264 : Upper (D 9) (R 9) [34,65,129,260,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4264 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4265 : Route 9 := (fun mask => (mask,id))

def c4265 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4265 : Upper (D 9) (R 9) [34,65,129,288,320,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,288,320,4] 13 (by decide) (choices 1) [8,16,128] r4265 c4265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1200
  · exact u1201
  · exact u1202

def b4266 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 470, targets := 32 },{ cop := 4, region := 43, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(4,5)], upper := (rows 35 67 133 296 336 40 212 148 404), lower := (rows 35 67 133 296 336 40 64 128 256), losses := [] }

theorem u4266 : Upper (D 9) (R 9) [34,65,129,288,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4266 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4267 : PairBound 9 := { available := 140, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8)], upper := (rows 35 67 133 296 336 48 204 140 396), lower := (rows 35 67 133 296 336 48 64 128 256), losses := [] }

theorem u4267 : Upper (D 9) (R 9) [34,65,129,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4267 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4268 : Route 9 := (fun mask => (mask,id))

def c4268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4268 : Upper (D 9) (R 9) [34,65,129,288,320,128] 13 := by
  apply FastRouting.sound _ _ [34,65,129,288,320,128] 13 (by decide) (choices 1) [4,8,16] r4268 c4268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1203
  · exact u1204
  · exact u1205

def r4269 : Route 9 := (fun mask => (mask,id))

def c4269 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4269 : Upper (D 9) (R 9) [34,65,129,288,384,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,288,384,4] 13 (by decide) (choices 1) [8,16] r4269 c4269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1206
  · exact u1207

def b4270 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 470, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 35 67 133 296 400 40 84 212 340), lower := (rows 35 67 133 296 400 40 64 128 256), losses := [] }

theorem u4270 : Upper (D 9) (R 9) [34,65,129,288,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4270 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4271 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 67 133 296 400 48 76 204 332), lower := (rows 35 67 133 296 400 48 64 128 256), losses := [] }

theorem u4271 : Upper (D 9) (R 9) [34,65,129,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4271 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4272 : PairBound 9 := { available := 28, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 133 296 400 96 92 156 284), lower := (rows 35 67 133 296 400 96 64 128 256), losses := [] }

theorem u4272 : Upper (D 9) (R 9) [34,65,129,288,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4272 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4273 : Route 9 := (fun mask => (mask,id))

def c4273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4273 : Upper (D 9) (R 9) [34,65,129,320,384,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,320,384,4] 13 (by decide) (choices 1) [8,16,32] r4273 c4273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1208
  · exact u1209
  · exact u1210

def b4274 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 133 328 400 40 116 180 308), lower := (rows 35 67 133 328 400 40 64 128 256), losses := [] }

theorem u4274 : Upper (D 9) (R 9) [34,65,129,320,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4274 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4275 : Route 9 := (fun mask => (mask,id))

def c4275 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4275 : Upper (D 9) (R 9) [34,65,129,320,384,16] 13 := by
  apply FastRouting.sound _ _ [34,65,129,320,384,16] 13 (by decide) (choices 1) [4,8,32] r4275 c4275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1211
  · exact u1212
  · exact u1213

def b4276 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 332, targets := 33 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 67 140 268 176 33 336 464 336), lower := (rows 35 67 140 268 176 33 64 128 256), losses := [] }

theorem u4276 : Upper (D 9) (R 9) [34,65,136,260,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4276 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4277 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 67 140 268 176 48 321 449 321), lower := (rows 35 67 140 268 176 48 64 128 256), losses := [] }

theorem u4277 : Upper (D 9) (R 9) [34,65,136,260,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4277 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4278 : PairBound 9 := { available := 273, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 140 268 176 96 337 401 273), lower := (rows 35 67 140 268 176 96 64 128 256), losses := [] }

theorem u4278 : Upper (D 9) (R 9) [34,65,136,260,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4278 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4279 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 211, targets := 256 },{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,8)], upper := (rows 35 67 140 268 176 288 81 209 337), lower := (rows 35 67 140 268 176 288 64 128 256), losses := [] }

theorem u4279 : Upper (D 9) (R 9) [34,65,136,260,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4279 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4280 : PairBound 9 := { available := 304, camps := [{ cop := 6, region := 35, targets := 384 },{ cop := 0, region := 476, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 140 268 208 33 368 432 304), lower := (rows 35 67 140 268 208 33 64 128 256), losses := [] }

theorem u4280 : Upper (D 9) (R 9) [34,65,136,260,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4280 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4281 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(2,6),(3,6)], upper := (rows 35 67 140 268 208 48 353 417 289), lower := (rows 35 67 140 268 208 48 64 128 256), losses := [] }

theorem u4281 : Upper (D 9) (R 9) [34,65,136,260,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4281 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4282 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 211, targets := 256 },{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,8)], upper := (rows 35 67 140 268 208 288 113 177 305), lower := (rows 35 67 140 268 208 288 64 128 256), losses := [] }

theorem u4282 : Upper (D 9) (R 9) [34,65,136,260,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4282 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4283 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 332, targets := 33 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 67 140 280 176 33 324 452 324), lower := (rows 35 67 140 280 176 33 64 128 256), losses := [] }

theorem u4283 : Upper (D 9) (R 9) [34,65,136,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4283 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4284 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 48, targets := 321 },{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7),(4,0),(4,6),(4,8)], upper := (rows 35 67 140 280 176 36 321 449 321), lower := (rows 35 67 140 280 176 36 64 128 256), losses := [] }

theorem u4284 : Upper (D 9) (R 9) [34,65,136,272,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4284 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4285 : PairBound 9 := { available := 261, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 140 280 176 96 325 389 261), lower := (rows 35 67 140 280 176 96 64 128 256), losses := [] }

theorem u4285 : Upper (D 9) (R 9) [34,65,136,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4285 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4286 : Route 9 := (fun mask => (mask,id))

def c4286 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4286 : Upper (D 9) (R 9) [34,65,136,272,160,256] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,160,256] 13 (by decide) (choices 1) [1,4] r4286 c4286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1214
  · exact u1215

def b4287 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 35, targets := 384 },{ cop := 0, region := 476, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 140 280 208 33 356 420 292), lower := (rows 35 67 140 280 208 33 64 128 256), losses := [] }

theorem u4287 : Upper (D 9) (R 9) [34,65,136,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4287 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4288 : Route 9 := (fun mask => (mask,id))

def c4288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4288 : Upper (D 9) (R 9) [34,65,136,272,192,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,192,4] 13 (by decide) (choices 1) [1,32,256] r4288 c4288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1216
  · exact u1217
  · exact u1218

def r4289 : Route 9 := (fun mask => (mask,id))

def c4289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4289 : Upper (D 9) (R 9) [34,65,136,272,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,192,256] 13 (by decide) (choices 1) [1,4,32] r4289 c4289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1219
  · exact u1220
  · exact u1221

def b4290 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 212, targets := 33 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(4,0),(4,5)], upper := (rows 35 67 140 296 208 33 340 404 276), lower := (rows 35 67 140 296 208 33 64 128 256), losses := [] }

theorem u4290 : Upper (D 9) (R 9) [34,65,136,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4290 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4291 : Route 9 := (fun mask => (mask,id))

def c4291 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4291 : Upper (D 9) (R 9) [34,65,136,288,192,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,192,4] 13 (by decide) (choices 1) [1,16,256] r4291 c4291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1222
  · exact u1223
  · exact u1224

def b4292 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 140 296 208 48 325 389 261), lower := (rows 35 67 140 296 208 48 64 128 256), losses := [] }

theorem u4292 : Upper (D 9) (R 9) [34,65,136,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4292 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4293 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 215, targets := 256 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 35 67 140 296 208 288 85 149 277), lower := (rows 35 67 140 296 208 288 64 128 256), losses := [] }

theorem u4293 : Upper (D 9) (R 9) [34,65,136,288,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4293 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4294 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 212, targets := 33 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(4,0),(4,5)], upper := (rows 35 67 140 296 336 33 212 148 404), lower := (rows 35 67 140 296 336 33 64 128 256), losses := [] }

theorem u4294 : Upper (D 9) (R 9) [34,65,136,288,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4294 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4295 : Route 9 := (fun mask => (mask,id))

def c4295 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4295 : Upper (D 9) (R 9) [34,65,136,288,320,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,320,4] 13 (by decide) (choices 1) [1,16,128] r4295 c4295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1225
  · exact u1226
  · exact u1227

def b4296 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8)], upper := (rows 35 67 140 296 336 48 197 133 389), lower := (rows 35 67 140 296 336 48 64 128 256), losses := [] }

theorem u4296 : Upper (D 9) (R 9) [34,65,136,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4296 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4297 : Route 9 := (fun mask => (mask,id))

def c4297 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4297 : Upper (D 9) (R 9) [34,65,136,288,320,128] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,320,128] 13 (by decide) (choices 1) [1,4,16] r4297 c4297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1228
  · exact u1229
  · exact u1230

def b4298 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 212, targets := 33 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(4,0),(4,5)], upper := (rows 35 67 140 296 400 33 84 212 340), lower := (rows 35 67 140 296 400 33 64 128 256), losses := [] }

theorem u4298 : Upper (D 9) (R 9) [34,65,136,288,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4298 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4299 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 35 67 140 296 400 36 81 209 337), lower := (rows 35 67 140 296 400 36 64 128 256), losses := [] }

theorem u4299 : Upper (D 9) (R 9) [34,65,136,288,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4299 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4300 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 35 67 140 296 400 48 69 197 325), lower := (rows 35 67 140 296 400 48 64 128 256), losses := [] }

theorem u4300 : Upper (D 9) (R 9) [34,65,136,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4300 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4301 : PairBound 9 := { available := 21, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 140 296 400 96 85 149 277), lower := (rows 35 67 140 296 400 96 64 128 256), losses := [] }

theorem u4301 : Upper (D 9) (R 9) [34,65,136,288,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4301 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4302 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 35, targets := 384 },{ cop := 4, region := 332, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 140 328 176 33 340 404 276), lower := (rows 35 67 140 328 176 33 64 128 256), losses := [] }

theorem u4302 : Upper (D 9) (R 9) [34,65,136,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4302 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4303 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 48, targets := 321 },{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7),(4,0),(4,6),(4,8)], upper := (rows 35 67 140 328 176 36 337 401 273), lower := (rows 35 67 140 328 176 36 64 128 256), losses := [] }

theorem u4303 : Upper (D 9) (R 9) [34,65,136,320,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4303 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4304 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 67 140 328 176 48 325 389 261), lower := (rows 35 67 140 328 176 48 64 128 256), losses := [] }

theorem u4304 : Upper (D 9) (R 9) [34,65,136,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4304 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4305 : Route 9 := (fun mask => (mask,id))

def c4305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4305 : Upper (D 9) (R 9) [34,65,136,320,160,256] 13 := by
  apply FastRouting.sound _ _ [34,65,136,320,160,256] 13 (by decide) (choices 1) [1,4,16] r4305 c4305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1231
  · exact u1232
  · exact u1233

def b4306 : PairBound 9 := { available := 148, camps := [{ cop := 4, region := 204, targets := 33 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 67 140 328 304 33 212 148 404), lower := (rows 35 67 140 328 304 33 64 128 256), losses := [] }

theorem u4306 : Upper (D 9) (R 9) [34,65,136,320,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4306 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4307 : Route 9 := (fun mask => (mask,id))

def c4307 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4307 : Upper (D 9) (R 9) [34,65,136,320,288,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,320,288,4] 13 (by decide) (choices 1) [1,16,128] r4307 c4307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1234
  · exact u1235
  · exact u1236

def b4308 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 51, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,5)], upper := (rows 35 67 140 328 304 48 197 133 389), lower := (rows 35 67 140 328 304 48 64 128 256), losses := [] }

theorem u4308 : Upper (D 9) (R 9) [34,65,136,320,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4308 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4309 : Route 9 := (fun mask => (mask,id))

def c4309 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4309 : Upper (D 9) (R 9) [34,65,136,320,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,136,320,288,128] 13 (by decide) (choices 1) [1,4,16] r4309 c4309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1237
  · exact u1238
  · exact u1239

def b4310 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 384 },{ cop := 0, region := 476, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 140 328 400 33 116 180 308), lower := (rows 35 67 140 328 400 33 64 128 256), losses := [] }

theorem u4310 : Upper (D 9) (R 9) [34,65,136,320,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4310 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4311 : Route 9 := (fun mask => (mask,id))

def c4311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4311 : Upper (D 9) (R 9) [34,65,136,320,384,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,320,384,4] 13 (by decide) (choices 1) [1,16,32] r4311 c4311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1240
  · exact u1241
  · exact u1242

def r4312 : Route 9 := (fun mask => (mask,id))

def c4312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4312 : Upper (D 9) (R 9) [34,65,136,320,384,16] 13 := by
  apply FastRouting.sound _ _ [34,65,136,320,384,16] 13 (by decide) (choices 1) [1,4,32] r4312 c4312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1243
  · exact u1244
  · exact u1245

def b4313 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 344, targets := 33 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 35 67 164 328 400 33 92 156 284), lower := (rows 35 67 164 328 400 33 64 128 256), losses := [] }

theorem u4313 : Upper (D 9) (R 9) [34,65,160,320,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4313 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4314 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 4, region := 36, targets := 1 }], pairs := [(1,5),(2,0),(3,5),(4,5)], upper := (rows 35 67 164 328 400 36 89 153 281), lower := (rows 35 67 164 328 400 36 64 128 256), losses := [] }

theorem u4314 : Upper (D 9) (R 9) [34,65,160,320,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4314 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4315 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 164 328 400 40 85 149 277), lower := (rows 35 67 164 328 400 40 64 128 256), losses := [] }

theorem u4315 : Upper (D 9) (R 9) [34,65,160,320,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4315 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4316 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 35 67 164 328 400 48 77 141 269), lower := (rows 35 67 164 328 400 48 64 128 256), losses := [] }

theorem u4316 : Upper (D 9) (R 9) [34,65,160,320,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4316 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4317 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 56 145 96 448 384 384), lower := (rows 35 70 13 56 145 96 64 128 256), losses := [] }

theorem u4317 : Upper (D 9) (R 9) [34,68,9,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4317 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4318 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 44, targets := 320 },{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(2,6),(2,8),(3,6),(3,8)], upper := (rows 35 70 13 56 145 160 320 448 320), lower := (rows 35 70 13 56 145 160 64 128 256), losses := [] }

theorem u4318 : Upper (D 9) (R 9) [34,68,9,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4318 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4319 : Route 9 := (fun mask => (mask,id))

def c4319 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4319 : Upper (D 9) (R 9) [34,68,9,48,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,48,129,256] 13 (by decide) (choices 1) [128,256] r4319 c4319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1246
  · exact u1247

#print axioms u4319
end Delivery.IrregularNine14.P09
