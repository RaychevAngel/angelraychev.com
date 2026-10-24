import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0085
import IrregularNine14P01C0086

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8280 : Route 9 := (fun mask => (mask,id))

def c8280 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8280 : Upper (D 1) (R 1) [276,48,192,66] 13 := by
  apply FastRouting.sound _ _ [276,48,192,66] 13 (by decide) (choices 1) [1,2,8,32,128] r8280 c8280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5110
  · exact u5111
  · exact u5112
  · exact u5113
  · exact u5114

def r8281 : Route 9 := (fun mask => (mask,id))

def c8281 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8281 : Upper (D 1) (R 1) [276,48,192,96] 13 := by
  apply FastRouting.sound _ _ [276,48,192,96] 13 (by decide) (choices 1) [1,2,8,128] r8281 c8281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5115
  · exact u5116
  · exact u5117
  · exact u5118

def b8282 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 277 50 196 200 59 43 107 171 299), lower := (rows 277 50 196 200 16 32 64 128 256), losses := [] }

theorem u8282 : Upper (D 1) (R 1) [276,48,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8282
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8283 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 7 26 248 232 232 232 488), lower := (rows 277 98 7 26 16 32 64 128 256), losses := [] }

theorem u8283 : Upper (D 1) (R 1) [276,96,3,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8283
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8284 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 98 7 42 216 248 216 216 472), lower := (rows 277 98 7 42 16 32 64 128 256), losses := [] }

theorem u8284 : Upper (D 1) (R 1) [276,96,3,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8284
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8285 : PairBound 9 := { available := 202, camps := [{ cop := 3, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 7 56 218 234 202 202 458), lower := (rows 277 98 7 56 16 32 64 128 256), losses := [] }

theorem u8285 : Upper (D 1) (R 1) [276,96,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8285
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8286 : PairBound 9 := { available := 154, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 98 7 104 154 186 218 154 410), lower := (rows 277 98 7 104 16 32 64 128 256), losses := [] }

theorem u8286 : Upper (D 1) (R 1) [276,96,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8286
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8287 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8287 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u8287 : Upper (D 1) (R 1) [276,96,3,130] 13 := by
  apply FastRouting.sound _ _ [276,96,3,130] 13 (by decide) (choices 1) [8,32,128] r8287 c8287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5119
  · exact u5120
  · exact u5121

def b8288 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 7 152 250 234 234 234 490), lower := (rows 277 98 7 152 16 32 64 128 256), losses := [] }

theorem u8288 : Upper (D 1) (R 1) [276,96,3,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8288
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8289 : Route 9 := (fun mask => (mask,id))

def c8289 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8289 : Upper (D 1) (R 1) [276,96,3,160] 13 := by
  apply FastRouting.sound _ _ [276,96,3,160] 13 (by decide) (choices 1) [2,8,64,128] r8289 c8289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5122
  · exact u5123
  · exact u5124
  · exact u5125

def b8290 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 13 26 242 226 226 226 482), lower := (rows 277 98 13 26 16 32 64 128 256), losses := [] }

theorem u8290 : Upper (D 1) (R 1) [276,96,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8290
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8291 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 98 13 42 210 242 210 210 466), lower := (rows 277 98 13 42 16 32 64 128 256), losses := [] }

theorem u8291 : Upper (D 1) (R 1) [276,96,9,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8291
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8292 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 13 56 210 226 194 194 450), lower := (rows 277 98 13 56 16 32 64 128 256), losses := [] }

theorem u8292 : Upper (D 1) (R 1) [276,96,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8292
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8293 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 98 13 104 146 178 210 146 402), lower := (rows 277 98 13 104 16 32 64 128 256), losses := [] }

theorem u8293 : Upper (D 1) (R 1) [276,96,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8293
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8294 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8294 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8294 : Upper (D 1) (R 1) [276,96,9,130] 13 := by
  apply FastRouting.sound _ _ [276,96,9,130] 13 (by decide) (choices 1) [2,32,128] r8294 c8294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5126
  · exact u5127
  · exact u5128

def b8295 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 13 152 242 226 226 226 482), lower := (rows 277 98 13 152 16 32 64 128 256), losses := [] }

theorem u8295 : Upper (D 1) (R 1) [276,96,9,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8295
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8296 : Route 9 := (fun mask => (mask,id))

def c8296 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8296 : Upper (D 1) (R 1) [276,96,9,160] 13 := by
  apply FastRouting.sound _ _ [276,96,9,160] 13 (by decide) (choices 1) [2,64,128] r8296 c8296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5129
  · exact u5130
  · exact u5131

def b8297 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 277 98 14 11 240 240 240 240 496), lower := (rows 277 98 14 11 16 32 64 128 256), losses := [] }

theorem u8297 : Upper (D 1) (R 1) [276,96,10,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8297
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8298 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 14 25 242 226 226 226 482), lower := (rows 277 98 14 25 16 32 64 128 256), losses := [] }

theorem u8298 : Upper (D 1) (R 1) [276,96,10,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8298
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8299 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 277 98 14 26 241 225 225 225 481), lower := (rows 277 98 14 26 16 32 64 128 256), losses := [] }

theorem u8299 : Upper (D 1) (R 1) [276,96,10,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8299
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8300 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 277 98 14 41 210 242 210 210 466), lower := (rows 277 98 14 41 16 32 64 128 256), losses := [] }

theorem u8300 : Upper (D 1) (R 1) [276,96,10,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8300
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8301 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 277 98 14 42 209 241 209 209 465), lower := (rows 277 98 14 42 16 32 64 128 256), losses := [] }

theorem u8301 : Upper (D 1) (R 1) [276,96,10,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8301
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8302 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 14 56 211 227 195 195 451), lower := (rows 277 98 14 56 16 32 64 128 256), losses := [] }

theorem u8302 : Upper (D 1) (R 1) [276,96,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8302
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8303 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 277 98 14 104 147 179 211 147 403), lower := (rows 277 98 14 104 16 32 64 128 256), losses := [] }

theorem u8303 : Upper (D 1) (R 1) [276,96,10,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8303
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8304 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8304 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8304 : Upper (D 1) (R 1) [276,96,10,129] 13 := by
  apply FastRouting.sound _ _ [276,96,10,129] 13 (by decide) (choices 1) [2,32,128] r8304 c8304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5132
  · exact u5133
  · exact u5134

def b8305 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 277 98 14 138 241 241 241 241 497), lower := (rows 277 98 14 138 16 32 64 128 256), losses := [] }

theorem u8305 : Upper (D 1) (R 1) [276,96,10,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8305
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8306 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 14 152 243 227 227 227 483), lower := (rows 277 98 14 152 16 32 64 128 256), losses := [] }

theorem u8306 : Upper (D 1) (R 1) [276,96,10,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8306
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8307 : PairBound 9 := { available := 211, camps := [{ cop := 2, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 277 98 14 168 211 243 211 211 467), lower := (rows 277 98 14 168 16 32 64 128 256), losses := [] }

theorem u8307 : Upper (D 1) (R 1) [276,96,10,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8307
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8308 : PairBound 9 := { available := 210, camps := [], pairs := [(0,5)], upper := (rows 277 98 44 11 210 242 210 210 466), lower := (rows 277 98 44 11 16 32 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 8 26 0 74 138 266), good := (rows 277 466 477 475 16 0 64 128 256) }] }

theorem u8308 : Upper (D 1) (R 1) [276,96,40,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8308
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8309 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 44 25 210 226 194 194 450), lower := (rows 277 98 44 25 16 32 64 128 256), losses := [] }

theorem u8309 : Upper (D 1) (R 1) [276,96,40,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8309
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8310 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 44 26 211 227 195 195 451), lower := (rows 277 98 44 26 16 32 64 128 256), losses := [] }

theorem u8310 : Upper (D 1) (R 1) [276,96,40,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8310
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8311 : Route 9 := (fun mask => (mask,id))

def c8311 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8311 : Upper (D 1) (R 1) [276,96,40,65] 13 := by
  apply FastRouting.sound _ _ [276,96,40,65] 13 (by decide) (choices 1) [2,128] r8311 c8311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5135
  · exact u5136

def b8312 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 277 98 44 74 147 179 211 147 403), lower := (rows 277 98 44 74 16 32 64 128 256), losses := [] }

theorem u8312 : Upper (D 1) (R 1) [276,96,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8312
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8313 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 44 88 147 163 195 131 387), lower := (rows 277 98 44 88 16 32 64 128 256), losses := [] }

theorem u8313 : Upper (D 1) (R 1) [276,96,40,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8313
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8314 : Route 9 := (fun mask => (mask,id))

def c8314 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8314 : Upper (D 1) (R 1) [276,96,40,129] 13 := by
  apply FastRouting.sound _ _ [276,96,40,129] 13 (by decide) (choices 1) [2,64,128] r8314 c8314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5137
  · exact u5138
  · exact u5139

def r8315 : Route 9 := (fun mask => (mask,id))

def c8315 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8315 : Upper (D 1) (R 1) [276,96,40,130] 13 := by
  apply FastRouting.sound _ _ [276,96,40,130] 13 (by decide) (choices 1) [1,2,64,128] r8315 c8315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5140
  · exact u5141
  · exact u5142
  · exact u5143

def b8316 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 44 152 211 227 195 195 451), lower := (rows 277 98 44 152 16 32 64 128 256), losses := [] }

theorem u8316 : Upper (D 1) (R 1) [276,96,40,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8316
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8317 : Route 9 := (fun mask => (mask,id))

def c8317 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8317 : Upper (D 1) (R 1) [276,96,40,192] 13 := by
  apply FastRouting.sound _ _ [276,96,40,192] 13 (by decide) (choices 1) [1,2,128] r8317 c8317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5144
  · exact u5145
  · exact u5146

def b8318 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 133 26 250 234 234 234 490), lower := (rows 277 98 133 26 16 32 64 128 256), losses := [] }

theorem u8318 : Upper (D 1) (R 1) [276,96,129,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8318
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8319 : PairBound 9 := { available := 218, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 98 133 42 218 250 218 218 474), lower := (rows 277 98 133 42 16 32 64 128 256), losses := [] }

theorem u8319 : Upper (D 1) (R 1) [276,96,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8319
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8320 : PairBound 9 := { available := 202, camps := [{ cop := 3, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 133 56 218 234 202 202 458), lower := (rows 277 98 133 56 16 32 64 128 256), losses := [] }

theorem u8320 : Upper (D 1) (R 1) [276,96,129,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8320
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8321 : PairBound 9 := { available := 154, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 98 133 104 154 186 218 154 410), lower := (rows 277 98 133 104 16 32 64 128 256), losses := [] }

theorem u8321 : Upper (D 1) (R 1) [276,96,129,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8321
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8322 : PairBound 9 := { available := 122, camps := [{ cop := 3, region := 114, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 133 138 122 122 122 250 378), lower := (rows 277 98 133 138 16 32 64 128 256), losses := [] }

theorem u8322 : Upper (D 1) (R 1) [276,96,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8322
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8323 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 133 152 122 106 106 234 362), lower := (rows 277 98 133 152 16 32 64 128 256), losses := [] }

theorem u8323 : Upper (D 1) (R 1) [276,96,129,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8323
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8324 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 82, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 133 168 90 122 90 218 346), lower := (rows 277 98 133 168 16 32 64 128 256), losses := [] }

theorem u8324 : Upper (D 1) (R 1) [276,96,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8324
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8325 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u8325 : Upper (D 1) (R 1) [276,96,130,3] 13 := by
  apply FastRouting.sound _ _ [276,96,130,3] 13 (by decide) (choices 1) [8,32,128] r8325 c8325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5147
  · exact u5148
  · exact u5149

def b8326 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 134 25 250 234 234 234 490), lower := (rows 277 98 134 25 16 32 64 128 256), losses := [] }

theorem u8326 : Upper (D 1) (R 1) [276,96,130,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8326
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8327 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u8327 : Upper (D 1) (R 1) [276,96,130,18] 13 := by
  apply FastRouting.sound _ _ [276,96,130,18] 13 (by decide) (choices 1) [1,8,32,128] r8327 c8327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5150
  · exact u5151
  · exact u5152
  · exact u5153

def r8328 : Route 9 := (fun mask => (mask,id))

def c8328 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8328 : Upper (D 1) (R 1) [276,96,130,33] 13 := by
  apply FastRouting.sound _ _ [276,96,130,33] 13 (by decide) (choices 1) [2,8,64,128] r8328 c8328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5154
  · exact u5155
  · exact u5156
  · exact u5157

def b8329 : PairBound 9 := { available := 217, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 98 134 42 217 249 217 217 473), lower := (rows 277 98 134 42 16 32 64 128 256), losses := [] }

theorem u8329 : Upper (D 1) (R 1) [276,96,130,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8329
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8330 : Route 9 := (fun mask => (mask,id))

def c8330 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8330 : Upper (D 1) (R 1) [276,96,130,48] 13 := by
  apply FastRouting.sound _ _ [276,96,130,48] 13 (by decide) (choices 1) [1,2,8,64,128] r8330 c8330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5158
  · exact u5159
  · exact u5160
  · exact u5161
  · exact u5162

def b8331 : PairBound 9 := { available := 155, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 98 134 104 155 187 219 155 411), lower := (rows 277 98 134 104 16 32 64 128 256), losses := [] }

theorem u8331 : Upper (D 1) (R 1) [276,96,130,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8331
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8332 : PairBound 9 := { available := 122, camps := [{ cop := 3, region := 114, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 134 137 122 122 122 250 378), lower := (rows 277 98 134 137 16 32 64 128 256), losses := [] }

theorem u8332 : Upper (D 1) (R 1) [276,96,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8332
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8333 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 98 134 138 121 121 121 249 377), lower := (rows 277 98 134 138 16 32 64 128 256), losses := [] }

theorem u8333 : Upper (D 1) (R 1) [276,96,130,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8333
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8334 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8334 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8334 : Upper (D 1) (R 1) [276,96,130,144] 13 := by
  apply FastRouting.sound _ _ [276,96,130,144] 13 (by decide) (choices 1) [1,2,8,32] r8334 c8334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5163
  · exact u5164
  · exact u5165
  · exact u5166

def r8335 : Route 9 := (fun mask => (mask,id))

def c8335 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8335 : Upper (D 1) (R 1) [276,96,130,160] 13 := by
  apply FastRouting.sound _ _ [276,96,130,160] 13 (by decide) (choices 1) [1,2,8,64] r8335 c8335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5167
  · exact u5168
  · exact u5169
  · exact u5170

def r8336 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8336 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8336 : Upper (D 1) (R 1) [276,96,136,3] 13 := by
  apply FastRouting.sound _ _ [276,96,136,3] 13 (by decide) (choices 1) [2,32,128] r8336 c8336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5171
  · exact u5172
  · exact u5173

def b8337 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 140 25 242 226 226 226 482), lower := (rows 277 98 140 25 16 32 64 128 256), losses := [] }

theorem u8337 : Upper (D 1) (R 1) [276,96,136,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8337
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8338 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 140 26 243 227 227 227 483), lower := (rows 277 98 140 26 16 32 64 128 256), losses := [] }

theorem u8338 : Upper (D 1) (R 1) [276,96,136,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8338
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8339 : Route 9 := (fun mask => (mask,id))

def c8339 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8339 : Upper (D 1) (R 1) [276,96,136,33] 13 := by
  apply FastRouting.sound _ _ [276,96,136,33] 13 (by decide) (choices 1) [2,64,128] r8339 c8339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5174
  · exact u5175
  · exact u5176

#print axioms u8339
end Delivery.IrregularNine14.P01
