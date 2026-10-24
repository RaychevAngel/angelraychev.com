import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0043
import IrregularNine14P09C0044

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6240 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 345, targets := 128 },{ cop := 0, region := 272, targets := 32 },{ cop := 4, region := 225, targets := 256 }], pairs := [(0,7),(0,8),(3,7),(4,5),(4,7)], upper := (rows 97 14 134 296 273 160 81 209 337), lower := (rows 97 14 134 296 273 160 64 128 256), losses := [] }

theorem u6240 : Upper (D 9) (R 9) [96,12,130,288,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6240 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6241 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 41, targets := 128 },{ cop := 0, region := 400, targets := 32 },{ cop := 4, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,5),(3,7),(4,5)], upper := (rows 97 14 134 296 336 33 209 145 401), lower := (rows 97 14 134 296 336 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 57 0 97 161 289), good := (rows 465 30 134 478 336 465 64 128 256) }] }

theorem u6241 : Upper (D 9) (R 9) [96,12,130,288,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6241 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6242 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 3, region := 193, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6)], upper := (rows 97 14 134 296 336 48 193 129 385), lower := (rows 97 14 134 296 336 48 64 128 256), losses := [] }

theorem u6242 : Upper (D 9) (R 9) [96,12,130,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6242 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6243 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 345, targets := 128 },{ cop := 0, region := 272, targets := 32 },{ cop := 4, region := 161, targets := 256 }], pairs := [(0,7),(0,8),(3,7),(4,5),(4,7)], upper := (rows 97 14 134 296 336 160 81 145 273), lower := (rows 97 14 134 296 336 160 64 128 256), losses := [] }

theorem u6243 : Upper (D 9) (R 9) [96,12,130,288,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6243 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6244 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 105, targets := 128 },{ cop := 0, region := 400, targets := 32 },{ cop := 4, region := 97, targets := 256 }], pairs := [(0,7),(0,8),(1,5),(3,7),(4,5)], upper := (rows 97 14 134 296 400 33 81 209 337), lower := (rows 97 14 134 296 400 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 57 0 97 161 289), good := (rows 465 30 134 478 400 465 64 128 256) }] }

theorem u6244 : Upper (D 9) (R 9) [96,12,130,288,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6244 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6245 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 46, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 14 134 296 400 48 65 193 321), lower := (rows 97 14 134 296 400 48 64 128 256), losses := [] }

theorem u6245 : Upper (D 9) (R 9) [96,12,130,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6245 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6246 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 134 296 400 96 81 145 273), lower := (rows 97 14 134 296 400 96 64 128 256), losses := [] }

theorem u6246 : Upper (D 9) (R 9) [96,12,130,288,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6246 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6247 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 0, region := 392, targets := 64 },{ cop := 4, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,5),(3,6),(4,7)], upper := (rows 97 14 148 168 82 33 321 385 257), lower := (rows 97 14 148 168 82 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 24 0 97 161 289), good := (rows 449 30 148 478 82 449 64 128 256) }] }

theorem u6247 : Upper (D 9) (R 9) [96,12,144,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6247 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6248 : Route 9 := (fun mask => (mask,id))

def c6248 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6248 : Upper (D 9) (R 9) [96,12,144,160,66,256] 13 := by
  apply FastRouting.sound _ _ [96,12,144,160,66,256] 13 (by decide) (choices 1) [1,256] r6248 c6248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2615
  · exact u2616

def b6249 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,6),(3,6),(4,7)], upper := (rows 97 14 148 168 273 33 322 450 322), lower := (rows 97 14 148 168 273 33 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 12 16 49 0 128 256), good := (rows 33 14 190 168 305 33 0 128 256) }] }

theorem u6249 : Upper (D 9) (R 9) [96,12,144,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6249 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6250 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 42, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(3,0)], upper := (rows 97 14 148 168 273 34 321 449 321), lower := (rows 97 14 148 168 273 34 64 128 256), losses := [] }

theorem u6250 : Upper (D 9) (R 9) [96,12,144,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6250 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6251 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 148 168 273 96 323 387 259), lower := (rows 97 14 148 168 273 96 64 128 256), losses := [] }

theorem u6251 : Upper (D 9) (R 9) [96,12,144,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6251 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6252 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(3,0),(4,7)], upper := (rows 97 14 148 168 273 288 67 195 323), lower := (rows 97 14 148 168 273 288 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 16 304 64 128 256), good := (rows 96 14 190 168 304 288 64 128 288) },{ target := 6, region := (rows 1 6 4 12 16 304 0 128 256), good := (rows 33 14 190 168 305 288 0 128 288) }] }

theorem u6252 : Upper (D 9) (R 9) [96,12,144,160,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6252 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6253 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,5),(2,5),(4,7)], upper := (rows 97 14 148 168 274 33 321 449 321), lower := (rows 97 14 148 168 274 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 24 0 97 161 289), good := (rows 449 30 148 478 274 449 64 128 256) }] }

theorem u6253 : Upper (D 9) (R 9) [96,12,144,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6253 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6254 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 148 168 274 96 321 385 257), lower := (rows 97 14 148 168 274 96 64 128 256), losses := [] }

theorem u6254 : Upper (D 9) (R 9) [96,12,144,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6254 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6255 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 5, region := 201, targets := 256 }], pairs := [(0,7),(0,8),(1,0),(3,8),(4,7)], upper := (rows 97 14 148 168 274 288 65 193 321), lower := (rows 97 14 148 168 274 288 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 16 304 64 128 256), good := (rows 96 14 190 168 306 288 64 128 288) }] }

theorem u6255 : Upper (D 9) (R 9) [96,12,144,160,258,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6255 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6256 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 4, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(3,8),(4,7)], upper := (rows 97 14 148 168 336 33 323 387 259), lower := (rows 97 14 148 168 336 33 64 128 256), losses := [{ target := 8, region := (rows 81 6 4 12 16 117 64 128 0), good := (rows 97 46 191 168 113 33 97 128 0) }] }

theorem u6256 : Upper (D 9) (R 9) [96,12,144,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6256 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6257 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 42, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(3,0)], upper := (rows 97 14 148 168 336 34 321 385 257), lower := (rows 97 14 148 168 336 34 64 128 256), losses := [] }

theorem u6257 : Upper (D 9) (R 9) [96,12,144,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6257 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6258 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,0),(1,6),(3,0),(4,7)], upper := (rows 97 14 148 168 336 288 67 131 259), lower := (rows 97 14 148 168 336 288 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 16 304 64 128 256), good := (rows 96 14 190 168 368 288 64 128 288) },{ target := 6, region := (rows 1 6 4 12 16 304 0 128 256), good := (rows 33 14 190 168 304 288 0 128 288) }] }

theorem u6258 : Upper (D 9) (R 9) [96,12,144,160,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6258 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6259 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 33, targets := 384 },{ cop := 0, region := 392, targets := 64 }], pairs := [(0,7),(0,8),(1,5),(2,5),(3,6)], upper := (rows 97 14 148 296 82 33 449 385 385), lower := (rows 97 14 148 296 82 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 24 0 97 161 289), good := (rows 449 30 148 478 82 449 64 128 256) }] }

theorem u6259 : Upper (D 9) (R 9) [96,12,144,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6259 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6260 : Route 9 := (fun mask => (mask,id))

def c6260 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6260 : Upper (D 9) (R 9) [96,12,144,288,66,128] 13 := by
  apply FastRouting.sound _ _ [96,12,144,288,66,128] 13 (by decide) (choices 1) [1,256] r6260 c6260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2617
  · exact u2618

def b6261 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 215, targets := 256 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 97 14 148 296 82 288 193 129 385), lower := (rows 97 14 148 296 82 288 64 128 256), losses := [] }

theorem u6261 : Upper (D 9) (R 9) [96,12,144,288,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6261 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6262 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 192 },{ cop := 6, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(1,6),(3,6),(3,7)], upper := (rows 97 14 148 296 273 33 194 194 450), lower := (rows 97 14 148 296 273 33 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 24 16 49 0 128 256), good := (rows 33 14 190 296 313 33 0 128 256) }] }

theorem u6262 : Upper (D 9) (R 9) [96,12,144,288,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6262 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6263 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 1, region := 225, targets := 256 },{ cop := 4, region := 196, targets := 256 }], pairs := [(0,8),(2,5),(2,8),(4,5)], upper := (rows 97 14 148 296 273 34 193 193 449), lower := (rows 97 14 148 296 273 34 64 128 256), losses := [] }

theorem u6263 : Upper (D 9) (R 9) [96,12,144,288,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6263 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6264 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 148 296 273 96 195 131 387), lower := (rows 97 14 148 296 273 96 64 128 256), losses := [] }

theorem u6264 : Upper (D 9) (R 9) [96,12,144,288,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6264 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6265 : Route 9 := (fun mask => (mask,id))

def c6265 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6265 : Upper (D 9) (R 9) [96,12,144,288,257,128] 13 := by
  apply FastRouting.sound _ _ [96,12,144,288,257,128] 13 (by decide) (choices 1) [1,2] r6265 c6265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2619
  · exact u2620

def b6266 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 229, targets := 256 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(1,5),(2,5),(2,8)], upper := (rows 97 14 148 296 274 33 193 193 449), lower := (rows 97 14 148 296 274 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 24 0 97 161 289), good := (rows 449 30 148 478 274 449 64 128 256) }] }

theorem u6266 : Upper (D 9) (R 9) [96,12,144,288,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6266 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6267 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 225, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 148 296 274 96 193 129 385), lower := (rows 97 14 148 296 274 96 64 128 256), losses := [] }

theorem u6267 : Upper (D 9) (R 9) [96,12,144,288,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6267 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6268 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 229, targets := 256 },{ cop := 5, region := 329, targets := 128 }], pairs := [(0,7),(0,8),(2,8),(3,7),(4,7)], upper := (rows 97 14 148 296 274 160 65 193 321), lower := (rows 97 14 148 296 274 160 64 128 256), losses := [{ target := 7, region := (rows 41 2 4 41 18 32 107 0 299), good := (rows 361 351 20 361 338 361 64 0 256) }] }

theorem u6268 : Upper (D 9) (R 9) [96,12,144,288,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6268 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6269 : Route 9 := (fun mask => (mask,id))

def c6269 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6269 : Upper (D 9) (R 9) [96,12,144,288,320,1] 13 := by
  apply FastRouting.sound _ _ [96,12,144,288,320,1] 13 (by decide) (choices 1) [1,2,128] r6269 c6269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2621
  · exact u2622
  · exact u2623

def b6270 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 392, targets := 64 },{ cop := 1, region := 225, targets := 256 }], pairs := [(0,8),(2,5),(3,6),(4,5)], upper := (rows 97 14 148 296 336 34 193 129 385), lower := (rows 97 14 148 296 336 34 64 128 256), losses := [] }

theorem u6270 : Upper (D 9) (R 9) [96,12,144,288,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6270 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6271 : Route 9 := (fun mask => (mask,id))

def c6271 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6271 : Upper (D 9) (R 9) [96,12,144,288,320,128] 13 := by
  apply FastRouting.sound _ _ [96,12,144,288,320,128] 13 (by decide) (choices 1) [1,2] r6271 c6271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2624
  · exact u2625

def b6272 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 0, region := 392, targets := 32 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,5),(3,5),(4,7)], upper := (rows 97 14 148 392 50 33 321 449 321), lower := (rows 97 14 148 392 50 33 64 128 256), losses := [{ target := 5, region := (rows 1 22 20 57 16 0 97 161 289), good := (rows 457 14 158 392 478 457 64 128 256) }] }

theorem u6272 : Upper (D 9) (R 9) [96,12,144,384,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6272 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6273 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 148 392 50 96 321 385 257), lower := (rows 97 14 148 392 50 96 64 128 256), losses := [] }

theorem u6273 : Upper (D 9) (R 9) [96,12,144,384,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6273 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6274 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 54, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6),(4,0)], upper := (rows 97 14 148 392 50 288 65 193 321), lower := (rows 97 14 148 392 50 288 64 128 256), losses := [] }

theorem u6274 : Upper (D 9) (R 9) [96,12,144,384,34,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6274 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6275 : Route 9 := (fun mask => (mask,id))

def c6275 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6275 : Upper (D 9) (R 9) [96,12,144,384,257,1] 13 := by
  apply FastRouting.sound _ _ [96,12,144,384,257,1] 13 (by decide) (choices 1) [2,32] r6275 c6275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2626
  · exact u2627

def b6276 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 1, region := 97, targets := 256 }], pairs := [(0,7),(0,8),(2,8),(4,7)], upper := (rows 97 14 148 392 273 34 97 225 353), lower := (rows 97 14 148 392 273 34 64 128 256), losses := [{ target := 8, region := (rows 35 2 20 8 16 34 99 163 0), good := (rows 225 239 148 136 213 227 64 128 0) }] }

theorem u6276 : Upper (D 9) (R 9) [96,12,144,384,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6276 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6277 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 148 392 273 96 99 163 291), lower := (rows 97 14 148 392 273 96 64 128 256), losses := [] }

theorem u6277 : Upper (D 9) (R 9) [96,12,144,384,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6277 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6278 : Route 9 := (fun mask => (mask,id))

def c6278 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6278 : Upper (D 9) (R 9) [96,12,144,384,288,1] 13 := by
  apply FastRouting.sound _ _ [96,12,144,384,288,1] 13 (by decide) (choices 1) [1,2] r6278 c6278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2628
  · exact u2629

def b6279 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 54, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 14 148 392 304 34 65 193 321), lower := (rows 97 14 148 392 304 34 64 128 256), losses := [] }

theorem u6279 : Upper (D 9) (R 9) [96,12,144,384,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6279 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6280 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 148 392 304 96 67 131 259), lower := (rows 97 14 148 392 304 96 64 128 256), losses := [] }

theorem u6280 : Upper (D 9) (R 9) [96,12,144,384,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6280 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6281 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,7)], upper := (rows 97 14 164 200 273 33 338 402 274), lower := (rows 97 14 164 200 273 33 64 128 256), losses := [] }

theorem u6281 : Upper (D 9) (R 9) [96,12,160,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6281 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6282 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 14 164 200 273 34 337 401 273), lower := (rows 97 14 164 200 273 34 64 128 256), losses := [] }

theorem u6282 : Upper (D 9) (R 9) [96,12,160,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6282 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6283_1 : Upper (D 9) (R 9) [96,12,160,192,257,16,1] 13 :=
  permutation_upper _ _ _ [96,12,160,192,257,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2630

theorem m6283_2 : Upper (D 9) (R 9) [96,12,160,192,257,16,2] 13 :=
  permutation_upper _ _ _ [96,12,160,192,257,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2632

def r6283 : Route 9 := (fun mask => (mask,id))

def c6283 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6283 : Upper (D 9) (R 9) [96,12,160,192,257,16] 13 := by
  apply FastRouting.sound _ _ [96,12,160,192,257,16] 13 (by decide) (choices 1) [1,2,256] r6283 c6283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6283_1
  · exact m6283_2
  · exact u2634

theorem m6284_1 : Upper (D 9) (R 9) [96,12,160,192,257,256,1] 13 :=
  permutation_upper _ _ _ [96,12,160,192,257,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2631

theorem m6284_2 : Upper (D 9) (R 9) [96,12,160,192,257,256,2] 13 :=
  permutation_upper _ _ _ [96,12,160,192,257,2,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2633

theorem m6284_16 : Upper (D 9) (R 9) [96,12,160,192,257,256,16] 13 :=
  permutation_upper _ _ _ [96,12,160,192,257,16,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2634

def r6284 : Route 9 := (fun mask => (mask,id))

def c6284 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6284 : Upper (D 9) (R 9) [96,12,160,192,257,256] 13 := by
  apply FastRouting.sound _ _ [96,12,160,192,257,256] 13 (by decide) (choices 1) [1,2,16] r6284 c6284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6284_1
  · exact m6284_2
  · exact m6284_16

def b6285 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,7)], upper := (rows 97 14 164 200 274 33 337 401 273), lower := (rows 97 14 164 200 274 33 64 128 256), losses := [] }

theorem u6285 : Upper (D 9) (R 9) [96,12,160,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6285 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6286 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 0, region := 392, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(0,7),(2,6),(3,5),(4,7)], upper := (rows 97 14 164 200 274 48 321 385 257), lower := (rows 97 14 164 200 274 48 64 128 256), losses := [] }

theorem u6286 : Upper (D 9) (R 9) [96,12,160,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6286 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6287_1 : Upper (D 9) (R 9) [96,12,160,192,258,256,1] 13 :=
  permutation_upper _ _ _ [96,12,160,192,258,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2635

theorem m6287_16 : Upper (D 9) (R 9) [96,12,160,192,258,256,16] 13 :=
  permutation_upper _ _ _ [96,12,160,192,258,16,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2636

def r6287 : Route 9 := (fun mask => (mask,id))

def c6287 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6287 : Upper (D 9) (R 9) [96,12,160,192,258,256] 13 := by
  apply FastRouting.sound _ _ [96,12,160,192,258,256] 13 (by decide) (choices 1) [1,16] r6287 c6287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m6287_1
  · exact m6287_16

def r6288 : Route 9 := (fun mask => (mask,id))

def c6288 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6288 : Upper (D 9) (R 9) [96,12,160,320,129,1] 13 := by
  apply FastRouting.sound _ _ [96,12,160,320,129,1] 13 (by decide) (choices 1) [2,16,256] r6288 c6288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2637
  · exact u2638
  · exact u2639

def b6289 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 97 14 164 328 145 34 337 401 273), lower := (rows 97 14 164 328 145 34 64 128 256), losses := [] }

theorem u6289 : Upper (D 9) (R 9) [96,12,160,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6289 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6290 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 97 14 164 328 145 48 323 387 259), lower := (rows 97 14 164 328 145 48 64 128 256), losses := [] }

theorem u6290 : Upper (D 9) (R 9) [96,12,160,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6290 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6291 : Route 9 := (fun mask => (mask,id))

def c6291 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6291 : Upper (D 9) (R 9) [96,12,160,320,129,256] 13 := by
  apply FastRouting.sound _ _ [96,12,160,320,129,256] 13 (by decide) (choices 1) [1,2,16] r6291 c6291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2640
  · exact u2641
  · exact u2642

def r6292 : Route 9 := (fun mask => (mask,id))

def c6292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6292 : Upper (D 9) (R 9) [96,12,160,320,130,1] 13 := by
  apply FastRouting.sound _ _ [96,12,160,320,130,1] 13 (by decide) (choices 1) [1,16,256] r6292 c6292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2643
  · exact u2644
  · exact u2645

def b6293 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 97 14 164 328 146 48 321 385 257), lower := (rows 97 14 164 328 146 48 64 128 256), losses := [] }

theorem u6293 : Upper (D 9) (R 9) [96,12,160,320,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6293 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6294 : Route 9 := (fun mask => (mask,id))

def c6294 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6294 : Upper (D 9) (R 9) [96,12,160,320,130,256] 13 := by
  apply FastRouting.sound _ _ [96,12,160,320,130,256] 13 (by decide) (choices 1) [1,16] r6294 c6294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2646
  · exact u2647

def r6295 : Route 9 := (fun mask => (mask,id))

def c6295 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6295 : Upper (D 9) (R 9) [96,12,160,320,384,1] 13 := by
  apply FastRouting.sound _ _ [96,12,160,320,384,1] 13 (by decide) (choices 1) [1,2,16] r6295 c6295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2648
  · exact u2649
  · exact u2650

def b6296 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 97 14 164 328 400 34 81 145 273), lower := (rows 97 14 164 328 400 34 64 128 256), losses := [] }

theorem u6296 : Upper (D 9) (R 9) [96,12,160,320,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6296 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6297 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 97 14 164 328 400 48 67 131 259), lower := (rows 97 14 164 328 400 48 64 128 256), losses := [] }

theorem u6297 : Upper (D 9) (R 9) [96,12,160,320,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6297 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6298 : Route 9 := (fun mask => (mask,id))

def c6298 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u6298 : Upper (D 9) (R 9) [96,12,160,384,66,1] 13 := by
  apply FastRouting.sound _ _ [96,12,160,384,66,1] 13 (by decide) (choices 1) [1,16,256] r6298 c6298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2651
  · exact u2652
  · exact u2653

def b6299 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 14 164 392 82 48 321 385 257), lower := (rows 97 14 164 392 82 48 64 128 256), losses := [] }

theorem u6299 : Upper (D 9) (R 9) [96,12,160,384,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6299 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u6299
end Delivery.IrregularNine14.P09
