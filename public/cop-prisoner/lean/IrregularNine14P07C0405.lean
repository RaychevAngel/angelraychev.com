import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0132
import IrregularNine14P07C0133

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24300 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 98 140 73 145 48 322 386 258), lower := (rows 37 98 140 73 145 48 64 128 256), losses := [] }

theorem u24300 : Upper (D 7) (R 7) [36,96,136,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24300 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24301 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 4, region := 354, targets := 1 }], pairs := [(1,0),(1,7),(3,7)], upper := (rows 37 98 140 73 145 288 82 146 274), lower := (rows 37 98 140 73 145 288 64 128 256), losses := [] }

theorem u24301 : Upper (D 7) (R 7) [36,96,136,65,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24301 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24302 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 140 73 146 33 338 402 274), lower := (rows 37 98 140 73 146 33 64 128 256), losses := [] }

theorem u24302 : Upper (D 7) (R 7) [36,96,136,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24303 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 34, targets := 129 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 140 73 146 34 337 401 273), lower := (rows 37 98 140 73 146 34 64 128 256), losses := [{ target := 0, region := (rows 0 74 4 8 20 126 64 128 256), good := (rows 52 98 190 106 178 34 98 128 256) },{ target := 7, region := (rows 5 74 4 8 16 126 64 0 256), good := (rows 37 98 47 107 50 34 98 0 256) }] }

theorem u24303 : Upper (D 7) (R 7) [36,96,136,65,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24304 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,0),(1,7),(3,7)], upper := (rows 37 98 140 73 146 48 323 387 259), lower := (rows 37 98 140 73 146 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 20 53 64 128 256), good := (rows 52 98 190 106 178 48 64 128 256) }] }

theorem u24304 : Upper (D 7) (R 7) [36,96,136,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24304 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24305 : Route 9 := (fun mask => (mask,id))

def c24305 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24305 : Upper (D 7) (R 7) [36,96,136,65,130,256] 13 := by
  apply FastRouting.sound _ _ [36,96,136,65,130,256] 13 (by decide) (choices 1) [1,2,16] r24305 c24305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7978
  · exact u7979
  · exact u7980

def r24306 : Route 9 := (fun mask => (mask,id))

def c24306 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24306 : Upper (D 7) (R 7) [36,96,136,65,257,2] 13 := by
  apply FastRouting.sound _ _ [36,96,136,65,257,2] 13 (by decide) (choices 1) [2,16,128] r24306 c24306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7981
  · exact u7982
  · exact u7983

def r24307 : Route 9 := (fun mask => (mask,id))

def c24307 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24307 : Upper (D 7) (R 7) [36,96,136,65,257,16] 13 := by
  apply FastRouting.sound _ _ [36,96,136,65,257,16] 13 (by decide) (choices 1) [2,128] r24307 c24307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7984
  · exact u7985

def b24308 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 73 273 160 82 146 274), lower := (rows 37 98 140 73 273 160 64 128 256), losses := [] }

theorem u24308 : Upper (D 7) (R 7) [36,96,136,65,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24309 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 140 73 274 33 210 146 402), lower := (rows 37 98 140 73 274 33 64 128 256), losses := [] }

theorem u24309 : Upper (D 7) (R 7) [36,96,136,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24310 : Route 9 := (fun mask => (mask,id))

def c24310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24310 : Upper (D 7) (R 7) [36,96,136,65,258,2] 13 := by
  apply FastRouting.sound _ _ [36,96,136,65,258,2] 13 (by decide) (choices 1) [1,16,128] r24310 c24310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7986
  · exact u7987
  · exact u7988

def r24311 : Route 9 := (fun mask => (mask,id))

def c24311 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24311 : Upper (D 7) (R 7) [36,96,136,65,258,16] 13 := by
  apply FastRouting.sound _ _ [36,96,136,65,258,16] 13 (by decide) (choices 1) [1,2,128] r24311 c24311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7989
  · exact u7990
  · exact u7991

def b24312 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 73 274 160 83 147 275), lower := (rows 37 98 140 73 274 160 64 128 256), losses := [] }

theorem u24312 : Upper (D 7) (R 7) [36,96,136,65,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24313 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 140 73 400 33 82 146 274), lower := (rows 37 98 140 73 400 33 64 128 256), losses := [] }

theorem u24313 : Upper (D 7) (R 7) [36,96,136,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24314 : Route 9 := (fun mask => (mask,id))

def c24314 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24314 : Upper (D 7) (R 7) [36,96,136,65,384,2] 13 := by
  apply FastRouting.sound _ _ [36,96,136,65,384,2] 13 (by decide) (choices 1) [1,2,16] r24314 c24314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7992
  · exact u7993
  · exact u7994

def r24315 : Route 9 := (fun mask => (mask,id))

def c24315 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24315 : Upper (D 7) (R 7) [36,96,136,65,384,16] 13 := by
  apply FastRouting.sound _ _ [36,96,136,65,384,16] 13 (by decide) (choices 1) [1,2] r24315 c24315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7995
  · exact u7996

def b24316 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 98 140 88 145 33 322 386 258), lower := (rows 37 98 140 88 145 33 64 128 256), losses := [] }

theorem u24316 : Upper (D 7) (R 7) [36,96,136,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24317 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 34, targets := 1 },{ cop := 4, region := 362, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 37 98 140 88 145 34 323 387 259), lower := (rows 37 98 140 88 145 34 64 128 256), losses := [] }

theorem u24317 : Upper (D 7) (R 7) [36,96,136,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24318 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 362, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 98 140 88 145 288 67 131 259), lower := (rows 37 98 140 88 145 288 64 128 256), losses := [] }

theorem u24318 : Upper (D 7) (R 7) [36,96,136,80,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24318 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24319 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 140 88 146 33 323 387 259), lower := (rows 37 98 140 88 146 33 64 128 256), losses := [] }

theorem u24319 : Upper (D 7) (R 7) [36,96,136,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24320 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 140 88 146 34 321 385 257), lower := (rows 37 98 140 88 146 34 64 128 256), losses := [{ target := 0, region := (rows 0 74 4 8 20 126 64 128 256), good := (rows 52 98 190 122 178 34 98 128 256) }] }

theorem u24320 : Upper (D 7) (R 7) [36,96,136,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24321 : Route 9 := (fun mask => (mask,id))

def c24321 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24321 : Upper (D 7) (R 7) [36,96,136,80,130,256] 13 := by
  apply FastRouting.sound _ _ [36,96,136,80,130,256] 13 (by decide) (choices 1) [1,2] r24321 c24321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7997
  · exact u7998

def b24322 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 140 88 273 33 194 130 386), lower := (rows 37 98 140 88 273 33 64 128 256), losses := [] }

theorem u24322 : Upper (D 7) (R 7) [36,96,136,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24323 : Route 9 := (fun mask => (mask,id))

def c24323 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24323 : Upper (D 7) (R 7) [36,96,136,80,257,2] 13 := by
  apply FastRouting.sound _ _ [36,96,136,80,257,2] 13 (by decide) (choices 1) [1,2,128] r24323 c24323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7999
  · exact u8000
  · exact u8001

def b24324 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 88 273 160 67 131 259), lower := (rows 37 98 140 88 273 160 64 128 256), losses := [] }

theorem u24324 : Upper (D 7) (R 7) [36,96,136,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24325 : Route 9 := (fun mask => (mask,id))

def c24325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24325 : Upper (D 7) (R 7) [36,96,136,80,258,1] 13 := by
  apply FastRouting.sound _ _ [36,96,136,80,258,1] 13 (by decide) (choices 1) [1,2,128] r24325 c24325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8002
  · exact u8003
  · exact u8004

def b24326 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 98 140 88 274 34 193 129 385), lower := (rows 37 98 140 88 274 34 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 50 0 141 269), good := (rows 421 34 397 445 306 34 0 128 256) }] }

theorem u24326 : Upper (D 7) (R 7) [36,96,136,80,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24327 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 88 274 160 67 131 259), lower := (rows 37 98 140 88 274 160 64 128 256), losses := [] }

theorem u24327 : Upper (D 7) (R 7) [36,96,136,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24328 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 140 88 400 33 67 131 259), lower := (rows 37 98 140 88 400 33 64 128 256), losses := [] }

theorem u24328 : Upper (D 7) (R 7) [36,96,136,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24329 : Route 9 := (fun mask => (mask,id))

def c24329 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24329 : Upper (D 7) (R 7) [36,96,136,80,384,2] 13 := by
  apply FastRouting.sound _ _ [36,96,136,80,384,2] 13 (by decide) (choices 1) [1,2] r24329 c24329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8005
  · exact u8006

def b24330 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 98 140 265 19 34 208 208 464), lower := (rows 37 98 140 265 19 34 64 128 256), losses := [] }

theorem u24330 : Upper (D 7) (R 7) [36,96,136,257,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24331 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 0, region := 194, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 37 98 140 265 19 48 194 194 450), lower := (rows 37 98 140 265 19 48 64 128 256), losses := [] }

theorem u24331 : Upper (D 7) (R 7) [36,96,136,257,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24331 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24332 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 265 19 96 210 146 402), lower := (rows 37 98 140 265 19 96 64 128 256), losses := [] }

theorem u24332 : Upper (D 7) (R 7) [36,96,136,257,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24333 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 265 19 160 82 210 338), lower := (rows 37 98 140 265 19 160 64 128 256), losses := [] }

theorem u24333 : Upper (D 7) (R 7) [36,96,136,257,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24334 : Route 9 := (fun mask => (mask,id))

def c24334 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24334 : Upper (D 7) (R 7) [36,96,136,257,65,2] 13 := by
  apply FastRouting.sound _ _ [36,96,136,257,65,2] 13 (by decide) (choices 1) [2,16,128] r24334 c24334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8007
  · exact u8008
  · exact u8009

def b24335 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 140 265 81 48 194 130 386), lower := (rows 37 98 140 265 81 48 64 128 256), losses := [] }

theorem u24335 : Upper (D 7) (R 7) [36,96,136,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24335 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24336 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 265 81 160 82 146 274), lower := (rows 37 98 140 265 81 160 64 128 256), losses := [] }

theorem u24336 : Upper (D 7) (R 7) [36,96,136,257,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24337 : Route 9 := (fun mask => (mask,id))

def c24337 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24337 : Upper (D 7) (R 7) [36,96,136,257,129,2] 13 := by
  apply FastRouting.sound _ _ [36,96,136,257,129,2] 13 (by decide) (choices 1) [2,16] r24337 c24337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8010
  · exact u8011

def b24338 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 98 140 265 145 48 66 194 322), lower := (rows 37 98 140 265 145 48 64 128 256), losses := [] }

theorem u24338 : Upper (D 7) (R 7) [36,96,136,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24338 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24339 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 265 145 96 82 146 274), lower := (rows 37 98 140 265 145 96 64 128 256), losses := [] }

theorem u24339 : Upper (D 7) (R 7) [36,96,136,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24340 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 140 265 146 33 82 210 338), lower := (rows 37 98 140 265 146 33 64 128 256), losses := [] }

theorem u24340 : Upper (D 7) (R 7) [36,96,136,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24341 : Route 9 := (fun mask => (mask,id))

def c24341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24341 : Upper (D 7) (R 7) [36,96,136,257,130,2] 13 := by
  apply FastRouting.sound _ _ [36,96,136,257,130,2] 13 (by decide) (choices 1) [1,16] r24341 c24341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8012
  · exact u8013

def r24342 : Route 9 := (fun mask => (mask,id))

def c24342 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24342 : Upper (D 7) (R 7) [36,96,136,257,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,136,257,130,16] 13 (by decide) (choices 1) [1,2] r24342 c24342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8014
  · exact u8015

def b24343 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 265 146 96 83 147 275), lower := (rows 37 98 140 265 146 96 64 128 256), losses := [] }

theorem u24343 : Upper (D 7) (R 7) [36,96,136,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24344 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 140 265 208 33 82 146 274), lower := (rows 37 98 140 265 208 33 64 128 256), losses := [] }

theorem u24344 : Upper (D 7) (R 7) [36,96,136,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24345 : Route 9 := (fun mask => (mask,id))

def c24345 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24345 : Upper (D 7) (R 7) [36,96,136,257,192,2] 13 := by
  apply FastRouting.sound _ _ [36,96,136,257,192,2] 13 (by decide) (choices 1) [1,2,16] r24345 c24345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8016
  · exact u8017
  · exact u8018

def b24346 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 140 265 208 48 67 131 259), lower := (rows 37 98 140 265 208 48 64 128 256), losses := [] }

theorem u24346 : Upper (D 7) (R 7) [36,96,136,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24346 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24347 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 140 266 19 33 208 208 464), lower := (rows 37 98 140 266 19 33 64 128 256), losses := [] }

theorem u24347 : Upper (D 7) (R 7) [36,96,136,258,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24348 : Route 9 := (fun mask => (mask,id))

def c24348 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24348 : Upper (D 7) (R 7) [36,96,136,258,3,16] 13 := by
  apply FastRouting.sound _ _ [36,96,136,258,3,16] 13 (by decide) (choices 1) [1,128] r24348 c24348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8019
  · exact u8020

def b24349 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 266 19 96 209 145 401), lower := (rows 37 98 140 266 19 96 64 128 256), losses := [] }

theorem u24349 : Upper (D 7) (R 7) [36,96,136,258,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24350 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 266 19 160 81 209 337), lower := (rows 37 98 140 266 19 160 64 128 256), losses := [] }

theorem u24350 : Upper (D 7) (R 7) [36,96,136,258,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24351 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 34, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 140 266 81 33 210 146 402), lower := (rows 37 98 140 266 81 33 64 128 256), losses := [] }

theorem u24351 : Upper (D 7) (R 7) [36,96,136,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24352 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 37 98 140 266 81 34 209 145 401), lower := (rows 37 98 140 266 81 34 64 128 256), losses := [] }

theorem u24352 : Upper (D 7) (R 7) [36,96,136,258,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24353 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 140 266 81 48 195 131 387), lower := (rows 37 98 140 266 81 48 64 128 256), losses := [] }

theorem u24353 : Upper (D 7) (R 7) [36,96,136,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24353 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24354 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 140 266 81 160 83 147 275), lower := (rows 37 98 140 266 81 160 64 128 256), losses := [] }

theorem u24354 : Upper (D 7) (R 7) [36,96,136,258,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24355 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 98 140 266 145 33 82 210 338), lower := (rows 37 98 140 266 145 33 64 128 256), losses := [] }

theorem u24355 : Upper (D 7) (R 7) [36,96,136,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24356 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7),(4,1),(4,5)], upper := (rows 37 98 140 266 145 34 81 209 337), lower := (rows 37 98 140 266 145 34 64 128 256), losses := [] }

theorem u24356 : Upper (D 7) (R 7) [36,96,136,258,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24357 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 98 140 266 145 48 67 195 323), lower := (rows 37 98 140 266 145 48 64 128 256), losses := [] }

theorem u24357 : Upper (D 7) (R 7) [36,96,136,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24357 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24358 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 140 266 145 96 83 147 275), lower := (rows 37 98 140 266 145 96 64 128 256), losses := [] }

theorem u24358 : Upper (D 7) (R 7) [36,96,136,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24359 : Route 9 := (fun mask => (mask,id))

def c24359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24359 : Upper (D 7) (R 7) [36,96,136,258,130,1] 13 := by
  apply FastRouting.sound _ _ [36,96,136,258,130,1] 13 (by decide) (choices 1) [1,16] r24359 c24359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8021
  · exact u8022

#print axioms u24359
end Delivery.IrregularNine14.P07
