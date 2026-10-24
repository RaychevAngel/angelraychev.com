import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0031

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r13380 : Route 9 := (fun mask => (mask,id))

def c13380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13380 : Upper (D 7) (R 7) [6,40,192,65,258,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,258,128] 13 (by decide) (choices 1) [1,16,32] r13380 c13380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1867
  · exact u1868
  · exact u1869

def b13381 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 1, region := 468, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 196 73 304 33 210 146 402), lower := (rows 7 42 196 73 304 33 64 128 256), losses := [] }

theorem u13381 : Upper (D 7) (R 7) [6,40,192,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13382 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 3, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(3,7)], upper := (rows 7 42 196 73 304 34 209 145 401), lower := (rows 7 42 196 73 304 34 64 128 256), losses := [] }

theorem u13382 : Upper (D 7) (R 7) [6,40,192,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13383 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 42 196 73 304 48 195 131 387), lower := (rows 7 42 196 73 304 48 64 128 256), losses := [] }

theorem u13383 : Upper (D 7) (R 7) [6,40,192,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13383 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13384 : Route 9 := (fun mask => (mask,id))

def c13384 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13384 : Upper (D 7) (R 7) [6,40,192,65,288,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,288,128] 13 (by decide) (choices 1) [1,2,16] r13384 c13384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1870
  · exact u1871
  · exact u1872

def b13385 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 1, region := 468, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 196 73 400 33 114 178 306), lower := (rows 7 42 196 73 400 33 64 128 256), losses := [] }

theorem u13385 : Upper (D 7) (R 7) [6,40,192,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13386 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 3, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(3,7)], upper := (rows 7 42 196 73 400 34 113 177 305), lower := (rows 7 42 196 73 400 34 64 128 256), losses := [] }

theorem u13386 : Upper (D 7) (R 7) [6,40,192,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13387 : Route 9 := (fun mask => (mask,id))

def c13387 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13387 : Upper (D 7) (R 7) [6,40,192,65,384,16] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,384,16] 13 (by decide) (choices 1) [1,2,32] r13387 c13387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1873
  · exact u1874
  · exact u1875

def b13388 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 0, region := 500, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(3,7)], upper := (rows 7 42 196 74 176 33 337 401 273), lower := (rows 7 42 196 74 176 33 64 128 256), losses := [] }

theorem u13388 : Upper (D 7) (R 7) [6,40,192,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13389 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 196 74 176 48 321 385 257), lower := (rows 7 42 196 74 176 48 64 128 256), losses := [] }

theorem u13389 : Upper (D 7) (R 7) [6,40,192,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13389 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13390 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 432, targets := 64 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 7 42 196 74 176 288 81 145 273), lower := (rows 7 42 196 74 176 288 64 128 256), losses := [] }

theorem u13390 : Upper (D 7) (R 7) [6,40,192,66,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13390 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13391 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 0, region := 500, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(3,7)], upper := (rows 7 42 196 74 273 33 240 176 432), lower := (rows 7 42 196 74 273 33 64 128 256), losses := [] }

theorem u13391 : Upper (D 7) (R 7) [6,40,192,66,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13392 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 432, targets := 64 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 7 42 196 74 273 48 225 161 417), lower := (rows 7 42 196 74 273 48 64 128 256), losses := [] }

theorem u13392 : Upper (D 7) (R 7) [6,40,192,66,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13392 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13393 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 2, region := 42, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 196 74 273 160 113 177 305), lower := (rows 7 42 196 74 273 160 64 128 256), losses := [] }

theorem u13393 : Upper (D 7) (R 7) [6,40,192,66,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13393 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13394 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 0, region := 500, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(3,7)], upper := (rows 7 42 196 74 304 33 209 145 401), lower := (rows 7 42 196 74 304 33 64 128 256), losses := [] }

theorem u13394 : Upper (D 7) (R 7) [6,40,192,66,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13395 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 42 196 74 304 48 193 129 385), lower := (rows 7 42 196 74 304 48 64 128 256), losses := [] }

theorem u13395 : Upper (D 7) (R 7) [6,40,192,66,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13395 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13396 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 2, region := 42, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 196 74 304 160 81 145 273), lower := (rows 7 42 196 74 304 160 64 128 256), losses := [] }

theorem u13396 : Upper (D 7) (R 7) [6,40,192,66,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13397 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 0, region := 500, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(3,7)], upper := (rows 7 42 196 74 400 33 113 177 305), lower := (rows 7 42 196 74 400 33 64 128 256), losses := [] }

theorem u13397 : Upper (D 7) (R 7) [6,40,192,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13398 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 432, targets := 64 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 7 42 196 74 400 48 97 161 289), lower := (rows 7 42 196 74 400 48 64 128 256), losses := [] }

theorem u13398 : Upper (D 7) (R 7) [6,40,192,66,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13398 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13399 : PairBound 9 := { available := 290, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 0, region := 432, targets := 64 },{ cop := 1, region := 452, targets := 1 }], pairs := [(1,7),(2,0),(3,7),(4,6)], upper := (rows 7 42 196 88 145 33 354 418 290), lower := (rows 7 42 196 88 145 33 64 128 256), losses := [] }

theorem u13399 : Upper (D 7) (R 7) [6,40,192,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13399 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13400 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 7 42 196 88 145 34 353 417 289), lower := (rows 7 42 196 88 145 34 64 128 256), losses := [] }

theorem u13400 : Upper (D 7) (R 7) [6,40,192,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13401 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,7),(3,7),(4,6)], upper := (rows 7 42 196 88 145 288 99 163 291), lower := (rows 7 42 196 88 145 288 64 128 256), losses := [] }

theorem u13401 : Upper (D 7) (R 7) [6,40,192,80,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13401 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13402 : Route 9 := (fun mask => (mask,id))

def c13402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u13402 : Upper (D 7) (R 7) [6,40,192,80,130,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,130,1] 13 (by decide) (choices 1) [1,32,256] r13402 c13402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1876
  · exact u1877
  · exact u1878

def r13403 : Route 9 := (fun mask => (mask,id))

def c13403 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13403 : Upper (D 7) (R 7) [6,40,192,80,130,256] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,130,256] 13 (by decide) (choices 1) [1,32] r13403 c13403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1879
  · exact u1880

def r13404 : Route 9 := (fun mask => (mask,id))

def c13404 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u13404 : Upper (D 7) (R 7) [6,40,192,80,160,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,160,1] 13 (by decide) (choices 1) [1,2,256] r13404 c13404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1881
  · exact u1882
  · exact u1883

def b13405 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 58, targets := 1 },{ cop := 0, region := 452, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 196 88 176 34 321 385 257), lower := (rows 7 42 196 88 176 34 64 128 256), losses := [] }

theorem u13405 : Upper (D 7) (R 7) [6,40,192,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13406 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 0, region := 432, targets := 64 }], pairs := [(0,5),(2,5),(4,6)], upper := (rows 7 42 196 88 176 288 67 131 259), lower := (rows 7 42 196 88 176 288 64 128 256), losses := [] }

theorem u13406 : Upper (D 7) (R 7) [6,40,192,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13406 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13407 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,6),(1,7),(2,0),(4,6)], upper := (rows 7 42 196 88 273 33 226 162 418), lower := (rows 7 42 196 88 273 33 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 49 49 0 139 267), good := (rows 439 442 132 442 433 433 0 128 256) },{ target := 7, region := (rows 1 10 4 8 16 49 64 0 256), good := (rows 39 42 68 122 305 33 64 0 256) }] }

theorem u13407 : Upper (D 7) (R 7) [6,40,192,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13408 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 7 42 196 88 273 34 225 161 417), lower := (rows 7 42 196 88 273 34 64 128 256), losses := [] }

theorem u13408 : Upper (D 7) (R 7) [6,40,192,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13409 : Route 9 := (fun mask => (mask,id))

def c13409 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13409 : Upper (D 7) (R 7) [6,40,192,80,257,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,257,128] 13 (by decide) (choices 1) [1,2,32] r13409 c13409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1884
  · exact u1885
  · exact u1886

def r13410 : Route 9 := (fun mask => (mask,id))

def c13410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13410 : Upper (D 7) (R 7) [6,40,192,80,258,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,258,1] 13 (by decide) (choices 1) [1,32,128] r13410 c13410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1887
  · exact u1888
  · exact u1889

def r13411 : Route 9 := (fun mask => (mask,id))

def c13411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13411 : Upper (D 7) (R 7) [6,40,192,80,258,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,258,128] 13 (by decide) (choices 1) [1,32] r13411 c13411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1890
  · exact u1891

def r13412 : Route 9 := (fun mask => (mask,id))

def c13412 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13412 : Upper (D 7) (R 7) [6,40,192,80,288,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,288,1] 13 (by decide) (choices 1) [1,2,128] r13412 c13412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1892
  · exact u1893
  · exact u1894

def b13413 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 42 196 88 304 34 193 129 385), lower := (rows 7 42 196 88 304 34 64 128 256), losses := [] }

theorem u13413 : Upper (D 7) (R 7) [6,40,192,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13414 : Route 9 := (fun mask => (mask,id))

def c13414 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13414 : Upper (D 7) (R 7) [6,40,192,80,288,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,288,128] 13 (by decide) (choices 1) [1,2] r13414 c13414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1895
  · exact u1896

def r13415 : Route 9 := (fun mask => (mask,id))

def c13415 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13415 : Upper (D 7) (R 7) [6,40,192,80,384,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,384,1] 13 (by decide) (choices 1) [1,2,32] r13415 c13415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1897
  · exact u1898
  · exact u1899

def b13416 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 7 42 196 88 400 34 97 161 289), lower := (rows 7 42 196 88 400 34 64 128 256), losses := [] }

theorem u13416 : Upper (D 7) (R 7) [6,40,192,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13416 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13417 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 7 42 196 265 49 34 208 208 464), lower := (rows 7 42 196 265 49 34 64 128 256), losses := [] }

theorem u13417 : Upper (D 7) (R 7) [6,40,192,257,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13418 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6)], upper := (rows 7 42 196 265 49 48 194 194 450), lower := (rows 7 42 196 265 49 48 64 128 256), losses := [] }

theorem u13418 : Upper (D 7) (R 7) [6,40,192,257,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13418 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13419 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 394, targets := 64 }], pairs := [(1,6),(3,6),(4,1),(4,7)], upper := (rows 7 42 196 265 49 96 210 146 402), lower := (rows 7 42 196 265 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 100 64 128 256), good := (rows 53 40 228 281 49 96 96 128 256) },{ target := 7, region := (rows 1 2 4 8 17 100 64 0 256), good := (rows 55 42 100 281 49 96 96 0 256) }] }

theorem u13419 : Upper (D 7) (R 7) [6,40,192,257,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13420 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(3,6)], upper := (rows 7 42 196 265 81 34 240 176 432), lower := (rows 7 42 196 265 81 34 64 128 256), losses := [] }

theorem u13420 : Upper (D 7) (R 7) [6,40,192,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13421 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,6),(2,0),(3,6)], upper := (rows 7 42 196 265 81 48 226 162 418), lower := (rows 7 42 196 265 81 48 64 128 256), losses := [] }

theorem u13421 : Upper (D 7) (R 7) [6,40,192,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13421 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13422 : Route 9 := (fun mask => (mask,id))

def c13422 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13422 : Upper (D 7) (R 7) [6,40,192,257,65,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,65,128] 13 (by decide) (choices 1) [2,16,32] r13422 c13422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1900
  · exact u1901
  · exact u1902

def b13423 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 196 265 82 33 240 176 432), lower := (rows 7 42 196 265 82 33 64 128 256), losses := [] }

theorem u13423 : Upper (D 7) (R 7) [6,40,192,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13424 : Route 9 := (fun mask => (mask,id))

def c13424 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13424 : Upper (D 7) (R 7) [6,40,192,257,66,16] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,66,16] 13 (by decide) (choices 1) [1,32,128] r13424 c13424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1903
  · exact u1904
  · exact u1905

def r13425 : Route 9 := (fun mask => (mask,id))

def c13425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13425 : Upper (D 7) (R 7) [6,40,192,257,66,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,66,128] 13 (by decide) (choices 1) [1,16,32] r13425 c13425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1906
  · exact u1907
  · exact u1908

def b13426 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 196 265 112 33 210 146 402), lower := (rows 7 42 196 265 112 33 64 128 256), losses := [] }

theorem u13426 : Upper (D 7) (R 7) [6,40,192,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13427 : Route 9 := (fun mask => (mask,id))

def c13427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13427 : Upper (D 7) (R 7) [6,40,192,257,96,2] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,96,2] 13 (by decide) (choices 1) [1,16,128] r13427 c13427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1909
  · exact u1910
  · exact u1911

def b13428 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 196 265 112 48 195 131 387), lower := (rows 7 42 196 265 112 48 64 128 256), losses := [] }

theorem u13428 : Upper (D 7) (R 7) [6,40,192,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13428 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13429 : Route 9 := (fun mask => (mask,id))

def c13429 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13429 : Upper (D 7) (R 7) [6,40,192,257,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,96,128] 13 (by decide) (choices 1) [1,2,16] r13429 c13429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1912
  · exact u1913
  · exact u1914

def b13430 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 1 },{ cop := 0, region := 244, targets := 2 }], pairs := [(1,0),(2,0),(2,1),(3,0)], upper := (rows 7 42 196 266 49 33 208 208 464), lower := (rows 7 42 196 266 49 33 64 128 256), losses := [] }

theorem u13430 : Upper (D 7) (R 7) [6,40,192,258,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13431 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 196 266 49 48 193 193 449), lower := (rows 7 42 196 266 49 48 64 128 256), losses := [] }

theorem u13431 : Upper (D 7) (R 7) [6,40,192,258,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13431 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13432 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 394, targets := 64 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 42 196 266 49 96 209 145 401), lower := (rows 7 42 196 266 49 96 64 128 256), losses := [] }

theorem u13432 : Upper (D 7) (R 7) [6,40,192,258,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13433 : Route 9 := (fun mask => (mask,id))

def c13433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13433 : Upper (D 7) (R 7) [6,40,192,258,96,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258,96,1] 13 (by decide) (choices 1) [1,16,128] r13433 c13433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1915
  · exact u1916
  · exact u1917

def b13434 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 196 266 112 48 193 129 385), lower := (rows 7 42 196 266 112 48 64 128 256), losses := [] }

theorem u13434 : Upper (D 7) (R 7) [6,40,192,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13434 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13435 : Route 9 := (fun mask => (mask,id))

def c13435 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13435 : Upper (D 7) (R 7) [6,40,192,258,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258,96,128] 13 (by decide) (choices 1) [1,16] r13435 c13435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1918
  · exact u1919

def b13436 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 },{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0),(4,1),(4,6),(4,7)], upper := (rows 7 42 196 280 49 33 194 194 450), lower := (rows 7 42 196 280 49 33 64 128 256), losses := [] }

theorem u13436 : Upper (D 7) (R 7) [6,40,192,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13437 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 7 42 196 280 49 34 193 193 449), lower := (rows 7 42 196 280 49 34 64 128 256), losses := [] }

theorem u13437 : Upper (D 7) (R 7) [6,40,192,272,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13438 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 4, region := 394, targets := 64 }], pairs := [(0,5),(1,6),(2,5),(3,6)], upper := (rows 7 42 196 280 49 96 195 131 387), lower := (rows 7 42 196 280 49 96 64 128 256), losses := [] }

theorem u13438 : Upper (D 7) (R 7) [6,40,192,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13439 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,6),(1,7),(2,0),(3,6)], upper := (rows 7 42 196 280 81 33 226 162 418), lower := (rows 7 42 196 280 81 33 64 128 256), losses := [{ target := 7, region := (rows 1 10 4 8 16 49 64 0 256), good := (rows 39 42 68 314 113 33 64 0 256) }] }

theorem u13439 : Upper (D 7) (R 7) [6,40,192,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u13439
end Delivery.IrregularNine14.P07
