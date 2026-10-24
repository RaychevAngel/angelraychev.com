import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0134
import IrregularNine14P07C0135

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r24420 : Route 9 := (fun mask => (mask,id))

def c24420 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u24420 : Upper (D 7) (R 7) [36,96,192,17,130,8] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,130,8] 13 (by decide) (choices 1) [1,2,256] r24420 c24420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8044
  · exact u8045
  · exact u8046

def r24421 : Route 9 := (fun mask => (mask,id))

def c24421 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24421 : Upper (D 7) (R 7) [36,96,192,17,130,256] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,130,256] 13 (by decide) (choices 1) [1,2,8] r24421 c24421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8047
  · exact u8048
  · exact u8049

def b24422 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 57, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 98 196 25 152 33 322 386 258), lower := (rows 37 98 196 25 152 33 64 128 256), losses := [] }

theorem u24422 : Upper (D 7) (R 7) [36,96,192,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24423 : Route 9 := (fun mask => (mask,id))

def c24423 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u24423 : Upper (D 7) (R 7) [36,96,192,17,136,2] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,136,2] 13 (by decide) (choices 1) [1,2,256] r24423 c24423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8050
  · exact u8051
  · exact u8052

def r24424 : Route 9 := (fun mask => (mask,id))

def c24424 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24424 : Upper (D 7) (R 7) [36,96,192,17,136,256] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,136,256] 13 (by decide) (choices 1) [1,2] r24424 c24424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8053
  · exact u8054

def b24425 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 196 25 274 33 202 138 394), lower := (rows 37 98 196 25 274 33 64 128 256), losses := [] }

theorem u24425 : Upper (D 7) (R 7) [36,96,192,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24426 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 3, region := 196, targets := 34 }], pairs := [(0,7),(1,7),(2,1),(2,5)], upper := (rows 37 98 196 25 274 34 201 137 393), lower := (rows 37 98 196 25 274 34 64 128 256), losses := [] }

theorem u24426 : Upper (D 7) (R 7) [36,96,192,17,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24427 : Route 9 := (fun mask => (mask,id))

def c24427 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24427 : Upper (D 7) (R 7) [36,96,192,17,258,8] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,258,8] 13 (by decide) (choices 1) [1,2,128] r24427 c24427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8055
  · exact u8056
  · exact u8057

def b24428 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 196 25 274 160 75 139 267), lower := (rows 37 98 196 25 274 160 64 128 256), losses := [] }

theorem u24428 : Upper (D 7) (R 7) [36,96,192,17,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24429 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 198, targets := 1 },{ cop := 2, region := 33, targets := 66 }], pairs := [(0,1),(0,6),(1,0),(2,0)], upper := (rows 37 98 196 25 280 33 194 130 386), lower := (rows 37 98 196 25 280 33 64 128 256), losses := [] }

theorem u24429 : Upper (D 7) (R 7) [36,96,192,17,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24430 : Route 9 := (fun mask => (mask,id))

def c24430 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24430 : Upper (D 7) (R 7) [36,96,192,17,264,2] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,264,2] 13 (by decide) (choices 1) [1,2,128] r24430 c24430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8058
  · exact u8059
  · exact u8060

def b24431 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 196 25 280 160 67 131 259), lower := (rows 37 98 196 25 280 160 64 128 256), losses := [] }

theorem u24431 : Upper (D 7) (R 7) [36,96,192,17,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24432 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 196 25 400 33 74 138 266), lower := (rows 37 98 196 25 400 33 64 128 256), losses := [] }

theorem u24432 : Upper (D 7) (R 7) [36,96,192,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24433 : Route 9 := (fun mask => (mask,id))

def c24433 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24433 : Upper (D 7) (R 7) [36,96,192,17,384,2] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,384,2] 13 (by decide) (choices 1) [1,2,8] r24433 c24433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8061
  · exact u8062
  · exact u8063

def r24434 : Route 9 := (fun mask => (mask,id))

def c24434 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24434 : Upper (D 7) (R 7) [36,96,192,17,384,8] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,384,8] 13 (by decide) (choices 1) [1,2] r24434 c24434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8064
  · exact u8065

def b24435 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 98 196 26 145 33 330 394 266), lower := (rows 37 98 196 26 145 33 64 128 256), losses := [] }

theorem u24435 : Upper (D 7) (R 7) [36,96,192,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24436 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 34, targets := 1 },{ cop := 4, region := 362, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 37 98 196 26 145 34 329 393 265), lower := (rows 37 98 196 26 145 34 64 128 256), losses := [] }

theorem u24436 : Upper (D 7) (R 7) [36,96,192,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24437 : Route 9 := (fun mask => (mask,id))

def c24437 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u24437 : Upper (D 7) (R 7) [36,96,192,18,129,8] 13 := by
  apply FastRouting.sound _ _ [36,96,192,18,129,8] 13 (by decide) (choices 1) [1,2,256] r24437 c24437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8066
  · exact u8067
  · exact u8068

def r24438 : Route 9 := (fun mask => (mask,id))

def c24438 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24438 : Upper (D 7) (R 7) [36,96,192,18,129,256] 13 := by
  apply FastRouting.sound _ _ [36,96,192,18,129,256] 13 (by decide) (choices 1) [1,2,8] r24438 c24438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8069
  · exact u8070
  · exact u8071

def b24439 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 196 26 152 33 323 387 259), lower := (rows 37 98 196 26 152 33 64 128 256), losses := [] }

theorem u24439 : Upper (D 7) (R 7) [36,96,192,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24440 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 58, targets := 1 },{ cop := 0, region := 452, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 37 98 196 26 152 34 321 385 257), lower := (rows 37 98 196 26 152 34 64 128 256), losses := [] }

theorem u24440 : Upper (D 7) (R 7) [36,96,192,18,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24441 : Route 9 := (fun mask => (mask,id))

def c24441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24441 : Upper (D 7) (R 7) [36,96,192,18,136,256] 13 := by
  apply FastRouting.sound _ _ [36,96,192,18,136,256] 13 (by decide) (choices 1) [1,2] r24441 c24441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8072
  · exact u8073

def b24442 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 196 26 273 33 202 138 394), lower := (rows 37 98 196 26 273 33 64 128 256), losses := [] }

theorem u24442 : Upper (D 7) (R 7) [36,96,192,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24443 : Route 9 := (fun mask => (mask,id))

def c24443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24443 : Upper (D 7) (R 7) [36,96,192,18,257,2] 13 := by
  apply FastRouting.sound _ _ [36,96,192,18,257,2] 13 (by decide) (choices 1) [1,8,128] r24443 c24443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8074
  · exact u8075
  · exact u8076

def r24444 : Route 9 := (fun mask => (mask,id))

def c24444 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24444 : Upper (D 7) (R 7) [36,96,192,18,257,8] 13 := by
  apply FastRouting.sound _ _ [36,96,192,18,257,8] 13 (by decide) (choices 1) [1,2,128] r24444 c24444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8077
  · exact u8078
  · exact u8079

def b24445 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 196 26 273 160 75 139 267), lower := (rows 37 98 196 26 273 160 64 128 256), losses := [] }

theorem u24445 : Upper (D 7) (R 7) [36,96,192,18,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24446 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 196 26 280 33 195 131 387), lower := (rows 37 98 196 26 280 33 64 128 256), losses := [] }

theorem u24446 : Upper (D 7) (R 7) [36,96,192,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24447 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(2,1),(2,5)], upper := (rows 37 98 196 26 280 34 193 129 385), lower := (rows 37 98 196 26 280 34 64 128 256), losses := [] }

theorem u24447 : Upper (D 7) (R 7) [36,96,192,18,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24448 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 196 26 280 160 67 131 259), lower := (rows 37 98 196 26 280 160 64 128 256), losses := [] }

theorem u24448 : Upper (D 7) (R 7) [36,96,192,18,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24449 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 196 26 400 33 75 139 267), lower := (rows 37 98 196 26 400 33 64 128 256), losses := [] }

theorem u24449 : Upper (D 7) (R 7) [36,96,192,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24450 : Route 9 := (fun mask => (mask,id))

def c24450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24450 : Upper (D 7) (R 7) [36,96,192,18,384,2] 13 := by
  apply FastRouting.sound _ _ [36,96,192,18,384,2] 13 (by decide) (choices 1) [1,8] r24450 c24450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8080
  · exact u8081

def r24451 : Route 9 := (fun mask => (mask,id))

def c24451 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24451 : Upper (D 7) (R 7) [36,96,192,18,384,8] 13 := by
  apply FastRouting.sound _ _ [36,96,192,18,384,8] 13 (by decide) (choices 1) [1,2] r24451 c24451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8082
  · exact u8083

def b24452 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 34, targets := 1 },{ cop := 3, region := 370, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 37 98 196 137 273 34 90 154 282), lower := (rows 37 98 196 137 273 34 64 128 256), losses := [] }

theorem u24452 : Upper (D 7) (R 7) [36,96,192,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24453 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 37 98 196 137 273 40 82 146 274), lower := (rows 37 98 196 137 273 40 64 128 256), losses := [] }

theorem u24453 : Upper (D 7) (R 7) [36,96,192,129,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24453 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24454 : Route 9 := (fun mask => (mask,id))

def c24454 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24454 : Upper (D 7) (R 7) [36,96,192,129,257,16] 13 := by
  apply FastRouting.sound _ _ [36,96,192,129,257,16] 13 (by decide) (choices 1) [2,8] r24454 c24454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8084
  · exact u8085

def b24455 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 98 196 137 274 33 90 154 282), lower := (rows 37 98 196 137 274 33 64 128 256), losses := [] }

theorem u24455 : Upper (D 7) (R 7) [36,96,192,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24456 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 34, targets := 1 },{ cop := 3, region := 370, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 37 98 196 137 274 34 89 153 281), lower := (rows 37 98 196 137 274 34 64 128 256), losses := [] }

theorem u24456 : Upper (D 7) (R 7) [36,96,192,129,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24457 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 37 98 196 137 274 40 83 147 275), lower := (rows 37 98 196 137 274 40 64 128 256), losses := [] }

theorem u24457 : Upper (D 7) (R 7) [36,96,192,129,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24457 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24458 : Route 9 := (fun mask => (mask,id))

def c24458 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24458 : Upper (D 7) (R 7) [36,96,192,129,258,16] 13 := by
  apply FastRouting.sound _ _ [36,96,192,129,258,16] 13 (by decide) (choices 1) [1,2,8] r24458 c24458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8086
  · exact u8087
  · exact u8088

def b24459 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 98 196 137 280 33 82 146 274), lower := (rows 37 98 196 137 280 33 64 128 256), losses := [] }

theorem u24459 : Upper (D 7) (R 7) [36,96,192,129,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24460 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 34, targets := 1 },{ cop := 3, region := 370, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 37 98 196 137 280 34 83 147 275), lower := (rows 37 98 196 137 280 34 64 128 256), losses := [] }

theorem u24460 : Upper (D 7) (R 7) [36,96,192,129,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24461 : Route 9 := (fun mask => (mask,id))

def c24461 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24461 : Upper (D 7) (R 7) [36,96,192,129,264,16] 13 := by
  apply FastRouting.sound _ _ [36,96,192,129,264,16] 13 (by decide) (choices 1) [1,2] r24461 c24461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8089
  · exact u8090

def b24462 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 196 138 273 33 90 154 282), lower := (rows 37 98 196 138 273 33 64 128 256), losses := [] }

theorem u24462 : Upper (D 7) (R 7) [36,96,192,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24463 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 42, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(3,0)], upper := (rows 37 98 196 138 273 34 89 153 281), lower := (rows 37 98 196 138 273 34 64 128 256), losses := [] }

theorem u24463 : Upper (D 7) (R 7) [36,96,192,130,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24464 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 42, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 37 98 196 138 273 40 83 147 275), lower := (rows 37 98 196 138 273 40 64 128 256), losses := [] }

theorem u24464 : Upper (D 7) (R 7) [36,96,192,130,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24464 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24465 : Route 9 := (fun mask => (mask,id))

def c24465 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24465 : Upper (D 7) (R 7) [36,96,192,130,257,16] 13 := by
  apply FastRouting.sound _ _ [36,96,192,130,257,16] 13 (by decide) (choices 1) [1,2,8] r24465 c24465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8091
  · exact u8092
  · exact u8093

def b24466 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 196 138 274 33 89 153 281), lower := (rows 37 98 196 138 274 33 64 128 256), losses := [] }

theorem u24466 : Upper (D 7) (R 7) [36,96,192,130,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24467 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 42, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 37 98 196 138 274 40 81 145 273), lower := (rows 37 98 196 138 274 40 64 128 256), losses := [] }

theorem u24467 : Upper (D 7) (R 7) [36,96,192,130,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24467 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24468 : Route 9 := (fun mask => (mask,id))

def c24468 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24468 : Upper (D 7) (R 7) [36,96,192,130,258,16] 13 := by
  apply FastRouting.sound _ _ [36,96,192,130,258,16] 13 (by decide) (choices 1) [1,8] r24468 c24468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8094
  · exact u8095

def b24469 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 196 138 280 33 83 147 275), lower := (rows 37 98 196 138 280 33 64 128 256), losses := [] }

theorem u24469 : Upper (D 7) (R 7) [36,96,192,130,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24470 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 42, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(3,0)], upper := (rows 37 98 196 138 280 34 81 145 273), lower := (rows 37 98 196 138 280 34 64 128 256), losses := [] }

theorem u24470 : Upper (D 7) (R 7) [36,96,192,130,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24471 : Route 9 := (fun mask => (mask,id))

def c24471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24471 : Upper (D 7) (R 7) [36,96,192,130,264,16] 13 := by
  apply FastRouting.sound _ _ [36,96,192,130,264,16] 13 (by decide) (choices 1) [1,2] r24471 c24471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8096
  · exact u8097

def b24472 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 196 152 273 33 74 138 266), lower := (rows 37 98 196 152 273 33 64 128 256), losses := [] }

theorem u24472 : Upper (D 7) (R 7) [36,96,192,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24473 : Route 9 := (fun mask => (mask,id))

def c24473 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24473 : Upper (D 7) (R 7) [36,96,192,144,257,2] 13 := by
  apply FastRouting.sound _ _ [36,96,192,144,257,2] 13 (by decide) (choices 1) [1,2,8] r24473 c24473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8098
  · exact u8099
  · exact u8100

def r24474 : Route 9 := (fun mask => (mask,id))

def c24474 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24474 : Upper (D 7) (R 7) [36,96,192,144,257,8] 13 := by
  apply FastRouting.sound _ _ [36,96,192,144,257,8] 13 (by decide) (choices 1) [1,2] r24474 c24474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8101
  · exact u8102

def b24475 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 196 152 274 33 75 139 267), lower := (rows 37 98 196 152 274 33 64 128 256), losses := [] }

theorem u24475 : Upper (D 7) (R 7) [36,96,192,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24476 : Route 9 := (fun mask => (mask,id))

def c24476 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24476 : Upper (D 7) (R 7) [36,96,192,144,258,2] 13 := by
  apply FastRouting.sound _ _ [36,96,192,144,258,2] 13 (by decide) (choices 1) [1,8] r24476 c24476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8103
  · exact u8104

def r24477 : Route 9 := (fun mask => (mask,id))

def c24477 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24477 : Upper (D 7) (R 7) [36,96,192,144,258,8] 13 := by
  apply FastRouting.sound _ _ [36,96,192,144,258,8] 13 (by decide) (choices 1) [1,2] r24477 c24477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8105
  · exact u8106

def b24478 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 196 152 280 33 67 131 259), lower := (rows 37 98 196 152 280 33 64 128 256), losses := [] }

theorem u24478 : Upper (D 7) (R 7) [36,96,192,144,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24479 : Route 9 := (fun mask => (mask,id))

def c24479 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24479 : Upper (D 7) (R 7) [36,96,192,144,264,2] 13 := by
  apply FastRouting.sound _ _ [36,96,192,144,264,2] 13 (by decide) (choices 1) [1,2] r24479 c24479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8107
  · exact u8108

#print axioms u24479
end Delivery.IrregularNine14.P07
