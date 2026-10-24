import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0010

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8040 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 140 328 146 48 66 129 257), lower := (rows 37 98 140 328 146 48 66 128 256), losses := [] }

theorem u8040 : Upper (D 7) (R 7) [36,96,136,320,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8040 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8041 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 90, targets := 128 }], pairs := [(1,7),(3,7),(4,7)], upper := (rows 37 98 196 25 26 288 65 130 386), lower := (rows 37 98 196 25 26 288 65 128 256), losses := [] }

theorem u8041 : Upper (D 7) (R 7) [36,96,192,17,10,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8041 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8042 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 90, targets := 128 }], pairs := [(1,7),(3,7),(4,7)], upper := (rows 37 98 196 25 26 288 66 129 385), lower := (rows 37 98 196 25 26 288 66 128 256), losses := [] }

theorem u8042 : Upper (D 7) (R 7) [36,96,192,17,10,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8042 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8043 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 98 196 25 26 288 192 131 259), lower := (rows 37 98 196 25 26 288 192 128 256), losses := [] }

theorem u8043 : Upper (D 7) (R 7) [36,96,192,17,10,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8043 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8044 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 196 25 146 40 65 386 258), lower := (rows 37 98 196 25 146 40 65 128 256), losses := [] }

theorem u8044 : Upper (D 7) (R 7) [36,96,192,17,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8044 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8045 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 389, targets := 2 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(2,1)], upper := (rows 37 98 196 25 146 40 66 385 257), lower := (rows 37 98 196 25 146 40 66 128 256), losses := [] }

theorem u8045 : Upper (D 7) (R 7) [36,96,192,17,130,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8045 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8046 : Route 9 := (fun mask => (mask,id))

def c8046 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8046 : Upper (D 7) (R 7) [36,96,192,17,130,8,256] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,130,8,256] 13 (by decide) (choices 1) [1,2] r8046 c8046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u626
  · exact u627

def r8047 : Route 9 := (fun mask => (mask,id))

def c8047 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8047 : Upper (D 7) (R 7) [36,96,192,17,130,256,1] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,130,256,1] 13 (by decide) (choices 1) [2,8] r8047 c8047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u628
  · exact u629

def b8048 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 68, targets := 33 },{ cop := 5, region := 66, targets := 1 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 37 98 196 25 146 288 66 137 265), lower := (rows 37 98 196 25 146 288 66 128 256), losses := [] }

theorem u8048 : Upper (D 7) (R 7) [36,96,192,17,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8048 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8049 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 98 196 25 146 288 72 131 259), lower := (rows 37 98 196 25 146 288 72 128 256), losses := [] }

theorem u8049 : Upper (D 7) (R 7) [36,96,192,17,130,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8049 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8050 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 6, region := 422, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 37 98 196 25 152 34 65 386 258), lower := (rows 37 98 196 25 152 34 65 128 256), losses := [] }

theorem u8050 : Upper (D 7) (R 7) [36,96,192,17,136,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8051 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 98 196 25 152 34 66 385 257), lower := (rows 37 98 196 25 152 34 66 128 256), losses := [] }

theorem u8051 : Upper (D 7) (R 7) [36,96,192,17,136,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8052 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 196 25 152 34 320 131 259), lower := (rows 37 98 196 25 152 34 320 128 256), losses := [] }

theorem u8052 : Upper (D 7) (R 7) [36,96,192,17,136,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8052 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8053 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 6, region := 290, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 196 25 152 288 65 130 258), lower := (rows 37 98 196 25 152 288 65 128 256), losses := [] }

theorem u8053 : Upper (D 7) (R 7) [36,96,192,17,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8053 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8054 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 196 25 152 288 66 131 259), lower := (rows 37 98 196 25 152 288 66 128 256), losses := [] }

theorem u8054 : Upper (D 7) (R 7) [36,96,192,17,136,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8054 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8055 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 196 25 274 40 65 130 386), lower := (rows 37 98 196 25 274 40 65 128 256), losses := [] }

theorem u8055 : Upper (D 7) (R 7) [36,96,192,17,258,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8055 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8056 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 133, targets := 2 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,1),(1,0),(2,1)], upper := (rows 37 98 196 25 274 40 66 129 385), lower := (rows 37 98 196 25 274 40 66 128 256), losses := [] }

theorem u8056 : Upper (D 7) (R 7) [36,96,192,17,258,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8056 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8057 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 98 196 25 274 40 192 131 259), lower := (rows 37 98 196 25 274 40 192 128 256), losses := [] }

theorem u8057 : Upper (D 7) (R 7) [36,96,192,17,258,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8057 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8058 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 6, region := 166, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 37 98 196 25 280 34 65 130 386), lower := (rows 37 98 196 25 280 34 65 128 256), losses := [] }

theorem u8058 : Upper (D 7) (R 7) [36,96,192,17,264,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8059 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 98 196 25 280 34 66 129 385), lower := (rows 37 98 196 25 280 34 66 128 256), losses := [] }

theorem u8059 : Upper (D 7) (R 7) [36,96,192,17,264,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8060 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 98 196 25 280 34 192 131 259), lower := (rows 37 98 196 25 280 34 192 128 256), losses := [] }

theorem u8060 : Upper (D 7) (R 7) [36,96,192,17,264,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8061 : Route 9 := (fun mask => (mask,id))

def c8061 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8061 : Upper (D 7) (R 7) [36,96,192,17,384,2,1] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,384,2,1] 13 (by decide) (choices 1) [2,8] r8061 c8061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u630
  · exact u631

def b8062 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 408, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 98 196 25 400 34 66 137 265), lower := (rows 37 98 196 25 400 34 66 128 256), losses := [] }

theorem u8062 : Upper (D 7) (R 7) [36,96,192,17,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8063 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 196 25 400 34 72 131 259), lower := (rows 37 98 196 25 400 34 72 128 256), losses := [] }

theorem u8063 : Upper (D 7) (R 7) [36,96,192,17,384,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8063 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8064 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 196 25 400 40 65 130 258), lower := (rows 37 98 196 25 400 40 65 128 256), losses := [] }

theorem u8064 : Upper (D 7) (R 7) [36,96,192,17,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8064 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8065 : Route 9 := (fun mask => (mask,id))

def c8065 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8065 : Upper (D 7) (R 7) [36,96,192,17,384,8,2] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17,384,8,2] 13 (by decide) (choices 1) [1,2] r8065 c8065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u632
  · exact u633

def b8066 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 388, targets := 33 },{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7),(2,0),(2,5)], upper := (rows 37 98 196 26 145 40 65 386 258), lower := (rows 37 98 196 26 145 40 65 128 256), losses := [] }

theorem u8066 : Upper (D 7) (R 7) [36,96,192,18,129,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8066 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8067 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 400, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 37 98 196 26 145 40 66 385 257), lower := (rows 37 98 196 26 145 40 66 128 256), losses := [] }

theorem u8067 : Upper (D 7) (R 7) [36,96,192,18,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8067 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8068 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 37 98 196 26 145 40 320 131 259), lower := (rows 37 98 196 26 145 40 320 128 256), losses := [] }

theorem u8068 : Upper (D 7) (R 7) [36,96,192,18,129,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8068 [(5,3),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8069 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 68, targets := 34 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,1),(2,5)], upper := (rows 37 98 196 26 145 288 65 138 266), lower := (rows 37 98 196 26 145 288 65 128 256), losses := [] }

theorem u8069 : Upper (D 7) (R 7) [36,96,192,18,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8069 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8070 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(3,7)], upper := (rows 37 98 196 26 145 288 66 137 265), lower := (rows 37 98 196 26 145 288 66 128 256), losses := [] }

theorem u8070 : Upper (D 7) (R 7) [36,96,192,18,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8070 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8071 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 98 196 26 145 288 72 131 259), lower := (rows 37 98 196 26 145 288 72 128 256), losses := [] }

theorem u8071 : Upper (D 7) (R 7) [36,96,192,18,129,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8071 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8072 : Route 9 := (fun mask => (mask,id))

def c8072 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8072 : Upper (D 7) (R 7) [36,96,192,18,136,256,1] 13 := by
  apply FastRouting.sound _ _ [36,96,192,18,136,256,1] 13 (by decide) (choices 1) [1,2] r8072 c8072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u634
  · exact u635

def b8073 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 133, targets := 2 },{ cop := 2, region := 289, targets := 128 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 98 196 26 152 288 66 129 257), lower := (rows 37 98 196 26 152 288 66 128 256), losses := [] }

theorem u8073 : Upper (D 7) (R 7) [36,96,192,18,136,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8073 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8074 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 34, targets := 1 },{ cop := 4, region := 106, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 37 98 196 26 273 34 65 136 392), lower := (rows 37 98 196 26 273 34 65 128 256), losses := [] }

theorem u8074 : Upper (D 7) (R 7) [36,96,192,18,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8075 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 196 26 273 34 72 129 385), lower := (rows 37 98 196 26 273 34 72 128 256), losses := [] }

theorem u8075 : Upper (D 7) (R 7) [36,96,192,18,257,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8075 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8076 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 98 196 26 273 34 192 137 265), lower := (rows 37 98 196 26 273 34 192 128 256), losses := [] }

theorem u8076 : Upper (D 7) (R 7) [36,96,192,18,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8077 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 132, targets := 33 },{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7),(2,0),(2,5)], upper := (rows 37 98 196 26 273 40 65 130 386), lower := (rows 37 98 196 26 273 40 65 128 256), losses := [] }

theorem u8077 : Upper (D 7) (R 7) [36,96,192,18,257,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8077 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8078 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 196 26 273 40 66 129 385), lower := (rows 37 98 196 26 273 40 66 128 256), losses := [] }

theorem u8078 : Upper (D 7) (R 7) [36,96,192,18,257,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8078 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8079 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 98 196 26 273 40 192 131 259), lower := (rows 37 98 196 26 273 40 192 128 256), losses := [] }

theorem u8079 : Upper (D 7) (R 7) [36,96,192,18,257,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8079 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8080 : Route 9 := (fun mask => (mask,id))

def c8080 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8080 : Upper (D 7) (R 7) [36,96,192,18,384,2,1] 13 := by
  apply FastRouting.sound _ _ [36,96,192,18,384,2,1] 13 (by decide) (choices 1) [1,8] r8080 c8080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u636
  · exact u637

def b8081 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 400, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 37 98 196 26 400 34 72 129 257), lower := (rows 37 98 196 26 400 34 72 128 256), losses := [] }

theorem u8081 : Upper (D 7) (R 7) [36,96,192,18,384,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8081 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8082 : Route 9 := (fun mask => (mask,id))

def c8082 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8082 : Upper (D 7) (R 7) [36,96,192,18,384,8,1] 13 := by
  apply FastRouting.sound _ _ [36,96,192,18,384,8,1] 13 (by decide) (choices 1) [1,2] r8082 c8082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u638
  · exact u639

def b8083 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 400, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 37 98 196 26 400 40 66 129 257), lower := (rows 37 98 196 26 400 40 66 128 256), losses := [] }

theorem u8083 : Upper (D 7) (R 7) [36,96,192,18,384,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8083 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8084 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 370, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 37 98 196 137 273 48 66 138 266), lower := (rows 37 98 196 137 273 48 66 128 256), losses := [] }

theorem u8084 : Upper (D 7) (R 7) [36,96,192,129,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8084 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8085 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 98 196 137 273 48 72 130 258), lower := (rows 37 98 196 137 273 48 72 128 256), losses := [] }

theorem u8085 : Upper (D 7) (R 7) [36,96,192,129,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8085 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8086 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 68, targets := 34 },{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(2,1),(2,5)], upper := (rows 37 98 196 137 274 48 65 138 266), lower := (rows 37 98 196 137 274 48 65 128 256), losses := [] }

theorem u8086 : Upper (D 7) (R 7) [36,96,192,129,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8086 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8087 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 196 137 274 48 66 137 265), lower := (rows 37 98 196 137 274 48 66 128 256), losses := [] }

theorem u8087 : Upper (D 7) (R 7) [36,96,192,129,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8087 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8088 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 98 196 137 274 48 72 131 259), lower := (rows 37 98 196 137 274 48 72 128 256), losses := [] }

theorem u8088 : Upper (D 7) (R 7) [36,96,192,129,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8088 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8089 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 132, targets := 33 },{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(2,0),(2,5)], upper := (rows 37 98 196 137 280 48 65 130 258), lower := (rows 37 98 196 137 280 48 65 128 256), losses := [] }

theorem u8089 : Upper (D 7) (R 7) [36,96,192,129,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8089 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8090 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 370, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 37 98 196 137 280 48 66 131 259), lower := (rows 37 98 196 137 280 48 66 128 256), losses := [] }

theorem u8090 : Upper (D 7) (R 7) [36,96,192,129,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8090 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8091 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 140, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 196 138 273 48 65 138 266), lower := (rows 37 98 196 138 273 48 65 128 256), losses := [] }

theorem u8091 : Upper (D 7) (R 7) [36,96,192,130,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8091 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8092 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 68, targets := 33 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 37 98 196 138 273 48 66 137 265), lower := (rows 37 98 196 138 273 48 66 128 256), losses := [] }

theorem u8092 : Upper (D 7) (R 7) [36,96,192,130,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8092 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8093 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 98 196 138 273 48 72 131 259), lower := (rows 37 98 196 138 273 48 72 128 256), losses := [] }

theorem u8093 : Upper (D 7) (R 7) [36,96,192,130,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8093 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8094 : Route 9 := (fun mask => (mask,id))

def c8094 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8094 : Upper (D 7) (R 7) [36,96,192,130,258,16,1] 13 := by
  apply FastRouting.sound _ _ [36,96,192,130,258,16,1] 13 (by decide) (choices 1) [1,8] r8094 c8094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u640
  · exact u641

def b8095 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 98 196 138 274 48 72 129 257), lower := (rows 37 98 196 138 274 48 72 128 256), losses := [] }

theorem u8095 : Upper (D 7) (R 7) [36,96,192,130,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8095 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8096 : Route 9 := (fun mask => (mask,id))

def c8096 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8096 : Upper (D 7) (R 7) [36,96,192,130,264,16,1] 13 := by
  apply FastRouting.sound _ _ [36,96,192,130,264,16,1] 13 (by decide) (choices 1) [1,2] r8096 c8096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u642
  · exact u643

def b8097 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 133, targets := 2 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(2,1)], upper := (rows 37 98 196 138 280 48 66 129 257), lower := (rows 37 98 196 138 280 48 66 128 256), losses := [] }

theorem u8097 : Upper (D 7) (R 7) [36,96,192,130,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8097 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8098 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,1)], upper := (rows 37 98 196 152 273 34 65 138 266), lower := (rows 37 98 196 152 273 34 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 32 81 128 256), good := (rows 101 96 196 220 337 32 65 128 256) }] }

theorem u8098 : Upper (D 7) (R 7) [36,96,192,144,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8099 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 408, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 98 196 152 273 34 66 137 265), lower := (rows 37 98 196 152 273 34 66 128 256), losses := [] }

theorem u8099 : Upper (D 7) (R 7) [36,96,192,144,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u8099
end Delivery.IrregularNine14.P07
