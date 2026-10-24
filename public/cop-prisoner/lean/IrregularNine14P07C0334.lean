import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0091
import IrregularNine14P07C0092

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20040 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 35 70 292 137 146 40 81 209 337), lower := (rows 35 70 292 137 146 40 64 128 256), losses := [] }

theorem u20040 : Upper (D 7) (R 7) [34,68,288,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20040 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20041 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 35 70 292 137 146 48 73 201 329), lower := (rows 35 70 292 137 146 48 64 128 256), losses := [] }

theorem u20041 : Upper (D 7) (R 7) [34,68,288,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20041 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20042 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 152, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 292 137 146 96 89 153 281), lower := (rows 35 70 292 137 146 96 64 128 256), losses := [] }

theorem u20042 : Upper (D 7) (R 7) [34,68,288,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20043 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 292 137 208 33 90 154 282), lower := (rows 35 70 292 137 208 33 64 128 256), losses := [] }

theorem u20043 : Upper (D 7) (R 7) [34,68,288,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20043 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20044 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 292 137 208 34 89 153 281), lower := (rows 35 70 292 137 208 34 64 128 256), losses := [] }

theorem u20044 : Upper (D 7) (R 7) [34,68,288,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20045 : Route 9 := (fun mask => (mask,id))

def c20045 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20045 : Upper (D 7) (R 7) [34,68,288,129,192,8] 13 := by
  apply FastRouting.sound _ _ [34,68,288,129,192,8] 13 (by decide) (choices 1) [1,2,16] r20045 c20045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5518
  · exact u5519
  · exact u5520

def b20046 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 292 137 208 48 75 139 267), lower := (rows 35 70 292 137 208 48 64 128 256), losses := [] }

theorem u20046 : Upper (D 7) (R 7) [34,68,288,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20046 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20047 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 292 138 208 33 89 153 281), lower := (rows 35 70 292 138 208 33 64 128 256), losses := [] }

theorem u20047 : Upper (D 7) (R 7) [34,68,288,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20048 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 35 70 292 138 208 40 81 145 273), lower := (rows 35 70 292 138 208 40 64 128 256), losses := [] }

theorem u20048 : Upper (D 7) (R 7) [34,68,288,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20048 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20049 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 292 138 208 48 73 137 265), lower := (rows 35 70 292 138 208 48 64 128 256), losses := [] }

theorem u20049 : Upper (D 7) (R 7) [34,68,288,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20049 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20050 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 57, targets := 128 },{ cop := 0, region := 454, targets := 1 }], pairs := [(0,7),(1,0),(3,7),(4,7)], upper := (rows 35 70 388 25 88 33 226 162 418), lower := (rows 35 70 388 25 88 33 64 128 256), losses := [] }

theorem u20050 : Upper (D 7) (R 7) [34,68,384,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20051 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 388 25 88 34 225 161 417), lower := (rows 35 70 388 25 88 34 64 128 256), losses := [] }

theorem u20051 : Upper (D 7) (R 7) [34,68,384,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20052 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 88, targets := 128 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,7)], upper := (rows 35 70 388 25 88 160 99 163 291), lower := (rows 35 70 388 25 88 160 64 128 256), losses := [] }

theorem u20052 : Upper (D 7) (R 7) [34,68,384,17,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20053 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 388 25 112 33 202 138 394), lower := (rows 35 70 388 25 112 33 64 128 256), losses := [] }

theorem u20053 : Upper (D 7) (R 7) [34,68,384,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20054 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 388 25 112 34 201 137 393), lower := (rows 35 70 388 25 112 34 64 128 256), losses := [] }

theorem u20054 : Upper (D 7) (R 7) [34,68,384,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20055 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 57, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 70 388 25 112 40 195 131 387), lower := (rows 35 70 388 25 112 40 64 128 256), losses := [] }

theorem u20055 : Upper (D 7) (R 7) [34,68,384,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20055 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20056 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 88, targets := 128 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,7),(4,7)], upper := (rows 35 70 388 25 112 160 75 139 267), lower := (rows 35 70 388 25 112 160 64 128 256), losses := [] }

theorem u20056 : Upper (D 7) (R 7) [34,68,384,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20057 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 3, region := 484, targets := 2 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(0,7),(2,1),(3,6)], upper := (rows 35 70 388 25 146 33 104 232 360), lower := (rows 35 70 388 25 146 33 64 128 256), losses := [] }

theorem u20057 : Upper (D 7) (R 7) [34,68,384,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20058 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 4, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 70 388 25 146 40 97 225 353), lower := (rows 35 70 388 25 146 40 64 128 256), losses := [] }

theorem u20058 : Upper (D 7) (R 7) [34,68,384,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20058 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20059 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 388 25 146 96 105 169 297), lower := (rows 35 70 388 25 146 96 64 128 256), losses := [] }

theorem u20059 : Upper (D 7) (R 7) [34,68,384,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20060 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 35 70 388 25 152 33 98 226 354), lower := (rows 35 70 388 25 152 33 64 128 256), losses := [] }

theorem u20060 : Upper (D 7) (R 7) [34,68,384,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20061 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 388 25 152 34 97 225 353), lower := (rows 35 70 388 25 152 34 64 128 256), losses := [] }

theorem u20061 : Upper (D 7) (R 7) [34,68,384,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20062 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 388 25 152 96 99 163 291), lower := (rows 35 70 388 25 152 96 64 128 256), losses := [] }

theorem u20062 : Upper (D 7) (R 7) [34,68,384,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20063 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 388 25 176 33 74 202 330), lower := (rows 35 70 388 25 176 33 64 128 256), losses := [] }

theorem u20063 : Upper (D 7) (R 7) [34,68,384,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20064 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 388 25 176 34 73 201 329), lower := (rows 35 70 388 25 176 34 64 128 256), losses := [] }

theorem u20064 : Upper (D 7) (R 7) [34,68,384,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20065 : Route 9 := (fun mask => (mask,id))

def c20065 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20065 : Upper (D 7) (R 7) [34,68,384,17,160,8] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,160,8] 13 (by decide) (choices 1) [1,2] r20065 c20065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5521
  · exact u5522

def b20066 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 388 25 176 96 75 139 267), lower := (rows 35 70 388 25 176 96 64 128 256), losses := [] }

theorem u20066 : Upper (D 7) (R 7) [34,68,384,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20067 : Route 9 := (fun mask => (mask,id))

def c20067 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20067 : Upper (D 7) (R 7) [34,68,384,17,192,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,192,1] 13 (by decide) (choices 1) [2,8,32] r20067 c20067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5523
  · exact u5524
  · exact u5525

def b20068 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 388 25 208 34 105 169 297), lower := (rows 35 70 388 25 208 34 64 128 256), losses := [] }

theorem u20068 : Upper (D 7) (R 7) [34,68,384,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20069 : Route 9 := (fun mask => (mask,id))

def c20069 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20069 : Upper (D 7) (R 7) [34,68,384,17,192,8] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,192,8] 13 (by decide) (choices 1) [1,2,32] r20069 c20069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5526
  · exact u5527
  · exact u5528

def b20070 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 57, targets := 128 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(3,7),(4,7)], upper := (rows 35 70 388 26 81 33 232 168 424), lower := (rows 35 70 388 26 81 33 64 128 256), losses := [] }

theorem u20070 : Upper (D 7) (R 7) [34,68,384,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20071 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 57, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 70 388 26 81 40 225 161 417), lower := (rows 35 70 388 26 81 40 64 128 256), losses := [] }

theorem u20071 : Upper (D 7) (R 7) [34,68,384,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20071 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20072 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 88, targets := 128 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,7)], upper := (rows 35 70 388 26 81 160 105 169 297), lower := (rows 35 70 388 26 81 160 64 128 256), losses := [] }

theorem u20072 : Upper (D 7) (R 7) [34,68,384,18,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20073 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 57, targets := 128 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(3,7),(4,7)], upper := (rows 35 70 388 26 112 33 201 137 393), lower := (rows 35 70 388 26 112 33 64 128 256), losses := [] }

theorem u20073 : Upper (D 7) (R 7) [34,68,384,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20074 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 57, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 70 388 26 112 40 193 129 385), lower := (rows 35 70 388 26 112 40 64 128 256), losses := [] }

theorem u20074 : Upper (D 7) (R 7) [34,68,384,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20074 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20075 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 88, targets := 128 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,7)], upper := (rows 35 70 388 26 112 160 73 137 265), lower := (rows 35 70 388 26 112 160 64 128 256), losses := [] }

theorem u20075 : Upper (D 7) (R 7) [34,68,384,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20076 : Route 9 := (fun mask => (mask,id))

def c20076 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20076 : Upper (D 7) (R 7) [34,68,384,18,129,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,18,129,1] 13 (by decide) (choices 1) [8,32] r20076 c20076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5529
  · exact u5530

def b20077 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 70 388 26 145 40 97 225 353), lower := (rows 35 70 388 26 145 40 64 128 256), losses := [] }

theorem u20077 : Upper (D 7) (R 7) [34,68,384,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20077 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20078 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 388 26 145 96 105 169 297), lower := (rows 35 70 388 26 145 96 64 128 256), losses := [] }

theorem u20078 : Upper (D 7) (R 7) [34,68,384,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20079 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 452, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,1)], upper := (rows 35 70 388 26 152 33 97 225 353), lower := (rows 35 70 388 26 152 33 64 128 256), losses := [] }

theorem u20079 : Upper (D 7) (R 7) [34,68,384,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20080 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 388 26 152 96 97 161 289), lower := (rows 35 70 388 26 152 96 64 128 256), losses := [] }

theorem u20080 : Upper (D 7) (R 7) [34,68,384,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20081 : Route 9 := (fun mask => (mask,id))

def c20081 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20081 : Upper (D 7) (R 7) [34,68,384,18,160,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,18,160,1] 13 (by decide) (choices 1) [1,8] r20081 c20081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5531
  · exact u5532

def b20082 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 70 388 26 176 40 65 193 321), lower := (rows 35 70 388 26 176 40 64 128 256), losses := [] }

theorem u20082 : Upper (D 7) (R 7) [34,68,384,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20082 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20083 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 388 26 176 96 73 137 265), lower := (rows 35 70 388 26 176 96 64 128 256), losses := [] }

theorem u20083 : Upper (D 7) (R 7) [34,68,384,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20084 : Route 9 := (fun mask => (mask,id))

def c20084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20084 : Upper (D 7) (R 7) [34,68,384,18,192,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,18,192,1] 13 (by decide) (choices 1) [1,8,32] r20084 c20084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5533
  · exact u5534
  · exact u5535

def b20085 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 70 388 26 208 40 97 161 289), lower := (rows 35 70 388 26 208 40 64 128 256), losses := [] }

theorem u20085 : Upper (D 7) (R 7) [34,68,384,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20085 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20086 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 388 56 81 33 202 138 394), lower := (rows 35 70 388 56 81 33 64 128 256), losses := [] }

theorem u20086 : Upper (D 7) (R 7) [34,68,384,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20087 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 388 56 81 34 201 137 393), lower := (rows 35 70 388 56 81 34 64 128 256), losses := [] }

theorem u20087 : Upper (D 7) (R 7) [34,68,384,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20088 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 70 388 56 81 40 195 131 387), lower := (rows 35 70 388 56 81 40 64 128 256), losses := [] }

theorem u20088 : Upper (D 7) (R 7) [34,68,384,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20088 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20089 : Route 9 := (fun mask => (mask,id))

def c20089 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20089 : Upper (D 7) (R 7) [34,68,384,48,65,128] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,65,128] 13 (by decide) (choices 1) [1,2,8] r20089 c20089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5536
  · exact u5537
  · exact u5538

def b20090 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 388 56 145 33 74 202 330), lower := (rows 35 70 388 56 145 33 64 128 256), losses := [] }

theorem u20090 : Upper (D 7) (R 7) [34,68,384,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20091 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 388 56 145 34 73 201 329), lower := (rows 35 70 388 56 145 34 64 128 256), losses := [] }

theorem u20091 : Upper (D 7) (R 7) [34,68,384,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20092 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 70 388 56 145 40 67 195 323), lower := (rows 35 70 388 56 145 40 64 128 256), losses := [] }

theorem u20092 : Upper (D 7) (R 7) [34,68,384,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20092 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20093 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 388 56 145 96 75 139 267), lower := (rows 35 70 388 56 145 96 64 128 256), losses := [] }

theorem u20093 : Upper (D 7) (R 7) [34,68,384,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20094 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 4, region := 41, targets := 64 },{ cop := 4, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 388 56 146 33 73 201 329), lower := (rows 35 70 388 56 146 33 64 128 256), losses := [] }

theorem u20094 : Upper (D 7) (R 7) [34,68,384,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20095 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 388 56 146 40 65 193 321), lower := (rows 35 70 388 56 146 40 64 128 256), losses := [] }

theorem u20095 : Upper (D 7) (R 7) [34,68,384,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20095 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20096 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 388 56 146 96 73 137 265), lower := (rows 35 70 388 56 146 96 64 128 256), losses := [] }

theorem u20096 : Upper (D 7) (R 7) [34,68,384,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20097 : Route 9 := (fun mask => (mask,id))

def c20097 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20097 : Upper (D 7) (R 7) [34,68,384,48,192,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,192,1] 13 (by decide) (choices 1) [1,2,8] r20097 c20097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5539
  · exact u5540
  · exact u5541

def b20098 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 388 56 208 34 73 137 265), lower := (rows 35 70 388 56 208 34 64 128 256), losses := [] }

theorem u20098 : Upper (D 7) (R 7) [34,68,384,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20099 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 70 388 56 208 40 67 131 259), lower := (rows 35 70 388 56 208 40 64 128 256), losses := [] }

theorem u20099 : Upper (D 7) (R 7) [34,68,384,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20099 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u20099
end Delivery.IrregularNine14.P07
