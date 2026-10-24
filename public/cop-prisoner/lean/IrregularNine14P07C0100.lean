import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0007

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6000 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 1 },{ cop := 0, region := 76, targets := 128 }], pairs := [(2,0),(2,7),(3,0)], upper := (rows 35 259 44 74 208 160 68 145 273), lower := (rows 35 259 44 74 208 160 68 128 256), losses := [] }

theorem u6000 : Upper (D 7) (R 7) [34,257,40,66,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6000 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6001 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 259 44 74 208 160 80 133 261), lower := (rows 35 259 44 74 208 160 80 128 256), losses := [] }

theorem u6001 : Upper (D 7) (R 7) [34,257,40,66,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6001 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6002 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 1 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,5)], upper := (rows 35 259 44 76 145 160 66 208 336), lower := (rows 35 259 44 76 145 160 66 128 256), losses := [] }

theorem u6002 : Upper (D 7) (R 7) [34,257,40,68,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6003 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 259 44 76 145 160 80 194 322), lower := (rows 35 259 44 76 145 160 80 128 256), losses := [] }

theorem u6003 : Upper (D 7) (R 7) [34,257,40,68,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6003 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6004 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 35 259 44 76 146 160 65 208 336), lower := (rows 35 259 44 76 146 160 65 128 256), losses := [] }

theorem u6004 : Upper (D 7) (R 7) [34,257,40,68,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6005 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 259 44 76 146 160 80 193 321), lower := (rows 35 259 44 76 146 160 80 128 256), losses := [] }

theorem u6005 : Upper (D 7) (R 7) [34,257,40,68,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6005 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6006 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7)], upper := (rows 35 259 69 74 148 48 72 160 416), lower := (rows 35 259 69 74 148 48 72 128 256), losses := [] }

theorem u6006 : Upper (D 7) (R 7) [34,257,65,66,132,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6006 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6007 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 259 69 74 148 48 96 136 392), lower := (rows 35 259 69 74 148 48 96 128 256), losses := [] }

theorem u6007 : Upper (D 7) (R 7) [34,257,65,66,132,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6007 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6008 : Route 9 := (fun mask => (mask,id))

def c6008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6008 : Upper (D 7) (R 7) [34,257,65,66,132,16,128] 13 := by
  apply FastRouting.sound _ _ [34,257,65,66,132,16,128] 13 (by decide) (choices 1) [8,32] r6008 c6008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u452
  · exact u453

def b6009 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 259 69 74 148 160 72 176 304), lower := (rows 35 259 69 74 148 160 72 128 256), losses := [] }

theorem u6009 : Upper (D 7) (R 7) [34,257,65,66,132,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6009 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6010 : Route 9 := (fun mask => (mask,id))

def c6010 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6010 : Upper (D 7) (R 7) [34,257,65,66,132,128,16] 13 := by
  apply FastRouting.sound _ _ [34,257,65,66,132,128,16] 13 (by decide) (choices 1) [8,32] r6010 c6010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u454
  · exact u455

def b6011 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 128 }], pairs := [(1,5),(2,7),(3,5),(4,5)], upper := (rows 35 259 69 74 148 160 96 152 280), lower := (rows 35 259 69 74 148 160 96 128 256), losses := [] }

theorem u6011 : Upper (D 7) (R 7) [34,257,65,66,132,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6012 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 68, targets := 160 }], pairs := [(2,5),(2,7)], upper := (rows 35 259 69 74 152 48 68 160 416), lower := (rows 35 259 69 74 152 48 68 128 256), losses := [] }

theorem u6012 : Upper (D 7) (R 7) [34,257,65,66,136,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6012 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6013 : PairBound 9 := { available := 132, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 259 69 74 152 48 96 132 388), lower := (rows 35 259 69 74 152 48 96 128 256), losses := [] }

theorem u6013 : Upper (D 7) (R 7) [34,257,65,66,136,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6013 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6014 : Route 9 := (fun mask => (mask,id))

def c6014 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6014 : Upper (D 7) (R 7) [34,257,65,66,136,16,128] 13 := by
  apply FastRouting.sound _ _ [34,257,65,66,136,16,128] 13 (by decide) (choices 1) [4,32] r6014 c6014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u456
  · exact u457

def b6015 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 259 69 74 152 160 68 176 304), lower := (rows 35 259 69 74 152 160 68 128 256), losses := [] }

theorem u6015 : Upper (D 7) (R 7) [34,257,65,66,136,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6015 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6016 : Route 9 := (fun mask => (mask,id))

def c6016 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6016 : Upper (D 7) (R 7) [34,257,65,66,136,128,16] 13 := by
  apply FastRouting.sound _ _ [34,257,65,66,136,128,16] 13 (by decide) (choices 1) [4,32] r6016 c6016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u458
  · exact u459

def b6017 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 128 }], pairs := [(1,5),(2,7),(3,5),(4,5)], upper := (rows 35 259 69 74 152 160 96 148 276), lower := (rows 35 259 69 74 152 160 96 128 256), losses := [] }

theorem u6017 : Upper (D 7) (R 7) [34,257,65,66,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6018 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 259 69 88 146 36 72 160 416), lower := (rows 35 259 69 88 146 36 72 128 256), losses := [] }

theorem u6018 : Upper (D 7) (R 7) [34,257,65,80,130,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6018 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6019 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 259 69 88 146 36 96 136 392), lower := (rows 35 259 69 88 146 36 96 128 256), losses := [] }

theorem u6019 : Upper (D 7) (R 7) [34,257,65,80,130,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6019 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6020 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 69 88 146 36 192 168 296), lower := (rows 35 259 69 88 146 36 192 128 256), losses := [] }

theorem u6020 : Upper (D 7) (R 7) [34,257,65,80,130,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6020 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6021 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 259 69 88 146 40 68 160 416), lower := (rows 35 259 69 88 146 40 68 128 256), losses := [] }

theorem u6021 : Upper (D 7) (R 7) [34,257,65,80,130,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6021 [(5,3),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6022 : PairBound 9 := { available := 132, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 259 69 88 146 40 96 132 388), lower := (rows 35 259 69 88 146 40 96 128 256), losses := [] }

theorem u6022 : Upper (D 7) (R 7) [34,257,65,80,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6022 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6023 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 69 88 146 40 192 164 292), lower := (rows 35 259 69 88 146 40 192 128 256), losses := [] }

theorem u6023 : Upper (D 7) (R 7) [34,257,65,80,130,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6023 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6024 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 35 259 69 88 146 160 68 168 296), lower := (rows 35 259 69 88 146 160 68 128 256), losses := [] }

theorem u6024 : Upper (D 7) (R 7) [34,257,65,80,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6024 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6025 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 259 69 88 146 160 72 164 292), lower := (rows 35 259 69 88 146 160 72 128 256), losses := [] }

theorem u6025 : Upper (D 7) (R 7) [34,257,65,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6025 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6026 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,5)], upper := (rows 35 259 69 88 146 160 96 140 268), lower := (rows 35 259 69 88 146 160 96 128 256), losses := [] }

theorem u6026 : Upper (D 7) (R 7) [34,257,65,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6026 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6027 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 69 88 148 160 66 168 296), lower := (rows 35 259 69 88 148 160 66 128 256), losses := [] }

theorem u6027 : Upper (D 7) (R 7) [34,257,65,80,132,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6028 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 259 69 88 148 160 72 162 290), lower := (rows 35 259 69 88 148 160 72 128 256), losses := [] }

theorem u6028 : Upper (D 7) (R 7) [34,257,65,80,132,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6028 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6029 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,5)], upper := (rows 35 259 69 88 148 160 96 138 266), lower := (rows 35 259 69 88 148 160 96 128 256), losses := [] }

theorem u6029 : Upper (D 7) (R 7) [34,257,65,80,132,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6030 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 259 69 88 176 36 66 136 392), lower := (rows 35 259 69 88 176 36 66 128 256), losses := [] }

theorem u6030 : Upper (D 7) (R 7) [34,257,65,80,160,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6030 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6031 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 259 69 88 176 36 72 130 386), lower := (rows 35 259 69 88 176 36 72 128 256), losses := [] }

theorem u6031 : Upper (D 7) (R 7) [34,257,65,80,160,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6031 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6032 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 69 88 176 36 192 138 266), lower := (rows 35 259 69 88 176 36 192 128 256), losses := [] }

theorem u6032 : Upper (D 7) (R 7) [34,257,65,80,160,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6032 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6033 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 259 69 104 146 160 68 152 280), lower := (rows 35 259 69 104 146 160 68 128 256), losses := [] }

theorem u6033 : Upper (D 7) (R 7) [34,257,65,96,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6033 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6034 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 259 69 104 146 160 72 148 276), lower := (rows 35 259 69 104 146 160 72 128 256), losses := [] }

theorem u6034 : Upper (D 7) (R 7) [34,257,65,96,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6034 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6035 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 69 104 146 160 80 140 268), lower := (rows 35 259 69 104 146 160 80 128 256), losses := [] }

theorem u6035 : Upper (D 7) (R 7) [34,257,65,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6035 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6036 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 69 104 148 160 66 152 280), lower := (rows 35 259 69 104 148 160 66 128 256), losses := [] }

theorem u6036 : Upper (D 7) (R 7) [34,257,65,96,132,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6037 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 259 69 104 148 160 72 146 274), lower := (rows 35 259 69 104 148 160 72 128 256), losses := [] }

theorem u6037 : Upper (D 7) (R 7) [34,257,65,96,132,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6037 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6038 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 69 104 148 160 80 138 266), lower := (rows 35 259 69 104 148 160 80 128 256), losses := [] }

theorem u6038 : Upper (D 7) (R 7) [34,257,65,96,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6038 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6039 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 69 104 152 160 66 148 276), lower := (rows 35 259 69 104 152 160 66 128 256), losses := [] }

theorem u6039 : Upper (D 7) (R 7) [34,257,65,96,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6040 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 259 69 104 152 160 68 146 274), lower := (rows 35 259 69 104 152 160 68 128 256), losses := [] }

theorem u6040 : Upper (D 7) (R 7) [34,257,65,96,136,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6040 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6041 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 259 69 104 152 160 80 134 262), lower := (rows 35 259 69 104 152 160 80 128 256), losses := [] }

theorem u6041 : Upper (D 7) (R 7) [34,257,65,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6041 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6042 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 176, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 259 69 138 148 48 72 224 352), lower := (rows 35 259 69 138 148 48 72 128 256), losses := [] }

theorem u6042 : Upper (D 7) (R 7) [34,257,65,130,132,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6042 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6043 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 259 69 138 148 48 96 200 328), lower := (rows 35 259 69 138 148 48 96 128 256), losses := [] }

theorem u6043 : Upper (D 7) (R 7) [34,257,65,130,132,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6043 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6044 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 176, targets := 3 },{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7),(4,0),(4,1)], upper := (rows 35 259 69 138 148 96 72 176 304), lower := (rows 35 259 69 138 148 96 72 128 256), losses := [] }

theorem u6044 : Upper (D 7) (R 7) [34,257,65,130,132,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6044 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6045 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 259 69 138 148 96 80 168 296), lower := (rows 35 259 69 138 148 96 80 128 256), losses := [] }

theorem u6045 : Upper (D 7) (R 7) [34,257,65,130,132,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6045 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6046 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 410, targets := 96 }], pairs := [(1,5),(1,6),(3,5),(3,6)], upper := (rows 35 259 69 138 148 96 96 152 280), lower := (rows 35 259 69 138 148 96 96 128 256), losses := [] }

theorem u6046 : Upper (D 7) (R 7) [34,257,65,130,132,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6047 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 259 69 138 176 36 72 208 336), lower := (rows 35 259 69 138 176 36 72 128 256), losses := [] }

theorem u6047 : Upper (D 7) (R 7) [34,257,65,130,160,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6047 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6048 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 259 69 138 176 36 80 200 328), lower := (rows 35 259 69 138 176 36 80 128 256), losses := [] }

theorem u6048 : Upper (D 7) (R 7) [34,257,65,130,160,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6048 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6049 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 259 69 138 176 96 68 152 280), lower := (rows 35 259 69 138 176 96 68 128 256), losses := [] }

theorem u6049 : Upper (D 7) (R 7) [34,257,65,130,160,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6049 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6050 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 176, targets := 3 },{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7),(4,0),(4,1)], upper := (rows 35 259 69 138 176 96 72 148 276), lower := (rows 35 259 69 138 176 96 72 128 256), losses := [] }

theorem u6050 : Upper (D 7) (R 7) [34,257,65,130,160,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6050 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6051 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 259 69 138 176 96 80 140 268), lower := (rows 35 259 69 138 176 96 80 128 256), losses := [] }

theorem u6051 : Upper (D 7) (R 7) [34,257,65,130,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6051 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6052 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 259 69 138 208 36 72 176 304), lower := (rows 35 259 69 138 208 36 72 128 256), losses := [] }

theorem u6052 : Upper (D 7) (R 7) [34,257,65,130,192,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6052 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6053 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 259 69 138 208 36 80 168 296), lower := (rows 35 259 69 138 208 36 80 128 256), losses := [] }

theorem u6053 : Upper (D 7) (R 7) [34,257,65,130,192,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6053 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6054 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 259 69 138 208 36 96 152 280), lower := (rows 35 259 69 138 208 36 96 128 256), losses := [] }

theorem u6054 : Upper (D 7) (R 7) [34,257,65,130,192,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6054 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6055 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 35 259 69 138 208 48 68 168 296), lower := (rows 35 259 69 138 208 48 68 128 256), losses := [] }

theorem u6055 : Upper (D 7) (R 7) [34,257,65,130,192,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6055 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6056 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 259 69 138 208 48 72 164 292), lower := (rows 35 259 69 138 208 48 72 128 256), losses := [] }

theorem u6056 : Upper (D 7) (R 7) [34,257,65,130,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6056 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6057 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 259 69 138 208 48 96 140 268), lower := (rows 35 259 69 138 208 48 96 128 256), losses := [] }

theorem u6057 : Upper (D 7) (R 7) [34,257,65,130,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6057 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6058 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 69 140 176 96 66 152 280), lower := (rows 35 259 69 140 176 96 66 128 256), losses := [] }

theorem u6058 : Upper (D 7) (R 7) [34,257,65,132,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6059 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 259 69 140 176 96 72 146 274), lower := (rows 35 259 69 140 176 96 72 128 256), losses := [] }

theorem u6059 : Upper (D 7) (R 7) [34,257,65,132,160,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6059 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u6059
end Delivery.IrregularNine14.P07
