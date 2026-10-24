import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0092

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20100 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 388 73 145 34 120 184 312), lower := (rows 35 70 388 73 145 34 64 128 256), losses := [] }

theorem u20100 : Upper (D 7) (R 7) [34,68,384,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20101 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(2,6),(4,6)], upper := (rows 35 70 388 73 145 40 114 178 306), lower := (rows 35 70 388 73 145 40 64 128 256), losses := [] }

theorem u20101 : Upper (D 7) (R 7) [34,68,384,65,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20101 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20102 : Route 9 := (fun mask => (mask,id))

def c20102 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20102 : Upper (D 7) (R 7) [34,68,384,65,129,16] 13 := by
  apply FastRouting.sound _ _ [34,68,384,65,129,16] 13 (by decide) (choices 1) [2,8,32] r20102 c20102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5542
  · exact u5543
  · exact u5544

def r20103 : Route 9 := (fun mask => (mask,id))

def c20103 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20103 : Upper (D 7) (R 7) [34,68,384,65,130,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,65,130,1] 13 (by decide) (choices 1) [8,16,32] r20103 c20103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5545
  · exact u5546
  · exact u5547

def b20104 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(2,6),(4,6)], upper := (rows 35 70 388 73 146 40 113 177 305), lower := (rows 35 70 388 73 146 40 64 128 256), losses := [] }

theorem u20104 : Upper (D 7) (R 7) [34,68,384,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20104 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20105 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 35 70 388 73 146 48 105 169 297), lower := (rows 35 70 388 73 146 48 64 128 256), losses := [] }

theorem u20105 : Upper (D 7) (R 7) [34,68,384,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20105 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20106 : Route 9 := (fun mask => (mask,id))

def c20106 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20106 : Upper (D 7) (R 7) [34,68,384,65,136,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,65,136,1] 13 (by decide) (choices 1) [2,16,32] r20106 c20106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5548
  · exact u5549
  · exact u5550

def b20107 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 388 73 152 34 113 177 305), lower := (rows 35 70 388 73 152 34 64 128 256), losses := [] }

theorem u20107 : Upper (D 7) (R 7) [34,68,384,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20108 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 388, targets := 64 },{ cop := 0, region := 72, targets := 128 }], pairs := [(2,6),(3,7),(4,6)], upper := (rows 35 70 388 73 152 48 99 163 291), lower := (rows 35 70 388 73 152 48 64 128 256), losses := [{ target := 6, region := (rows 1 2 13 8 24 56 0 129 257), good := (rows 423 6 388 445 188 48 0 128 256) }] }

theorem u20108 : Upper (D 7) (R 7) [34,68,384,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20108 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20109 : Route 9 := (fun mask => (mask,id))

def c20109 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20109 : Upper (D 7) (R 7) [34,68,384,65,160,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,65,160,1] 13 (by decide) (choices 1) [2,8,16] r20109 c20109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5551
  · exact u5552
  · exact u5553

def b20110 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 388 73 176 34 89 153 281), lower := (rows 35 70 388 73 176 34 64 128 256), losses := [] }

theorem u20110 : Upper (D 7) (R 7) [34,68,384,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20111 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(2,6),(4,6)], upper := (rows 35 70 388 73 176 40 83 147 275), lower := (rows 35 70 388 73 176 40 64 128 256), losses := [] }

theorem u20111 : Upper (D 7) (R 7) [34,68,384,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20111 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20112 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 388 73 176 48 75 139 267), lower := (rows 35 70 388 73 176 48 64 128 256), losses := [] }

theorem u20112 : Upper (D 7) (R 7) [34,68,384,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20112 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20113 : Route 9 := (fun mask => (mask,id))

def c20113 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20113 : Upper (D 7) (R 7) [34,68,384,80,129,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80,129,1] 13 (by decide) (choices 1) [2,8,32] r20113 c20113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5554
  · exact u5555
  · exact u5556

def b20114 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 388 88 145 34 105 169 297), lower := (rows 35 70 388 88 145 34 64 128 256), losses := [] }

theorem u20114 : Upper (D 7) (R 7) [34,68,384,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20115 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,7),(4,6)], upper := (rows 35 70 388 88 145 40 99 163 291), lower := (rows 35 70 388 88 145 40 64 128 256), losses := [{ target := 7, region := (rows 1 2 4 24 16 56 65 0 257), good := (rows 355 70 260 120 377 40 64 0 256) }] }

theorem u20115 : Upper (D 7) (R 7) [34,68,384,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20115 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20116 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,7)], upper := (rows 35 70 388 88 146 33 105 169 297), lower := (rows 35 70 388 88 146 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 16 59 0 136 264), good := (rows 35 39 388 445 179 33 0 128 256) }] }

theorem u20116 : Upper (D 7) (R 7) [34,68,384,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20117 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(2,6),(4,6)], upper := (rows 35 70 388 88 146 40 97 161 289), lower := (rows 35 70 388 88 146 40 64 128 256), losses := [] }

theorem u20117 : Upper (D 7) (R 7) [34,68,384,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20117 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20118 : Route 9 := (fun mask => (mask,id))

def c20118 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20118 : Upper (D 7) (R 7) [34,68,384,80,160,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80,160,1] 13 (by decide) (choices 1) [1,2,8] r20118 c20118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5557
  · exact u5558
  · exact u5559

def b20119 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 388 88 176 34 73 137 265), lower := (rows 35 70 388 88 176 34 64 128 256), losses := [] }

theorem u20119 : Upper (D 7) (R 7) [34,68,384,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20120 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(1,5),(2,5),(2,6)], upper := (rows 35 70 388 88 176 40 67 131 259), lower := (rows 35 70 388 88 176 40 64 128 256), losses := [] }

theorem u20120 : Upper (D 7) (R 7) [34,68,384,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20120 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20121 : Route 9 := (fun mask => (mask,id))

def c20121 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20121 : Upper (D 7) (R 7) [34,68,384,96,129,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96,129,1] 13 (by decide) (choices 1) [2,8,16] r20121 c20121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5560
  · exact u5561
  · exact u5562

def b20122 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 388 104 145 34 89 153 281), lower := (rows 35 70 388 104 145 34 64 128 256), losses := [] }

theorem u20122 : Upper (D 7) (R 7) [34,68,384,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20123 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 388 104 145 40 83 147 275), lower := (rows 35 70 388 104 145 40 64 128 256), losses := [] }

theorem u20123 : Upper (D 7) (R 7) [34,68,384,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20123 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20124 : Route 9 := (fun mask => (mask,id))

def c20124 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20124 : Upper (D 7) (R 7) [34,68,384,96,129,16] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96,129,16] 13 (by decide) (choices 1) [1,2,8] r20124 c20124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5563
  · exact u5564
  · exact u5565

def r20125 : Route 9 := (fun mask => (mask,id))

def c20125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20125 : Upper (D 7) (R 7) [34,68,384,96,130,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96,130,1] 13 (by decide) (choices 1) [1,8,16] r20125 c20125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5566
  · exact u5567
  · exact u5568

def b20126 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 70 388 104 146 40 81 145 273), lower := (rows 35 70 388 104 146 40 64 128 256), losses := [] }

theorem u20126 : Upper (D 7) (R 7) [34,68,384,96,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20126 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20127 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 35 70 388 104 146 48 73 137 265), lower := (rows 35 70 388 104 146 48 64 128 256), losses := [] }

theorem u20127 : Upper (D 7) (R 7) [34,68,384,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20127 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20128 : Route 9 := (fun mask => (mask,id))

def c20128 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20128 : Upper (D 7) (R 7) [34,68,384,96,136,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96,136,1] 13 (by decide) (choices 1) [1,2,16] r20128 c20128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5569
  · exact u5570
  · exact u5571

def b20129 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 388 104 152 34 81 145 273), lower := (rows 35 70 388 104 152 34 64 128 256), losses := [] }

theorem u20129 : Upper (D 7) (R 7) [34,68,384,96,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20130 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(1,5),(2,5),(2,6)], upper := (rows 35 70 388 104 152 48 67 131 259), lower := (rows 35 70 388 104 152 48 64 128 256), losses := [] }

theorem u20130 : Upper (D 7) (R 7) [34,68,384,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20130 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20131 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 26 84 33 480 416 416), lower := (rows 35 194 13 26 84 33 64 128 256), losses := [] }

theorem u20131 : Upper (D 7) (R 7) [34,192,9,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20132 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 26 84 160 353 417 289), lower := (rows 35 194 13 26 84 160 64 128 256), losses := [] }

theorem u20132 : Upper (D 7) (R 7) [34,192,9,18,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20133 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 2, region := 496, targets := 2 }], pairs := [(0,6),(2,6),(4,1)], upper := (rows 35 194 13 26 84 288 225 161 417), lower := (rows 35 194 13 26 84 288 64 128 256), losses := [] }

theorem u20133 : Upper (D 7) (R 7) [34,192,9,18,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20133 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20134 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 194 13 26 273 36 224 224 480), lower := (rows 35 194 13 26 273 36 64 128 256), losses := [] }

theorem u20134 : Upper (D 7) (R 7) [34,192,9,18,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20134 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20135 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 26 273 96 228 164 420), lower := (rows 35 194 13 26 273 96 64 128 256), losses := [] }

theorem u20135 : Upper (D 7) (R 7) [34,192,9,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20136 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 13 26 276 33 224 224 480), lower := (rows 35 194 13 26 276 33 64 128 256), losses := [] }

theorem u20136 : Upper (D 7) (R 7) [34,192,9,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20137 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 26 276 96 225 161 417), lower := (rows 35 194 13 26 276 96 64 128 256), losses := [] }

theorem u20137 : Upper (D 7) (R 7) [34,192,9,18,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20138 : PairBound 9 := { available := 196, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 13 26 304 33 196 196 452), lower := (rows 35 194 13 26 304 33 64 128 256), losses := [] }

theorem u20138 : Upper (D 7) (R 7) [34,192,9,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20139 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 194 13 26 304 36 193 193 449), lower := (rows 35 194 13 26 304 36 64 128 256), losses := [] }

theorem u20139 : Upper (D 7) (R 7) [34,192,9,18,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20139 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20140 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 26 304 96 197 133 389), lower := (rows 35 194 13 26 304 96 64 128 256), losses := [] }

theorem u20140 : Upper (D 7) (R 7) [34,192,9,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20141 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 2, region := 496, targets := 2 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(0,7),(2,6),(4,1)], upper := (rows 35 194 13 26 336 33 228 164 420), lower := (rows 35 194 13 26 336 33 64 128 256), losses := [] }

theorem u20141 : Upper (D 7) (R 7) [34,192,9,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20142 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 194 13 26 336 36 225 161 417), lower := (rows 35 194 13 26 336 36 64 128 256), losses := [] }

theorem u20142 : Upper (D 7) (R 7) [34,192,9,18,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20142 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20143 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 26 336 160 101 165 293), lower := (rows 35 194 13 26 336 160 64 128 256), losses := [] }

theorem u20143 : Upper (D 7) (R 7) [34,192,9,18,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20144 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 28 112 33 450 386 386), lower := (rows 35 194 13 28 112 33 64 128 256), losses := [] }

theorem u20144 : Upper (D 7) (R 7) [34,192,9,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20145 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 28 112 34 449 385 385), lower := (rows 35 194 13 28 112 34 64 128 256), losses := [] }

theorem u20145 : Upper (D 7) (R 7) [34,192,9,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20146 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 28 112 160 323 387 259), lower := (rows 35 194 13 28 112 160 64 128 256), losses := [] }

theorem u20146 : Upper (D 7) (R 7) [34,192,9,20,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20147 : Route 9 := (fun mask => (mask,id))

def c20147 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20147 : Upper (D 7) (R 7) [34,192,9,20,96,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,20,96,256] 13 (by decide) (choices 1) [1,2,128] r20147 c20147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5572
  · exact u5573
  · exact u5574

def b20148 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 13 28 274 33 224 224 480), lower := (rows 35 194 13 28 274 33 64 128 256), losses := [] }

theorem u20148 : Upper (D 7) (R 7) [34,192,9,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20149 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 28 274 96 225 161 417), lower := (rows 35 194 13 28 274 96 64 128 256), losses := [] }

theorem u20149 : Upper (D 7) (R 7) [34,192,9,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20150 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(1,0),(4,0)], upper := (rows 35 194 13 28 304 33 194 194 450), lower := (rows 35 194 13 28 304 33 64 128 256), losses := [] }

theorem u20150 : Upper (D 7) (R 7) [34,192,9,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20151 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 28 304 34 193 193 449), lower := (rows 35 194 13 28 304 34 64 128 256), losses := [] }

theorem u20151 : Upper (D 7) (R 7) [34,192,9,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20152 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 28 304 96 195 131 387), lower := (rows 35 194 13 28 304 96 64 128 256), losses := [] }

theorem u20152 : Upper (D 7) (R 7) [34,192,9,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20153 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(4,0)], upper := (rows 35 194 13 28 336 33 226 162 418), lower := (rows 35 194 13 28 336 33 64 128 256), losses := [] }

theorem u20153 : Upper (D 7) (R 7) [34,192,9,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20154 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 28 336 34 225 161 417), lower := (rows 35 194 13 28 336 34 64 128 256), losses := [] }

theorem u20154 : Upper (D 7) (R 7) [34,192,9,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20155 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 28 336 160 99 163 291), lower := (rows 35 194 13 28 336 160 64 128 256), losses := [] }

theorem u20155 : Upper (D 7) (R 7) [34,192,9,20,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20156 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 56 81 34 452 388 388), lower := (rows 35 194 13 56 81 34 64 128 256), losses := [] }

theorem u20156 : Upper (D 7) (R 7) [34,192,9,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20157 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 44, targets := 194 }], pairs := [(2,1),(2,6),(2,7)], upper := (rows 35 194 13 56 81 36 450 386 386), lower := (rows 35 194 13 56 81 36 64 128 256), losses := [] }

theorem u20157 : Upper (D 7) (R 7) [34,192,9,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20157 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20158 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 56 81 160 326 390 262), lower := (rows 35 194 13 56 81 160 64 128 256), losses := [] }

theorem u20158 : Upper (D 7) (R 7) [34,192,9,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20159 : PairBound 9 := { available := 134, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 35 194 13 56 81 288 198 134 390), lower := (rows 35 194 13 56 81 288 64 128 256), losses := [] }

theorem u20159 : Upper (D 7) (R 7) [34,192,9,48,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20159 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u20159
end Delivery.IrregularNine14.P07
