import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0089

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19740 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 261 25 176 96 202 138 394), lower := (rows 35 70 261 25 176 96 64 128 256), losses := [] }

theorem u19740 : Upper (D 7) (R 7) [34,68,257,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19741 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 261 25 176 160 74 202 330), lower := (rows 35 70 261 25 176 160 64 128 256), losses := [] }

theorem u19741 : Upper (D 7) (R 7) [34,68,257,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19742 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 25 208 34 232 168 424), lower := (rows 35 70 261 25 208 34 64 128 256), losses := [] }

theorem u19742 : Upper (D 7) (R 7) [34,68,257,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19743 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 208, targets := 1 },{ cop := 0, region := 388, targets := 64 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 35 70 261 25 208 40 226 162 418), lower := (rows 35 70 261 25 208 40 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 29 40 65 129 257), good := (rows 498 86 470 504 208 56 64 128 256) }] }

theorem u19743 : Upper (D 7) (R 7) [34,68,257,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19743 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19744 : Route 9 := (fun mask => (mask,id))

def c19744 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19744 : Upper (D 7) (R 7) [34,68,257,17,192,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,17,192,128] 13 (by decide) (choices 1) [2,8,32] r19744 c19744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5365
  · exact u5366
  · exact u5367

def b19745 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 57, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 70 261 26 81 40 224 160 416), lower := (rows 35 70 261 26 81 40 64 128 256), losses := [] }

theorem u19745 : Upper (D 7) (R 7) [34,68,257,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19745 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19746 : Route 9 := (fun mask => (mask,id))

def c19746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u19746 : Upper (D 7) (R 7) [34,68,257,18,65,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,18,65,128] 13 (by decide) (choices 1) [8,32,128] r19746 c19746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5368
  · exact u5369
  · exact u5370

def b19747 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 57, targets := 128 },{ cop := 0, region := 216, targets := 1 }], pairs := [(0,7),(3,0),(3,7),(4,7)], upper := (rows 35 70 261 26 112 33 200 136 392), lower := (rows 35 70 261 26 112 33 64 128 256), losses := [] }

theorem u19747 : Upper (D 7) (R 7) [34,68,257,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19748 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 57, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 70 261 26 112 40 193 129 385), lower := (rows 35 70 261 26 112 40 64 128 256), losses := [] }

theorem u19748 : Upper (D 7) (R 7) [34,68,257,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19748 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19749 : Route 9 := (fun mask => (mask,id))

def c19749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19749 : Upper (D 7) (R 7) [34,68,257,18,96,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,18,96,128] 13 (by decide) (choices 1) [1,8,128] r19749 c19749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5371
  · exact u5372
  · exact u5373

def b19750 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 70 261 26 145 40 224 224 480), lower := (rows 35 70 261 26 145 40 64 128 256), losses := [] }

theorem u19750 : Upper (D 7) (R 7) [34,68,257,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19750 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19751 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 261 26 145 96 232 168 424), lower := (rows 35 70 261 26 145 96 64 128 256), losses := [] }

theorem u19751 : Upper (D 7) (R 7) [34,68,257,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19752 : Route 9 := (fun mask => (mask,id))

def c19752 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19752 : Upper (D 7) (R 7) [34,68,257,18,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,18,129,128] 13 (by decide) (choices 1) [8,32] r19752 c19752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5374
  · exact u5375

def b19753 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 261 26 152 33 224 224 480), lower := (rows 35 70 261 26 152 33 64 128 256), losses := [] }

theorem u19753 : Upper (D 7) (R 7) [34,68,257,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19754 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 388, targets := 2 }], pairs := [(2,1),(2,6),(3,6),(4,6)], upper := (rows 35 70 261 26 152 96 225 161 417), lower := (rows 35 70 261 26 152 96 64 128 256), losses := [] }

theorem u19754 : Upper (D 7) (R 7) [34,68,257,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19755 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(2,7)], upper := (rows 35 70 261 26 152 160 97 225 353), lower := (rows 35 70 261 26 152 160 64 128 256), losses := [] }

theorem u19755 : Upper (D 7) (R 7) [34,68,257,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19756 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 261 26 176 33 200 200 456), lower := (rows 35 70 261 26 176 33 64 128 256), losses := [] }

theorem u19756 : Upper (D 7) (R 7) [34,68,257,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19757 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 70 261 26 176 40 193 193 449), lower := (rows 35 70 261 26 176 40 64 128 256), losses := [] }

theorem u19757 : Upper (D 7) (R 7) [34,68,257,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19757 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19758 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 261 26 176 96 201 137 393), lower := (rows 35 70 261 26 176 96 64 128 256), losses := [] }

theorem u19758 : Upper (D 7) (R 7) [34,68,257,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19759 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 261 26 176 160 73 201 329), lower := (rows 35 70 261 26 176 160 64 128 256), losses := [] }

theorem u19759 : Upper (D 7) (R 7) [34,68,257,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19760 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 261 26 208 33 232 168 424), lower := (rows 35 70 261 26 208 33 64 128 256), losses := [] }

theorem u19760 : Upper (D 7) (R 7) [34,68,257,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19761 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 70 261 26 208 40 225 161 417), lower := (rows 35 70 261 26 208 40 64 128 256), losses := [] }

theorem u19761 : Upper (D 7) (R 7) [34,68,257,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19761 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19762 : Route 9 := (fun mask => (mask,id))

def c19762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19762 : Upper (D 7) (R 7) [34,68,257,18,192,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,18,192,128] 13 (by decide) (choices 1) [1,8,32] r19762 c19762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5376
  · exact u5377
  · exact u5378

def b19763 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 56 81 34 200 136 392), lower := (rows 35 70 261 56 81 34 64 128 256), losses := [] }

theorem u19763 : Upper (D 7) (R 7) [34,68,257,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19764 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 70 261 56 81 40 194 130 386), lower := (rows 35 70 261 56 81 40 64 128 256), losses := [] }

theorem u19764 : Upper (D 7) (R 7) [34,68,257,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19764 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19765 : Route 9 := (fun mask => (mask,id))

def c19765 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19765 : Upper (D 7) (R 7) [34,68,257,48,65,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,48,65,128] 13 (by decide) (choices 1) [2,8,128] r19765 c19765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5379
  · exact u5380
  · exact u5381

def b19766 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 56 145 34 200 200 456), lower := (rows 35 70 261 56 145 34 64 128 256), losses := [] }

theorem u19766 : Upper (D 7) (R 7) [34,68,257,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19767 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 70 261 56 145 40 194 194 450), lower := (rows 35 70 261 56 145 40 64 128 256), losses := [] }

theorem u19767 : Upper (D 7) (R 7) [34,68,257,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19767 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19768 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 261 56 145 96 202 138 394), lower := (rows 35 70 261 56 145 96 64 128 256), losses := [] }

theorem u19768 : Upper (D 7) (R 7) [34,68,257,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19769 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 261 56 145 160 74 202 330), lower := (rows 35 70 261 56 145 160 64 128 256), losses := [] }

theorem u19769 : Upper (D 7) (R 7) [34,68,257,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19770 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 261 56 146 33 200 200 456), lower := (rows 35 70 261 56 146 33 64 128 256), losses := [] }

theorem u19770 : Upper (D 7) (R 7) [34,68,257,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19771 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 70 261 56 146 40 193 193 449), lower := (rows 35 70 261 56 146 40 64 128 256), losses := [] }

theorem u19771 : Upper (D 7) (R 7) [34,68,257,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19771 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19772 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 261 56 146 96 201 137 393), lower := (rows 35 70 261 56 146 96 64 128 256), losses := [] }

theorem u19772 : Upper (D 7) (R 7) [34,68,257,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19773 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 261 56 146 160 73 201 329), lower := (rows 35 70 261 56 146 160 64 128 256), losses := [] }

theorem u19773 : Upper (D 7) (R 7) [34,68,257,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19774 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,0),(4,0)], upper := (rows 35 70 261 56 152 33 194 194 450), lower := (rows 35 70 261 56 152 33 64 128 256), losses := [] }

theorem u19774 : Upper (D 7) (R 7) [34,68,257,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19775 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 56 152 34 193 193 449), lower := (rows 35 70 261 56 152 34 64 128 256), losses := [] }

theorem u19775 : Upper (D 7) (R 7) [34,68,257,48,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19776 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 261 56 152 96 195 131 387), lower := (rows 35 70 261 56 152 96 64 128 256), losses := [] }

theorem u19776 : Upper (D 7) (R 7) [34,68,257,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19777 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6),(4,0)], upper := (rows 35 70 261 56 152 160 67 195 323), lower := (rows 35 70 261 56 152 160 64 128 256), losses := [] }

theorem u19777 : Upper (D 7) (R 7) [34,68,257,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19778 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 261 56 208 33 202 138 394), lower := (rows 35 70 261 56 208 33 64 128 256), losses := [] }

theorem u19778 : Upper (D 7) (R 7) [34,68,257,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19779 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 56 208 34 201 137 393), lower := (rows 35 70 261 56 208 34 64 128 256), losses := [] }

theorem u19779 : Upper (D 7) (R 7) [34,68,257,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19780 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 70 261 56 208 40 195 131 387), lower := (rows 35 70 261 56 208 40 64 128 256), losses := [] }

theorem u19780 : Upper (D 7) (R 7) [34,68,257,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19780 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19781 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 261 56 208 160 75 139 267), lower := (rows 35 70 261 56 208 160 64 128 256), losses := [] }

theorem u19781 : Upper (D 7) (R 7) [34,68,257,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19782 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(2,6),(4,6)], upper := (rows 35 70 261 73 146 40 240 176 432), lower := (rows 35 70 261 73 146 40 64 128 256), losses := [] }

theorem u19782 : Upper (D 7) (R 7) [34,68,257,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19782 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19783 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 261 73 146 48 232 168 424), lower := (rows 35 70 261 73 146 48 64 128 256), losses := [] }

theorem u19783 : Upper (D 7) (R 7) [34,68,257,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19783 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19784 : Route 9 := (fun mask => (mask,id))

def c19784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19784 : Upper (D 7) (R 7) [34,68,257,65,130,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,65,130,128] 13 (by decide) (choices 1) [8,16,32] r19784 c19784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5382
  · exact u5383
  · exact u5384

def b19785 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 73 152 34 240 176 432), lower := (rows 35 70 261 73 152 34 64 128 256), losses := [] }

theorem u19785 : Upper (D 7) (R 7) [34,68,257,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19786 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 35 70 261 73 152 48 226 162 418), lower := (rows 35 70 261 73 152 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 24 56 65 129 257), good := (rows 482 70 454 504 184 48 64 128 256) }] }

theorem u19786 : Upper (D 7) (R 7) [34,68,257,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19786 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19787 : Route 9 := (fun mask => (mask,id))

def c19787 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19787 : Upper (D 7) (R 7) [34,68,257,65,136,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,65,136,128] 13 (by decide) (choices 1) [2,16,32] r19787 c19787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5385
  · exact u5386
  · exact u5387

def b19788 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 73 176 34 216 152 408), lower := (rows 35 70 261 73 176 34 64 128 256), losses := [] }

theorem u19788 : Upper (D 7) (R 7) [34,68,257,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19789 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(2,6),(4,6)], upper := (rows 35 70 261 73 176 40 210 146 402), lower := (rows 35 70 261 73 176 40 64 128 256), losses := [] }

theorem u19789 : Upper (D 7) (R 7) [34,68,257,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19789 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19790 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 261 73 176 48 202 138 394), lower := (rows 35 70 261 73 176 48 64 128 256), losses := [] }

theorem u19790 : Upper (D 7) (R 7) [34,68,257,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19790 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19791 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 261 73 176 160 90 154 282), lower := (rows 35 70 261 73 176 160 64 128 256), losses := [] }

theorem u19791 : Upper (D 7) (R 7) [34,68,257,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19792 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 88 145 34 232 168 424), lower := (rows 35 70 261 88 145 34 64 128 256), losses := [] }

theorem u19792 : Upper (D 7) (R 7) [34,68,257,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19793 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(1,0),(2,6),(4,6)], upper := (rows 35 70 261 88 145 40 226 162 418), lower := (rows 35 70 261 88 145 40 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 56 65 129 257), good := (rows 482 70 454 120 504 40 64 128 256) }] }

theorem u19793 : Upper (D 7) (R 7) [34,68,257,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19793 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19794 : Route 9 := (fun mask => (mask,id))

def c19794 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19794 : Upper (D 7) (R 7) [34,68,257,80,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,80,129,128] 13 (by decide) (choices 1) [2,8,32] r19794 c19794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5388
  · exact u5389
  · exact u5390

def b19795 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,0),(4,0)], upper := (rows 35 70 261 88 146 33 232 168 424), lower := (rows 35 70 261 88 146 33 64 128 256), losses := [] }

theorem u19795 : Upper (D 7) (R 7) [34,68,257,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19796 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 0, region := 388, targets := 2 }], pairs := [(2,1),(2,6),(4,6)], upper := (rows 35 70 261 88 146 40 225 161 417), lower := (rows 35 70 261 88 146 40 64 128 256), losses := [] }

theorem u19796 : Upper (D 7) (R 7) [34,68,257,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19796 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19797 : Route 9 := (fun mask => (mask,id))

def c19797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19797 : Upper (D 7) (R 7) [34,68,257,80,130,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,80,130,128] 13 (by decide) (choices 1) [1,8,32] r19797 c19797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5391
  · exact u5392
  · exact u5393

def b19798 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(4,0)], upper := (rows 35 70 261 88 152 33 226 162 418), lower := (rows 35 70 261 88 152 33 64 128 256), losses := [] }

theorem u19798 : Upper (D 7) (R 7) [34,68,257,80,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19799 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 261 88 152 34 225 161 417), lower := (rows 35 70 261 88 152 34 64 128 256), losses := [] }

theorem u19799 : Upper (D 7) (R 7) [34,68,257,80,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19799 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u19799
end Delivery.IrregularNine14.P07
