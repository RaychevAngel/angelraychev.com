import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0095
import IrregularNine14P07C0096

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20580 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 194 44 328 145 36 83 147 275), lower := (rows 35 194 44 328 145 36 64 128 256), losses := [] }

theorem u20580 : Upper (D 7) (R 7) [34,192,40,320,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20580 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20581 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(2,7),(3,7)], upper := (rows 35 194 44 328 145 48 71 135 263), lower := (rows 35 194 44 328 145 48 64 128 256), losses := [] }

theorem u20581 : Upper (D 7) (R 7) [34,192,40,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20581 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20582 : Route 9 := (fun mask => (mask,id))

def c20582 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20582 : Upper (D 7) (R 7) [34,192,40,320,132,1] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,132,1] 13 (by decide) (choices 1) [1,2,16] r20582 c20582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5739
  · exact u5740
  · exact u5741

def b20583 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 44 328 148 34 81 145 273), lower := (rows 35 194 44 328 148 34 64 128 256), losses := [] }

theorem u20583 : Upper (D 7) (R 7) [34,192,40,320,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20584 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 332, targets := 128 }], pairs := [(1,5),(2,7),(3,5)], upper := (rows 35 194 44 328 148 48 67 131 259), lower := (rows 35 194 44 328 148 48 64 128 256), losses := [] }

theorem u20584 : Upper (D 7) (R 7) [34,192,40,320,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20584 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20585 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,6),(4,6)], upper := (rows 35 194 69 137 274 36 120 184 312), lower := (rows 35 194 69 137 274 36 64 128 256), losses := [] }

theorem u20585 : Upper (D 7) (R 7) [34,192,65,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20585 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20586 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 194 69 137 274 48 108 172 300), lower := (rows 35 194 69 137 274 48 64 128 256), losses := [] }

theorem u20586 : Upper (D 7) (R 7) [34,192,65,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20586 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20587 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 69 137 276 34 120 184 312), lower := (rows 35 194 69 137 276 34 64 128 256), losses := [] }

theorem u20587 : Upper (D 7) (R 7) [34,192,65,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20588 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(2,7),(4,7)], upper := (rows 35 194 69 137 276 40 114 178 306), lower := (rows 35 194 69 137 276 40 64 128 256), losses := [] }

theorem u20588 : Upper (D 7) (R 7) [34,192,65,129,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20588 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20589 : Route 9 := (fun mask => (mask,id))

def c20589 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20589 : Upper (D 7) (R 7) [34,192,65,129,260,16] 13 := by
  apply FastRouting.sound _ _ [34,192,65,129,260,16] 13 (by decide) (choices 1) [2,8,32] r20589 c20589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5742
  · exact u5743
  · exact u5744

def b20590 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 69 137 304 34 92 156 284), lower := (rows 35 194 69 137 304 34 64 128 256), losses := [] }

theorem u20590 : Upper (D 7) (R 7) [34,192,65,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20591 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,6),(4,6)], upper := (rows 35 194 69 137 304 36 90 154 282), lower := (rows 35 194 69 137 304 36 64 128 256), losses := [] }

theorem u20591 : Upper (D 7) (R 7) [34,192,65,129,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20591 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20592 : PairBound 9 := { available := 14, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 69 137 304 48 78 142 270), lower := (rows 35 194 69 137 304 48 64 128 256), losses := [] }

theorem u20592 : Upper (D 7) (R 7) [34,192,65,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20592 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20593 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 69 140 273 34 120 184 312), lower := (rows 35 194 69 140 273 34 64 128 256), losses := [] }

theorem u20593 : Upper (D 7) (R 7) [34,192,65,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20594 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 0, region := 272, targets := 64 }], pairs := [(2,7),(4,6),(4,7)], upper := (rows 35 194 69 140 273 40 114 178 306), lower := (rows 35 194 69 140 273 40 64 128 256), losses := [] }

theorem u20594 : Upper (D 7) (R 7) [34,192,65,132,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20594 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20595 : Route 9 := (fun mask => (mask,id))

def c20595 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20595 : Upper (D 7) (R 7) [34,192,65,132,257,16] 13 := by
  apply FastRouting.sound _ _ [34,192,65,132,257,16] 13 (by decide) (choices 1) [2,8,32] r20595 c20595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5745
  · exact u5746
  · exact u5747

def r20596 : Route 9 := (fun mask => (mask,id))

def c20596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20596 : Upper (D 7) (R 7) [34,192,65,132,258,1] 13 := by
  apply FastRouting.sound _ _ [34,192,65,132,258,1] 13 (by decide) (choices 1) [8,16,32] r20596 c20596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5748
  · exact u5749
  · exact u5750

def b20597 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 0, region := 272, targets := 64 }], pairs := [(2,7),(4,6),(4,7)], upper := (rows 35 194 69 140 274 40 113 177 305), lower := (rows 35 194 69 140 274 40 64 128 256), losses := [] }

theorem u20597 : Upper (D 7) (R 7) [34,192,65,132,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20597 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20598 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 194 69 140 274 48 105 169 297), lower := (rows 35 194 69 140 274 48 64 128 256), losses := [] }

theorem u20598 : Upper (D 7) (R 7) [34,192,65,132,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20598 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20599 : Route 9 := (fun mask => (mask,id))

def c20599 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20599 : Upper (D 7) (R 7) [34,192,65,132,264,1] 13 := by
  apply FastRouting.sound _ _ [34,192,65,132,264,1] 13 (by decide) (choices 1) [2,16,32] r20599 c20599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5751
  · exact u5752
  · exact u5753

def b20600 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 69 140 280 34 113 177 305), lower := (rows 35 194 69 140 280 34 64 128 256), losses := [] }

theorem u20600 : Upper (D 7) (R 7) [34,192,65,132,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20601 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 68, targets := 128 }], pairs := [(2,7),(3,6),(4,6)], upper := (rows 35 194 69 140 280 48 99 163 291), lower := (rows 35 194 69 140 280 48 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 12 20 60 0 129 257), good := (rows 419 130 445 188 312 48 0 128 256) }] }

theorem u20601 : Upper (D 7) (R 7) [34,192,65,132,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20601 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20602 : Route 9 := (fun mask => (mask,id))

def c20602 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20602 : Upper (D 7) (R 7) [34,192,65,132,288,1] 13 := by
  apply FastRouting.sound _ _ [34,192,65,132,288,1] 13 (by decide) (choices 1) [2,8,16] r20602 c20602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5754
  · exact u5755
  · exact u5756

def b20603 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 69 140 304 34 89 153 281), lower := (rows 35 194 69 140 304 34 64 128 256), losses := [] }

theorem u20603 : Upper (D 7) (R 7) [34,192,65,132,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20604 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 0, region := 272, targets := 64 }], pairs := [(2,7),(4,6),(4,7)], upper := (rows 35 194 69 140 304 40 83 147 275), lower := (rows 35 194 69 140 304 40 64 128 256), losses := [] }

theorem u20604 : Upper (D 7) (R 7) [34,192,65,132,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20604 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20605 : PairBound 9 := { available := 11, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 69 140 304 48 75 139 267), lower := (rows 35 194 69 140 304 48 64 128 256), losses := [] }

theorem u20605 : Upper (D 7) (R 7) [34,192,65,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20605 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20606 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 69 152 273 34 108 172 300), lower := (rows 35 194 69 152 273 34 64 128 256), losses := [] }

theorem u20606 : Upper (D 7) (R 7) [34,192,65,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20607 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,6),(4,6)], upper := (rows 35 194 69 152 273 36 106 170 298), lower := (rows 35 194 69 152 273 36 64 128 256), losses := [] }

theorem u20607 : Upper (D 7) (R 7) [34,192,65,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20607 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20608 : Route 9 := (fun mask => (mask,id))

def c20608 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20608 : Upper (D 7) (R 7) [34,192,65,144,257,8] 13 := by
  apply FastRouting.sound _ _ [34,192,65,144,257,8] 13 (by decide) (choices 1) [2,4,32] r20608 c20608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5757
  · exact u5758
  · exact u5759

def r20609 : Route 9 := (fun mask => (mask,id))

def c20609 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20609 : Upper (D 7) (R 7) [34,192,65,144,258,1] 13 := by
  apply FastRouting.sound _ _ [34,192,65,144,258,1] 13 (by decide) (choices 1) [4,8,32] r20609 c20609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5760
  · exact u5761
  · exact u5762

def b20610 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,6),(4,6)], upper := (rows 35 194 69 152 274 36 105 169 297), lower := (rows 35 194 69 152 274 36 64 128 256), losses := [] }

theorem u20610 : Upper (D 7) (R 7) [34,192,65,144,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20610 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20611 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(2,7),(4,7)], upper := (rows 35 194 69 152 274 40 101 165 293), lower := (rows 35 194 69 152 274 40 64 128 256), losses := [] }

theorem u20611 : Upper (D 7) (R 7) [34,192,65,144,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20611 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20612 : Route 9 := (fun mask => (mask,id))

def c20612 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20612 : Upper (D 7) (R 7) [34,192,65,144,260,1] 13 := by
  apply FastRouting.sound _ _ [34,192,65,144,260,1] 13 (by decide) (choices 1) [2,8,32] r20612 c20612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5763
  · exact u5764
  · exact u5765

def b20613 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 69 152 276 34 105 169 297), lower := (rows 35 194 69 152 276 34 64 128 256), losses := [] }

theorem u20613 : Upper (D 7) (R 7) [34,192,65,144,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20614 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 340, targets := 128 }], pairs := [(2,7),(3,6),(4,7)], upper := (rows 35 194 69 152 276 40 99 163 291), lower := (rows 35 194 69 152 276 40 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 12 20 60 0 129 257), good := (rows 419 130 445 184 316 40 0 128 256) }] }

theorem u20614 : Upper (D 7) (R 7) [34,192,65,144,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20614 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20615 : Route 9 := (fun mask => (mask,id))

def c20615 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20615 : Upper (D 7) (R 7) [34,192,65,144,264,1] 13 := by
  apply FastRouting.sound _ _ [34,192,65,144,264,1] 13 (by decide) (choices 1) [2,4,32] r20615 c20615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5766
  · exact u5767
  · exact u5768

def b20616 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 69 152 280 34 101 165 293), lower := (rows 35 194 69 152 280 34 64 128 256), losses := [] }

theorem u20616 : Upper (D 7) (R 7) [34,192,65,144,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20617 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,6),(4,6)], upper := (rows 35 194 69 152 280 36 99 163 291), lower := (rows 35 194 69 152 280 36 64 128 256), losses := [] }

theorem u20617 : Upper (D 7) (R 7) [34,192,65,144,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20617 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20618 : Route 9 := (fun mask => (mask,id))

def c20618 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20618 : Upper (D 7) (R 7) [34,192,65,144,288,1] 13 := by
  apply FastRouting.sound _ _ [34,192,65,144,288,1] 13 (by decide) (choices 1) [2,4,8] r20618 c20618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5769
  · exact u5770
  · exact u5771

def b20619 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 69 152 304 34 77 141 269), lower := (rows 35 194 69 152 304 34 64 128 256), losses := [] }

theorem u20619 : Upper (D 7) (R 7) [34,192,65,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20620 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,6),(4,6)], upper := (rows 35 194 69 152 304 36 75 139 267), lower := (rows 35 194 69 152 304 36 64 128 256), losses := [] }

theorem u20620 : Upper (D 7) (R 7) [34,192,65,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20620 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20621 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 0, region := 68, targets := 128 }], pairs := [(1,5),(2,5),(2,7)], upper := (rows 35 194 69 152 304 40 71 135 263), lower := (rows 35 194 69 152 304 40 64 128 256), losses := [] }

theorem u20621 : Upper (D 7) (R 7) [34,192,65,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20621 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20622 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 69 168 273 34 92 156 284), lower := (rows 35 194 69 168 273 34 64 128 256), losses := [] }

theorem u20622 : Upper (D 7) (R 7) [34,192,65,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20623 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,6),(4,6)], upper := (rows 35 194 69 168 273 36 90 154 282), lower := (rows 35 194 69 168 273 36 64 128 256), losses := [] }

theorem u20623 : Upper (D 7) (R 7) [34,192,65,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20623 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20624 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 194 69 168 273 40 86 150 278), lower := (rows 35 194 69 168 273 40 64 128 256), losses := [] }

theorem u20624 : Upper (D 7) (R 7) [34,192,65,160,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20624 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20625 : Route 9 := (fun mask => (mask,id))

def c20625 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20625 : Upper (D 7) (R 7) [34,192,65,160,257,16] 13 := by
  apply FastRouting.sound _ _ [34,192,65,160,257,16] 13 (by decide) (choices 1) [2,4,8] r20625 c20625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5772
  · exact u5773
  · exact u5774

def b20626 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,7),(3,6)], upper := (rows 35 194 69 168 274 33 92 156 284), lower := (rows 35 194 69 168 274 33 64 128 256), losses := [] }

theorem u20626 : Upper (D 7) (R 7) [34,192,65,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20627 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,6),(4,6)], upper := (rows 35 194 69 168 274 36 89 153 281), lower := (rows 35 194 69 168 274 36 64 128 256), losses := [] }

theorem u20627 : Upper (D 7) (R 7) [34,192,65,160,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20627 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20628 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 194 69 168 274 40 85 149 277), lower := (rows 35 194 69 168 274 40 64 128 256), losses := [] }

theorem u20628 : Upper (D 7) (R 7) [34,192,65,160,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20628 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20629 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 194 69 168 274 48 77 141 269), lower := (rows 35 194 69 168 274 48 64 128 256), losses := [] }

theorem u20629 : Upper (D 7) (R 7) [34,192,65,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20629 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20630 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,7),(3,6)], upper := (rows 35 194 69 168 276 33 90 154 282), lower := (rows 35 194 69 168 276 33 64 128 256), losses := [] }

theorem u20630 : Upper (D 7) (R 7) [34,192,65,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20631 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 69 168 276 34 89 153 281), lower := (rows 35 194 69 168 276 34 64 128 256), losses := [] }

theorem u20631 : Upper (D 7) (R 7) [34,192,65,160,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20632 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 194 69 168 276 40 83 147 275), lower := (rows 35 194 69 168 276 40 64 128 256), losses := [] }

theorem u20632 : Upper (D 7) (R 7) [34,192,65,160,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20632 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20633 : Route 9 := (fun mask => (mask,id))

def c20633 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20633 : Upper (D 7) (R 7) [34,192,65,160,260,16] 13 := by
  apply FastRouting.sound _ _ [34,192,65,160,260,16] 13 (by decide) (choices 1) [1,2,8] r20633 c20633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5775
  · exact u5776
  · exact u5777

def b20634 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,7),(3,6)], upper := (rows 35 194 69 168 280 33 86 150 278), lower := (rows 35 194 69 168 280 33 64 128 256), losses := [] }

theorem u20634 : Upper (D 7) (R 7) [34,192,65,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20635 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 69 168 280 34 85 149 277), lower := (rows 35 194 69 168 280 34 64 128 256), losses := [] }

theorem u20635 : Upper (D 7) (R 7) [34,192,65,160,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20636 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,6),(4,6)], upper := (rows 35 194 69 168 280 36 83 147 275), lower := (rows 35 194 69 168 280 36 64 128 256), losses := [] }

theorem u20636 : Upper (D 7) (R 7) [34,192,65,160,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20636 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20637 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 0, region := 68, targets := 128 }], pairs := [(1,5),(2,5),(2,7)], upper := (rows 35 194 69 168 280 48 71 135 263), lower := (rows 35 194 69 168 280 48 64 128 256), losses := [] }

theorem u20637 : Upper (D 7) (R 7) [34,192,65,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20637 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20638 : Route 9 := (fun mask => (mask,id))

def c20638 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20638 : Upper (D 7) (R 7) [34,192,72,144,257,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,257,1] 13 (by decide) (choices 1) [2,4,32] r20638 c20638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5778
  · exact u5779
  · exact u5780

def b20639 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 76 152 273 34 101 165 293), lower := (rows 35 194 76 152 273 34 64 128 256), losses := [] }

theorem u20639 : Upper (D 7) (R 7) [34,192,72,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u20639
end Delivery.IrregularNine14.P07
