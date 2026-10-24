import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0180
import IrregularNine14P07C0181

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28680 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 38 138 148 96 89 153 281), lower := (rows 97 259 38 138 148 96 64 128 256), losses := [] }

theorem u28680 : Upper (D 7) (R 7) [96,257,34,130,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28681 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 259 38 138 208 33 92 156 284), lower := (rows 97 259 38 138 208 33 64 128 256), losses := [] }

theorem u28681 : Upper (D 7) (R 7) [96,257,34,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28682 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 38 138 208 36 89 153 281), lower := (rows 97 259 38 138 208 36 64 128 256), losses := [] }

theorem u28682 : Upper (D 7) (R 7) [96,257,34,130,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28682 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28683 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 36, targets := 193 }], pairs := [(2,0),(2,6),(2,7)], upper := (rows 97 259 38 138 208 40 85 149 277), lower := (rows 97 259 38 138 208 40 64 128 256), losses := [] }

theorem u28683 : Upper (D 7) (R 7) [96,257,34,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28683 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28684 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 38 138 208 48 77 141 269), lower := (rows 97 259 38 138 208 48 64 128 256), losses := [] }

theorem u28684 : Upper (D 7) (R 7) [96,257,34,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28684 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28685 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 259 38 140 208 33 90 154 282), lower := (rows 97 259 38 140 208 33 64 128 256), losses := [] }

theorem u28685 : Upper (D 7) (R 7) [96,257,34,132,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28686 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 217, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 97 259 38 140 208 34 89 153 281), lower := (rows 97 259 38 140 208 34 64 128 256), losses := [] }

theorem u28686 : Upper (D 7) (R 7) [96,257,34,132,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28687 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 402, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 38 140 208 40 83 147 275), lower := (rows 97 259 38 140 208 40 64 128 256), losses := [{ target := 5, region := (rows 1 3 4 12 23 0 67 131 259), good := (rows 467 467 478 156 208 8 64 128 256) }] }

theorem u28687 : Upper (D 7) (R 7) [96,257,34,132,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28687 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28688 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 38 140 208 48 75 139 267), lower := (rows 97 259 38 140 208 48 64 128 256), losses := [] }

theorem u28688 : Upper (D 7) (R 7) [96,257,34,132,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28688 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28689 : Route 9 := (fun mask => (mask,id))

def c28689 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28689 : Upper (D 7) (R 7) [96,257,40,80,129,2] 13 := by
  apply FastRouting.sound _ _ [96,257,40,80,129,2] 13 (by decide) (choices 1) [2,4,128] r28689 c28689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10833
  · exact u10834
  · exact u10835

def b28690 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 259 44 88 145 36 194 130 386), lower := (rows 97 259 44 88 145 36 64 128 256), losses := [] }

theorem u28690 : Upper (D 7) (R 7) [96,257,40,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28690 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28691 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(2,0)], upper := (rows 97 259 44 88 145 160 70 134 262), lower := (rows 97 259 44 88 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 96 258 44 124 176 160 64 160 256) },{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 97 257 45 125 177 160 64 160 256) }] }

theorem u28691 : Upper (D 7) (R 7) [96,257,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28692 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 259 44 88 146 33 198 134 390), lower := (rows 97 259 44 88 146 33 64 128 256), losses := [] }

theorem u28692 : Upper (D 7) (R 7) [96,257,40,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28693 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 193, targets := 2 }], pairs := [(0,1),(0,7),(2,0),(2,6)], upper := (rows 97 259 44 88 146 34 197 133 389), lower := (rows 97 259 44 88 146 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 50 64 128 256), good := (rows 96 290 44 124 178 34 64 128 256) },{ target := 6, region := (rows 1 2 12 8 16 50 0 128 256), good := (rows 33 291 44 60 178 34 0 128 256) },{ target := 7, region := (rows 9 2 12 8 16 50 64 0 256), good := (rows 97 291 45 125 50 34 64 0 256) }] }

theorem u28693 : Upper (D 7) (R 7) [96,257,40,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28694 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 259 44 88 146 36 195 131 387), lower := (rows 97 259 44 88 146 36 64 128 256), losses := [] }

theorem u28694 : Upper (D 7) (R 7) [96,257,40,80,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28694 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28695 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(2,0)], upper := (rows 97 259 44 88 146 160 71 135 263), lower := (rows 97 259 44 88 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 96 258 44 124 178 160 64 160 256) },{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 97 257 45 125 176 160 64 160 256) }] }

theorem u28695 : Upper (D 7) (R 7) [96,257,40,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28696 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 259 44 88 148 33 194 130 386), lower := (rows 97 259 44 88 148 33 64 128 256), losses := [] }

theorem u28696 : Upper (D 7) (R 7) [96,257,40,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28697 : Route 9 := (fun mask => (mask,id))

def c28697 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28697 : Upper (D 7) (R 7) [96,257,40,80,132,2] 13 := by
  apply FastRouting.sound _ _ [96,257,40,80,132,2] 13 (by decide) (choices 1) [1,2,128] r28697 c28697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10836
  · exact u10837
  · exact u10838

def b28698 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 0, region := 258, targets := 32 },{ cop := 0, region := 258, targets := 64 }], pairs := [(0,7),(1,5),(1,6),(1,7)], upper := (rows 97 259 44 88 148 160 67 131 259), lower := (rows 97 259 44 88 148 160 64 128 256), losses := [] }

theorem u28698 : Upper (D 7) (R 7) [96,257,40,80,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28699 : Route 9 := (fun mask => (mask,id))

def c28699 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28699 : Upper (D 7) (R 7) [96,257,40,129,130,2] 13 := by
  apply FastRouting.sound _ _ [96,257,40,129,130,2] 13 (by decide) (choices 1) [4,16] r28699 c28699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10839
  · exact u10840

def b28700 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 259 44 137 146 36 82 210 338), lower := (rows 97 259 44 137 146 36 64 128 256), losses := [] }

theorem u28700 : Upper (D 7) (R 7) [96,257,40,129,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28700 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28701 : Route 9 := (fun mask => (mask,id))

def c28701 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28701 : Upper (D 7) (R 7) [96,257,40,129,130,16] 13 := by
  apply FastRouting.sound _ _ [96,257,40,129,130,16] 13 (by decide) (choices 1) [2,4] r28701 c28701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10841
  · exact u10842

def b28702 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 44 137 146 96 86 150 278), lower := (rows 97 259 44 137 146 96 64 128 256), losses := [] }

theorem u28702 : Upper (D 7) (R 7) [96,257,40,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28703 : Route 9 := (fun mask => (mask,id))

def c28703 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28703 : Upper (D 7) (R 7) [96,257,40,129,132,2] 13 := by
  apply FastRouting.sound _ _ [96,257,40,129,132,2] 13 (by decide) (choices 1) [2,16] r28703 c28703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10843
  · exact u10844

def b28704 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 259 44 137 148 48 66 194 322), lower := (rows 97 259 44 137 148 48 64 128 256), losses := [] }

theorem u28704 : Upper (D 7) (R 7) [96,257,40,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28704 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28705 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 44 137 148 96 82 146 274), lower := (rows 97 259 44 137 148 96 64 128 256), losses := [] }

theorem u28705 : Upper (D 7) (R 7) [96,257,40,129,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28706 : Route 9 := (fun mask => (mask,id))

def c28706 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28706 : Upper (D 7) (R 7) [96,257,40,129,192,2] 13 := by
  apply FastRouting.sound _ _ [96,257,40,129,192,2] 13 (by decide) (choices 1) [2,4,16] r28706 c28706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10845
  · exact u10846
  · exact u10847

def b28707 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 259 44 137 208 36 82 146 274), lower := (rows 97 259 44 137 208 36 64 128 256), losses := [] }

theorem u28707 : Upper (D 7) (R 7) [96,257,40,129,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28707 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28708 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 44 137 208 48 70 134 262), lower := (rows 97 259 44 137 208 48 64 128 256), losses := [] }

theorem u28708 : Upper (D 7) (R 7) [96,257,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28708 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28709 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 36, targets := 193 },{ cop := 2, region := 209, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 97 259 44 138 145 34 84 212 340), lower := (rows 97 259 44 138 145 34 64 128 256), losses := [] }

theorem u28709 : Upper (D 7) (R 7) [96,257,40,130,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28710 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 259 44 138 145 36 82 210 338), lower := (rows 97 259 44 138 145 36 64 128 256), losses := [] }

theorem u28710 : Upper (D 7) (R 7) [96,257,40,130,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28710 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28711 : Route 9 := (fun mask => (mask,id))

def c28711 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28711 : Upper (D 7) (R 7) [96,257,40,130,129,16] 13 := by
  apply FastRouting.sound _ _ [96,257,40,130,129,16] 13 (by decide) (choices 1) [2,4] r28711 c28711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10848
  · exact u10849

def b28712 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 44 138 145 96 86 150 278), lower := (rows 97 259 44 138 145 96 64 128 256), losses := [] }

theorem u28712 : Upper (D 7) (R 7) [96,257,40,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28713 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,1)], upper := (rows 97 259 44 138 148 33 82 210 338), lower := (rows 97 259 44 138 148 33 64 128 256), losses := [{ target := 1, region := (rows 65 0 12 8 24 99 64 128 256), good := (rows 97 289 60 188 148 33 97 128 256) }] }

theorem u28713 : Upper (D 7) (R 7) [96,257,40,130,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28714 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 52, targets := 65 }], pairs := [(2,0),(2,6),(4,0),(4,6)], upper := (rows 97 259 44 138 148 34 81 209 337), lower := (rows 97 259 44 138 148 34 64 128 256), losses := [] }

theorem u28714 : Upper (D 7) (R 7) [96,257,40,130,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28715 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 259 44 138 148 48 67 195 323), lower := (rows 97 259 44 138 148 48 64 128 256), losses := [] }

theorem u28715 : Upper (D 7) (R 7) [96,257,40,130,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28715 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28716 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 259 44 138 148 96 83 147 275), lower := (rows 97 259 44 138 148 96 64 128 256), losses := [] }

theorem u28716 : Upper (D 7) (R 7) [96,257,40,130,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28717 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,6)], upper := (rows 97 259 44 138 208 33 86 150 278), lower := (rows 97 259 44 138 208 33 64 128 256), losses := [{ target := 1, region := (rows 81 0 12 8 16 115 64 128 256), good := (rows 97 289 44 172 241 33 97 128 256) },{ target := 6, region := (rows 1 2 12 8 16 35 0 128 256), good := (rows 33 291 44 174 144 33 0 128 256) }] }

theorem u28717 : Upper (D 7) (R 7) [96,257,40,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28718 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 36, targets := 193 },{ cop := 2, region := 209, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 97 259 44 138 208 34 85 149 277), lower := (rows 97 259 44 138 208 34 64 128 256), losses := [] }

theorem u28718 : Upper (D 7) (R 7) [96,257,40,130,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28719 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 97 259 44 138 208 36 83 147 275), lower := (rows 97 259 44 138 208 36 64 128 256), losses := [] }

theorem u28719 : Upper (D 7) (R 7) [96,257,40,130,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28719 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28720 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 259 44 138 208 48 71 135 263), lower := (rows 97 259 44 138 208 48 64 128 256), losses := [] }

theorem u28720 : Upper (D 7) (R 7) [96,257,40,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28720 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28721 : Route 9 := (fun mask => (mask,id))

def c28721 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28721 : Upper (D 7) (R 7) [96,257,40,192,129,2] 13 := by
  apply FastRouting.sound _ _ [96,257,40,192,129,2] 13 (by decide) (choices 1) [2,4,16] r28721 c28721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10850
  · exact u10851
  · exact u10852

def b28722 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 259 44 200 145 36 82 146 274), lower := (rows 97 259 44 200 145 36 64 128 256), losses := [] }

theorem u28722 : Upper (D 7) (R 7) [96,257,40,192,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28722 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28723 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 53, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 259 44 200 145 48 70 134 262), lower := (rows 97 259 44 200 145 48 64 128 256), losses := [] }

theorem u28723 : Upper (D 7) (R 7) [96,257,40,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28723 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28724 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 259 44 200 146 33 86 150 278), lower := (rows 97 259 44 200 146 33 64 128 256), losses := [] }

theorem u28724 : Upper (D 7) (R 7) [96,257,40,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28725 : Route 9 := (fun mask => (mask,id))

def c28725 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28725 : Upper (D 7) (R 7) [96,257,40,192,130,2] 13 := by
  apply FastRouting.sound _ _ [96,257,40,192,130,2] 13 (by decide) (choices 1) [1,4,16] r28725 c28725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10853
  · exact u10854
  · exact u10855

def b28726 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 259 44 200 146 36 83 147 275), lower := (rows 97 259 44 200 146 36 64 128 256), losses := [] }

theorem u28726 : Upper (D 7) (R 7) [96,257,40,192,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28726 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28727 : Route 9 := (fun mask => (mask,id))

def c28727 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28727 : Upper (D 7) (R 7) [96,257,40,192,130,16] 13 := by
  apply FastRouting.sound _ _ [96,257,40,192,130,16] 13 (by decide) (choices 1) [1,2,4] r28727 c28727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10856
  · exact u10857
  · exact u10858

def b28728 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 53, targets := 2 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 97 259 44 200 148 33 82 146 274), lower := (rows 97 259 44 200 148 33 64 128 256), losses := [] }

theorem u28728 : Upper (D 7) (R 7) [96,257,40,192,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28729 : Route 9 := (fun mask => (mask,id))

def c28729 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28729 : Upper (D 7) (R 7) [96,257,40,192,132,2] 13 := by
  apply FastRouting.sound _ _ [96,257,40,192,132,2] 13 (by decide) (choices 1) [1,2,16] r28729 c28729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10859
  · exact u10860
  · exact u10861

def b28730 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 52, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 97 259 44 200 148 48 67 131 259), lower := (rows 97 259 44 200 148 48 64 128 256), losses := [] }

theorem u28730 : Upper (D 7) (R 7) [96,257,40,192,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28730 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28731 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 105, targets := 2 }], pairs := [(0,1),(1,0),(3,1)], upper := (rows 97 262 7 25 146 40 224 224 480), lower := (rows 97 262 7 25 146 40 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 20 40 105 169 297), good := (rows 480 278 470 504 146 488 64 128 256) }] }

theorem u28731 : Upper (D 7) (R 7) [96,260,3,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28731 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28732 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 7 25 146 96 232 168 424), lower := (rows 97 262 7 25 146 96 64 128 256), losses := [] }

theorem u28732 : Upper (D 7) (R 7) [96,260,3,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28733_8 : Upper (D 7) (R 7) [96,260,3,17,130,128,8] 13 :=
  permutation_upper _ _ _ [96,260,3,17,130,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10862

theorem m28733_32 : Upper (D 7) (R 7) [96,260,3,17,130,128,32] 13 :=
  permutation_upper _ _ _ [96,260,3,17,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10863

def r28733 : Route 9 := (fun mask => (mask,id))

def c28733 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28733 : Upper (D 7) (R 7) [96,260,3,17,130,128] 13 := by
  apply FastRouting.sound _ _ [96,260,3,17,130,128] 13 (by decide) (choices 1) [8,32] r28733 c28733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28733_8
  · exact m28733_32

def b28734 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 217, targets := 2 },{ cop := 2, region := 482, targets := 1 }], pairs := [(0,1),(1,0),(3,1),(4,1)], upper := (rows 97 262 7 25 152 34 224 224 480), lower := (rows 97 262 7 25 152 34 64 128 256), losses := [] }

theorem u28734 : Upper (D 7) (R 7) [96,260,3,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28735 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 7 25 152 96 226 162 418), lower := (rows 97 262 7 25 152 96 64 128 256), losses := [] }

theorem u28735 : Upper (D 7) (R 7) [96,260,3,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28736 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 482, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 97 262 7 25 152 160 98 226 354), lower := (rows 97 262 7 25 152 160 64 128 256), losses := [] }

theorem u28736 : Upper (D 7) (R 7) [96,260,3,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28737 : PairBound 9 := { available := 200, camps := [{ cop := 5, region := 217, targets := 2 },{ cop := 3, region := 454, targets := 32 }], pairs := [(0,1),(1,5),(3,1),(4,1)], upper := (rows 97 262 7 25 176 34 200 200 456), lower := (rows 97 262 7 25 176 34 64 128 256), losses := [] }

theorem u28737 : Upper (D 7) (R 7) [96,260,3,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28738 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(2,5)], upper := (rows 97 262 7 25 176 40 194 194 450), lower := (rows 97 262 7 25 176 40 64 128 256), losses := [] }

theorem u28738 : Upper (D 7) (R 7) [96,260,3,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28738 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28739 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 7 25 176 96 202 138 394), lower := (rows 97 262 7 25 176 96 64 128 256), losses := [] }

theorem u28739 : Upper (D 7) (R 7) [96,260,3,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u28739
end Delivery.IrregularNine14.P07
