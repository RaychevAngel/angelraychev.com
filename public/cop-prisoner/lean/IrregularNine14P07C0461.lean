import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0170

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27660 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 42 88 160 83 147 275), lower := (rows 37 322 133 42 88 160 64 128 256), losses := [] }

theorem u27660 : Upper (D 7) (R 7) [36,320,129,34,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27661 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 322 133 42 146 33 88 216 344), lower := (rows 37 322 133 42 146 33 64 128 256), losses := [] }

theorem u27661 : Upper (D 7) (R 7) [36,320,129,34,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27662 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 133 42 146 40 81 209 337), lower := (rows 37 322 133 42 146 40 64 128 256), losses := [] }

theorem u27662 : Upper (D 7) (R 7) [36,320,129,34,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27662 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27663 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 322 133 42 146 48 73 201 329), lower := (rows 37 322 133 42 146 48 64 128 256), losses := [] }

theorem u27663 : Upper (D 7) (R 7) [36,320,129,34,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27663 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27664 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 149, targets := 64 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,6),(2,6),(3,0),(4,6)], upper := (rows 37 322 133 42 146 96 89 153 281), lower := (rows 37 322 133 42 146 96 64 128 256), losses := [] }

theorem u27664 : Upper (D 7) (R 7) [36,320,129,34,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27665 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 322 133 42 152 33 82 210 338), lower := (rows 37 322 133 42 152 33 64 128 256), losses := [] }

theorem u27665 : Upper (D 7) (R 7) [36,320,129,34,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27666 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 322 133 42 152 34 81 209 337), lower := (rows 37 322 133 42 152 34 64 128 256), losses := [] }

theorem u27666 : Upper (D 7) (R 7) [36,320,129,34,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27667 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 133 42 152 48 67 195 323), lower := (rows 37 322 133 42 152 48 64 128 256), losses := [] }

theorem u27667 : Upper (D 7) (R 7) [36,320,129,34,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27667 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27668 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 149, targets := 64 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,6),(2,6),(3,0),(4,6)], upper := (rows 37 322 133 42 152 96 83 147 275), lower := (rows 37 322 133 42 152 96 64 128 256), losses := [] }

theorem u27668 : Upper (D 7) (R 7) [36,320,129,34,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27669 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 322 133 42 208 33 90 154 282), lower := (rows 37 322 133 42 208 33 64 128 256), losses := [] }

theorem u27669 : Upper (D 7) (R 7) [36,320,129,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27670 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 322 133 42 208 34 89 153 281), lower := (rows 37 322 133 42 208 34 64 128 256), losses := [] }

theorem u27670 : Upper (D 7) (R 7) [36,320,129,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27671 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 133 42 208 40 83 147 275), lower := (rows 37 322 133 42 208 40 64 128 256), losses := [] }

theorem u27671 : Upper (D 7) (R 7) [36,320,129,34,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27671 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27672 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 133 42 208 48 75 139 267), lower := (rows 37 322 133 42 208 48 64 128 256), losses := [] }

theorem u27672 : Upper (D 7) (R 7) [36,320,129,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27672 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27673 : Route 9 := (fun mask => (mask,id))

def c27673 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27673 : Upper (D 7) (R 7) [36,320,129,48,65,2] 13 := by
  apply FastRouting.sound _ _ [36,320,129,48,65,2] 13 (by decide) (choices 1) [2,8,128] r27673 c27673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10228
  · exact u10229
  · exact u10230

def b27674 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 133 56 81 40 194 130 386), lower := (rows 37 322 133 56 81 40 64 128 256), losses := [] }

theorem u27674 : Upper (D 7) (R 7) [36,320,129,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27674 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27675 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 56 81 160 74 138 266), lower := (rows 37 322 133 56 81 160 64 128 256), losses := [] }

theorem u27675 : Upper (D 7) (R 7) [36,320,129,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27676 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 56 146 33 74 202 330), lower := (rows 37 322 133 56 146 33 64 128 256), losses := [] }

theorem u27676 : Upper (D 7) (R 7) [36,320,129,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27677 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 3, region := 197, targets := 2 }], pairs := [(0,1),(0,6),(2,6),(3,6)], upper := (rows 37 322 133 56 146 34 73 201 329), lower := (rows 37 322 133 56 146 34 64 128 256), losses := [] }

theorem u27677 : Upper (D 7) (R 7) [36,320,129,48,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27678 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 133 56 146 40 67 195 323), lower := (rows 37 322 133 56 146 40 64 128 256), losses := [] }

theorem u27678 : Upper (D 7) (R 7) [36,320,129,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27678 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27679 : PairBound 9 := { available := 11, camps := [], pairs := [(0,1),(2,1),(3,0),(3,1)], upper := (rows 37 322 133 56 146 96 75 139 267), lower := (rows 37 322 133 56 146 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 98 64 128 256), good := (rows 36 354 132 56 186 96 96 128 256) },{ target := 1, region := (rows 25 0 20 24 16 98 64 128 256), good := (rows 37 352 133 61 189 96 96 128 256) }] }

theorem u27679 : Upper (D 7) (R 7) [36,320,129,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27680 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 56 208 33 74 138 266), lower := (rows 37 322 133 56 208 33 64 128 256), losses := [] }

theorem u27680 : Upper (D 7) (R 7) [36,320,129,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27681 : Route 9 := (fun mask => (mask,id))

def c27681 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27681 : Upper (D 7) (R 7) [36,320,129,48,192,2] 13 := by
  apply FastRouting.sound _ _ [36,320,129,48,192,2] 13 (by decide) (choices 1) [1,2,8] r27681 c27681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10231
  · exact u10232
  · exact u10233

def b27682 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 133 56 208 40 67 131 259), lower := (rows 37 322 133 56 208 40 64 128 256), losses := [] }

theorem u27682 : Upper (D 7) (R 7) [36,320,129,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27682 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27683 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 322 133 73 146 34 120 184 312), lower := (rows 37 322 133 73 146 34 64 128 256), losses := [] }

theorem u27683 : Upper (D 7) (R 7) [36,320,129,65,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27684 : Route 9 := (fun mask => (mask,id))

def c27684 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27684 : Upper (D 7) (R 7) [36,320,129,65,130,8] 13 := by
  apply FastRouting.sound _ _ [36,320,129,65,130,8] 13 (by decide) (choices 1) [2,16,32] r27684 c27684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10234
  · exact u10235
  · exact u10236

def b27685 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 133 73 146 48 106 170 298), lower := (rows 37 322 133 73 146 48 64 128 256), losses := [] }

theorem u27685 : Upper (D 7) (R 7) [36,320,129,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27685 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27686 : Route 9 := (fun mask => (mask,id))

def c27686 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27686 : Upper (D 7) (R 7) [36,320,129,65,136,2] 13 := by
  apply FastRouting.sound _ _ [36,320,129,65,136,2] 13 (by decide) (choices 1) [2,16,32] r27686 c27686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10237
  · exact u10238
  · exact u10239

def b27687 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 133 73 152 48 98 162 290), lower := (rows 37 322 133 73 152 48 64 128 256), losses := [] }

theorem u27687 : Upper (D 7) (R 7) [36,320,129,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27687 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27688 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 88 146 33 106 170 298), lower := (rows 37 322 133 88 146 33 64 128 256), losses := [] }

theorem u27688 : Upper (D 7) (R 7) [36,320,129,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27689 : Route 9 := (fun mask => (mask,id))

def c27689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27689 : Upper (D 7) (R 7) [36,320,129,80,130,2] 13 := by
  apply FastRouting.sound _ _ [36,320,129,80,130,2] 13 (by decide) (choices 1) [1,8,32] r27689 c27689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10240
  · exact u10241
  · exact u10242

def r27690 : Route 9 := (fun mask => (mask,id))

def c27690 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27690 : Upper (D 7) (R 7) [36,320,129,80,130,8] 13 := by
  apply FastRouting.sound _ _ [36,320,129,80,130,8] 13 (by decide) (choices 1) [1,2,32] r27690 c27690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10243
  · exact u10244
  · exact u10245

def b27691 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 322 133 104 146 33 90 154 282), lower := (rows 37 322 133 104 146 33 64 128 256), losses := [] }

theorem u27691 : Upper (D 7) (R 7) [36,320,129,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27692 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 40, targets := 129 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(3,7)], upper := (rows 37 322 133 104 146 34 89 153 281), lower := (rows 37 322 133 104 146 34 64 128 256), losses := [] }

theorem u27692 : Upper (D 7) (R 7) [36,320,129,96,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27693 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 133 104 146 40 83 147 275), lower := (rows 37 322 133 104 146 40 64 128 256), losses := [] }

theorem u27693 : Upper (D 7) (R 7) [36,320,129,96,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27693 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27694 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 133 104 146 48 75 139 267), lower := (rows 37 322 133 104 146 48 64 128 256), losses := [] }

theorem u27694 : Upper (D 7) (R 7) [36,320,129,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27694 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27695 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 322 133 104 152 33 82 146 274), lower := (rows 37 322 133 104 152 33 64 128 256), losses := [] }

theorem u27695 : Upper (D 7) (R 7) [36,320,129,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27696 : Route 9 := (fun mask => (mask,id))

def c27696 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27696 : Upper (D 7) (R 7) [36,320,129,96,136,2] 13 := by
  apply FastRouting.sound _ _ [36,320,129,96,136,2] 13 (by decide) (choices 1) [1,2,16] r27696 c27696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10246
  · exact u10247
  · exact u10248

def b27697 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 133 104 152 48 67 131 259), lower := (rows 37 322 133 104 152 48 64 128 256), losses := [] }

theorem u27697 : Upper (D 7) (R 7) [36,320,129,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27697 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27698 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 322 134 11 56 33 208 208 464), lower := (rows 37 322 134 11 56 33 64 128 256), losses := [] }

theorem u27698 : Upper (D 7) (R 7) [36,320,130,3,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27699 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 57, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 322 134 11 56 48 193 193 449), lower := (rows 37 322 134 11 56 48 64 128 256), losses := [] }

theorem u27699 : Upper (D 7) (R 7) [36,320,130,3,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27699 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27700 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 240, targets := 2 }], pairs := [(0,1),(0,7),(4,0),(4,1)], upper := (rows 37 322 134 11 56 96 209 145 401), lower := (rows 37 322 134 11 56 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 98 64 128 256), good := (rows 36 354 166 58 56 96 96 128 256) },{ target := 1, region := (rows 5 0 4 8 24 122 72 136 264), good := (rows 37 352 165 505 504 96 96 128 256) },{ target := 7, region := (rows 5 2 4 12 29 98 64 0 256), good := (rows 61 354 63 59 56 96 96 0 256) }] }

theorem u27700 : Upper (D 7) (R 7) [36,320,130,3,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27701 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 322 134 11 56 160 81 209 337), lower := (rows 37 322 134 11 56 160 64 128 256), losses := [] }

theorem u27701 : Upper (D 7) (R 7) [36,320,130,3,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27702 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 322 134 11 81 40 240 176 432), lower := (rows 37 322 134 11 81 40 64 128 256), losses := [] }

theorem u27702 : Upper (D 7) (R 7) [36,320,130,3,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27702 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27703 : Route 9 := (fun mask => (mask,id))

def c27703 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27703 : Upper (D 7) (R 7) [36,320,130,3,65,16] 13 := by
  apply FastRouting.sound _ _ [36,320,130,3,65,16] 13 (by decide) (choices 1) [8,32,128] r27703 c27703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10249
  · exact u10250
  · exact u10251

def b27704 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 322 134 11 81 160 120 184 312), lower := (rows 37 322 134 11 81 160 64 128 256), losses := [] }

theorem u27704 : Upper (D 7) (R 7) [36,320,130,3,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27705 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 322 134 11 88 33 240 176 432), lower := (rows 37 322 134 11 88 33 64 128 256), losses := [] }

theorem u27705 : Upper (D 7) (R 7) [36,320,130,3,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27706 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 240, targets := 2 }], pairs := [(0,6),(2,6),(4,1)], upper := (rows 37 322 134 11 88 48 225 161 417), lower := (rows 37 322 134 11 88 48 64 128 256), losses := [{ target := 6, region := (rows 17 2 12 8 16 48 0 177 305), good := (rows 421 258 134 399 445 433 0 128 256) }] }

theorem u27706 : Upper (D 7) (R 7) [36,320,130,3,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27706 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27707 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 322 134 11 88 160 113 177 305), lower := (rows 37 322 134 11 88 160 64 128 256), losses := [] }

theorem u27707 : Upper (D 7) (R 7) [36,320,130,3,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27708 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 322 134 11 112 33 216 152 408), lower := (rows 37 322 134 11 112 33 64 128 256), losses := [] }

theorem u27708 : Upper (D 7) (R 7) [36,320,130,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27709 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 322 134 11 112 40 209 145 401), lower := (rows 37 322 134 11 112 40 64 128 256), losses := [] }

theorem u27709 : Upper (D 7) (R 7) [36,320,130,3,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27709 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27710 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 134 11 112 48 201 137 393), lower := (rows 37 322 134 11 112 48 64 128 256), losses := [] }

theorem u27710 : Upper (D 7) (R 7) [36,320,130,3,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27710 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27711 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 322 134 11 112 160 89 153 281), lower := (rows 37 322 134 11 112 160 64 128 256), losses := [] }

theorem u27711 : Upper (D 7) (R 7) [36,320,130,3,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27712 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 322 134 11 145 40 112 240 368), lower := (rows 37 322 134 11 145 40 64 128 256), losses := [] }

theorem u27712 : Upper (D 7) (R 7) [36,320,130,3,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27712 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27713 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 322 134 11 145 48 104 232 360), lower := (rows 37 322 134 11 145 48 64 128 256), losses := [] }

theorem u27713 : Upper (D 7) (R 7) [36,320,130,3,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27713 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27714 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 3, region := 240, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,1)], upper := (rows 37 322 134 11 145 96 120 184 312), lower := (rows 37 322 134 11 145 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 28 106 72 136 264), good := (rows 53 352 181 505 145 96 96 128 256) }] }

theorem u27714 : Upper (D 7) (R 7) [36,320,130,3,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27715 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 57, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,6),(4,6)], upper := (rows 37 322 134 11 152 33 112 240 368), lower := (rows 37 322 134 11 152 33 64 128 256), losses := [] }

theorem u27715 : Upper (D 7) (R 7) [36,320,130,3,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27716 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 322 134 11 152 48 97 225 353), lower := (rows 37 322 134 11 152 48 64 128 256), losses := [] }

theorem u27716 : Upper (D 7) (R 7) [36,320,130,3,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27716 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27717 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 240, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,1)], upper := (rows 37 322 134 11 152 96 113 177 305), lower := (rows 37 322 134 11 152 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 24 122 72 136 264), good := (rows 37 352 165 505 504 96 96 128 256) },{ target := 7, region := (rows 5 2 4 12 16 98 64 0 256), good := (rows 45 354 47 43 24 96 96 0 256) }] }

theorem u27717 : Upper (D 7) (R 7) [36,320,130,3,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27718 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 57, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(3,6),(4,6)], upper := (rows 37 322 134 11 176 33 88 216 344), lower := (rows 37 322 134 11 176 33 64 128 256), losses := [] }

theorem u27718 : Upper (D 7) (R 7) [36,320,130,3,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27719 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 322 134 11 176 40 81 209 337), lower := (rows 37 322 134 11 176 40 64 128 256), losses := [] }

theorem u27719 : Upper (D 7) (R 7) [36,320,130,3,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27719 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u27719
end Delivery.IrregularNine14.P07
