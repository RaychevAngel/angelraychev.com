import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0171

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27780 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 322 134 42 208 33 89 153 281), lower := (rows 37 322 134 42 208 33 64 128 256), losses := [] }

theorem u27780 : Upper (D 7) (R 7) [36,320,130,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27781 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 322 134 42 208 40 81 145 273), lower := (rows 37 322 134 42 208 40 64 128 256), losses := [] }

theorem u27781 : Upper (D 7) (R 7) [36,320,130,34,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27781 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27782 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 133, targets := 64 }], pairs := [(0,6),(1,7),(3,7)], upper := (rows 37 322 134 42 208 48 73 137 265), lower := (rows 37 322 134 42 208 48 64 128 256), losses := [] }

theorem u27782 : Upper (D 7) (R 7) [36,320,130,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27782 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27783 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 322 134 56 81 33 202 138 394), lower := (rows 37 322 134 56 81 33 64 128 256), losses := [] }

theorem u27783 : Upper (D 7) (R 7) [36,320,130,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27784 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 322 134 56 81 34 201 137 393), lower := (rows 37 322 134 56 81 34 64 128 256), losses := [] }

theorem u27784 : Upper (D 7) (R 7) [36,320,130,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27785 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 37 322 134 56 81 40 195 131 387), lower := (rows 37 322 134 56 81 40 64 128 256), losses := [] }

theorem u27785 : Upper (D 7) (R 7) [36,320,130,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27785 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27786 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 134 56 81 160 75 139 267), lower := (rows 37 322 134 56 81 160 64 128 256), losses := [] }

theorem u27786 : Upper (D 7) (R 7) [36,320,130,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27787 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 57, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 322 134 56 145 33 74 202 330), lower := (rows 37 322 134 56 145 33 64 128 256), losses := [] }

theorem u27787 : Upper (D 7) (R 7) [36,320,130,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27788 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 57, targets := 64 },{ cop := 0, region := 216, targets := 2 }], pairs := [(0,6),(3,1),(3,6),(4,6)], upper := (rows 37 322 134 56 145 34 73 201 329), lower := (rows 37 322 134 56 145 34 64 128 256), losses := [] }

theorem u27788 : Upper (D 7) (R 7) [36,320,130,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27789 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 57, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 37 322 134 56 145 40 67 195 323), lower := (rows 37 322 134 56 145 40 64 128 256), losses := [] }

theorem u27789 : Upper (D 7) (R 7) [36,320,130,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27789 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27790 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(0,1),(1,7),(3,1),(3,7)], upper := (rows 37 322 134 56 145 96 75 139 267), lower := (rows 37 322 134 56 145 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 13 20 98 64 128 256), good := (rows 61 352 189 56 153 96 96 128 256) }] }

theorem u27790 : Upper (D 7) (R 7) [36,320,130,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27791 : Route 9 := (fun mask => (mask,id))

def c27791 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27791 : Upper (D 7) (R 7) [36,320,130,48,192,1] 13 := by
  apply FastRouting.sound _ _ [36,320,130,48,192,1] 13 (by decide) (choices 1) [1,2,8] r27791 c27791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10261
  · exact u10262
  · exact u10263

def b27792 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 322 134 56 208 34 73 137 265), lower := (rows 37 322 134 56 208 34 64 128 256), losses := [] }

theorem u27792 : Upper (D 7) (R 7) [36,320,130,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27793 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 37 322 134 56 208 40 67 131 259), lower := (rows 37 322 134 56 208 40 64 128 256), losses := [] }

theorem u27793 : Upper (D 7) (R 7) [36,320,130,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27793 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27794 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 49, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 322 134 73 145 34 120 184 312), lower := (rows 37 322 134 73 145 34 64 128 256), losses := [] }

theorem u27794 : Upper (D 7) (R 7) [36,320,130,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27795 : Route 9 := (fun mask => (mask,id))

def c27795 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27795 : Upper (D 7) (R 7) [36,320,130,65,129,8] 13 := by
  apply FastRouting.sound _ _ [36,320,130,65,129,8] 13 (by decide) (choices 1) [2,16,32] r27795 c27795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10264
  · exact u10265
  · exact u10266

def b27796 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 322 134 73 145 48 106 170 298), lower := (rows 37 322 134 73 145 48 64 128 256), losses := [] }

theorem u27796 : Upper (D 7) (R 7) [36,320,130,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27796 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27797 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 322 134 73 152 33 114 178 306), lower := (rows 37 322 134 73 152 33 64 128 256), losses := [{ target := 7, region := (rows 5 18 4 8 16 45 80 0 272), good := (rows 37 322 39 105 378 33 64 0 256) }] }

theorem u27797 : Upper (D 7) (R 7) [36,320,130,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27798 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 322 134 73 152 34 113 177 305), lower := (rows 37 322 134 73 152 34 64 128 256), losses := [] }

theorem u27798 : Upper (D 7) (R 7) [36,320,130,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27799 : Route 9 := (fun mask => (mask,id))

def c27799 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27799 : Upper (D 7) (R 7) [36,320,130,65,136,16] 13 := by
  apply FastRouting.sound _ _ [36,320,130,65,136,16] 13 (by decide) (choices 1) [1,2,32] r27799 c27799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10267
  · exact u10268
  · exact u10269

def b27800 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 134 73 176 33 90 154 282), lower := (rows 37 322 134 73 176 33 64 128 256), losses := [] }

theorem u27800 : Upper (D 7) (R 7) [36,320,130,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27801 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 49, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 322 134 73 176 34 89 153 281), lower := (rows 37 322 134 73 176 34 64 128 256), losses := [] }

theorem u27801 : Upper (D 7) (R 7) [36,320,130,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27802 : Route 9 := (fun mask => (mask,id))

def c27802 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27802 : Upper (D 7) (R 7) [36,320,130,65,160,8] 13 := by
  apply FastRouting.sound _ _ [36,320,130,65,160,8] 13 (by decide) (choices 1) [1,2,16] r27802 c27802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10270
  · exact u10271
  · exact u10272

def b27803 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 322 134 73 176 48 75 139 267), lower := (rows 37 322 134 73 176 48 64 128 256), losses := [] }

theorem u27803 : Upper (D 7) (R 7) [36,320,130,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27803 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27804 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 134 88 145 33 106 170 298), lower := (rows 37 322 134 88 145 33 64 128 256), losses := [] }

theorem u27804 : Upper (D 7) (R 7) [36,320,130,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27805 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 49, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 322 134 88 145 34 105 169 297), lower := (rows 37 322 134 88 145 34 64 128 256), losses := [] }

theorem u27805 : Upper (D 7) (R 7) [36,320,130,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27805 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27806 : Route 9 := (fun mask => (mask,id))

def c27806 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27806 : Upper (D 7) (R 7) [36,320,130,80,129,8] 13 := by
  apply FastRouting.sound _ _ [36,320,130,80,129,8] 13 (by decide) (choices 1) [1,2,32] r27806 c27806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10273
  · exact u10274
  · exact u10275

def b27807 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 134 88 176 33 75 139 267), lower := (rows 37 322 134 88 176 33 64 128 256), losses := [] }

theorem u27807 : Upper (D 7) (R 7) [36,320,130,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27808 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 49, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,6)], upper := (rows 37 322 134 88 176 34 73 137 265), lower := (rows 37 322 134 88 176 34 64 128 256), losses := [] }

theorem u27808 : Upper (D 7) (R 7) [36,320,130,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27809 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 37 322 134 88 176 40 67 131 259), lower := (rows 37 322 134 88 176 40 64 128 256), losses := [] }

theorem u27809 : Upper (D 7) (R 7) [36,320,130,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27809 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27810 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 134 104 145 33 90 154 282), lower := (rows 37 322 134 104 145 33 64 128 256), losses := [] }

theorem u27810 : Upper (D 7) (R 7) [36,320,130,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27811 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 40, targets := 129 }], pairs := [(3,0),(3,1),(3,7),(4,1)], upper := (rows 37 322 134 104 145 34 89 153 281), lower := (rows 37 322 134 104 145 34 64 128 256), losses := [] }

theorem u27811 : Upper (D 7) (R 7) [36,320,130,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27812 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 134 104 145 40 83 147 275), lower := (rows 37 322 134 104 145 40 64 128 256), losses := [] }

theorem u27812 : Upper (D 7) (R 7) [36,320,130,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27812 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27813 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 322 134 104 145 48 75 139 267), lower := (rows 37 322 134 104 145 48 64 128 256), losses := [] }

theorem u27813 : Upper (D 7) (R 7) [36,320,130,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27813 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27814 : Route 9 := (fun mask => (mask,id))

def c27814 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27814 : Upper (D 7) (R 7) [36,320,130,96,136,1] 13 := by
  apply FastRouting.sound _ _ [36,320,130,96,136,1] 13 (by decide) (choices 1) [1,2,16] r27814 c27814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10276
  · exact u10277
  · exact u10278

def b27815 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 40, targets := 129 }], pairs := [(3,0),(3,1),(3,7),(4,1)], upper := (rows 37 322 134 104 152 34 81 145 273), lower := (rows 37 322 134 104 152 34 64 128 256), losses := [] }

theorem u27815 : Upper (D 7) (R 7) [36,320,130,96,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27816 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 37 322 134 104 152 48 67 131 259), lower := (rows 37 322 134 104 152 48 64 128 256), losses := [] }

theorem u27816 : Upper (D 7) (R 7) [36,320,130,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27816 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27817 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 140 11 50 33 208 208 464), lower := (rows 37 322 140 11 50 33 64 128 256), losses := [] }

theorem u27817 : Upper (D 7) (R 7) [36,320,136,3,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27818 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 140 11 50 48 193 193 449), lower := (rows 37 322 140 11 50 48 64 128 256), losses := [] }

theorem u27818 : Upper (D 7) (R 7) [36,320,136,3,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27818 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27819 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 141, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 322 140 11 50 96 209 145 401), lower := (rows 37 322 140 11 50 96 64 128 256), losses := [] }

theorem u27819 : Upper (D 7) (R 7) [36,320,136,3,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27820 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 140 11 50 160 81 209 337), lower := (rows 37 322 140 11 50 160 64 128 256), losses := [] }

theorem u27820 : Upper (D 7) (R 7) [36,320,136,3,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27821 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 208, targets := 2 },{ cop := 4, region := 418, targets := 1 }], pairs := [(0,6),(1,0),(2,1),(4,1)], upper := (rows 37 322 140 11 81 34 240 176 432), lower := (rows 37 322 140 11 81 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 25 32 65 129 257), good := (rows 501 320 156 477 465 32 64 128 256) },{ target := 6, region := (rows 5 2 4 8 16 42 0 128 256), good := (rows 37 290 173 43 17 34 0 128 256) }] }

theorem u27821 : Upper (D 7) (R 7) [36,320,136,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27822 : Route 9 := (fun mask => (mask,id))

def c27822 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27822 : Upper (D 7) (R 7) [36,320,136,3,65,16] 13 := by
  apply FastRouting.sound _ _ [36,320,136,3,65,16] 13 (by decide) (choices 1) [2,32,128] r27822 c27822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10279
  · exact u10280
  · exact u10281

def b27823 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 140 11 81 160 114 178 306), lower := (rows 37 322 140 11 81 160 64 128 256), losses := [] }

theorem u27823 : Upper (D 7) (R 7) [36,320,136,3,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27824 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 140 11 112 33 210 146 402), lower := (rows 37 322 140 11 112 33 64 128 256), losses := [] }

theorem u27824 : Upper (D 7) (R 7) [36,320,136,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27825 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 48, targets := 129 },{ cop := 0, region := 208, targets := 2 }], pairs := [(2,1),(4,0),(4,1),(4,7)], upper := (rows 37 322 140 11 112 34 209 145 401), lower := (rows 37 322 140 11 112 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 32 73 137 265), good := (rows 501 320 460 477 112 32 64 128 256) }] }

theorem u27825 : Upper (D 7) (R 7) [36,320,136,3,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27826 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 140 11 112 48 195 131 387), lower := (rows 37 322 140 11 112 48 64 128 256), losses := [] }

theorem u27826 : Upper (D 7) (R 7) [36,320,136,3,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27826 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27827 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 322 140 11 112 160 83 147 275), lower := (rows 37 322 140 11 112 160 64 128 256), losses := [] }

theorem u27827 : Upper (D 7) (R 7) [36,320,136,3,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27828 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 4, region := 354, targets := 1 }], pairs := [(1,0),(1,7),(3,7),(4,1)], upper := (rows 37 322 140 11 145 34 112 240 368), lower := (rows 37 322 140 11 145 34 64 128 256), losses := [] }

theorem u27828 : Upper (D 7) (R 7) [36,320,136,3,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27829 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 322 140 11 145 48 98 226 354), lower := (rows 37 322 140 11 145 48 64 128 256), losses := [] }

theorem u27829 : Upper (D 7) (R 7) [36,320,136,3,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27829 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27830 : Route 9 := (fun mask => (mask,id))

def c27830 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27830 : Upper (D 7) (R 7) [36,320,136,3,129,64] 13 := by
  apply FastRouting.sound _ _ [36,320,136,3,129,64] 13 (by decide) (choices 1) [2,16,32] r27830 c27830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10282
  · exact u10283
  · exact u10284

def b27831 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 140 11 146 33 112 240 368), lower := (rows 37 322 140 11 146 33 64 128 256), losses := [] }

theorem u27831 : Upper (D 7) (R 7) [36,320,136,3,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27831 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27832 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 322 140 11 146 48 97 225 353), lower := (rows 37 322 140 11 146 48 64 128 256), losses := [] }

theorem u27832 : Upper (D 7) (R 7) [36,320,136,3,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27832 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27833 : Route 9 := (fun mask => (mask,id))

def c27833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27833 : Upper (D 7) (R 7) [36,320,136,3,130,64] 13 := by
  apply FastRouting.sound _ _ [36,320,136,3,130,64] 13 (by decide) (choices 1) [1,16,32] r27833 c27833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10285
  · exact u10286
  · exact u10287

def b27834 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 140 11 176 33 82 210 338), lower := (rows 37 322 140 11 176 33 64 128 256), losses := [] }

theorem u27834 : Upper (D 7) (R 7) [36,320,136,3,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27835 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(2,1),(4,0),(4,1)], upper := (rows 37 322 140 11 176 34 81 209 337), lower := (rows 37 322 140 11 176 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 42 64 128 256), good := (rows 52 354 188 42 176 34 64 128 256) },{ target := 1, region := (rows 1 0 12 8 17 32 73 137 265), good := (rows 501 320 460 477 176 32 64 128 256) },{ target := 6, region := (rows 5 2 4 8 20 42 0 128 256), good := (rows 53 290 189 43 176 34 0 128 256) }] }

theorem u27835 : Upper (D 7) (R 7) [36,320,136,3,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27836 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 322 140 11 176 48 67 195 323), lower := (rows 37 322 140 11 176 48 64 128 256), losses := [] }

theorem u27836 : Upper (D 7) (R 7) [36,320,136,3,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27836 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27837 : Route 9 := (fun mask => (mask,id))

def c27837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27837 : Upper (D 7) (R 7) [36,320,136,3,160,64] 13 := by
  apply FastRouting.sound _ _ [36,320,136,3,160,64] 13 (by decide) (choices 1) [1,2,16] r27837 c27837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10288
  · exact u10289
  · exact u10290

def b27838 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 140 11 208 33 114 178 306), lower := (rows 37 322 140 11 208 33 64 128 256), losses := [] }

theorem u27838 : Upper (D 7) (R 7) [36,320,136,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27839 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(0,7),(2,1),(4,1)], upper := (rows 37 322 140 11 208 34 113 177 305), lower := (rows 37 322 140 11 208 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 25 32 65 129 257), good := (rows 501 320 156 477 208 32 64 128 256) },{ target := 6, region := (rows 5 2 4 8 16 42 0 128 256), good := (rows 37 290 173 43 144 34 0 128 256) },{ target := 7, region := (rows 5 2 4 8 16 42 64 0 256), good := (rows 37 354 45 43 80 34 64 0 256) }] }

theorem u27839 : Upper (D 7) (R 7) [36,320,136,3,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u27839
end Delivery.IrregularNine14.P07
