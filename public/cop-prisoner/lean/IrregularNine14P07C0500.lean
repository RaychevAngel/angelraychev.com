import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0193
import IrregularNine14P07C0194

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30000 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 60, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 386 28 42 148 34 65 193 321), lower := (rows 97 386 28 42 148 34 64 128 256), losses := [] }

theorem u30000 : Upper (D 7) (R 7) [96,384,24,34,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30001 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 28 42 148 96 67 131 259), lower := (rows 97 386 28 42 148 96 64 128 256), losses := [] }

theorem u30001 : Upper (D 7) (R 7) [96,384,24,34,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30002 : Route 9 := (fun mask => (mask,id))

def c30002 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30002 : Upper (D 7) (R 7) [96,384,24,34,192,1] 13 := by
  apply FastRouting.sound _ _ [96,384,24,34,192,1] 13 (by decide) (choices 1) [1,2,4] r30002 c30002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11622
  · exact u11623
  · exact u11624

def b30003 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 386 28 42 208 34 69 133 261), lower := (rows 97 386 28 42 208 34 64 128 256), losses := [] }

theorem u30003 : Upper (D 7) (R 7) [96,384,24,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30004 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 97 386 28 42 208 36 67 131 259), lower := (rows 97 386 28 42 208 36 64 128 256), losses := [] }

theorem u30004 : Upper (D 7) (R 7) [96,384,24,34,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30004 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30005 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 44, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 97 386 28 44 145 33 66 194 322), lower := (rows 97 386 28 44 145 33 64 128 256), losses := [] }

theorem u30005 : Upper (D 7) (R 7) [96,384,24,36,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30006 : Route 9 := (fun mask => (mask,id))

def c30006 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30006 : Upper (D 7) (R 7) [96,384,24,36,129,2] 13 := by
  apply FastRouting.sound _ _ [96,384,24,36,129,2] 13 (by decide) (choices 1) [1,2] r30006 c30006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11625
  · exact u11626

def b30007 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 386 28 44 145 96 67 131 259), lower := (rows 97 386 28 44 145 96 64 128 256), losses := [] }

theorem u30007 : Upper (D 7) (R 7) [96,384,24,36,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30008 : Route 9 := (fun mask => (mask,id))

def c30008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30008 : Upper (D 7) (R 7) [96,384,34,66,129,1] 13 := by
  apply FastRouting.sound _ _ [96,384,34,66,129,1] 13 (by decide) (choices 1) [4,8,16] r30008 c30008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11627
  · exact u11628
  · exact u11629

def b30009 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 386 38 74 145 36 89 153 281), lower := (rows 97 386 38 74 145 36 64 128 256), losses := [] }

theorem u30009 : Upper (D 7) (R 7) [96,384,34,66,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30009 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30010 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 386 38 74 145 40 85 149 277), lower := (rows 97 386 38 74 145 40 64 128 256), losses := [] }

theorem u30010 : Upper (D 7) (R 7) [96,384,34,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30010 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m30011_1 : Upper (D 7) (R 7) [96,384,34,66,129,16,1] 13 :=
  permutation_upper _ _ _ [96,384,34,66,129,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11629

theorem m30011_4 : Upper (D 7) (R 7) [96,384,34,66,129,16,4] 13 :=
  permutation_upper _ _ _ [96,384,34,66,129,8,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11631

theorem m30011_8 : Upper (D 7) (R 7) [96,384,34,66,129,16,8] 13 :=
  permutation_upper _ _ _ [96,384,34,66,129,4,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11630

def r30011 : Route 9 := (fun mask => (mask,id))

def c30011 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30011 : Upper (D 7) (R 7) [96,384,34,66,129,16] 13 := by
  apply FastRouting.sound _ _ [96,384,34,66,129,16] 13 (by decide) (choices 1) [1,4,8] r30011 c30011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m30011_1
  · exact m30011_4
  · exact m30011_8

def r30012 : Route 9 := (fun mask => (mask,id))

def c30012 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30012 : Upper (D 7) (R 7) [96,384,34,66,132,1] 13 := by
  apply FastRouting.sound _ _ [96,384,34,66,132,1] 13 (by decide) (choices 1) [1,8,16] r30012 c30012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11632
  · exact u11633
  · exact u11634

def b30013 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 386 38 74 148 40 81 145 273), lower := (rows 97 386 38 74 148 40 64 128 256), losses := [] }

theorem u30013 : Upper (D 7) (R 7) [96,384,34,66,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30013 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30014 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 52, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 97 386 38 74 148 48 73 137 265), lower := (rows 97 386 38 74 148 48 64 128 256), losses := [] }

theorem u30014 : Upper (D 7) (R 7) [96,384,34,66,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30014 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30015 : Route 9 := (fun mask => (mask,id))

def c30015 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30015 : Upper (D 7) (R 7) [96,384,34,68,129,1] 13 := by
  apply FastRouting.sound _ _ [96,384,34,68,129,1] 13 (by decide) (choices 1) [2,8,16] r30015 c30015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11635
  · exact u11636
  · exact u11637

def b30016 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 217, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 97 386 38 76 145 34 89 153 281), lower := (rows 97 386 38 76 145 34 64 128 256), losses := [] }

theorem u30016 : Upper (D 7) (R 7) [96,384,34,68,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30017 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 386 38 76 145 40 83 147 275), lower := (rows 97 386 38 76 145 40 64 128 256), losses := [] }

theorem u30017 : Upper (D 7) (R 7) [96,384,34,68,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30017 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30018 : Route 9 := (fun mask => (mask,id))

def c30018 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30018 : Upper (D 7) (R 7) [96,384,34,68,129,16] 13 := by
  apply FastRouting.sound _ _ [96,384,34,68,129,16] 13 (by decide) (choices 1) [1,2,8] r30018 c30018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11638
  · exact u11639
  · exact u11640

def r30019 : Route 9 := (fun mask => (mask,id))

def c30019 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30019 : Upper (D 7) (R 7) [96,384,34,68,136,1] 13 := by
  apply FastRouting.sound _ _ [96,384,34,68,136,1] 13 (by decide) (choices 1) [1,2,16] r30019 c30019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11641
  · exact u11642
  · exact u11643

def b30020 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 217, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 97 386 38 76 152 34 81 145 273), lower := (rows 97 386 38 76 152 34 64 128 256), losses := [] }

theorem u30020 : Upper (D 7) (R 7) [96,384,34,68,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30021 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7),(1,6),(2,6)], upper := (rows 97 386 38 76 152 48 67 131 259), lower := (rows 97 386 38 76 152 48 64 128 256), losses := [] }

theorem u30021 : Upper (D 7) (R 7) [96,384,34,68,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30021 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30022 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(2,6)], upper := (rows 97 386 38 88 145 33 78 142 270), lower := (rows 97 386 38 88 145 33 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 16 49 0 136 264), good := (rows 33 386 38 446 177 33 0 128 256) }] }

theorem u30022 : Upper (D 7) (R 7) [96,384,34,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30023 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 217, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 97 386 38 88 145 34 77 141 269), lower := (rows 97 386 38 88 145 34 64 128 256), losses := [] }

theorem u30023 : Upper (D 7) (R 7) [96,384,34,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30024 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 97 386 38 88 145 36 75 139 267), lower := (rows 97 386 38 88 145 36 64 128 256), losses := [] }

theorem u30024 : Upper (D 7) (R 7) [96,384,34,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30024 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30025 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 386 38 88 145 40 71 135 263), lower := (rows 97 386 38 88 145 40 64 128 256), losses := [] }

theorem u30025 : Upper (D 7) (R 7) [96,384,34,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30025 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30026 : Route 9 := (fun mask => (mask,id))

def c30026 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30026 : Upper (D 7) (R 7) [96,384,34,80,132,1] 13 := by
  apply FastRouting.sound _ _ [96,384,34,80,132,1] 13 (by decide) (choices 1) [1,2,8] r30026 c30026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11644
  · exact u11645
  · exact u11646

def b30027 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 52, targets := 65 }], pairs := [(2,0),(2,6),(4,0),(4,6)], upper := (rows 97 386 38 88 148 34 73 137 265), lower := (rows 97 386 38 88 148 34 64 128 256), losses := [] }

theorem u30027 : Upper (D 7) (R 7) [96,384,34,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30028 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 386 38 88 148 40 67 131 259), lower := (rows 97 386 38 88 148 40 64 128 256), losses := [] }

theorem u30028 : Upper (D 7) (R 7) [96,384,34,80,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30028 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30029 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 386 44 88 145 33 70 134 262), lower := (rows 97 386 44 88 145 33 64 128 256), losses := [] }

theorem u30029 : Upper (D 7) (R 7) [96,384,40,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30030 : Route 9 := (fun mask => (mask,id))

def c30030 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30030 : Upper (D 7) (R 7) [96,384,40,80,129,2] 13 := by
  apply FastRouting.sound _ _ [96,384,40,80,129,2] 13 (by decide) (choices 1) [1,2,4] r30030 c30030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11647
  · exact u11648
  · exact u11649

def b30031 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 386 44 88 145 36 67 131 259), lower := (rows 97 386 44 88 145 36 64 128 256), losses := [] }

theorem u30031 : Upper (D 7) (R 7) [96,384,40,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30031 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30032 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 386 44 88 148 33 67 131 259), lower := (rows 97 386 44 88 148 33 64 128 256), losses := [] }

theorem u30032 : Upper (D 7) (R 7) [96,384,40,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30033 : Route 9 := (fun mask => (mask,id))

def c30033 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30033 : Upper (D 7) (R 7) [96,384,40,80,132,2] 13 := by
  apply FastRouting.sound _ _ [96,384,40,80,132,2] 13 (by decide) (choices 1) [1,2] r30033 c30033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11650
  · exact u11651

def b30034 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 23, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 21 104 50 480 448 448 448), lower := (rows 7 11 21 104 50 32 64 128 256), losses := [] }

theorem u30034 : Upper (D 7) (R 7) [6,9,17,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30035 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 23, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 21 104 112 418 450 386 386), lower := (rows 7 11 21 104 112 32 64 128 256), losses := [] }

theorem u30035 : Upper (D 7) (R 7) [6,9,17,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30036 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 11 21 104 146 480 480 480 480), lower := (rows 7 11 21 104 146 32 64 128 256), losses := [] }

theorem u30036 : Upper (D 7) (R 7) [6,9,17,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30037 : Route 9 := (fun mask => (mask,id))

def c30037 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30037 : Upper (D 7) (R 7) [6,9,17,96,160] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,160] 13 (by decide) (choices 1) [2,64,128,256] r30037 c30037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11652
  · exact u11653
  · exact u11654
  · exact u11655

def b30038 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 11 21 104 274 224 224 224 480), lower := (rows 7 11 21 104 274 32 64 128 256), losses := [] }

theorem u30038 : Upper (D 7) (R 7) [6,9,17,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30039 : Route 9 := (fun mask => (mask,id))

def c30039 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30039 : Upper (D 7) (R 7) [6,9,17,96,288] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,288] 13 (by decide) (choices 1) [2,64,128] r30039 c30039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11656
  · exact u11657
  · exact u11658

def r30040 : Route 9 := (fun mask => (mask,id))

def c30040 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30040 : Upper (D 7) (R 7) [6,9,17,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,384] 13 (by decide) (choices 1) [2,64,128] r30040 c30040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11659
  · exact u11660
  · exact u11661

def b30041 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 23, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 11 21 296 50 224 192 192 448), lower := (rows 7 11 21 296 50 32 64 128 256), losses := [] }

theorem u30041 : Upper (D 7) (R 7) [6,9,17,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30042 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 7 11 21 296 82 224 224 224 480), lower := (rows 7 11 21 296 82 32 64 128 256), losses := [] }

theorem u30042 : Upper (D 7) (R 7) [6,9,17,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30043 : Route 9 := (fun mask => (mask,id))

def c30043 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30043 : Upper (D 7) (R 7) [6,9,17,288,96] 13 := by
  apply FastRouting.sound _ _ [6,9,17,288,96] 13 (by decide) (choices 1) [2,64,128] r30043 c30043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11662
  · exact u11663
  · exact u11664

def r30044 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30044 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30044 : Upper (D 7) (R 7) [6,9,17,288,192] 13 := by
  apply FastRouting.sound _ _ [6,9,17,288,192] 13 (by decide) (choices 1) [2,64] r30044 c30044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11665
  · exact u11666

def b30045 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 11 37 88 50 480 448 448 448), lower := (rows 7 11 37 88 50 32 64 128 256), losses := [] }

theorem u30045 : Upper (D 7) (R 7) [6,9,33,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30046 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 423, targets := 64 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 11 37 88 82 416 480 416 416), lower := (rows 7 11 37 88 82 32 64 128 256), losses := [] }

theorem u30046 : Upper (D 7) (R 7) [6,9,33,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30047 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 37 88 112 418 450 386 386), lower := (rows 7 11 37 88 112 32 64 128 256), losses := [] }

theorem u30047 : Upper (D 7) (R 7) [6,9,33,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30048 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 484, targets := 2 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,1),(3,0),(3,1),(4,0)], upper := (rows 7 11 37 88 146 480 480 480 480), lower := (rows 7 11 37 88 146 32 64 128 256), losses := [] }

theorem u30048 : Upper (D 7) (R 7) [6,9,33,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30049 : Route 9 := (fun mask => (mask,id))

def c30049 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30049 : Upper (D 7) (R 7) [6,9,33,80,160] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80,160] 13 (by decide) (choices 1) [2,64,128,256] r30049 c30049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11667
  · exact u11668
  · exact u11669
  · exact u11670

def b30050 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 11 37 88 208 418 482 418 418), lower := (rows 7 11 37 88 208 32 64 128 256), losses := [] }

theorem u30050 : Upper (D 7) (R 7) [6,9,33,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30051 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 228, targets := 2 },{ cop := 4, region := 232, targets := 2 }], pairs := [(2,1),(3,0),(3,1),(4,0)], upper := (rows 7 11 37 88 274 224 224 224 480), lower := (rows 7 11 37 88 274 32 64 128 256), losses := [] }

theorem u30051 : Upper (D 7) (R 7) [6,9,33,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30052 : Route 9 := (fun mask => (mask,id))

def c30052 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30052 : Upper (D 7) (R 7) [6,9,33,80,288] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80,288] 13 (by decide) (choices 1) [2,64,128] r30052 c30052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11671
  · exact u11672
  · exact u11673

def b30053 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 11 37 88 336 162 226 162 418), lower := (rows 7 11 37 88 336 32 64 128 256), losses := [] }

theorem u30053 : Upper (D 7) (R 7) [6,9,33,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30054 : Route 9 := (fun mask => (mask,id))

def c30054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30054 : Upper (D 7) (R 7) [6,9,33,80,384] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80,384] 13 (by decide) (choices 1) [2,64,128] r30054 c30054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11674
  · exact u11675
  · exact u11676

def b30055 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 11 37 200 50 496 464 464 464), lower := (rows 7 11 37 200 50 32 64 128 256), losses := [] }

theorem u30055 : Upper (D 7) (R 7) [6,9,33,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30056 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(4,0)], upper := (rows 7 11 37 200 82 432 496 432 432), lower := (rows 7 11 37 200 82 32 64 128 256), losses := [] }

theorem u30056 : Upper (D 7) (R 7) [6,9,33,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30057 : Route 9 := (fun mask => (mask,id))

def c30057 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u30057 : Upper (D 7) (R 7) [6,9,33,192,96] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,96] 13 (by decide) (choices 1) [2,16,128,256] r30057 c30057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11677
  · exact u11678
  · exact u11679
  · exact u11680

def b30058 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 11 37 200 208 306 370 434 306), lower := (rows 7 11 37 200 208 32 64 128 256), losses := [] }

theorem u30058 : Upper (D 7) (R 7) [6,9,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30059 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30059 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30059 : Upper (D 7) (R 7) [6,9,33,192,258] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,258] 13 (by decide) (choices 1) [16,64] r30059 c30059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11681
  · exact u11682

#print axioms u30059
end Delivery.IrregularNine14.P07
