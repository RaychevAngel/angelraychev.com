import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0181
import IrregularNine14P07C0182

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28800 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 450, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(1,5)], upper := (rows 97 262 13 26 176 33 194 194 450), lower := (rows 97 262 13 26 176 33 64 128 256), losses := [] }

theorem u28800 : Upper (D 7) (R 7) [96,260,9,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28801 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 209, targets := 2 },{ cop := 2, region := 450, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 97 262 13 26 176 34 193 193 449), lower := (rows 97 262 13 26 176 34 64 128 256), losses := [{ target := 1, region := (rows 49 0 12 8 49 32 125 189 317), good := (rows 497 452 477 477 497 497 64 128 256) }] }

theorem u28801 : Upper (D 7) (R 7) [96,260,9,18,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28802 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 26 176 96 195 131 387), lower := (rows 97 262 13 26 176 96 64 128 256), losses := [] }

theorem u28802 : Upper (D 7) (R 7) [96,260,9,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28803 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 262 13 26 176 160 67 195 323), lower := (rows 97 262 13 26 176 160 64 128 256), losses := [] }

theorem u28803 : Upper (D 7) (R 7) [96,260,9,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28804 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 262 13 42 82 33 208 144 400), lower := (rows 97 262 13 42 82 33 64 128 256), losses := [] }

theorem u28804 : Upper (D 7) (R 7) [96,260,9,34,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28805 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 13 42 82 48 193 129 385), lower := (rows 97 262 13 42 82 48 64 128 256), losses := [] }

theorem u28805 : Upper (D 7) (R 7) [96,260,9,34,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28805 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28806 : Route 9 := (fun mask => (mask,id))

def c28806 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28806 : Upper (D 7) (R 7) [96,260,9,34,66,128] 13 := by
  apply FastRouting.sound _ _ [96,260,9,34,66,128] 13 (by decide) (choices 1) [1,16,128] r28806 c28806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10902
  · exact u10903
  · exact u10904

def b28807 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 209, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 262 13 42 145 34 208 208 464), lower := (rows 97 262 13 42 145 34 64 128 256), losses := [] }

theorem u28807 : Upper (D 7) (R 7) [96,260,9,34,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28808 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 97 262 13 42 145 48 194 194 450), lower := (rows 97 262 13 42 145 48 64 128 256), losses := [] }

theorem u28808 : Upper (D 7) (R 7) [96,260,9,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28808 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28809 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 42 145 96 210 146 402), lower := (rows 97 262 13 42 145 96 64 128 256), losses := [] }

theorem u28809 : Upper (D 7) (R 7) [96,260,9,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28810 : Route 9 := (fun mask => (mask,id))

def c28810 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28810 : Upper (D 7) (R 7) [96,260,9,34,129,128] 13 := by
  apply FastRouting.sound _ _ [96,260,9,34,129,128] 13 (by decide) (choices 1) [2,16] r28810 c28810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10905
  · exact u10906

def b28811 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 262 13 42 146 33 208 208 464), lower := (rows 97 262 13 42 146 33 64 128 256), losses := [] }

theorem u28811 : Upper (D 7) (R 7) [96,260,9,34,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28812 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 97 262 13 42 146 48 193 193 449), lower := (rows 97 262 13 42 146 48 64 128 256), losses := [] }

theorem u28812 : Upper (D 7) (R 7) [96,260,9,34,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28812 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28813 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 42 146 96 209 145 401), lower := (rows 97 262 13 42 146 96 64 128 256), losses := [] }

theorem u28813 : Upper (D 7) (R 7) [96,260,9,34,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28814 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 40, targets := 65 }], pairs := [(1,5),(3,0),(3,6),(4,5)], upper := (rows 97 262 13 42 146 160 81 209 337), lower := (rows 97 262 13 42 146 160 64 128 256), losses := [] }

theorem u28814 : Upper (D 7) (R 7) [96,260,9,34,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28815 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 262 13 42 208 33 210 146 402), lower := (rows 97 262 13 42 208 33 64 128 256), losses := [] }

theorem u28815 : Upper (D 7) (R 7) [96,260,9,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28816 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 209, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 97 262 13 42 208 34 209 145 401), lower := (rows 97 262 13 42 208 34 64 128 256), losses := [] }

theorem u28816 : Upper (D 7) (R 7) [96,260,9,34,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28816 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28817 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 13 42 208 48 195 131 387), lower := (rows 97 262 13 42 208 48 64 128 256), losses := [] }

theorem u28817 : Upper (D 7) (R 7) [96,260,9,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28817 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28818 : Route 9 := (fun mask => (mask,id))

def c28818 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28818 : Upper (D 7) (R 7) [96,260,9,34,192,128] 13 := by
  apply FastRouting.sound _ _ [96,260,9,34,192,128] 13 (by decide) (choices 1) [1,2,16] r28818 c28818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10907
  · exact u10908
  · exact u10909

def b28819 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 13 56 82 33 194 130 386), lower := (rows 97 262 13 56 82 33 64 128 256), losses := [] }

theorem u28819 : Upper (D 7) (R 7) [96,260,9,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28820 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 2, region := 386, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(3,7)], upper := (rows 97 262 13 56 82 34 193 129 385), lower := (rows 97 262 13 56 82 34 64 128 256), losses := [] }

theorem u28820 : Upper (D 7) (R 7) [96,260,9,48,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28821 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(3,6),(4,5)], upper := (rows 97 262 13 56 82 160 195 131 387), lower := (rows 97 262 13 56 82 160 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 24 16 166 0 132 260), good := (rows 33 422 431 56 58 160 0 160 256) }] }

theorem u28821 : Upper (D 7) (R 7) [96,260,9,48,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28822 : Route 9 := (fun mask => (mask,id))

def c28822 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28822 : Upper (D 7) (R 7) [96,260,9,48,129,2] 13 := by
  apply FastRouting.sound _ _ [96,260,9,48,129,2] 13 (by decide) (choices 1) [2,128] r28822 c28822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10910
  · exact u10911

def b28823 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 56 145 96 194 130 386), lower := (rows 97 262 13 56 145 96 64 128 256), losses := [] }

theorem u28823 : Upper (D 7) (R 7) [96,260,9,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28824 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1),(3,6)], upper := (rows 97 262 13 56 145 160 66 194 322), lower := (rows 97 262 13 56 145 160 64 128 256), losses := [] }

theorem u28824 : Upper (D 7) (R 7) [96,260,9,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28825 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 262 13 56 146 33 194 194 450), lower := (rows 97 262 13 56 146 33 64 128 256), losses := [] }

theorem u28825 : Upper (D 7) (R 7) [96,260,9,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28826 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(3,0),(3,6),(3,7)], upper := (rows 97 262 13 56 146 34 193 193 449), lower := (rows 97 262 13 56 146 34 64 128 256), losses := [] }

theorem u28826 : Upper (D 7) (R 7) [96,260,9,48,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28827 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 56 146 96 195 131 387), lower := (rows 97 262 13 56 146 96 64 128 256), losses := [] }

theorem u28827 : Upper (D 7) (R 7) [96,260,9,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28828 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 262 13 56 146 160 67 195 323), lower := (rows 97 262 13 56 146 160 64 128 256), losses := [] }

theorem u28828 : Upper (D 7) (R 7) [96,260,9,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28829 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 13 56 208 33 194 130 386), lower := (rows 97 262 13 56 208 33 64 128 256), losses := [] }

theorem u28829 : Upper (D 7) (R 7) [96,260,9,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28830 : Route 9 := (fun mask => (mask,id))

def c28830 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28830 : Upper (D 7) (R 7) [96,260,9,48,192,2] 13 := by
  apply FastRouting.sound _ _ [96,260,9,48,192,2] 13 (by decide) (choices 1) [1,2,128] r28830 c28830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10912
  · exact u10913
  · exact u10914

def b28831 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 97 262 13 56 208 160 67 131 259), lower := (rows 97 262 13 56 208 160 64 128 256), losses := [] }

theorem u28831 : Upper (D 7) (R 7) [96,260,9,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28831 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28832 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 232, targets := 1 },{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1),(1,0),(3,0)], upper := (rows 97 262 13 138 19 48 224 224 480), lower := (rows 97 262 13 138 19 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 28 16 48 113 177 305), good := (rows 480 270 462 138 506 504 64 128 256) }] }

theorem u28832 : Upper (D 7) (R 7) [96,260,9,130,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28832 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28833 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 138 19 96 240 176 432), lower := (rows 97 262 13 138 19 96 64 128 256), losses := [] }

theorem u28833 : Upper (D 7) (R 7) [96,260,9,130,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28834_16 : Upper (D 7) (R 7) [96,260,9,130,3,128,16] 13 :=
  permutation_upper _ _ _ [96,260,9,130,3,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10915

theorem m28834_32 : Upper (D 7) (R 7) [96,260,9,130,3,128,32] 13 :=
  permutation_upper _ _ _ [96,260,9,130,3,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10916

def r28834 : Route 9 := (fun mask => (mask,id))

def c28834 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28834 : Upper (D 7) (R 7) [96,260,9,130,3,128] 13 := by
  apply FastRouting.sound _ _ [96,260,9,130,3,128] 13 (by decide) (choices 1) [16,32] r28834 c28834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28834_16
  · exact m28834_32

def b28835 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 200, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(3,0),(3,5)], upper := (rows 97 262 13 138 50 33 208 208 464), lower := (rows 97 262 13 138 50 33 64 128 256), losses := [] }

theorem u28835 : Upper (D 7) (R 7) [96,260,9,130,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28836 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 13 138 50 48 193 193 449), lower := (rows 97 262 13 138 50 48 64 128 256), losses := [] }

theorem u28836 : Upper (D 7) (R 7) [96,260,9,130,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28836 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28837 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 138 50 96 209 145 401), lower := (rows 97 262 13 138 50 96 64 128 256), losses := [] }

theorem u28837 : Upper (D 7) (R 7) [96,260,9,130,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28838 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 65 },{ cop := 4, region := 65, targets := 2 },{ cop := 4, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(4,0),(4,6)], upper := (rows 97 262 13 138 50 160 81 209 337), lower := (rows 97 262 13 138 50 160 64 128 256), losses := [] }

theorem u28838 : Upper (D 7) (R 7) [96,260,9,130,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28839 : Route 9 := (fun mask => (mask,id))

def c28839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28839 : Upper (D 7) (R 7) [96,260,9,130,129,2] 13 := by
  apply FastRouting.sound _ _ [96,260,9,130,129,2] 13 (by decide) (choices 1) [16,32] r28839 c28839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10917
  · exact u10918

theorem m28840_2 : Upper (D 7) (R 7) [96,260,9,130,129,16,2] 13 :=
  permutation_upper _ _ _ [96,260,9,130,129,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10917

def r28840 : Route 9 := (fun mask => (mask,id))

def c28840 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28840 : Upper (D 7) (R 7) [96,260,9,130,129,16] 13 := by
  apply FastRouting.sound _ _ [96,260,9,130,129,16] 13 (by decide) (choices 1) [2,32] r28840 c28840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28840_2
  · exact u10919

def b28841 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 138 145 96 114 178 306), lower := (rows 97 262 13 138 145 96 64 128 256), losses := [] }

theorem u28841 : Upper (D 7) (R 7) [96,260,9,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28842 : Route 9 := (fun mask => (mask,id))

def c28842 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28842 : Upper (D 7) (R 7) [96,260,9,130,160,1] 13 := by
  apply FastRouting.sound _ _ [96,260,9,130,160,1] 13 (by decide) (choices 1) [2,16] r28842 c28842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10920
  · exact u10921

def b28843 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 65 },{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1),(4,0),(4,1),(4,6)], upper := (rows 97 262 13 138 176 34 81 209 337), lower := (rows 97 262 13 138 176 34 64 128 256), losses := [] }

theorem u28843 : Upper (D 7) (R 7) [96,260,9,130,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28844 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 13 138 176 48 67 195 323), lower := (rows 97 262 13 138 176 48 64 128 256), losses := [] }

theorem u28844 : Upper (D 7) (R 7) [96,260,9,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28844 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28845 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 138 176 96 83 147 275), lower := (rows 97 262 13 138 176 96 64 128 256), losses := [] }

theorem u28845 : Upper (D 7) (R 7) [96,260,9,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28846 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 482, targets := 1 },{ cop := 4, region := 232, targets := 1 },{ cop := 5, region := 193, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 97 262 13 152 19 34 224 224 480), lower := (rows 97 262 13 152 19 34 64 128 256), losses := [{ target := 1, region := (rows 33 0 20 24 16 32 97 161 289), good := (rows 481 260 461 156 477 481 64 128 256) }] }

theorem u28846 : Upper (D 7) (R 7) [96,260,9,144,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28847 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 152 19 96 226 162 418), lower := (rows 97 262 13 152 19 96 64 128 256), losses := [] }

theorem u28847 : Upper (D 7) (R 7) [96,260,9,144,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28848_2 : Upper (D 7) (R 7) [96,260,9,144,3,128,2] 13 :=
  permutation_upper _ _ _ [96,260,9,144,3,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10922

theorem m28848_32 : Upper (D 7) (R 7) [96,260,9,144,3,128,32] 13 :=
  permutation_upper _ _ _ [96,260,9,144,3,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10923

def r28848 : Route 9 := (fun mask => (mask,id))

def c28848 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28848 : Upper (D 7) (R 7) [96,260,9,144,3,128] 13 := by
  apply FastRouting.sound _ _ [96,260,9,144,3,128] 13 (by decide) (choices 1) [2,32] r28848 c28848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28848_2
  · exact m28848_32

def b28849 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 450, targets := 33 },{ cop := 4, region := 200, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 97 262 13 152 50 33 194 194 450), lower := (rows 97 262 13 152 50 33 64 128 256), losses := [] }

theorem u28849 : Upper (D 7) (R 7) [96,260,9,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28850 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 193, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 97 262 13 152 50 34 193 193 449), lower := (rows 97 262 13 152 50 34 64 128 256), losses := [] }

theorem u28850 : Upper (D 7) (R 7) [96,260,9,144,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28851 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 152 50 96 195 131 387), lower := (rows 97 262 13 152 50 96 64 128 256), losses := [] }

theorem u28851 : Upper (D 7) (R 7) [96,260,9,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28852 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 322, targets := 32 },{ cop := 2, region := 322, targets := 128 },{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(2,7)], upper := (rows 97 262 13 152 50 160 67 195 323), lower := (rows 97 262 13 152 50 160 64 128 256), losses := [{ target := 7, region := (rows 17 14 12 8 16 32 92 0 284), good := (rows 97 326 335 351 371 32 64 0 256) }] }

theorem u28852 : Upper (D 7) (R 7) [96,260,9,144,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28853 : Route 9 := (fun mask => (mask,id))

def c28853 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28853 : Upper (D 7) (R 7) [96,260,9,160,3,2] 13 := by
  apply FastRouting.sound _ _ [96,260,9,160,3,2] 13 (by decide) (choices 1) [16,128] r28853 c28853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10924
  · exact u10925

def b28854 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 97 262 13 168 19 48 194 194 450), lower := (rows 97 262 13 168 19 48 64 128 256), losses := [] }

theorem u28854 : Upper (D 7) (R 7) [96,260,9,160,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28854 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28855 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 168 19 96 210 146 402), lower := (rows 97 262 13 168 19 96 64 128 256), losses := [] }

theorem u28855 : Upper (D 7) (R 7) [96,260,9,160,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28856 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 97 262 13 168 19 160 82 210 338), lower := (rows 97 262 13 168 19 160 64 128 256), losses := [] }

theorem u28856 : Upper (D 7) (R 7) [96,260,9,160,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28857 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 262 13 168 82 33 210 146 402), lower := (rows 97 262 13 168 82 33 64 128 256), losses := [] }

theorem u28857 : Upper (D 7) (R 7) [96,260,9,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28858 : Route 9 := (fun mask => (mask,id))

def c28858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28858 : Upper (D 7) (R 7) [96,260,9,160,66,2] 13 := by
  apply FastRouting.sound _ _ [96,260,9,160,66,2] 13 (by decide) (choices 1) [1,16,128] r28858 c28858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10926
  · exact u10927
  · exact u10928

def b28859 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 13 168 82 48 195 131 387), lower := (rows 97 262 13 168 82 48 64 128 256), losses := [] }

theorem u28859 : Upper (D 7) (R 7) [96,260,9,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28859 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u28859
end Delivery.IrregularNine14.P07
