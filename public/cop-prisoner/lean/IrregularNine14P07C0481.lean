import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0182

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28860 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 97 262 13 168 82 160 83 147 275), lower := (rows 97 262 13 168 82 160 64 128 256), losses := [] }

theorem u28860 : Upper (D 7) (R 7) [96,260,9,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28861 : Route 9 := (fun mask => (mask,id))

def c28861 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28861 : Upper (D 7) (R 7) [96,260,9,160,129,2] 13 := by
  apply FastRouting.sound _ _ [96,260,9,160,129,2] 13 (by decide) (choices 1) [2,16] r28861 c28861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10929
  · exact u10930

def b28862 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 97 262 13 168 145 48 66 194 322), lower := (rows 97 262 13 168 145 48 64 128 256), losses := [] }

theorem u28862 : Upper (D 7) (R 7) [96,260,9,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28862 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28863 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 168 145 96 82 146 274), lower := (rows 97 262 13 168 145 96 64 128 256), losses := [] }

theorem u28863 : Upper (D 7) (R 7) [96,260,9,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28864 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 262 13 168 146 33 82 210 338), lower := (rows 97 262 13 168 146 33 64 128 256), losses := [] }

theorem u28864 : Upper (D 7) (R 7) [96,260,9,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28865 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 40, targets := 65 }], pairs := [(1,5),(3,0),(3,6),(4,5)], upper := (rows 97 262 13 168 146 34 81 209 337), lower := (rows 97 262 13 168 146 34 64 128 256), losses := [] }

theorem u28865 : Upper (D 7) (R 7) [96,260,9,160,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28866 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 262 13 168 146 48 67 195 323), lower := (rows 97 262 13 168 146 48 64 128 256), losses := [] }

theorem u28866 : Upper (D 7) (R 7) [96,260,9,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28866 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28867 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 168 146 96 83 147 275), lower := (rows 97 262 13 168 146 96 64 128 256), losses := [] }

theorem u28867 : Upper (D 7) (R 7) [96,260,9,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28868 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 262 13 168 208 33 82 146 274), lower := (rows 97 262 13 168 208 33 64 128 256), losses := [] }

theorem u28868 : Upper (D 7) (R 7) [96,260,9,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28869 : Route 9 := (fun mask => (mask,id))

def c28869 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28869 : Upper (D 7) (R 7) [96,260,9,160,192,2] 13 := by
  apply FastRouting.sound _ _ [96,260,9,160,192,2] 13 (by decide) (choices 1) [1,2,16] r28869 c28869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10931
  · exact u10932
  · exact u10933

def b28870 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 13 168 208 48 67 131 259), lower := (rows 97 262 13 168 208 48 64 128 256), losses := [] }

theorem u28870 : Upper (D 7) (R 7) [96,260,9,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28870 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28871 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 105, targets := 2 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(3,1)], upper := (rows 97 262 14 25 146 33 224 224 480), lower := (rows 97 262 14 25 146 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 24 32 97 161 289), good := (rows 480 262 30 478 146 480 64 128 256) }] }

theorem u28871 : Upper (D 7) (R 7) [96,260,10,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28872 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 14 25 146 96 225 161 417), lower := (rows 97 262 14 25 146 96 64 128 256), losses := [] }

theorem u28872 : Upper (D 7) (R 7) [96,260,10,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28873 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 105, targets := 2 },{ cop := 5, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(3,1)], upper := (rows 97 262 14 25 146 160 97 225 353), lower := (rows 97 262 14 25 146 160 64 128 256), losses := [{ target := 7, region := (rows 33 10 12 8 16 32 97 0 289), good := (rows 353 262 14 351 18 353 64 0 256) }] }

theorem u28873 : Upper (D 7) (R 7) [96,260,10,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28874 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 97 262 14 25 176 33 194 194 450), lower := (rows 97 262 14 25 176 33 64 128 256), losses := [] }

theorem u28874 : Upper (D 7) (R 7) [96,260,10,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28875 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 217, targets := 2 },{ cop := 3, region := 454, targets := 32 }], pairs := [(0,1),(1,5),(3,1),(4,1)], upper := (rows 97 262 14 25 176 34 193 193 449), lower := (rows 97 262 14 25 176 34 64 128 256), losses := [] }

theorem u28875 : Upper (D 7) (R 7) [96,260,10,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28876 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 14 25 176 96 195 131 387), lower := (rows 97 262 14 25 176 96 64 128 256), losses := [] }

theorem u28876 : Upper (D 7) (R 7) [96,260,10,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28877 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 262 14 25 176 160 67 195 323), lower := (rows 97 262 14 25 176 160 64 128 256), losses := [] }

theorem u28877 : Upper (D 7) (R 7) [96,260,10,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28878 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 97 262 14 56 82 33 193 129 385), lower := (rows 97 262 14 56 82 33 64 128 256), losses := [] }

theorem u28878 : Upper (D 7) (R 7) [96,260,10,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28879 : Route 9 := (fun mask => (mask,id))

def c28879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28879 : Upper (D 7) (R 7) [96,260,10,48,66,128] 13 := by
  apply FastRouting.sound _ _ [96,260,10,48,66,128] 13 (by decide) (choices 1) [1,128] r28879 c28879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10934
  · exact u10935

def b28880 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 97 262 14 56 145 33 194 194 450), lower := (rows 97 262 14 56 145 33 64 128 256), losses := [] }

theorem u28880 : Upper (D 7) (R 7) [96,260,10,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28881 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 217, targets := 2 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,1),(3,1),(4,1),(4,5)], upper := (rows 97 262 14 56 145 34 193 193 449), lower := (rows 97 262 14 56 145 34 64 128 256), losses := [] }

theorem u28881 : Upper (D 7) (R 7) [96,260,10,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28882 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 14 56 145 96 195 131 387), lower := (rows 97 262 14 56 145 96 64 128 256), losses := [] }

theorem u28882 : Upper (D 7) (R 7) [96,260,10,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28883 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 262 14 56 145 160 67 195 323), lower := (rows 97 262 14 56 145 160 64 128 256), losses := [] }

theorem u28883 : Upper (D 7) (R 7) [96,260,10,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28884 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 105, targets := 2 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(1,5),(3,1)], upper := (rows 97 262 14 56 146 33 193 193 449), lower := (rows 97 262 14 56 146 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 24 0 97 161 289), good := (rows 449 262 30 478 146 449 64 128 256) }] }

theorem u28884 : Upper (D 7) (R 7) [96,260,10,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28885 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 14 56 146 96 193 129 385), lower := (rows 97 262 14 56 146 96 64 128 256), losses := [] }

theorem u28885 : Upper (D 7) (R 7) [96,260,10,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28886 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 44, targets := 65 }], pairs := [(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 262 14 56 146 160 65 193 321), lower := (rows 97 262 14 56 146 160 64 128 256), losses := [] }

theorem u28886 : Upper (D 7) (R 7) [96,260,10,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28887 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 262 14 56 208 33 195 131 387), lower := (rows 97 262 14 56 208 33 64 128 256), losses := [] }

theorem u28887 : Upper (D 7) (R 7) [96,260,10,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28888 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 217, targets := 2 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,1),(3,1),(4,1),(4,5)], upper := (rows 97 262 14 56 208 34 193 129 385), lower := (rows 97 262 14 56 208 34 64 128 256), losses := [] }

theorem u28888 : Upper (D 7) (R 7) [96,260,10,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28889 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 262 14 56 208 160 67 131 259), lower := (rows 97 262 14 56 208 160 64 128 256), losses := [] }

theorem u28889 : Upper (D 7) (R 7) [96,260,10,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28889 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28890 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 233, targets := 2 }], pairs := [(0,1),(1,0),(3,1)], upper := (rows 97 262 14 137 19 48 224 224 480), lower := (rows 97 262 14 137 19 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 48 113 177 305), good := (rows 480 262 14 462 498 496 64 128 256) }] }

theorem u28890 : Upper (D 7) (R 7) [96,260,10,129,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28890 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28891 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 14 137 19 96 240 176 432), lower := (rows 97 262 14 137 19 96 64 128 256), losses := [] }

theorem u28891 : Upper (D 7) (R 7) [96,260,10,129,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28892_16 : Upper (D 7) (R 7) [96,260,10,129,3,128,16] 13 :=
  permutation_upper _ _ _ [96,260,10,129,3,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10936

theorem m28892_32 : Upper (D 7) (R 7) [96,260,10,129,3,128,32] 13 :=
  permutation_upper _ _ _ [96,260,10,129,3,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10937

def r28892 : Route 9 := (fun mask => (mask,id))

def c28892 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28892 : Upper (D 7) (R 7) [96,260,10,129,3,128] 13 := by
  apply FastRouting.sound _ _ [96,260,10,129,3,128] 13 (by decide) (choices 1) [16,32] r28892 c28892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28892_16
  · exact m28892_32

def b28893 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 201, targets := 2 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,6)], upper := (rows 97 262 14 137 50 33 208 208 464), lower := (rows 97 262 14 137 50 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 20 41 0 128 256), good := (rows 33 278 62 169 50 33 0 128 256) }] }

theorem u28893 : Upper (D 7) (R 7) [96,260,10,129,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28894 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 14 137 50 48 193 193 449), lower := (rows 97 262 14 137 50 48 64 128 256), losses := [] }

theorem u28894 : Upper (D 7) (R 7) [96,260,10,129,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28894 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28895 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 14 137 50 96 209 145 401), lower := (rows 97 262 14 137 50 96 64 128 256), losses := [] }

theorem u28895 : Upper (D 7) (R 7) [96,260,10,129,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28896 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 201, targets := 2 },{ cop := 4, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,0)], upper := (rows 97 262 14 137 50 160 81 209 337), lower := (rows 97 262 14 137 50 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 96 278 62 168 50 160 64 160 256) }] }

theorem u28896 : Upper (D 7) (R 7) [96,260,10,129,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28897 : Route 9 := (fun mask => (mask,id))

def c28897 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28897 : Upper (D 7) (R 7) [96,260,10,129,130,1] 13 := by
  apply FastRouting.sound _ _ [96,260,10,129,130,1] 13 (by decide) (choices 1) [16,32] r28897 c28897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10938
  · exact u10939

def b28898 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 105, targets := 2 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 262 14 137 146 48 97 225 353), lower := (rows 97 262 14 137 146 48 64 128 256), losses := [] }

theorem u28898 : Upper (D 7) (R 7) [96,260,10,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28898 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28899 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 14 137 146 96 113 177 305), lower := (rows 97 262 14 137 146 96 64 128 256), losses := [] }

theorem u28899 : Upper (D 7) (R 7) [96,260,10,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28900 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 66 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,6)], upper := (rows 97 262 14 137 176 33 82 210 338), lower := (rows 97 262 14 137 176 33 64 128 256), losses := [] }

theorem u28900 : Upper (D 7) (R 7) [96,260,10,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28901 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 217, targets := 2 },{ cop := 4, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,1)], upper := (rows 97 262 14 137 176 34 81 209 337), lower := (rows 97 262 14 137 176 34 64 128 256), losses := [] }

theorem u28901 : Upper (D 7) (R 7) [96,260,10,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28902 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 14 137 176 48 67 195 323), lower := (rows 97 262 14 137 176 48 64 128 256), losses := [] }

theorem u28902 : Upper (D 7) (R 7) [96,260,10,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28902 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28903 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 14 137 176 96 83 147 275), lower := (rows 97 262 14 137 176 96 64 128 256), losses := [] }

theorem u28903 : Upper (D 7) (R 7) [96,260,10,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28904 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 233, targets := 2 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(3,1)], upper := (rows 97 262 14 152 19 33 224 224 480), lower := (rows 97 262 14 152 19 33 64 128 256), losses := [{ target := 0, region := (rows 0 18 28 24 16 32 97 161 289), good := (rows 480 262 14 158 478 480 64 128 256) }] }

theorem u28904 : Upper (D 7) (R 7) [96,260,10,144,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28905 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 14 152 19 96 225 161 417), lower := (rows 97 262 14 152 19 96 64 128 256), losses := [] }

theorem u28905 : Upper (D 7) (R 7) [96,260,10,144,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28906_1 : Upper (D 7) (R 7) [96,260,10,144,3,128,1] 13 :=
  permutation_upper _ _ _ [96,260,10,144,3,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10940

theorem m28906_32 : Upper (D 7) (R 7) [96,260,10,144,3,128,32] 13 :=
  permutation_upper _ _ _ [96,260,10,144,3,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10941

def r28906 : Route 9 := (fun mask => (mask,id))

def c28906 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28906 : Upper (D 7) (R 7) [96,260,10,144,3,128] 13 := by
  apply FastRouting.sound _ _ [96,260,10,144,3,128] 13 (by decide) (choices 1) [1,32] r28906 c28906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28906_1
  · exact m28906_32

def b28907 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 201, targets := 2 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(1,5),(3,1)], upper := (rows 97 262 14 152 50 33 193 193 449), lower := (rows 97 262 14 152 50 33 64 128 256), losses := [{ target := 5, region := (rows 1 18 28 24 16 0 97 161 289), good := (rows 449 262 14 158 478 449 64 128 256) }] }

theorem u28907 : Upper (D 7) (R 7) [96,260,10,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28908 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 14 152 50 96 193 129 385), lower := (rows 97 262 14 152 50 96 64 128 256), losses := [] }

theorem u28908 : Upper (D 7) (R 7) [96,260,10,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28909 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 201, targets := 2 },{ cop := 4, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(3,1),(4,0)], upper := (rows 97 262 14 152 50 160 65 193 321), lower := (rows 97 262 14 152 50 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 96 278 62 184 50 160 64 160 256) }] }

theorem u28909 : Upper (D 7) (R 7) [96,260,10,144,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28910 : Route 9 := (fun mask => (mask,id))

def c28910 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28910 : Upper (D 7) (R 7) [96,260,10,160,3,1] 13 := by
  apply FastRouting.sound _ _ [96,260,10,160,3,1] 13 (by decide) (choices 1) [16,128] r28910 c28910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10942
  · exact u10943

def r28911 : Route 9 := (fun mask => (mask,id))

def c28911 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28911 : Upper (D 7) (R 7) [96,260,10,160,3,16] 13 := by
  apply FastRouting.sound _ _ [96,260,10,160,3,16] 13 (by decide) (choices 1) [1,128] r28911 c28911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10944
  · exact u10945

def b28912 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 14 168 19 96 209 145 401), lower := (rows 97 262 14 168 19 96 64 128 256), losses := [] }

theorem u28912 : Upper (D 7) (R 7) [96,260,10,160,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28913 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 97 262 14 168 19 160 81 209 337), lower := (rows 97 262 14 168 19 160 64 128 256), losses := [] }

theorem u28913 : Upper (D 7) (R 7) [96,260,10,160,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28914 : Route 9 := (fun mask => (mask,id))

def c28914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28914 : Upper (D 7) (R 7) [96,260,10,160,66,1] 13 := by
  apply FastRouting.sound _ _ [96,260,10,160,66,1] 13 (by decide) (choices 1) [1,16,128] r28914 c28914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10946
  · exact u10947
  · exact u10948

def b28915 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 14 168 82 48 193 129 385), lower := (rows 97 262 14 168 82 48 64 128 256), losses := [] }

theorem u28915 : Upper (D 7) (R 7) [96,260,10,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28915 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28916 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 97 262 14 168 82 160 81 145 273), lower := (rows 97 262 14 168 82 160 64 128 256), losses := [] }

theorem u28916 : Upper (D 7) (R 7) [96,260,10,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28917 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 40, targets := 66 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,6)], upper := (rows 97 262 14 168 145 33 82 210 338), lower := (rows 97 262 14 168 145 33 64 128 256), losses := [] }

theorem u28917 : Upper (D 7) (R 7) [96,260,10,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28918 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 217, targets := 2 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,1),(3,1),(4,1),(4,5)], upper := (rows 97 262 14 168 145 34 81 209 337), lower := (rows 97 262 14 168 145 34 64 128 256), losses := [] }

theorem u28918 : Upper (D 7) (R 7) [96,260,10,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28919 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 262 14 168 145 48 67 195 323), lower := (rows 97 262 14 168 145 48 64 128 256), losses := [] }

theorem u28919 : Upper (D 7) (R 7) [96,260,10,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28919 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u28919
end Delivery.IrregularNine14.P07
