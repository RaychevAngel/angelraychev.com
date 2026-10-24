import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0108
import IrregularNine14P07C0109

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21840 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 322 14 140 81 48 225 161 417), lower := (rows 35 322 14 140 81 48 64 128 256), losses := [] }

theorem u21840 : Upper (D 7) (R 7) [34,320,10,132,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21840 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21841 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 0, region := 80, targets := 2 }], pairs := [(0,7),(1,7),(4,1),(4,7)], upper := (rows 35 322 14 140 81 160 113 177 305), lower := (rows 35 322 14 140 81 160 64 128 256), losses := [] }

theorem u21841 : Upper (D 7) (R 7) [34,320,10,132,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21842 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,7)], upper := (rows 35 322 14 140 112 33 209 145 401), lower := (rows 35 322 14 140 112 33 64 128 256), losses := [] }

theorem u21842 : Upper (D 7) (R 7) [34,320,10,132,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21843 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 14 140 112 48 193 129 385), lower := (rows 35 322 14 140 112 48 64 128 256), losses := [] }

theorem u21843 : Upper (D 7) (R 7) [34,320,10,132,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21843 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21844 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 0, region := 80, targets := 2 }], pairs := [(0,7),(1,7),(4,1),(4,7)], upper := (rows 35 322 14 140 112 160 81 145 273), lower := (rows 35 322 14 140 112 160 64 128 256), losses := [] }

theorem u21844 : Upper (D 7) (R 7) [34,320,10,132,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21845 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 },{ cop := 4, region := 354, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 35 322 14 140 145 33 112 240 368), lower := (rows 35 322 14 140 145 33 64 128 256), losses := [] }

theorem u21845 : Upper (D 7) (R 7) [34,320,10,132,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21846 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,7),(1,7),(4,1)], upper := (rows 35 322 14 140 145 48 97 225 353), lower := (rows 35 322 14 140 145 48 64 128 256), losses := [] }

theorem u21846 : Upper (D 7) (R 7) [34,320,10,132,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21846 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21847 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 14 140 145 96 113 177 305), lower := (rows 35 322 14 140 145 96 64 128 256), losses := [] }

theorem u21847 : Upper (D 7) (R 7) [34,320,10,132,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21848 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 },{ cop := 4, region := 323, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 35 322 14 140 176 33 81 209 337), lower := (rows 35 322 14 140 176 33 64 128 256), losses := [] }

theorem u21848 : Upper (D 7) (R 7) [34,320,10,132,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21849 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 14 140 176 48 65 193 321), lower := (rows 35 322 14 140 176 48 64 128 256), losses := [] }

theorem u21849 : Upper (D 7) (R 7) [34,320,10,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21849 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21850 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 14 140 176 96 81 145 273), lower := (rows 35 322 14 140 176 96 64 128 256), losses := [] }

theorem u21850 : Upper (D 7) (R 7) [34,320,10,132,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21851 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 },{ cop := 4, region := 291, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 35 322 14 140 208 33 113 177 305), lower := (rows 35 322 14 140 208 33 64 128 256), losses := [] }

theorem u21851 : Upper (D 7) (R 7) [34,320,10,132,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21852 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 322 14 140 208 48 97 161 289), lower := (rows 35 322 14 140 208 48 64 128 256), losses := [] }

theorem u21852 : Upper (D 7) (R 7) [34,320,10,132,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21852 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21853 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 322 14 152 52 33 193 193 449), lower := (rows 35 322 14 152 52 33 64 128 256), losses := [] }

theorem u21853 : Upper (D 7) (R 7) [34,320,10,144,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21854 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 322 14 152 52 96 193 129 385), lower := (rows 35 322 14 152 52 96 64 128 256), losses := [] }

theorem u21854 : Upper (D 7) (R 7) [34,320,10,144,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21855 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 323, targets := 128 },{ cop := 0, region := 322, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(4,0)], upper := (rows 35 322 14 152 52 160 65 193 321), lower := (rows 35 322 14 152 52 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 34 322 62 184 52 160 64 160 256) }] }

theorem u21855 : Upper (D 7) (R 7) [34,320,10,144,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21856 : Route 9 := (fun mask => (mask,id))

def c21856 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21856 : Upper (D 7) (R 7) [34,320,10,144,65,1] 13 := by
  apply FastRouting.sound _ _ [34,320,10,144,65,1] 13 (by decide) (choices 1) [4,32,128] r21856 c21856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6523
  · exact u6524
  · exact u6525

def b21857 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 322 14 152 81 36 225 161 417), lower := (rows 35 322 14 152 81 36 64 128 256), losses := [] }

theorem u21857 : Upper (D 7) (R 7) [34,320,10,144,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21857 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21858 : Route 9 := (fun mask => (mask,id))

def c21858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21858 : Upper (D 7) (R 7) [34,320,10,144,65,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,144,65,128] 13 (by decide) (choices 1) [1,4,32] r21858 c21858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6526
  · exact u6527
  · exact u6528

def r21859 : Route 9 := (fun mask => (mask,id))

def c21859 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21859 : Upper (D 7) (R 7) [34,320,10,144,68,1] 13 := by
  apply FastRouting.sound _ _ [34,320,10,144,68,1] 13 (by decide) (choices 1) [1,32,128] r21859 c21859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6529
  · exact u6530
  · exact u6531

def b21860 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(3,6)], upper := (rows 35 322 14 152 84 160 97 161 289), lower := (rows 35 322 14 152 84 160 64 128 256), losses := [{ target := 6, region := (rows 7 2 4 24 16 191 0 151 279), good := (rows 419 419 431 440 445 160 0 160 256) }] }

theorem u21860 : Upper (D 7) (R 7) [34,320,10,144,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21861 : Route 9 := (fun mask => (mask,id))

def c21861 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21861 : Upper (D 7) (R 7) [34,320,10,144,96,1] 13 := by
  apply FastRouting.sound _ _ [34,320,10,144,96,1] 13 (by decide) (choices 1) [1,4,128] r21861 c21861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6532
  · exact u6533
  · exact u6534

def b21862 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 322 14 152 112 36 193 129 385), lower := (rows 35 322 14 152 112 36 64 128 256), losses := [] }

theorem u21862 : Upper (D 7) (R 7) [34,320,10,144,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21862 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21863 : Route 9 := (fun mask => (mask,id))

def c21863 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21863 : Upper (D 7) (R 7) [34,320,10,144,96,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,144,96,128] 13 (by decide) (choices 1) [1,4] r21863 c21863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6535
  · exact u6536

def r21864 : Route 9 := (fun mask => (mask,id))

def c21864 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21864 : Upper (D 7) (R 7) [34,320,10,160,65,1] 13 := by
  apply FastRouting.sound _ _ [34,320,10,160,65,1] 13 (by decide) (choices 1) [4,16,128] r21864 c21864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6537
  · exact u6538
  · exact u6539

def b21865 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 322 14 168 81 36 209 145 401), lower := (rows 35 322 14 168 81 36 64 128 256), losses := [] }

theorem u21865 : Upper (D 7) (R 7) [34,320,10,160,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21865 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21866 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 322 14 168 81 48 197 133 389), lower := (rows 35 322 14 168 81 48 64 128 256), losses := [] }

theorem u21866 : Upper (D 7) (R 7) [34,320,10,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21866 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21867 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 322 14 168 81 160 85 149 277), lower := (rows 35 322 14 168 81 160 64 128 256), losses := [] }

theorem u21867 : Upper (D 7) (R 7) [34,320,10,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21868 : Route 9 := (fun mask => (mask,id))

def c21868 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21868 : Upper (D 7) (R 7) [34,320,10,160,68,1] 13 := by
  apply FastRouting.sound _ _ [34,320,10,160,68,1] 13 (by decide) (choices 1) [1,16,128] r21868 c21868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6540
  · exact u6541
  · exact u6542

def b21869 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 0, region := 136, targets := 2 }], pairs := [(2,6),(3,1),(3,6)], upper := (rows 35 322 14 168 84 48 193 129 385), lower := (rows 35 322 14 168 84 48 64 128 256), losses := [] }

theorem u21869 : Upper (D 7) (R 7) [34,320,10,160,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21869 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21870 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 322 14 168 84 160 81 145 273), lower := (rows 35 322 14 168 84 160 64 128 256), losses := [] }

theorem u21870 : Upper (D 7) (R 7) [34,320,10,160,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21871 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 4, region := 40, targets := 66 }], pairs := [(0,6),(0,7),(3,1),(3,6)], upper := (rows 35 322 14 168 145 33 84 212 340), lower := (rows 35 322 14 168 145 33 64 128 256), losses := [] }

theorem u21871 : Upper (D 7) (R 7) [34,320,10,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21872 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 322 14 168 145 36 81 209 337), lower := (rows 35 322 14 168 145 36 64 128 256), losses := [] }

theorem u21872 : Upper (D 7) (R 7) [34,320,10,160,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21872 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21873 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 14 168 145 48 69 197 325), lower := (rows 35 322 14 168 145 48 64 128 256), losses := [] }

theorem u21873 : Upper (D 7) (R 7) [34,320,10,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21873 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21874 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 14 168 145 96 85 149 277), lower := (rows 35 322 14 168 145 96 64 128 256), losses := [] }

theorem u21874 : Upper (D 7) (R 7) [34,320,10,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21875 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(3,6)], upper := (rows 35 322 14 168 148 33 81 209 337), lower := (rows 35 322 14 168 148 33 64 128 256), losses := [{ target := 6, region := (rows 7 2 4 24 16 55 0 128 256), good := (rows 35 291 47 168 189 33 0 128 256) }] }

theorem u21875 : Upper (D 7) (R 7) [34,320,10,160,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21876 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 14 168 148 48 65 193 321), lower := (rows 35 322 14 168 148 48 64 128 256), losses := [] }

theorem u21876 : Upper (D 7) (R 7) [34,320,10,160,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21876 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21877 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 14 168 148 96 81 145 273), lower := (rows 35 322 14 168 148 96 64 128 256), losses := [] }

theorem u21877 : Upper (D 7) (R 7) [34,320,10,160,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21878 : Route 9 := (fun mask => (mask,id))

def c21878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21878 : Upper (D 7) (R 7) [34,320,10,160,192,1] 13 := by
  apply FastRouting.sound _ _ [34,320,10,160,192,1] 13 (by decide) (choices 1) [1,4,16] r21878 c21878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6543
  · exact u6544
  · exact u6545

def b21879 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 322 14 168 208 36 81 145 273), lower := (rows 35 322 14 168 208 36 64 128 256), losses := [] }

theorem u21879 : Upper (D 7) (R 7) [34,320,10,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21879 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21880 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 322 14 168 208 48 69 133 261), lower := (rows 35 322 14 168 208 48 64 128 256), losses := [] }

theorem u21880 : Upper (D 7) (R 7) [34,320,10,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21880 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21881 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 2, region := 49, targets := 64 },{ cop := 2, region := 49, targets := 128 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 322 14 200 52 33 209 145 401), lower := (rows 35 322 14 200 52 33 64 128 256), losses := [] }

theorem u21881 : Upper (D 7) (R 7) [34,320,10,192,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21882 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 14 200 52 48 193 129 385), lower := (rows 35 322 14 200 52 48 64 128 256), losses := [] }

theorem u21882 : Upper (D 7) (R 7) [34,320,10,192,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21882 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21883 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 323, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 322 14 200 52 160 81 145 273), lower := (rows 35 322 14 200 52 160 64 128 256), losses := [] }

theorem u21883 : Upper (D 7) (R 7) [34,320,10,192,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21884 : Route 9 := (fun mask => (mask,id))

def c21884 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21884 : Upper (D 7) (R 7) [34,320,10,192,129,1] 13 := by
  apply FastRouting.sound _ _ [34,320,10,192,129,1] 13 (by decide) (choices 1) [4,16,32] r21884 c21884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6546
  · exact u6547
  · exact u6548

def b21885 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 322 14 200 145 36 113 177 305), lower := (rows 35 322 14 200 145 36 64 128 256), losses := [] }

theorem u21885 : Upper (D 7) (R 7) [34,320,10,192,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21885 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21886 : Route 9 := (fun mask => (mask,id))

def c21886 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21886 : Upper (D 7) (R 7) [34,320,10,192,129,16] 13 := by
  apply FastRouting.sound _ _ [34,320,10,192,129,16] 13 (by decide) (choices 1) [1,4,32] r21886 c21886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6549
  · exact u6550
  · exact u6551

def r21887 : Route 9 := (fun mask => (mask,id))

def c21887 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21887 : Upper (D 7) (R 7) [34,320,10,192,160,1] 13 := by
  apply FastRouting.sound _ _ [34,320,10,192,160,1] 13 (by decide) (choices 1) [1,4,16] r21887 c21887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6552
  · exact u6553
  · exact u6554

def b21888 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 322 14 200 176 36 81 145 273), lower := (rows 35 322 14 200 176 36 64 128 256), losses := [] }

theorem u21888 : Upper (D 7) (R 7) [34,320,10,192,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21888 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21889 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 14 200 176 48 69 133 261), lower := (rows 35 322 14 200 176 48 64 128 256), losses := [] }

theorem u21889 : Upper (D 7) (R 7) [34,320,10,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21889 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21890 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 44, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 322 28 44 145 33 194 194 450), lower := (rows 35 322 28 44 145 33 64 128 256), losses := [] }

theorem u21890 : Upper (D 7) (R 7) [34,320,24,36,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21891 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 322 28 44 145 34 193 193 449), lower := (rows 35 322 28 44 145 34 64 128 256), losses := [] }

theorem u21891 : Upper (D 7) (R 7) [34,320,24,36,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21892 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 322 28 44 145 96 195 131 387), lower := (rows 35 322 28 44 145 96 64 128 256), losses := [] }

theorem u21892 : Upper (D 7) (R 7) [34,320,24,36,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21893 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6),(3,0)], upper := (rows 35 322 28 44 145 160 67 195 323), lower := (rows 35 322 28 44 145 160 64 128 256), losses := [] }

theorem u21893 : Upper (D 7) (R 7) [34,320,24,36,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21894 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 28 44 146 33 193 193 449), lower := (rows 35 322 28 44 146 33 64 128 256), losses := [] }

theorem u21894 : Upper (D 7) (R 7) [34,320,24,36,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21895 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 322 28 44 146 96 193 129 385), lower := (rows 35 322 28 44 146 96 64 128 256), losses := [] }

theorem u21895 : Upper (D 7) (R 7) [34,320,24,36,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21896 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 35 322 28 44 146 160 65 193 321), lower := (rows 35 322 28 44 146 160 64 128 256), losses := [] }

theorem u21896 : Upper (D 7) (R 7) [34,320,24,36,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21897 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(4,5)], upper := (rows 35 322 28 44 208 33 195 131 387), lower := (rows 35 322 28 44 208 33 64 128 256), losses := [] }

theorem u21897 : Upper (D 7) (R 7) [34,320,24,36,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21898 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 322 28 44 208 34 193 129 385), lower := (rows 35 322 28 44 208 34 64 128 256), losses := [] }

theorem u21898 : Upper (D 7) (R 7) [34,320,24,36,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21899 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 67 }], pairs := [(2,0),(2,1),(2,6),(3,0)], upper := (rows 35 322 28 44 208 160 67 131 259), lower := (rows 35 322 28 44 208 160 64 128 256), losses := [] }

theorem u21899 : Upper (D 7) (R 7) [34,320,24,36,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u21899
end Delivery.IrregularNine14.P07
