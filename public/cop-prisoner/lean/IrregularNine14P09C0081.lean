import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0027

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4860 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 57, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8),(4,7)], upper := (rows 35 70 388 25 88 33 480 416 416), lower := (rows 35 70 388 25 88 33 64 128 256), losses := [] }

theorem u4860 : Upper (D 9) (R 9) [34,68,384,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4860 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4861 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(0,8),(2,6),(3,7),(4,7)], upper := (rows 35 70 388 25 88 160 353 417 289), lower := (rows 35 70 388 25 88 160 64 128 256), losses := [{ target := 8, region := (rows 3 2 4 11 18 164 64 128 0), good := (rows 59 127 164 25 88 160 64 160 0) }] }

theorem u4861 : Upper (D 9) (R 9) [34,68,384,17,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4861 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4862 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 57, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8),(4,7)], upper := (rows 35 70 388 25 112 33 456 392 392), lower := (rows 35 70 388 25 112 33 64 128 256), losses := [] }

theorem u4862 : Upper (D 9) (R 9) [34,68,384,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4862 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4863 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 57, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 388 25 112 40 449 385 385), lower := (rows 35 70 388 25 112 40 64 128 256), losses := [] }

theorem u4863 : Upper (D 9) (R 9) [34,68,384,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4863 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4864 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 3, region := 454, targets := 32 },{ cop := 3, region := 388, targets := 64 }], pairs := [(1,5),(2,5),(2,6),(3,7),(4,7)], upper := (rows 35 70 388 25 112 160 329 393 265), lower := (rows 35 70 388 25 112 160 64 128 256), losses := [] }

theorem u4864 : Upper (D 9) (R 9) [34,68,384,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4864 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4865 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 1, region := 33, targets := 320 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(1,0),(2,0)], upper := (rows 35 70 388 25 152 33 352 480 352), lower := (rows 35 70 388 25 152 33 64 128 256), losses := [] }

theorem u4865 : Upper (D 9) (R 9) [34,68,384,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4865 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4866 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 388 25 152 96 353 417 289), lower := (rows 35 70 388 25 152 96 64 128 256), losses := [] }

theorem u4866 : Upper (D 9) (R 9) [34,68,384,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4866 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4867 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 216, targets := 256 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(3,8),(4,8)], upper := (rows 35 70 388 25 152 288 97 225 353), lower := (rows 35 70 388 25 152 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 292 0 128 256), good := (rows 35 39 420 25 152 288 0 128 288) }] }

theorem u4867 : Upper (D 9) (R 9) [34,68,384,17,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4867 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4868 : PairBound 9 := { available := 328, camps := [{ cop := 3, region := 454, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 388 25 176 33 328 456 328), lower := (rows 35 70 388 25 176 33 64 128 256), losses := [] }

theorem u4868 : Upper (D 9) (R 9) [34,68,384,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4868 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4869 : Route 9 := (fun mask => (mask,id))

def c4869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4869 : Upper (D 9) (R 9) [34,68,384,17,160,8] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,160,8] 13 (by decide) (choices 1) [1,256] r4869 c4869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1632
  · exact u1633

def b4870 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 388 25 176 96 329 393 265), lower := (rows 35 70 388 25 176 96 64 128 256), losses := [] }

theorem u4870 : Upper (D 9) (R 9) [34,68,384,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4870 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4871 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 216, targets := 256 },{ cop := 2, region := 48, targets := 65 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(3,8),(4,0),(4,6),(4,8)], upper := (rows 35 70 388 25 176 288 73 201 329), lower := (rows 35 70 388 25 176 288 64 128 256), losses := [] }

theorem u4871 : Upper (D 9) (R 9) [34,68,384,17,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4871 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4872 : Route 9 := (fun mask => (mask,id))

def c4872 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4872 : Upper (D 9) (R 9) [34,68,384,17,192,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,192,1] 13 (by decide) (choices 1) [8,32,256] r4872 c4872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1634
  · exact u1635
  · exact u1636

def r4873 : Route 9 := (fun mask => (mask,id))

def c4873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4873 : Upper (D 9) (R 9) [34,68,384,17,192,8] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,192,8] 13 (by decide) (choices 1) [1,32,256] r4873 c4873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1637
  · exact u1638
  · exact u1639

def b4874 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 216, targets := 256 },{ cop := 3, region := 420, targets := 64 }], pairs := [(0,6),(0,7),(2,6),(3,8),(4,8)], upper := (rows 35 70 388 25 208 288 105 169 297), lower := (rows 35 70 388 25 208 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 16 300 0 136 264), good := (rows 35 39 420 445 144 288 0 128 288) },{ target := 7, region := (rows 3 2 4 8 16 300 72 0 264), good := (rows 35 103 292 377 80 288 64 0 288) }] }

theorem u4874 : Upper (D 9) (R 9) [34,68,384,17,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4874 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4875 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 57, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8),(4,7)], upper := (rows 35 70 388 56 81 33 456 392 392), lower := (rows 35 70 388 56 81 33 64 128 256), losses := [] }

theorem u4875 : Upper (D 9) (R 9) [34,68,384,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4875 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4876 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 57, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 388 56 81 40 449 385 385), lower := (rows 35 70 388 56 81 40 64 128 256), losses := [] }

theorem u4876 : Upper (D 9) (R 9) [34,68,384,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4876 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4877 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 4, region := 428, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(3,7),(4,7)], upper := (rows 35 70 388 56 81 160 329 393 265), lower := (rows 35 70 388 56 81 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 28 24 16 188 0 144 272), good := (rows 35 39 420 444 445 160 0 160 256) }] }

theorem u4877 : Upper (D 9) (R 9) [34,68,384,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4877 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4878 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 57, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8),(4,7)], upper := (rows 35 70 388 56 88 33 449 385 385), lower := (rows 35 70 388 56 88 33 64 128 256), losses := [] }

theorem u4878 : Upper (D 9) (R 9) [34,68,384,48,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4878 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4879 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(3,7),(4,7)], upper := (rows 35 70 388 56 88 160 321 385 257), lower := (rows 35 70 388 56 88 160 64 128 256), losses := [] }

theorem u4879 : Upper (D 9) (R 9) [34,68,384,48,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4879 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4880 : PairBound 9 := { available := 328, camps := [{ cop := 3, region := 454, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 388 56 145 33 328 456 328), lower := (rows 35 70 388 56 145 33 64 128 256), losses := [] }

theorem u4880 : Upper (D 9) (R 9) [34,68,384,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4880 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4881 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 470, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 35 70 388 56 145 40 321 449 321), lower := (rows 35 70 388 56 145 40 64 128 256), losses := [] }

theorem u4881 : Upper (D 9) (R 9) [34,68,384,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4881 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4882 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 388 56 145 96 329 393 265), lower := (rows 35 70 388 56 145 96 64 128 256), losses := [] }

theorem u4882 : Upper (D 9) (R 9) [34,68,384,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4882 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4883 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 216, targets := 256 },{ cop := 4, region := 360, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(3,8),(4,8)], upper := (rows 35 70 388 56 145 288 73 201 329), lower := (rows 35 70 388 56 145 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 292 0 128 256), good := (rows 35 39 420 56 145 288 0 128 288) },{ target := 7, region := (rows 3 2 4 24 16 316 80 0 272), good := (rows 35 103 292 376 377 288 64 0 288) }] }

theorem u4883 : Upper (D 9) (R 9) [34,68,384,48,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4883 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4884 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 33, targets := 320 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(1,5),(2,5)], upper := (rows 35 70 388 56 152 33 321 449 321), lower := (rows 35 70 388 56 152 33 64 128 256), losses := [] }

theorem u4884 : Upper (D 9) (R 9) [34,68,384,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4884 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4885 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 388 56 152 96 321 385 257), lower := (rows 35 70 388 56 152 96 64 128 256), losses := [] }

theorem u4885 : Upper (D 9) (R 9) [34,68,384,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4885 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4886 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 56, targets := 65 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(3,0),(3,6),(4,0),(4,6)], upper := (rows 35 70 388 56 152 288 65 193 321), lower := (rows 35 70 388 56 152 288 64 128 256), losses := [] }

theorem u4886 : Upper (D 9) (R 9) [34,68,384,48,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4886 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4887 : Route 9 := (fun mask => (mask,id))

def c4887 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4887 : Upper (D 9) (R 9) [34,68,384,48,192,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,192,1] 13 (by decide) (choices 1) [1,8,256] r4887 c4887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1640
  · exact u1641
  · exact u1642

def b4888 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 40, targets := 449 }], pairs := [(3,0),(3,6),(3,7),(3,8)], upper := (rows 35 70 388 56 208 40 321 385 257), lower := (rows 35 70 388 56 208 40 64 128 256), losses := [] }

theorem u4888 : Upper (D 9) (R 9) [34,68,384,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4888 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4889 : Route 9 := (fun mask => (mask,id))

def c4889 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4889 : Upper (D 9) (R 9) [34,68,384,48,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,192,256] 13 (by decide) (choices 1) [1,8] r4889 c4889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1643
  · exact u1644

def b4890 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 41, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 388 73 145 40 368 432 304), lower := (rows 35 70 388 73 145 40 64 128 256), losses := [] }

theorem u4890 : Upper (D 9) (R 9) [34,68,384,65,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4890 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4891 : Route 9 := (fun mask => (mask,id))

def c4891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4891 : Upper (D 9) (R 9) [34,68,384,65,129,16] 13 := by
  apply FastRouting.sound _ _ [34,68,384,65,129,16] 13 (by decide) (choices 1) [8,32,256] r4891 c4891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1645
  · exact u1646
  · exact u1647

def b4892 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 216, targets := 256 },{ cop := 3, region := 436, targets := 64 },{ cop := 4, region := 360, targets := 128 }], pairs := [(2,6),(3,7),(3,8),(4,6),(4,8)], upper := (rows 35 70 388 73 145 288 120 184 312), lower := (rows 35 70 388 73 145 288 64 128 256), losses := [] }

theorem u4892 : Upper (D 9) (R 9) [34,68,384,65,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4892 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4893 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,7),(0,8),(2,6),(3,7),(3,8)], upper := (rows 35 70 388 73 152 33 368 432 304), lower := (rows 35 70 388 73 152 33 64 128 256), losses := [] }

theorem u4893 : Upper (D 9) (R 9) [34,68,384,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4893 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4894 : Route 9 := (fun mask => (mask,id))

def c4894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4894 : Upper (D 9) (R 9) [34,68,384,65,136,16] 13 := by
  apply FastRouting.sound _ _ [34,68,384,65,136,16] 13 (by decide) (choices 1) [1,32,256] r4894 c4894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1648
  · exact u1649
  · exact u1650

def b4895 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 216, targets := 256 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,6),(2,6),(3,8),(4,6),(4,8)], upper := (rows 35 70 388 73 152 288 113 177 305), lower := (rows 35 70 388 73 152 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 28 8 24 316 0 136 264), good := (rows 35 39 420 445 444 288 0 128 288) }] }

theorem u4895 : Upper (D 9) (R 9) [34,68,384,65,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4895 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4896 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,7),(0,8),(2,6),(3,7),(3,8)], upper := (rows 35 70 388 73 176 33 344 408 280), lower := (rows 35 70 388 73 176 33 64 128 256), losses := [] }

theorem u4896 : Upper (D 9) (R 9) [34,68,384,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4896 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4897 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 41, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 388 73 176 40 337 401 273), lower := (rows 35 70 388 73 176 40 64 128 256), losses := [] }

theorem u4897 : Upper (D 9) (R 9) [34,68,384,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4897 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4898 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 70 388 73 176 48 329 393 265), lower := (rows 35 70 388 73 176 48 64 128 256), losses := [] }

theorem u4898 : Upper (D 9) (R 9) [34,68,384,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4898 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4899 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 256 },{ cop := 2, region := 48, targets := 65 },{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(3,8),(4,0),(4,6),(4,8)], upper := (rows 35 70 388 73 176 288 89 153 281), lower := (rows 35 70 388 73 176 288 64 128 256), losses := [] }

theorem u4899 : Upper (D 9) (R 9) [34,68,384,65,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4899 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4900 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 4, region := 360, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(2,6),(3,7)], upper := (rows 35 70 388 88 145 33 360 424 296), lower := (rows 35 70 388 88 145 33 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 16 51 0 136 264), good := (rows 35 39 388 444 177 33 0 128 256) }] }

theorem u4900 : Upper (D 9) (R 9) [34,68,384,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4900 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4901 : Route 9 := (fun mask => (mask,id))

def c4901 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4901 : Upper (D 9) (R 9) [34,68,384,80,129,8] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80,129,8] 13 (by decide) (choices 1) [1,32,256] r4901 c4901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1651
  · exact u1652
  · exact u1653

def b4902 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 216, targets := 256 },{ cop := 4, region := 360, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(3,8),(4,8)], upper := (rows 35 70 388 88 145 288 105 169 297), lower := (rows 35 70 388 88 145 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 292 0 128 256), good := (rows 35 39 420 24 145 288 0 128 288) },{ target := 7, region := (rows 3 2 4 24 16 316 80 0 272), good := (rows 35 103 292 376 377 288 64 0 288) }] }

theorem u4902 : Upper (D 9) (R 9) [34,68,384,80,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4902 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4903 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 99, targets := 128 },{ cop := 1, region := 33, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(1,7),(2,6)], upper := (rows 35 70 388 88 152 33 353 417 289), lower := (rows 35 70 388 88 152 33 64 128 256), losses := [] }

theorem u4903 : Upper (D 9) (R 9) [34,68,384,80,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4903 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4904 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 216, targets := 256 },{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,8),(4,8)], upper := (rows 35 70 388 88 152 288 97 161 289), lower := (rows 35 70 388 88 152 288 64 128 256), losses := [] }

theorem u4904 : Upper (D 9) (R 9) [34,68,384,80,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4904 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4905 : Route 9 := (fun mask => (mask,id))

def c4905 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4905 : Upper (D 9) (R 9) [34,68,384,80,160,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80,160,1] 13 (by decide) (choices 1) [1,8,256] r4905 c4905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1654
  · exact u1655
  · exact u1656

def b4906 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(1,5),(2,5),(2,6),(4,6)], upper := (rows 35 70 388 88 176 40 321 385 257), lower := (rows 35 70 388 88 176 40 64 128 256), losses := [] }

theorem u4906 : Upper (D 9) (R 9) [34,68,384,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4906 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4907 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 256 },{ cop := 2, region := 48, targets := 65 }], pairs := [(3,0),(3,8),(4,0),(4,6),(4,8)], upper := (rows 35 70 388 88 176 288 73 137 265), lower := (rows 35 70 388 88 176 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 20 292 64 128 256), good := (rows 42 126 436 88 176 288 64 128 288) }] }

theorem u4907 : Upper (D 9) (R 9) [34,68,384,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4907 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4908 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 388 104 145 33 344 408 280), lower := (rows 35 70 388 104 145 33 64 128 256), losses := [] }

theorem u4908 : Upper (D 9) (R 9) [34,68,384,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4908 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4909 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 41, targets := 384 }], pairs := [(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 388 104 145 40 337 401 273), lower := (rows 35 70 388 104 145 40 64 128 256), losses := [] }

theorem u4909 : Upper (D 9) (R 9) [34,68,384,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4909 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4910 : Route 9 := (fun mask => (mask,id))

def c4910 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4910 : Upper (D 9) (R 9) [34,68,384,96,129,16] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96,129,16] 13 (by decide) (choices 1) [1,8,256] r4910 c4910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1657
  · exact u1658
  · exact u1659

def b4911 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 256 },{ cop := 4, region := 360, targets := 128 }], pairs := [(0,6),(3,0),(3,7),(3,8),(4,8)], upper := (rows 35 70 388 104 145 288 89 153 281), lower := (rows 35 70 388 104 145 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 292 64 128 256), good := (rows 42 110 420 104 144 288 64 128 288) },{ target := 6, region := (rows 3 2 4 8 16 292 0 128 256), good := (rows 35 39 420 40 145 288 0 128 288) }] }

theorem u4911 : Upper (D 9) (R 9) [34,68,384,96,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4911 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4912 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 41, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,7),(3,8)], upper := (rows 35 70 388 104 152 33 337 401 273), lower := (rows 35 70 388 104 152 33 64 128 256), losses := [] }

theorem u4912 : Upper (D 9) (R 9) [34,68,384,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4912 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4913 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 388, targets := 64 },{ cop := 0, region := 328, targets := 128 }], pairs := [(1,5),(2,5),(2,6),(3,7)], upper := (rows 35 70 388 104 152 48 321 385 257), lower := (rows 35 70 388 104 152 48 64 128 256), losses := [] }

theorem u4913 : Upper (D 9) (R 9) [34,68,384,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4913 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4914 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 256 }], pairs := [(0,6),(0,7),(3,0),(3,8),(4,8)], upper := (rows 35 70 388 104 152 288 81 145 273), lower := (rows 35 70 388 104 152 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 292 64 128 256), good := (rows 42 110 420 104 152 288 64 128 288) },{ target := 6, region := (rows 3 2 4 8 16 292 0 128 256), good := (rows 35 39 420 40 152 288 0 128 288) },{ target := 7, region := (rows 3 2 4 10 16 292 64 0 256), good := (rows 43 111 292 104 24 288 64 0 288) }] }

theorem u4914 : Upper (D 9) (R 9) [34,68,384,96,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4914 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4915 : Route 9 := (fun mask => (mask,id))

def c4915 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4915 : Upper (D 9) (R 9) [34,68,384,129,257,8] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129,257,8] 13 (by decide) (choices 1) [16,32] r4915 c4915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1660
  · exact u1661

def b4916 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 388 137 273 96 120 184 312), lower := (rows 35 70 388 137 273 96 64 128 256), losses := [] }

theorem u4916 : Upper (D 9) (R 9) [34,68,384,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4916 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4917 : Route 9 := (fun mask => (mask,id))

def c4917 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4917 : Upper (D 9) (R 9) [34,68,384,129,264,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129,264,1] 13 (by decide) (choices 1) [16,32] r4917 c4917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1662
  · exact u1663

def r4918 : Route 9 := (fun mask => (mask,id))

def c4918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4918 : Upper (D 9) (R 9) [34,68,384,129,264,16] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129,264,16] 13 (by decide) (choices 1) [1,32] r4918 c4918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1664
  · exact u1665

def b4919 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(3,6),(4,6)], upper := (rows 35 70 388 137 280 96 113 177 305), lower := (rows 35 70 388 137 280 96 64 128 256), losses := [] }

theorem u4919 : Upper (D 9) (R 9) [34,68,384,129,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4919 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u4919
end Delivery.IrregularNine14.P09
