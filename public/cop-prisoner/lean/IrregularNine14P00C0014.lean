import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0002

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b840 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 275 98 52 137 144 40 69 197 325), lower := (rows 275 98 52 137 144 40 64 128 256), losses := [] }

theorem u840 : Upper (D 0) (R 0) [274,96,48,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b840
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b841 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 52 137 144 96 77 141 269), lower := (rows 275 98 52 137 144 96 64 128 256), losses := [] }

theorem u841 : Upper (D 0) (R 0) [274,96,48,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b841
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b842 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 275 98 52 140 17 33 200 200 456), lower := (rows 275 98 52 140 17 33 64 128 256), losses := [] }

theorem u842 : Upper (D 0) (R 0) [274,96,48,132,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b842
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b843 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 98 52 140 17 40 193 193 449), lower := (rows 275 98 52 140 17 40 64 128 256), losses := [] }

theorem u843 : Upper (D 0) (R 0) [274,96,48,132,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b843
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b844 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 52 140 17 96 201 137 393), lower := (rows 275 98 52 140 17 96 64 128 256), losses := [] }

theorem u844 : Upper (D 0) (R 0) [274,96,48,132,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b844
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r845 : Route 9 := (fun mask => (mask,id))

def c845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u845 : Upper (D 0) (R 0) [274,96,48,132,1,128] 13 := by
  apply FastRouting.sound _ _ [274,96,48,132,1,128] 13 (by decide) (choices 1) [1,8] r845 c845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u144
  · exact u145

def b846 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 52 140 144 33 73 201 329), lower := (rows 275 98 52 140 144 33 64 128 256), losses := [] }

theorem u846 : Upper (D 0) (R 0) [274,96,48,132,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b846
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b847 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 275 98 52 140 144 40 65 193 321), lower := (rows 275 98 52 140 144 40 64 128 256), losses := [] }

theorem u847 : Upper (D 0) (R 0) [274,96,48,132,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b847
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b848 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 52 140 144 96 73 137 265), lower := (rows 275 98 52 140 144 96 64 128 256), losses := [] }

theorem u848 : Upper (D 0) (R 0) [274,96,48,132,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b848
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b849 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 275 98 52 200 17 33 204 140 396), lower := (rows 275 98 52 200 17 33 64 128 256), losses := [] }

theorem u849 : Upper (D 0) (R 0) [274,96,48,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b849
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b850 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 275 98 52 200 17 36 201 137 393), lower := (rows 275 98 52 200 17 36 64 128 256), losses := [] }

theorem u850 : Upper (D 0) (R 0) [274,96,48,192,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b850
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b851 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 275 98 52 200 17 40 197 133 389), lower := (rows 275 98 52 200 17 40 64 128 256), losses := [] }

theorem u851 : Upper (D 0) (R 0) [274,96,48,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b851
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b852 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 275 98 52 200 17 160 77 141 269), lower := (rows 275 98 52 200 17 160 64 128 256), losses := [] }

theorem u852 : Upper (D 0) (R 0) [274,96,48,192,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b852
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b853 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 52 200 144 33 77 141 269), lower := (rows 275 98 52 200 144 33 64 128 256), losses := [] }

theorem u853 : Upper (D 0) (R 0) [274,96,48,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b853
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b854 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 275 98 52 200 144 36 73 137 265), lower := (rows 275 98 52 200 144 36 64 128 256), losses := [] }

theorem u854 : Upper (D 0) (R 0) [274,96,48,192,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b854
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b855 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 275 98 52 200 144 40 69 133 261), lower := (rows 275 98 52 200 144 40 64 128 256), losses := [] }

theorem u855 : Upper (D 0) (R 0) [274,96,48,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b855
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b856 : PairBound 9 := { available := 88, camps := [], pairs := [], upper := (rows 275 98 133 168 17 36 88 216 344), lower := (rows 275 98 133 168 17 36 64 128 256), losses := [] }

theorem u856 : Upper (D 0) (R 0) [274,96,129,160,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b856
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b857 : PairBound 9 := { available := 84, camps := [], pairs := [], upper := (rows 275 98 133 168 17 40 84 212 340), lower := (rows 275 98 133 168 17 40 64 128 256), losses := [] }

theorem u857 : Upper (D 0) (R 0) [274,96,129,160,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b857
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b858 : PairBound 9 := { available := 76, camps := [{ cop := 2, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 275 98 133 168 17 48 76 204 332), lower := (rows 275 98 133 168 17 48 64 128 256), losses := [] }

theorem u858 : Upper (D 0) (R 0) [274,96,129,160,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b858
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b859 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 133 168 17 96 92 156 284), lower := (rows 275 98 133 168 17 96 64 128 256), losses := [] }

theorem u859 : Upper (D 0) (R 0) [274,96,129,160,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b859
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b860 : PairBound 9 := { available := 76, camps := [], pairs := [(1,0)], upper := (rows 275 98 148 168 17 33 76 204 332), lower := (rows 275 98 148 168 17 33 64 128 256), losses := [{ target := 0, region := (rows 0 42 21 42 16 32 97 161 289), good := (rows 478 490 148 490 468 494 64 128 256) }] }

theorem u860 : Upper (D 0) (R 0) [274,96,144,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b860
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b861 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 275 98 148 168 17 36 73 201 329), lower := (rows 275 98 148 168 17 36 64 128 256), losses := [] }

theorem u861 : Upper (D 0) (R 0) [274,96,144,160,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b861
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b862 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 275 98 148 168 17 40 69 197 325), lower := (rows 275 98 148 168 17 40 64 128 256), losses := [] }

theorem u862 : Upper (D 0) (R 0) [274,96,144,160,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b862
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b863 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 148 168 17 96 77 141 269), lower := (rows 275 98 148 168 17 96 64 128 256), losses := [] }

theorem u863 : Upper (D 0) (R 0) [274,96,144,160,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b863
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b864 : PairBound 9 := { available := 28, camps := [], pairs := [(3,5)], upper := (rows 275 98 164 200 17 33 92 156 284), lower := (rows 275 98 164 200 17 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 49 0 68 132 260), good := (rows 275 82 476 200 17 17 64 128 256) }] }

theorem u864 : Upper (D 0) (R 0) [274,96,160,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b864
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b865 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 275 98 164 200 17 36 89 153 281), lower := (rows 275 98 164 200 17 36 64 128 256), losses := [] }

theorem u865 : Upper (D 0) (R 0) [274,96,160,192,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b865
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b866 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 275 98 164 200 17 40 85 149 277), lower := (rows 275 98 164 200 17 40 64 128 256), losses := [] }

theorem u866 : Upper (D 0) (R 0) [274,96,160,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b866
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m867_1 : Upper (D 0) (R 0) [274,96,160,192,1,16,1] 13 :=
  permutation_upper _ _ _ [274,96,160,192,1,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u146

theorem m867_4 : Upper (D 0) (R 0) [274,96,160,192,1,16,4] 13 :=
  permutation_upper _ _ _ [274,96,160,192,1,8,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u148

theorem m867_8 : Upper (D 0) (R 0) [274,96,160,192,1,16,8] 13 :=
  permutation_upper _ _ _ [274,96,160,192,1,4,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u147

def r867 : Route 9 := (fun mask => (mask,id))

def c867 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u867 : Upper (D 0) (R 0) [274,96,160,192,1,16] 13 := by
  apply FastRouting.sound _ _ [274,96,160,192,1,16] 13 (by decide) (choices 1) [1,4,8] r867 c867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m867_1
  · exact m867_4
  · exact m867_8

def b868 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 305 7 14 88 144 33 224 224 480), lower := (rows 305 7 14 88 144 33 64 128 256), losses := [] }

theorem u868 : Upper (D 0) (R 0) [304,5,10,80,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b868
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b869 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 305 7 14 88 144 96 225 161 417), lower := (rows 305 7 14 88 144 96 64 128 256), losses := [] }

theorem u869 : Upper (D 0) (R 0) [304,5,10,80,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b869
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b870 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 78, targets := 128 }], pairs := [(1,7)], upper := (rows 305 7 14 88 144 160 97 225 353), lower := (rows 305 7 14 88 144 160 64 128 256), losses := [] }

theorem u870 : Upper (D 0) (R 0) [304,5,10,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b870
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b871 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 305 7 70 137 24 160 112 240 368), lower := (rows 305 7 70 137 24 160 64 128 256), losses := [] }

theorem u871 : Upper (D 0) (R 0) [304,5,66,129,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b871
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b872 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 70 137 48 160 88 216 344), lower := (rows 305 7 70 137 48 160 64 128 256), losses := [] }

theorem u872 : Upper (D 0) (R 0) [304,5,66,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b872
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b873 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 425, targets := 64 }], pairs := [(0,6)], upper := (rows 305 7 70 137 80 160 120 184 312), lower := (rows 305 7 70 137 80 160 64 128 256), losses := [] }

theorem u873 : Upper (D 0) (R 0) [304,5,66,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b873
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b874 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 305 7 76 137 18 96 240 176 432), lower := (rows 305 7 76 137 18 96 64 128 256), losses := [] }

theorem u874 : Upper (D 0) (R 0) [304,5,72,129,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b874
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b875 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 305 7 76 137 18 160 112 240 368), lower := (rows 305 7 76 137 18 160 64 128 256), losses := [] }

theorem u875 : Upper (D 0) (R 0) [304,5,72,129,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b875
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b876 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 76 137 48 96 210 146 402), lower := (rows 305 7 76 137 48 96 64 128 256), losses := [] }

theorem u876 : Upper (D 0) (R 0) [304,5,72,129,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b876
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b877 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 76 137 48 160 82 210 338), lower := (rows 305 7 76 137 48 160 64 128 256), losses := [] }

theorem u877 : Upper (D 0) (R 0) [304,5,72,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b877
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r878 : Route 9 := (fun mask => (mask,id))

def c878 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u878 : Upper (D 0) (R 0) [304,5,72,129,64,128] 13 := by
  apply FastRouting.sound _ _ [304,5,72,129,64,128] 13 (by decide) (choices 1) [2,16,32] r878 c878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u149
  · exact u150
  · exact u151

def b879 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 305 7 76 152 17 34 224 224 480), lower := (rows 305 7 76 152 17 34 64 128 256), losses := [] }

theorem u879 : Upper (D 0) (R 0) [304,5,72,144,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b879
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r880 : Route 9 := (fun mask => (mask,id))

def c880 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u880 : Upper (D 0) (R 0) [304,5,72,144,1,64] 13 := by
  apply FastRouting.sound _ _ [304,5,72,144,1,64] 13 (by decide) (choices 1) [2,32,128] r880 c880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u152
  · exact u153
  · exact u154

def r881 : Route 9 := (fun mask => (mask,id))

def c881 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u881 : Upper (D 0) (R 0) [304,5,72,144,1,128] 13 := by
  apply FastRouting.sound _ _ [304,5,72,144,1,128] 13 (by decide) (choices 1) [2,32] r881 c881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u155
  · exact u156

def r882 : Route 9 := (fun mask => (mask,id))

def c882 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u882 : Upper (D 0) (R 0) [304,5,72,144,64,1] 13 := by
  apply FastRouting.sound _ _ [304,5,72,144,64,1] 13 (by decide) (choices 1) [2,32,128] r882 c882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u157
  · exact u158
  · exact u159

def b883 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 305 7 76 152 80 34 225 161 417), lower := (rows 305 7 76 152 80 34 64 128 256), losses := [] }

theorem u883 : Upper (D 0) (R 0) [304,5,72,144,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b883
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r884 : Route 9 := (fun mask => (mask,id))

def c884 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u884 : Upper (D 0) (R 0) [304,5,72,144,64,128] 13 := by
  apply FastRouting.sound _ _ [304,5,72,144,64,128] 13 (by decide) (choices 1) [1,2,32] r884 c884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u160
  · exact u161
  · exact u162

def b885 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 305 7 196 73 18 160 120 184 312), lower := (rows 305 7 196 73 18 160 64 128 256), losses := [] }

theorem u885 : Upper (D 0) (R 0) [304,5,192,65,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b885
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b886 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 305 7 196 73 24 160 114 178 306), lower := (rows 305 7 196 73 24 160 64 128 256), losses := [] }

theorem u886 : Upper (D 0) (R 0) [304,5,192,65,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b886
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b887 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 196 73 48 160 90 154 282), lower := (rows 305 7 196 73 48 160 64 128 256), losses := [] }

theorem u887 : Upper (D 0) (R 0) [304,5,192,65,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b887
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b888 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 305 7 196 88 17 34 232 168 424), lower := (rows 305 7 196 88 17 34 64 128 256), losses := [] }

theorem u888 : Upper (D 0) (R 0) [304,5,192,80,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b888
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b889 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 7 196 88 17 40 226 162 418), lower := (rows 305 7 196 88 17 40 64 128 256), losses := [] }

theorem u889 : Upper (D 0) (R 0) [304,5,192,80,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b889
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r890 : Route 9 := (fun mask => (mask,id))

def c890 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u890 : Upper (D 0) (R 0) [304,5,192,80,1,128] 13 := by
  apply FastRouting.sound _ _ [304,5,192,80,1,128] 13 (by decide) (choices 1) [2,8,32] r890 c890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u163
  · exact u164
  · exact u165

def b891 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 305 14 69 137 18 96 240 176 432), lower := (rows 305 14 69 137 18 96 64 128 256), losses := [] }

theorem u891 : Upper (D 0) (R 0) [304,12,65,129,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b891
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b892 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 69 137 48 96 210 146 402), lower := (rows 305 14 69 137 48 96 64 128 256), losses := [] }

theorem u892 : Upper (D 0) (R 0) [304,12,65,129,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b892
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r893 : Route 9 := (fun mask => (mask,id))

def c893 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u893 : Upper (D 0) (R 0) [304,12,65,129,64,128] 13 := by
  apply FastRouting.sound _ _ [304,12,65,129,64,128] 13 (by decide) (choices 1) [2,16,32] r893 c893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u166
  · exact u167
  · exact u168

def b894 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 305 14 69 152 17 34 224 224 480), lower := (rows 305 14 69 152 17 34 64 128 256), losses := [] }

theorem u894 : Upper (D 0) (R 0) [304,12,65,144,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b894
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r895 : Route 9 := (fun mask => (mask,id))

def c895 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u895 : Upper (D 0) (R 0) [304,12,65,144,1,64] 13 := by
  apply FastRouting.sound _ _ [304,12,65,144,1,64] 13 (by decide) (choices 1) [2,32,128] r895 c895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u169
  · exact u170
  · exact u171

def r896 : Route 9 := (fun mask => (mask,id))

def c896 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u896 : Upper (D 0) (R 0) [304,12,65,144,1,128] 13 := by
  apply FastRouting.sound _ _ [304,12,65,144,1,128] 13 (by decide) (choices 1) [2,32] r896 c896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u172
  · exact u173

def r897 : Route 9 := (fun mask => (mask,id))

def c897 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u897 : Upper (D 0) (R 0) [304,12,65,144,64,1] 13 := by
  apply FastRouting.sound _ _ [304,12,65,144,64,1] 13 (by decide) (choices 1) [2,32,128] r897 c897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u174
  · exact u175
  · exact u176

def b898 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 305 14 69 152 80 34 225 161 417), lower := (rows 305 14 69 152 80 34 64 128 256), losses := [] }

theorem u898 : Upper (D 0) (R 0) [304,12,65,144,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b898
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r899 : Route 9 := (fun mask => (mask,id))

def c899 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u899 : Upper (D 0) (R 0) [304,12,65,144,64,128] 13 := by
  apply FastRouting.sound _ _ [304,12,65,144,64,128] 13 (by decide) (choices 1) [1,2,32] r899 c899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u177
  · exact u178
  · exact u179

#print axioms u899
end Delivery.IrregularNine14.P00
