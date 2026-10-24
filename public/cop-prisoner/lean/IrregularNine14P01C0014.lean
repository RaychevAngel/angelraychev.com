import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0001

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b840 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 262 73 144 160 106 170 298), lower := (rows 53 82 262 73 144 160 64 128 256), losses := [] }

theorem u840 : Upper (D 1) (R 1) [52,80,258,65,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b840
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b841 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 53 82 262 104 144 33 202 138 394), lower := (rows 53 82 262 104 144 33 64 128 256), losses := [] }

theorem u841 : Upper (D 1) (R 1) [52,80,258,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b841
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b842 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 53 82 262 104 144 34 201 137 393), lower := (rows 53 82 262 104 144 34 64 128 256), losses := [] }

theorem u842 : Upper (D 1) (R 1) [52,80,258,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b842
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b843 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 53 82 262 104 144 40 195 131 387), lower := (rows 53 82 262 104 144 40 64 128 256), losses := [] }

theorem u843 : Upper (D 1) (R 1) [52,80,258,96,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b843
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b844 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 262 104 144 160 75 139 267), lower := (rows 53 82 262 104 144 160 64 128 256), losses := [] }

theorem u844 : Upper (D 1) (R 1) [52,80,258,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b844
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b845 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 262 137 144 34 104 232 360), lower := (rows 53 82 262 137 144 34 64 128 256), losses := [] }

theorem u845 : Upper (D 1) (R 1) [52,80,258,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b845
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b846 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 53 82 262 137 144 40 98 226 354), lower := (rows 53 82 262 137 144 40 64 128 256), losses := [] }

theorem u846 : Upper (D 1) (R 1) [52,80,258,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b846
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r847 : Route 9 := (fun mask => (mask,id))

def c847 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u847 : Upper (D 1) (R 1) [52,80,258,129,128,64] 13 := by
  apply FastRouting.sound _ _ [52,80,258,129,128,64] 13 (by decide) (choices 1) [2,8,32] r847 c847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u89
  · exact u90
  · exact u91

def b848 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 53 82 262 138 144 33 104 232 360), lower := (rows 53 82 262 138 144 33 64 128 256), losses := [] }

theorem u848 : Upper (D 1) (R 1) [52,80,258,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b848
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b849 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 53 82 262 138 144 40 97 225 353), lower := (rows 53 82 262 138 144 40 64 128 256), losses := [] }

theorem u849 : Upper (D 1) (R 1) [52,80,258,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b849
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r850 : Route 9 := (fun mask => (mask,id))

def c850 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u850 : Upper (D 1) (R 1) [52,80,258,130,128,64] 13 := by
  apply FastRouting.sound _ _ [52,80,258,130,128,64] 13 (by decide) (choices 1) [1,8,32] r850 c850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u92
  · exact u93
  · exact u94

def b851 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 53 82 262 168 144 33 74 202 330), lower := (rows 53 82 262 168 144 33 64 128 256), losses := [] }

theorem u851 : Upper (D 1) (R 1) [52,80,258,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b851
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b852 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 262 168 144 34 73 201 329), lower := (rows 53 82 262 168 144 34 64 128 256), losses := [] }

theorem u852 : Upper (D 1) (R 1) [52,80,258,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b852
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b853 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 53 82 262 168 144 40 67 195 323), lower := (rows 53 82 262 168 144 40 64 128 256), losses := [] }

theorem u853 : Upper (D 1) (R 1) [52,80,258,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b853
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r854 : Route 9 := (fun mask => (mask,id))

def c854 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u854 : Upper (D 1) (R 1) [52,80,258,160,128,64] 13 := by
  apply FastRouting.sound _ _ [52,80,258,160,128,64] 13 (by decide) (choices 1) [1,2,8] r854 c854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u95
  · exact u96
  · exact u97

def b855 : PairBound 9 := { available := 162, camps := [], pairs := [(2,4)], upper := (rows 53 82 268 73 144 34 226 162 418), lower := (rows 53 82 268 73 144 34 64 128 256), losses := [{ target := 4, region := (rows 1 2 5 9 0 34 98 162 290), good := (rows 493 482 268 77 128 482 64 128 256) }] }

theorem u855 : Upper (D 1) (R 1) [52,80,264,65,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b855
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b856 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 268 73 144 160 98 162 290), lower := (rows 53 82 268 73 144 160 64 128 256), losses := [] }

theorem u856 : Upper (D 1) (R 1) [52,80,264,65,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b856
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b857 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 53 82 324 42 144 33 202 138 394), lower := (rows 53 82 324 42 144 33 64 128 256), losses := [] }

theorem u857 : Upper (D 1) (R 1) [52,80,320,34,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b857
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b858 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 53 82 324 42 144 34 201 137 393), lower := (rows 53 82 324 42 144 34 64 128 256), losses := [] }

theorem u858 : Upper (D 1) (R 1) [52,80,320,34,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b858
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b859 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 53 82 324 42 144 40 195 131 387), lower := (rows 53 82 324 42 144 40 64 128 256), losses := [] }

theorem u859 : Upper (D 1) (R 1) [52,80,320,34,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b859
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b860 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 324 42 144 160 75 139 267), lower := (rows 53 82 324 42 144 160 64 128 256), losses := [] }

theorem u860 : Upper (D 1) (R 1) [52,80,320,34,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b860
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r861 : Route 9 := (fun mask => (mask,id))

def c861 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u861 : Upper (D 1) (R 1) [52,80,320,129,128,2] 13 := by
  apply FastRouting.sound _ _ [52,80,320,129,128,2] 13 (by decide) (choices 1) [2,8,32] r861 c861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u98
  · exact u99
  · exact u100

def b862 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 53 82 324 137 144 40 98 162 290), lower := (rows 53 82 324 137 144 40 64 128 256), losses := [] }

theorem u862 : Upper (D 1) (R 1) [52,80,320,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b862
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b863 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 53 82 324 138 144 33 106 170 298), lower := (rows 53 82 324 138 144 33 64 128 256), losses := [] }

theorem u863 : Upper (D 1) (R 1) [52,80,320,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b863
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r864 : Route 9 := (fun mask => (mask,id))

def c864 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u864 : Upper (D 1) (R 1) [52,80,320,130,128,2] 13 := by
  apply FastRouting.sound _ _ [52,80,320,130,128,2] 13 (by decide) (choices 1) [1,8,32] r864 c864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u101
  · exact u102
  · exact u103

def b865 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 53 82 324 138 144 40 99 163 291), lower := (rows 53 82 324 138 144 40 64 128 256), losses := [] }

theorem u865 : Upper (D 1) (R 1) [52,80,320,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b865
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b866 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 53 82 324 168 144 33 74 138 266), lower := (rows 53 82 324 168 144 33 64 128 256), losses := [] }

theorem u866 : Upper (D 1) (R 1) [52,80,320,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b866
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r867 : Route 9 := (fun mask => (mask,id))

def c867 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u867 : Upper (D 1) (R 1) [52,80,320,160,128,2] 13 := by
  apply FastRouting.sound _ _ [52,80,320,160,128,2] 13 (by decide) (choices 1) [1,2,8] r867 c867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u104
  · exact u105
  · exact u106

def b868 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 53 82 324 168 144 40 67 131 259), lower := (rows 53 82 324 168 144 40 64 128 256), losses := [] }

theorem u868 : Upper (D 1) (R 1) [52,80,320,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b868
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b869 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 53, targets := 64 }], pairs := [(0,6)], upper := (rows 53 194 7 328 18 160 120 184 312), lower := (rows 53 194 7 328 18 160 64 128 256), losses := [] }

theorem u869 : Upper (D 1) (R 1) [52,192,3,320,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b869
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b870 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 194 7 328 24 160 114 178 306), lower := (rows 53 194 7 328 24 160 64 128 256), losses := [] }

theorem u870 : Upper (D 1) (R 1) [52,192,3,320,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b870
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b871 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 7 328 48 160 90 154 282), lower := (rows 53 194 7 328 48 160 64 128 256), losses := [] }

theorem u871 : Upper (D 1) (R 1) [52,192,3,320,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b871
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b872 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6)], upper := (rows 53 194 13 266 18 48 224 224 480), lower := (rows 53 194 13 266 18 48 64 128 256), losses := [] }

theorem u872 : Upper (D 1) (R 1) [52,192,9,258,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b872
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b873 : PairBound 9 := { available := 176, camps := [], pairs := [(0,7)], upper := (rows 53 194 13 266 18 96 240 176 432), lower := (rows 53 194 13 266 18 96 64 128 256), losses := [{ target := 7, region := (rows 9 2 12 8 26 98 64 0 256), good := (rows 53 114 29 319 50 96 96 0 256) }] }

theorem u873 : Upper (D 1) (R 1) [52,192,9,258,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b873
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b874 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 13 266 48 96 210 146 402), lower := (rows 53 194 13 266 48 96 64 128 256), losses := [] }

theorem u874 : Upper (D 1) (R 1) [52,192,9,258,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b874
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b875 : PairBound 9 := { available := 50, camps := [], pairs := [(0,1)], upper := (rows 53 194 13 266 80 160 114 178 306), lower := (rows 53 194 13 266 80 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 82 162 64 128 256), good := (rows 53 240 13 317 80 160 80 160 256) }] }

theorem u875 : Upper (D 1) (R 1) [52,192,9,258,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b875
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b876 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 53 194 13 328 18 34 240 176 432), lower := (rows 53 194 13 328 18 34 64 128 256), losses := [] }

theorem u876 : Upper (D 1) (R 1) [52,192,9,320,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b876
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b877 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 13 328 18 48 226 162 418), lower := (rows 53 194 13 328 18 48 64 128 256), losses := [] }

theorem u877 : Upper (D 1) (R 1) [52,192,9,320,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b877
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r878 : Route 9 := (fun mask => (mask,id))

def c878 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u878 : Upper (D 1) (R 1) [52,192,9,320,2,128] 13 := by
  apply FastRouting.sound _ _ [52,192,9,320,2,128] 13 (by decide) (choices 1) [2,16,32] r878 c878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u107
  · exact u108
  · exact u109

def b879 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 13 328 48 160 82 146 274), lower := (rows 53 194 13 328 48 160 64 128 256), losses := [] }

theorem u879 : Upper (D 1) (R 1) [52,192,9,320,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b879
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b880 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 392, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 14 265 18 96 240 176 432), lower := (rows 53 194 14 265 18 96 64 128 256), losses := [] }

theorem u880 : Upper (D 1) (R 1) [52,192,10,257,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b880
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b881 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 14 265 48 96 210 146 402), lower := (rows 53 194 14 265 48 96 64 128 256), losses := [] }

theorem u881 : Upper (D 1) (R 1) [52,192,10,257,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b881
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b882 : PairBound 9 := { available := 50, camps := [], pairs := [(0,1)], upper := (rows 53 194 14 265 80 160 114 178 306), lower := (rows 53 194 14 265 80 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 82 162 64 128 256), good := (rows 53 240 61 265 80 160 80 160 256) }] }

theorem u882 : Upper (D 1) (R 1) [52,192,10,257,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b882
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b883 : PairBound 9 := { available := 50, camps := [], pairs := [(3,6)], upper := (rows 53 194 76 265 18 160 114 178 306), lower := (rows 53 194 76 265 18 160 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 18 179 0 146 274), good := (rows 445 434 12 297 434 160 0 160 256) }] }

theorem u883 : Upper (D 1) (R 1) [52,192,72,257,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b883
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b884 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 76 265 48 160 82 146 274), lower := (rows 53 194 76 265 48 160 64 128 256), losses := [] }

theorem u884 : Upper (D 1) (R 1) [52,192,72,257,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b884
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b885 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 194 76 266 17 160 114 178 306), lower := (rows 53 194 76 266 17 160 64 128 256), losses := [] }

theorem u885 : Upper (D 1) (R 1) [52,192,72,258,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b885
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b886 : PairBound 9 := { available := 49, camps := [], pairs := [(0,6)], upper := (rows 53 194 76 266 18 160 113 177 305), lower := (rows 53 194 76 266 18 160 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 26 167 0 133 261), good := (rows 437 178 445 314 50 160 0 160 256) }] }

theorem u886 : Upper (D 1) (R 1) [52,192,72,258,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b886
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b887 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 76 266 48 160 83 147 275), lower := (rows 53 194 76 266 48 160 64 128 256), losses := [] }

theorem u887 : Upper (D 1) (R 1) [52,192,72,258,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b887
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b888 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 194 76 392 17 34 114 178 306), lower := (rows 53 194 76 392 17 34 64 128 256), losses := [] }

theorem u888 : Upper (D 1) (R 1) [52,192,72,384,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b888
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b889 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 53 194 76 392 18 34 113 177 305), lower := (rows 53 194 76 392 18 34 64 128 256), losses := [] }

theorem u889 : Upper (D 1) (R 1) [52,192,72,384,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b889
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b890 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 76 392 18 48 99 163 291), lower := (rows 53 194 76 392 18 48 64 128 256), losses := [] }

theorem u890 : Upper (D 1) (R 1) [52,192,72,384,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b890
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b891 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 53 194 262 11 24 96 240 176 432), lower := (rows 53 194 262 11 24 96 64 128 256), losses := [] }

theorem u891 : Upper (D 1) (R 1) [52,192,258,3,8,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b891
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b892 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 262 11 48 96 216 152 408), lower := (rows 53 194 262 11 48 96 64 128 256), losses := [] }

theorem u892 : Upper (D 1) (R 1) [52,192,258,3,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b892
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b893 : PairBound 9 := { available := 56, camps := [], pairs := [(0,1)], upper := (rows 53 194 262 11 80 160 120 184 312), lower := (rows 53 194 262 11 80 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 90 170 72 136 264), good := (rows 53 240 309 505 80 160 80 160 256) }] }

theorem u893 : Upper (D 1) (R 1) [52,192,258,3,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b893
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b894 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 262 73 18 160 120 184 312), lower := (rows 53 194 262 73 18 160 64 128 256), losses := [] }

theorem u894 : Upper (D 1) (R 1) [52,192,258,65,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b894
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b895 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 194 262 73 24 160 114 178 306), lower := (rows 53 194 262 73 24 160 64 128 256), losses := [] }

theorem u895 : Upper (D 1) (R 1) [52,192,258,65,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b895
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b896 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 262 73 48 160 90 154 282), lower := (rows 53 194 262 73 48 160 64 128 256), losses := [] }

theorem u896 : Upper (D 1) (R 1) [52,192,258,65,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b896
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b897 : PairBound 9 := { available := 176, camps := [], pairs := [(2,1)], upper := (rows 53 194 268 11 18 96 240 176 432), lower := (rows 53 194 268 11 18 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 123 81 145 273), good := (rows 501 224 300 493 496 96 96 128 256) }] }

theorem u897 : Upper (D 1) (R 1) [52,192,264,3,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b897
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b898 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 268 11 48 96 210 146 402), lower := (rows 53 194 268 11 48 96 64 128 256), losses := [] }

theorem u898 : Upper (D 1) (R 1) [52,192,264,3,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b898
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r899 : Route 9 := (fun mask => (mask,id))

def c899 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u899 : Upper (D 1) (R 1) [52,192,264,3,64,128] 13 := by
  apply FastRouting.sound _ _ [52,192,264,3,64,128] 13 (by decide) (choices 1) [2,16,32] r899 c899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u110
  · exact u111
  · exact u112

#print axioms u899
end Delivery.IrregularNine14.P01
