import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0002

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b840 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 73 176 33 208 208 464), lower := (rows 35 7 268 73 176 33 64 128 256), losses := [] }

theorem u840 : Upper (D 3) (R 3) [34,5,264,65,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b840
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b841 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 7 268 73 176 48 193 193 449), lower := (rows 35 7 268 73 176 48 64 128 256), losses := [] }

theorem u841 : Upper (D 3) (R 3) [34,5,264,65,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b841
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b842 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 268 73 176 96 209 145 401), lower := (rows 35 7 268 73 176 96 64 128 256), losses := [] }

theorem u842 : Upper (D 3) (R 3) [34,5,264,65,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b842
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b843 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 268 73 176 160 81 209 337), lower := (rows 35 7 268 73 176 160 64 128 256), losses := [] }

theorem u843 : Upper (D 3) (R 3) [34,5,264,65,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b843
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b844 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 73 208 33 240 176 432), lower := (rows 35 7 268 73 208 33 64 128 256), losses := [] }

theorem u844 : Upper (D 3) (R 3) [34,5,264,65,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b844
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b845 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 268 73 208 48 225 161 417), lower := (rows 35 7 268 73 208 48 64 128 256), losses := [] }

theorem u845 : Upper (D 3) (R 3) [34,5,264,65,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b845
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r846 : Route 9 := (fun mask => (mask,id))

def c846 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u846 : Upper (D 3) (R 3) [34,5,264,65,192,128] 13 := by
  apply FastRouting.sound _ _ [34,5,264,65,192,128] 13 (by decide) (choices 1) [1,16,32] r846 c846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u121
  · exact u122
  · exact u123

def b847 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 88 145 33 224 224 480), lower := (rows 35 7 268 88 145 33 64 128 256), losses := [] }

theorem u847 : Upper (D 3) (R 3) [34,5,264,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b847
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b848 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 268 88 145 96 225 161 417), lower := (rows 35 7 268 88 145 96 64 128 256), losses := [] }

theorem u848 : Upper (D 3) (R 3) [34,5,264,80,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b848
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b849 : PairBound 9 := { available := 97, camps := [], pairs := [(1,7)], upper := (rows 35 7 268 88 145 160 97 225 353), lower := (rows 35 7 268 88 145 160 64 128 256), losses := [{ target := 7, region := (rows 1 18 20 24 16 32 65 0 257), good := (rows 355 327 268 94 351 32 64 0 256) }] }

theorem u849 : Upper (D 3) (R 3) [34,5,264,80,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b849
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b850 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 88 176 33 193 193 449), lower := (rows 35 7 268 88 176 33 64 128 256), losses := [] }

theorem u850 : Upper (D 3) (R 3) [34,5,264,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b850
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b851 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 268 88 176 96 193 129 385), lower := (rows 35 7 268 88 176 96 64 128 256), losses := [] }

theorem u851 : Upper (D 3) (R 3) [34,5,264,80,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b851
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b852 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 268 88 176 160 65 193 321), lower := (rows 35 7 268 88 176 160 64 128 256), losses := [] }

theorem u852 : Upper (D 3) (R 3) [34,5,264,80,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b852
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b853 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 200 81 33 240 176 432), lower := (rows 35 7 268 200 81 33 64 128 256), losses := [] }

theorem u853 : Upper (D 3) (R 3) [34,5,264,192,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b853
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b854 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 268 200 81 48 225 161 417), lower := (rows 35 7 268 200 81 48 64 128 256), losses := [] }

theorem u854 : Upper (D 3) (R 3) [34,5,264,192,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b854
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b855 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 35 7 268 200 81 160 113 177 305), lower := (rows 35 7 268 200 81 160 64 128 256), losses := [] }

theorem u855 : Upper (D 3) (R 3) [34,5,264,192,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b855
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b856 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 200 112 33 209 145 401), lower := (rows 35 7 268 200 112 33 64 128 256), losses := [] }

theorem u856 : Upper (D 3) (R 3) [34,5,264,192,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b856
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b857 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 7 268 200 112 48 193 129 385), lower := (rows 35 7 268 200 112 48 64 128 256), losses := [] }

theorem u857 : Upper (D 3) (R 3) [34,5,264,192,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b857
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b858 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 35 7 268 200 112 160 81 145 273), lower := (rows 35 7 268 200 112 160 64 128 256), losses := [] }

theorem u858 : Upper (D 3) (R 3) [34,5,264,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b858
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b859 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 25 152 33 224 224 480), lower := (rows 35 7 324 25 152 33 64 128 256), losses := [] }

theorem u859 : Upper (D 3) (R 3) [34,5,320,17,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b859
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b860 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 324 25 152 96 225 161 417), lower := (rows 35 7 324 25 152 96 64 128 256), losses := [] }

theorem u860 : Upper (D 3) (R 3) [34,5,320,17,136,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b860
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b861 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 324 25 152 160 97 225 353), lower := (rows 35 7 324 25 152 160 64 128 256), losses := [] }

theorem u861 : Upper (D 3) (R 3) [34,5,320,17,136,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b861
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b862 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 25 208 33 232 168 424), lower := (rows 35 7 324 25 208 33 64 128 256), losses := [] }

theorem u862 : Upper (D 3) (R 3) [34,5,320,17,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b862
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b863 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 324 25 208 40 225 161 417), lower := (rows 35 7 324 25 208 40 64 128 256), losses := [] }

theorem u863 : Upper (D 3) (R 3) [34,5,320,17,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b863
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r864 : Route 9 := (fun mask => (mask,id))

def c864 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u864 : Upper (D 3) (R 3) [34,5,320,17,192,128] 13 := by
  apply FastRouting.sound _ _ [34,5,320,17,192,128] 13 (by decide) (choices 1) [1,8,32] r864 c864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u124
  · exact u125
  · exact u126

def b865 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 56 145 33 200 200 456), lower := (rows 35 7 324 56 145 33 64 128 256), losses := [] }

theorem u865 : Upper (D 3) (R 3) [34,5,320,48,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b865
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b866 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 7 324 56 145 40 193 193 449), lower := (rows 35 7 324 56 145 40 64 128 256), losses := [] }

theorem u866 : Upper (D 3) (R 3) [34,5,320,48,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b866
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b867 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 324 56 145 96 201 137 393), lower := (rows 35 7 324 56 145 96 64 128 256), losses := [] }

theorem u867 : Upper (D 3) (R 3) [34,5,320,48,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b867
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b868 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 324 56 145 160 73 201 329), lower := (rows 35 7 324 56 145 160 64 128 256), losses := [] }

theorem u868 : Upper (D 3) (R 3) [34,5,320,48,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b868
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b869 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 56 208 33 201 137 393), lower := (rows 35 7 324 56 208 33 64 128 256), losses := [] }

theorem u869 : Upper (D 3) (R 3) [34,5,320,48,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b869
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b870 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 7 324 56 208 40 193 129 385), lower := (rows 35 7 324 56 208 40 64 128 256), losses := [] }

theorem u870 : Upper (D 3) (R 3) [34,5,320,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b870
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b871 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 324 56 208 160 73 137 265), lower := (rows 35 7 324 56 208 160 64 128 256), losses := [] }

theorem u871 : Upper (D 3) (R 3) [34,5,320,48,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b871
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b872 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 88 145 33 232 168 424), lower := (rows 35 7 324 88 145 33 64 128 256), losses := [] }

theorem u872 : Upper (D 3) (R 3) [34,5,320,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b872
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b873 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 324 88 145 40 225 161 417), lower := (rows 35 7 324 88 145 40 64 128 256), losses := [] }

theorem u873 : Upper (D 3) (R 3) [34,5,320,80,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b873
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r874 : Route 9 := (fun mask => (mask,id))

def c874 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u874 : Upper (D 3) (R 3) [34,5,320,80,129,128] 13 := by
  apply FastRouting.sound _ _ [34,5,320,80,129,128] 13 (by decide) (choices 1) [1,8,32] r874 c874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u127
  · exact u128
  · exact u129

def b875 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 88 176 33 201 137 393), lower := (rows 35 7 324 88 176 33 64 128 256), losses := [] }

theorem u875 : Upper (D 3) (R 3) [34,5,320,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b875
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b876 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 7 324 88 176 40 193 129 385), lower := (rows 35 7 324 88 176 40 64 128 256), losses := [] }

theorem u876 : Upper (D 3) (R 3) [34,5,320,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b876
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b877 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 324 88 176 160 73 137 265), lower := (rows 35 7 324 88 176 160 64 128 256), losses := [] }

theorem u877 : Upper (D 3) (R 3) [34,5,320,80,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b877
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b878 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 324 104 145 33 216 152 408), lower := (rows 35 7 324 104 145 33 64 128 256), losses := [] }

theorem u878 : Upper (D 3) (R 3) [34,5,320,96,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b878
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b879 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 7 324 104 145 40 209 145 401), lower := (rows 35 7 324 104 145 40 64 128 256), losses := [] }

theorem u879 : Upper (D 3) (R 3) [34,5,320,96,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b879
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b880 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 35 7 324 104 145 48 201 137 393), lower := (rows 35 7 324 104 145 48 64 128 256), losses := [] }

theorem u880 : Upper (D 3) (R 3) [34,5,320,96,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b880
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r881 : Route 9 := (fun mask => (mask,id))

def c881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u881 : Upper (D 3) (R 3) [34,5,320,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,5,320,96,129,128] 13 (by decide) (choices 1) [1,8,16] r881 c881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u130
  · exact u131
  · exact u132

def b882 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 324 104 152 33 209 145 401), lower := (rows 35 7 324 104 152 33 64 128 256), losses := [] }

theorem u882 : Upper (D 3) (R 3) [34,5,320,96,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b882
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b883 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 7 324 104 152 48 193 129 385), lower := (rows 35 7 324 104 152 48 64 128 256), losses := [] }

theorem u883 : Upper (D 3) (R 3) [34,5,320,96,136,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b883
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r884 : Route 9 := (fun mask => (mask,id))

def c884 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u884 : Upper (D 3) (R 3) [34,5,320,96,136,128] 13 := by
  apply FastRouting.sound _ _ [34,5,320,96,136,128] 13 (by decide) (choices 1) [1,16] r884 c884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u133
  · exact u134

def b885 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 137 176 33 88 216 344), lower := (rows 35 7 324 137 176 33 64 128 256), losses := [] }

theorem u885 : Upper (D 3) (R 3) [34,5,320,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b885
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b886 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 7 324 137 176 40 81 209 337), lower := (rows 35 7 324 137 176 40 64 128 256), losses := [] }

theorem u886 : Upper (D 3) (R 3) [34,5,320,129,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b886
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b887 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 35 7 324 137 176 48 73 201 329), lower := (rows 35 7 324 137 176 48 64 128 256), losses := [] }

theorem u887 : Upper (D 3) (R 3) [34,5,320,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b887
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b888 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 324 137 176 96 89 153 281), lower := (rows 35 7 324 137 176 96 64 128 256), losses := [] }

theorem u888 : Upper (D 3) (R 3) [34,5,320,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b888
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b889 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 137 208 33 120 184 312), lower := (rows 35 7 324 137 208 33 64 128 256), losses := [] }

theorem u889 : Upper (D 3) (R 3) [34,5,320,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b889
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b890 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 7 324 137 208 40 113 177 305), lower := (rows 35 7 324 137 208 40 64 128 256), losses := [] }

theorem u890 : Upper (D 3) (R 3) [34,5,320,129,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b890
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b891 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 7 324 137 208 48 105 169 297), lower := (rows 35 7 324 137 208 48 64 128 256), losses := [] }

theorem u891 : Upper (D 3) (R 3) [34,5,320,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b891
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b892 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 168 208 33 89 153 281), lower := (rows 35 7 324 168 208 33 64 128 256), losses := [] }

theorem u892 : Upper (D 3) (R 3) [34,5,320,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b892
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b893 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 7 324 168 208 40 81 145 273), lower := (rows 35 7 324 168 208 40 64 128 256), losses := [] }

theorem u893 : Upper (D 3) (R 3) [34,5,320,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b893
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b894 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 7 324 168 208 48 73 137 265), lower := (rows 35 7 324 168 208 48 64 128 256), losses := [] }

theorem u894 : Upper (D 3) (R 3) [34,5,320,160,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b894
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b895 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 73 400 33 224 224 480), lower := (rows 35 14 21 73 400 33 64 128 256), losses := [] }

theorem u895 : Upper (D 3) (R 3) [34,12,17,65,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b895
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b896 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6)], upper := (rows 35 14 21 73 400 96 225 161 417), lower := (rows 35 14 21 73 400 96 64 128 256), losses := [] }

theorem u896 : Upper (D 3) (R 3) [34,12,17,65,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b896
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b897 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 35 14 21 73 400 160 97 225 353), lower := (rows 35 14 21 73 400 160 64 128 256), losses := [] }

theorem u897 : Upper (D 3) (R 3) [34,12,17,65,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b897
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b898 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 21 265 208 33 224 224 480), lower := (rows 35 14 21 265 208 33 64 128 256), losses := [] }

theorem u898 : Upper (D 3) (R 3) [34,12,17,257,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b898
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b899 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 21 265 208 96 225 161 417), lower := (rows 35 14 21 265 208 96 64 128 256), losses := [] }

theorem u899 : Upper (D 3) (R 3) [34,12,17,257,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b899
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u899
end Delivery.IrregularNine14.P03
