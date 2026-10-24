import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0165
import IrregularNine14P06C0166
import IrregularNine14P06C0167

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28680 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 196 42 81 316 348 412 284), lower := (rows 7 35 196 42 81 32 64 128 256), losses := [] }

theorem u28680 : Upper (D 6) (R 6) [6,33,192,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28680
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28681 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 196 42 88 309 341 405 277), lower := (rows 7 35 196 42 88 32 64 128 256), losses := [] }

theorem u28681 : Upper (D 6) (R 6) [6,33,192,34,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28681
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28682 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 196 42 273 124 92 220 348), lower := (rows 7 35 196 42 273 32 64 128 256), losses := [] }

theorem u28682 : Upper (D 6) (R 6) [6,33,192,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28682
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28683 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 196 42 276 121 89 217 345), lower := (rows 7 35 196 42 276 32 64 128 256), losses := [] }

theorem u28683 : Upper (D 6) (R 6) [6,33,192,34,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28683
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28684 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 196 42 280 117 85 213 341), lower := (rows 7 35 196 42 280 32 64 128 256), losses := [] }

theorem u28684 : Upper (D 6) (R 6) [6,33,192,34,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28684
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28685 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 196 42 336 61 93 157 285), lower := (rows 7 35 196 42 336 32 64 128 256), losses := [] }

theorem u28685 : Upper (D 6) (R 6) [6,33,192,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28685
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28686 : Route 9 := (fun mask => (mask,id))

def c28686 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28686 : Upper (D 6) (R 6) [6,33,192,36,65] 13 := by
  apply FastRouting.sound _ _ [6,33,192,36,65] 13 (by decide) (choices 1) [2,8,16,256] r28686 c28686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9936
  · exact u9937
  · exact u9938
  · exact u9939

def r28687 : Route 9 := (fun mask => (mask,id))

def c28687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28687 : Upper (D 6) (R 6) [6,33,192,36,66] 13 := by
  apply FastRouting.sound _ _ [6,33,192,36,66] 13 (by decide) (choices 1) [1,8,16,256] r28687 c28687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9940
  · exact u9941
  · exact u9942
  · exact u9943

def r28688 : Route 9 := (fun mask => (mask,id))

def c28688 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28688 : Upper (D 6) (R 6) [6,33,192,36,72] 13 := by
  apply FastRouting.sound _ _ [6,33,192,36,72] 13 (by decide) (choices 1) [1,2,16,256] r28688 c28688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9944
  · exact u9945
  · exact u9946
  · exact u9947

def r28689 : Route 9 := (fun mask => (mask,id))

def c28689 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28689 : Upper (D 6) (R 6) [6,33,192,36,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,36,257] 13 (by decide) (choices 1) [2,8,16,64] r28689 c28689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9948
  · exact u9949
  · exact u9950
  · exact u9951

def r28690 : Route 9 := (fun mask => (mask,id))

def c28690 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28690 : Upper (D 6) (R 6) [6,33,192,36,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,36,258] 13 (by decide) (choices 1) [1,8,16,64] r28690 c28690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9952
  · exact u9953
  · exact u9954
  · exact u9955

def r28691 : Route 9 := (fun mask => (mask,id))

def c28691 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28691 : Upper (D 6) (R 6) [6,33,192,36,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,36,264] 13 (by decide) (choices 1) [1,2,16,64] r28691 c28691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9956
  · exact u9957
  · exact u9958
  · exact u9959

def r28692 : Route 9 := (fun mask => (mask,id))

def c28692 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28692 : Upper (D 6) (R 6) [6,33,192,36,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,36,320] 13 (by decide) (choices 1) [1,2,8,16] r28692 c28692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9960
  · exact u9961
  · exact u9962
  · exact u9963

def r28693 : Route 9 := (fun mask => (mask,id))

def c28693 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28693 : Upper (D 6) (R 6) [6,33,192,48,65] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,65] 13 (by decide) (choices 1) [2,4,8,256] r28693 c28693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9964
  · exact u9965
  · exact u9966
  · exact u9967

def r28694 : Route 9 := (fun mask => (mask,id))

def c28694 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28694 : Upper (D 6) (R 6) [6,33,192,48,66] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,66] 13 (by decide) (choices 1) [1,4,8,256] r28694 c28694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9968
  · exact u9969
  · exact u9970
  · exact u9971

def b28695 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 35 196 56 84 299 331 395 267), lower := (rows 7 35 196 56 84 32 64 128 256), losses := [] }

theorem u28695 : Upper (D 6) (R 6) [6,33,192,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28695
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28696 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 35 196 56 88 295 327 391 263), lower := (rows 7 35 196 56 88 32 64 128 256), losses := [] }

theorem u28696 : Upper (D 6) (R 6) [6,33,192,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28696
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28697 : Route 9 := (fun mask => (mask,id))

def c28697 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28697 : Upper (D 6) (R 6) [6,33,192,48,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,257] 13 (by decide) (choices 1) [2,4,8,64] r28697 c28697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9972
  · exact u9973
  · exact u9974
  · exact u9975

def r28698 : Route 9 := (fun mask => (mask,id))

def c28698 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28698 : Upper (D 6) (R 6) [6,33,192,48,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,258] 13 (by decide) (choices 1) [1,4,8,64] r28698 c28698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9976
  · exact u9977
  · exact u9978
  · exact u9979

def r28699 : Route 9 := (fun mask => (mask,id))

def c28699 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28699 : Upper (D 6) (R 6) [6,33,192,48,260] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,260] 13 (by decide) (choices 1) [1,2,8,64] r28699 c28699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9980
  · exact u9981
  · exact u9982
  · exact u9983

def r28700 : Route 9 := (fun mask => (mask,id))

def c28700 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28700 : Upper (D 6) (R 6) [6,33,192,48,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,264] 13 (by decide) (choices 1) [1,2,4,64] r28700 c28700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9984
  · exact u9985
  · exact u9986
  · exact u9987

def r28701 : Route 9 := (fun mask => (mask,id))

def c28701 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28701 : Upper (D 6) (R 6) [6,33,192,48,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,320] 13 (by decide) (choices 1) [1,2,4,8] r28701 c28701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9988
  · exact u9989
  · exact u9990
  · exact u9991

def r28702 : Route 9 := (fun mask => (mask,id))

def c28702 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28702 : Upper (D 6) (R 6) [6,33,192,65,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,258] 13 (by decide) (choices 1) [4,8,16] r28702 c28702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9992
  · exact u9993
  · exact u9994

def r28703 : Route 9 := (fun mask => (mask,id))

def c28703 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28703 : Upper (D 6) (R 6) [6,33,192,65,260] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,260] 13 (by decide) (choices 1) [2,8,16] r28703 c28703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9995
  · exact u9996
  · exact u9997

def r28704 : Route 9 := (fun mask => (mask,id))

def c28704 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28704 : Upper (D 6) (R 6) [6,33,192,65,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,264] 13 (by decide) (choices 1) [2,4,16] r28704 c28704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9998
  · exact u9999
  · exact u10000

def r28705 : Route 9 := (fun mask => (mask,id))

def c28705 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28705 : Upper (D 6) (R 6) [6,33,192,65,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,288] 13 (by decide) (choices 1) [2,4,8,16] r28705 c28705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10001
  · exact u10002
  · exact u10003
  · exact u10004

def r28706 : Route 9 := (fun mask => (mask,id))

def c28706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28706 : Upper (D 6) (R 6) [6,33,192,66,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,66,257] 13 (by decide) (choices 1) [4,8,16] r28706 c28706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10005
  · exact u10006
  · exact u10007

def r28707 : Route 9 := (fun mask => (mask,id))

def c28707 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28707 : Upper (D 6) (R 6) [6,33,192,66,260] 13 := by
  apply FastRouting.sound _ _ [6,33,192,66,260] 13 (by decide) (choices 1) [1,8,16] r28707 c28707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10008
  · exact u10009
  · exact u10010

def r28708 : Route 9 := (fun mask => (mask,id))

def c28708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28708 : Upper (D 6) (R 6) [6,33,192,66,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,66,264] 13 (by decide) (choices 1) [1,4,16] r28708 c28708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10011
  · exact u10012
  · exact u10013

def r28709 : Route 9 := (fun mask => (mask,id))

def c28709 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28709 : Upper (D 6) (R 6) [6,33,192,66,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,66,288] 13 (by decide) (choices 1) [1,4,8,16] r28709 c28709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10014
  · exact u10015
  · exact u10016
  · exact u10017

def b28710 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 35 196 76 273 58 122 186 314), lower := (rows 7 35 196 76 273 32 64 128 256), losses := [] }

theorem u28710 : Upper (D 6) (R 6) [6,33,192,68,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28710
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28711 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 35 196 76 274 57 121 185 313), lower := (rows 7 35 196 76 274 32 64 128 256), losses := [] }

theorem u28711 : Upper (D 6) (R 6) [6,33,192,68,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28711
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28712 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 35 196 76 280 51 115 179 307), lower := (rows 7 35 196 76 280 32 64 128 256), losses := [] }

theorem u28712 : Upper (D 6) (R 6) [6,33,192,68,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28712
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28713 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 35 196 76 304 59 91 155 283), lower := (rows 7 35 196 76 304 32 64 128 256), losses := [] }

theorem u28713 : Upper (D 6) (R 6) [6,33,192,68,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28713
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28714 : Route 9 := (fun mask => (mask,id))

def c28714 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28714 : Upper (D 6) (R 6) [6,33,192,80,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,257] 13 (by decide) (choices 1) [2,4,8] r28714 c28714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10018
  · exact u10019
  · exact u10020

def r28715 : Route 9 := (fun mask => (mask,id))

def c28715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28715 : Upper (D 6) (R 6) [6,33,192,80,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,258] 13 (by decide) (choices 1) [1,4,8] r28715 c28715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10021
  · exact u10022
  · exact u10023

def r28716 : Route 9 := (fun mask => (mask,id))

def c28716 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28716 : Upper (D 6) (R 6) [6,33,192,80,260] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,260] 13 (by decide) (choices 1) [1,2,8] r28716 c28716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10024
  · exact u10025
  · exact u10026

def r28717 : Route 9 := (fun mask => (mask,id))

def c28717 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28717 : Upper (D 6) (R 6) [6,33,192,80,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,264] 13 (by decide) (choices 1) [1,2,4] r28717 c28717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10027
  · exact u10028
  · exact u10029

def r28718 : Route 9 := (fun mask => (mask,id))

def c28718 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28718 : Upper (D 6) (R 6) [6,33,192,80,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,288] 13 (by decide) (choices 1) [1,2,4,8] r28718 c28718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10030
  · exact u10031
  · exact u10032
  · exact u10033

def r28719 : Route 9 := (fun mask => (mask,id))

def c28719 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28719 : Upper (D 6) (R 6) [6,33,192,96,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,257] 13 (by decide) (choices 1) [2,4,8,16] r28719 c28719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10034
  · exact u10035
  · exact u10036
  · exact u10037

def r28720 : Route 9 := (fun mask => (mask,id))

def c28720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28720 : Upper (D 6) (R 6) [6,33,192,96,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,258] 13 (by decide) (choices 1) [1,4,8,16] r28720 c28720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10038
  · exact u10039
  · exact u10040
  · exact u10041

def r28721 : Route 9 := (fun mask => (mask,id))

def c28721 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28721 : Upper (D 6) (R 6) [6,33,192,96,260] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,260] 13 (by decide) (choices 1) [1,2,8,16] r28721 c28721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10042
  · exact u10043
  · exact u10044
  · exact u10045

def r28722 : Route 9 := (fun mask => (mask,id))

def c28722 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28722 : Upper (D 6) (R 6) [6,33,192,96,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,264] 13 (by decide) (choices 1) [1,2,4,16] r28722 c28722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10046
  · exact u10047
  · exact u10048
  · exact u10049

def b28723 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 388 11 28 112 112 240 368), lower := (rows 7 35 388 11 28 32 64 128 256), losses := [] }

theorem u28723 : Upper (D 6) (R 6) [6,33,384,3,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28723
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28724 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 388 11 52 120 88 216 344), lower := (rows 7 35 388 11 52 32 64 128 256), losses := [] }

theorem u28724 : Upper (D 6) (R 6) [6,33,384,3,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28724
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28725 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 35 388 11 56 116 84 212 340), lower := (rows 7 35 388 11 56 32 64 128 256), losses := [] }

theorem u28725 : Upper (D 6) (R 6) [6,33,384,3,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28725
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28726 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 388 11 84 120 120 248 376), lower := (rows 7 35 388 11 84 32 64 128 256), losses := [] }

theorem u28726 : Upper (D 6) (R 6) [6,33,384,3,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28726
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28727 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 388 11 88 116 116 244 372), lower := (rows 7 35 388 11 88 32 64 128 256), losses := [] }

theorem u28727 : Upper (D 6) (R 6) [6,33,384,3,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28727
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28728 : PairBound 9 := { available := 92, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 388 11 112 124 92 220 348), lower := (rows 7 35 388 11 112 32 64 128 256), losses := [] }

theorem u28728 : Upper (D 6) (R 6) [6,33,384,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28728
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28729 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 388 13 26 112 112 240 368), lower := (rows 7 35 388 13 26 32 64 128 256), losses := [] }

theorem u28729 : Upper (D 6) (R 6) [6,33,384,5,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28729
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28730 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 388 13 56 114 82 210 338), lower := (rows 7 35 388 13 56 32 64 128 256), losses := [] }

theorem u28730 : Upper (D 6) (R 6) [6,33,384,5,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28730
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28731 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 388 13 82 120 120 248 376), lower := (rows 7 35 388 13 82 32 64 128 256), losses := [] }

theorem u28731 : Upper (D 6) (R 6) [6,33,384,5,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28731
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28732 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 388 13 88 114 114 242 370), lower := (rows 7 35 388 13 88 32 64 128 256), losses := [] }

theorem u28732 : Upper (D 6) (R 6) [6,33,384,5,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28732
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28733 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 388 13 112 122 90 218 346), lower := (rows 7 35 388 13 112 32 64 128 256), losses := [] }

theorem u28733 : Upper (D 6) (R 6) [6,33,384,5,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28733
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28734 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 388 14 25 112 112 240 368), lower := (rows 7 35 388 14 25 32 64 128 256), losses := [] }

theorem u28734 : Upper (D 6) (R 6) [6,33,384,6,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28734
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28735 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 35 388 14 56 113 81 209 337), lower := (rows 7 35 388 14 56 32 64 128 256), losses := [] }

theorem u28735 : Upper (D 6) (R 6) [6,33,384,6,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28735
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28736 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 35 388 14 81 120 120 248 376), lower := (rows 7 35 388 14 81 32 64 128 256), losses := [] }

theorem u28736 : Upper (D 6) (R 6) [6,33,384,6,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28736
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28737 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 35 388 14 88 113 113 241 369), lower := (rows 7 35 388 14 88 32 64 128 256), losses := [] }

theorem u28737 : Upper (D 6) (R 6) [6,33,384,6,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28737
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28738 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 96 },{ cop := 3, region := 1, targets := 32 }], pairs := [(0,5),(3,5),(3,6)], upper := (rows 7 35 388 14 112 121 89 217 345), lower := (rows 7 35 388 14 112 32 64 128 256), losses := [] }

theorem u28738 : Upper (D 6) (R 6) [6,33,384,6,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28738
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28739 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 35 388 25 26 100 100 228 356), lower := (rows 7 35 388 25 26 32 64 128 256), losses := [] }

theorem u28739 : Upper (D 6) (R 6) [6,33,384,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28739
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u28739
end Delivery.IrregularNine14.P06
