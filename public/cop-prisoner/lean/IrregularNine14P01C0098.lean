import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0036

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r5880 : Route 9 := (fun mask => (mask,id))

def c5880 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5880 : Upper (D 1) (R 1) [22,33,320,160] 13 := by
  apply FastRouting.sound _ _ [22,33,320,160] 13 (by decide) (choices 1) [2,8,64,128] r5880 c5880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2160
  · exact u2161
  · exact u2162
  · exact u2163

def r5881 : Route 9 := (fun mask => (mask,id))

def c5881 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5881 : Upper (D 1) (R 1) [22,33,320,192] 13 := by
  apply FastRouting.sound _ _ [22,33,320,192] 13 (by decide) (choices 1) [2,8,32,128] r5881 c5881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2164
  · exact u2165
  · exact u2166
  · exact u2167

def b5882 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 42 69 26 496 480 480 480 480), lower := (rows 23 42 69 26 16 32 64 128 256), losses := [] }

theorem u5882 : Upper (D 1) (R 1) [22,40,65,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5882
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5883 : PairBound 9 := { available := 464, camps := [{ cop := 5, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 69 42 464 496 464 464 464), lower := (rows 23 42 69 42 16 32 64 128 256), losses := [] }

theorem u5883 : Upper (D 1) (R 1) [22,40,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5883
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5884 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 23 42 69 56 466 482 450 450 450), lower := (rows 23 42 69 56 16 32 64 128 256), losses := [] }

theorem u5884 : Upper (D 1) (R 1) [22,40,65,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5884
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5885 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1)], upper := (rows 23 42 69 74 432 432 496 432 432), lower := (rows 23 42 69 74 16 32 64 128 256), losses := [] }

theorem u5885 : Upper (D 1) (R 1) [22,40,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5885
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5886 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 69 88 434 418 482 418 418), lower := (rows 23 42 69 88 16 32 64 128 256), losses := [] }

theorem u5886 : Upper (D 1) (R 1) [22,40,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5886
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5887 : PairBound 9 := { available := 402, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 23 42 69 104 402 434 466 402 402), lower := (rows 23 42 69 104 16 32 64 128 256), losses := [] }

theorem u5887 : Upper (D 1) (R 1) [22,40,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5887
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5888 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1)], upper := (rows 23 42 69 138 496 496 496 496 496), lower := (rows 23 42 69 138 16 32 64 128 256), losses := [] }

theorem u5888 : Upper (D 1) (R 1) [22,40,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5888
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5889 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 69 152 498 482 482 482 482), lower := (rows 23 42 69 152 16 32 64 128 256), losses := [] }

theorem u5889 : Upper (D 1) (R 1) [22,40,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5889
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5890 : PairBound 9 := { available := 466, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 69 168 466 498 466 466 466), lower := (rows 23 42 69 168 16 32 64 128 256), losses := [] }

theorem u5890 : Upper (D 1) (R 1) [22,40,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5890
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5891 : PairBound 9 := { available := 434, camps := [{ cop := 3, region := 306, targets := 64 }], pairs := [(1,6)], upper := (rows 23 42 69 200 434 434 498 434 434), lower := (rows 23 42 69 200 16 32 64 128 256), losses := [] }

theorem u5891 : Upper (D 1) (R 1) [22,40,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5891
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5892 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 23 42 69 266 240 240 240 240 496), lower := (rows 23 42 69 266 16 32 64 128 256), losses := [] }

theorem u5892 : Upper (D 1) (R 1) [22,40,65,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5892
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5893 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 69 280 242 226 226 226 482), lower := (rows 23 42 69 280 16 32 64 128 256), losses := [] }

theorem u5893 : Upper (D 1) (R 1) [22,40,65,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5893
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5894 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 69 296 210 242 210 210 466), lower := (rows 23 42 69 296 16 32 64 128 256), losses := [] }

theorem u5894 : Upper (D 1) (R 1) [22,40,65,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5894
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5895 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 23 42 69 328 178 178 242 178 434), lower := (rows 23 42 69 328 16 32 64 128 256), losses := [] }

theorem u5895 : Upper (D 1) (R 1) [22,40,65,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5895
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5896 : Route 9 := (fun mask => (mask,id))

def c5896 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5896 : Upper (D 1) (R 1) [22,40,65,384] 13 := by
  apply FastRouting.sound _ _ [22,40,65,384] 13 (by decide) (choices 1) [2,32,64,128] r5896 c5896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2168
  · exact u2169
  · exact u2170
  · exact u2171

def b5897 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 42 196 11 496 496 496 496 496), lower := (rows 23 42 196 11 16 32 64 128 256), losses := [] }

theorem u5897 : Upper (D 1) (R 1) [22,40,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5897
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5898 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 23 42 196 25 498 482 482 482 482), lower := (rows 23 42 196 25 16 32 64 128 256), losses := [] }

theorem u5898 : Upper (D 1) (R 1) [22,40,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5898
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5899 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 42 196 26 497 481 481 481 481), lower := (rows 23 42 196 26 16 32 64 128 256), losses := [] }

theorem u5899 : Upper (D 1) (R 1) [22,40,192,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5899
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5900 : PairBound 9 := { available := 466, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 196 41 466 498 466 466 466), lower := (rows 23 42 196 41 16 32 64 128 256), losses := [] }

theorem u5900 : Upper (D 1) (R 1) [22,40,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5900
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5901 : PairBound 9 := { available := 465, camps := [{ cop := 5, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 196 42 465 497 465 465 465), lower := (rows 23 42 196 42 16 32 64 128 256), losses := [] }

theorem u5901 : Upper (D 1) (R 1) [22,40,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5901
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5902 : PairBound 9 := { available := 451, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 196 56 467 483 451 451 451), lower := (rows 23 42 196 56 16 32 64 128 256), losses := [] }

theorem u5902 : Upper (D 1) (R 1) [22,40,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5902
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5903 : PairBound 9 := { available := 434, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 23 42 196 73 434 434 498 434 434), lower := (rows 23 42 196 73 16 32 64 128 256), losses := [] }

theorem u5903 : Upper (D 1) (R 1) [22,40,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5903
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5904 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1)], upper := (rows 23 42 196 74 433 433 497 433 433), lower := (rows 23 42 196 74 16 32 64 128 256), losses := [] }

theorem u5904 : Upper (D 1) (R 1) [22,40,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5904
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5905 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 196 88 435 419 483 419 419), lower := (rows 23 42 196 88 16 32 64 128 256), losses := [] }

theorem u5905 : Upper (D 1) (R 1) [22,40,192,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5905
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5906 : PairBound 9 := { available := 403, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 196 104 403 435 467 403 403), lower := (rows 23 42 196 104 16 32 64 128 256), losses := [] }

theorem u5906 : Upper (D 1) (R 1) [22,40,192,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5906
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5907 : PairBound 9 := { available := 307, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 23 42 196 200 307 307 371 435 307), lower := (rows 23 42 196 200 16 32 64 128 256), losses := [] }

theorem u5907 : Upper (D 1) (R 1) [22,40,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5907
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5908 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5908 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5908 : Upper (D 1) (R 1) [22,40,192,257] 13 := by
  apply FastRouting.sound _ _ [22,40,192,257] 13 (by decide) (choices 1) [2,32,64] r5908 c5908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2172
  · exact u2173
  · exact u2174

def b5909 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 23 42 196 266 241 241 241 241 497), lower := (rows 23 42 196 266 16 32 64 128 256), losses := [] }

theorem u5909 : Upper (D 1) (R 1) [22,40,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5909
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5910 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 196 280 243 227 227 227 483), lower := (rows 23 42 196 280 16 32 64 128 256), losses := [] }

theorem u5910 : Upper (D 1) (R 1) [22,40,192,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5910
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5911 : PairBound 9 := { available := 211, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 196 296 211 243 211 211 467), lower := (rows 23 42 196 296 16 32 64 128 256), losses := [] }

theorem u5911 : Upper (D 1) (R 1) [22,40,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5911
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5912 : Route 9 := (fun mask => (mask,id))

def c5912 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5912 : Upper (D 1) (R 1) [22,40,192,320] 13 := by
  apply FastRouting.sound _ _ [22,40,192,320] 13 (by decide) (choices 1) [1,2,32,128] r5912 c5912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2175
  · exact u2176
  · exact u2177
  · exact u2178

def b5913 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 42 261 26 240 224 224 224 480), lower := (rows 23 42 261 26 16 32 64 128 256), losses := [] }

theorem u5913 : Upper (D 1) (R 1) [22,40,257,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5913
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5914 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 261 42 208 240 208 208 464), lower := (rows 23 42 261 42 16 32 64 128 256), losses := [] }

theorem u5914 : Upper (D 1) (R 1) [22,40,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5914
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5915 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 23 42 261 56 210 226 194 194 450), lower := (rows 23 42 261 56 16 32 64 128 256), losses := [] }

theorem u5915 : Upper (D 1) (R 1) [22,40,257,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5915
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5916 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1)], upper := (rows 23 42 261 74 240 240 240 240 496), lower := (rows 23 42 261 74 16 32 64 128 256), losses := [] }

theorem u5916 : Upper (D 1) (R 1) [22,40,257,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5916
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5917 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 261 88 242 226 226 226 482), lower := (rows 23 42 261 88 16 32 64 128 256), losses := [] }

theorem u5917 : Upper (D 1) (R 1) [22,40,257,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5917
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5918 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 261 104 210 242 210 210 466), lower := (rows 23 42 261 104 16 32 64 128 256), losses := [] }

theorem u5918 : Upper (D 1) (R 1) [22,40,257,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5918
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5919 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5919 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5919 : Upper (D 1) (R 1) [22,40,257,192] 13 := by
  apply FastRouting.sound _ _ [22,40,257,192] 13 (by decide) (choices 1) [2,32,64] r5919 c5919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2179
  · exact u2180
  · exact u2181

def b5920 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 42 324 11 240 240 240 240 496), lower := (rows 23 42 324 11 16 32 64 128 256), losses := [] }

theorem u5920 : Upper (D 1) (R 1) [22,40,320,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5920
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5921 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 23 42 324 25 242 226 226 226 482), lower := (rows 23 42 324 25 16 32 64 128 256), losses := [] }

theorem u5921 : Upper (D 1) (R 1) [22,40,320,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5921
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5922 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 42 324 26 241 225 225 225 481), lower := (rows 23 42 324 26 16 32 64 128 256), losses := [] }

theorem u5922 : Upper (D 1) (R 1) [22,40,320,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5922
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5923 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 324 41 210 242 210 210 466), lower := (rows 23 42 324 41 16 32 64 128 256), losses := [] }

theorem u5923 : Upper (D 1) (R 1) [22,40,320,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5923
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5924 : PairBound 9 := { available := 209, camps := [{ cop := 5, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 324 42 209 241 209 209 465), lower := (rows 23 42 324 42 16 32 64 128 256), losses := [] }

theorem u5924 : Upper (D 1) (R 1) [22,40,320,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5924
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5925 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 324 56 211 227 195 195 451), lower := (rows 23 42 324 56 16 32 64 128 256), losses := [] }

theorem u5925 : Upper (D 1) (R 1) [22,40,320,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5925
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5926 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 23 42 324 73 178 178 242 178 434), lower := (rows 23 42 324 73 16 32 64 128 256), losses := [] }

theorem u5926 : Upper (D 1) (R 1) [22,40,320,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5926
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5927 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1)], upper := (rows 23 42 324 74 177 177 241 177 433), lower := (rows 23 42 324 74 16 32 64 128 256), losses := [] }

theorem u5927 : Upper (D 1) (R 1) [22,40,320,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5927
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5928 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 324 88 179 163 227 163 419), lower := (rows 23 42 324 88 16 32 64 128 256), losses := [] }

theorem u5928 : Upper (D 1) (R 1) [22,40,320,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5928
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5929 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 324 104 147 179 211 147 403), lower := (rows 23 42 324 104 16 32 64 128 256), losses := [] }

theorem u5929 : Upper (D 1) (R 1) [22,40,320,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5929
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5930 : Route 9 := (fun mask => (mask,id))

def c5930 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5930 : Upper (D 1) (R 1) [22,40,320,129] 13 := by
  apply FastRouting.sound _ _ [22,40,320,129] 13 (by decide) (choices 1) [2,32,64,128] r5930 c5930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2182
  · exact u2183
  · exact u2184
  · exact u2185

def b5931 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1)], upper := (rows 23 42 324 138 241 241 241 241 497), lower := (rows 23 42 324 138 16 32 64 128 256), losses := [] }

theorem u5931 : Upper (D 1) (R 1) [22,40,320,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5931
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5932 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 42 324 152 243 227 227 227 483), lower := (rows 23 42 324 152 16 32 64 128 256), losses := [] }

theorem u5932 : Upper (D 1) (R 1) [22,40,320,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5932
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5933 : PairBound 9 := { available := 211, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 23 42 324 168 211 243 211 211 467), lower := (rows 23 42 324 168 16 32 64 128 256), losses := [] }

theorem u5933 : Upper (D 1) (R 1) [22,40,320,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5933
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5934 : Route 9 := (fun mask => (mask,id))

def c5934 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5934 : Upper (D 1) (R 1) [22,40,320,192] 13 := by
  apply FastRouting.sound _ _ [22,40,320,192] 13 (by decide) (choices 1) [1,2,32,128] r5934 c5934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2186
  · exact u2187
  · exact u2188
  · exact u2189

def b5935 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 13 26 496 480 480 480 480), lower := (rows 23 98 13 26 16 32 64 128 256), losses := [] }

theorem u5935 : Upper (D 1) (R 1) [22,96,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5935
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5936 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 98 13 42 464 496 464 464 464), lower := (rows 23 98 13 42 16 32 64 128 256), losses := [] }

theorem u5936 : Upper (D 1) (R 1) [22,96,9,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5936
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5937 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 13 56 466 482 450 450 450), lower := (rows 23 98 13 56 16 32 64 128 256), losses := [] }

theorem u5937 : Upper (D 1) (R 1) [22,96,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5937
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5938 : PairBound 9 := { available := 402, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 98 13 104 402 434 466 402 402), lower := (rows 23 98 13 104 16 32 64 128 256), losses := [] }

theorem u5938 : Upper (D 1) (R 1) [22,96,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5938
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5939 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5939 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u5939 : Upper (D 1) (R 1) [22,96,9,130] 13 := by
  apply FastRouting.sound _ _ [22,96,9,130] 13 (by decide) (choices 1) [32,128,256] r5939 c5939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2190
  · exact u2191
  · exact u2192

#print axioms u5939
end Delivery.IrregularNine14.P01
