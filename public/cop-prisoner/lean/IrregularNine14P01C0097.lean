import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0034
import IrregularNine14P01C0035

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5820 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 15 274 100 168 211 243 211 211 467), lower := (rows 15 274 100 168 16 32 64 128 256), losses := [] }

theorem u5820 : Upper (D 1) (R 1) [14,272,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5820
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5821 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 23 11 100 26 496 480 480 480 480), lower := (rows 23 11 100 26 16 32 64 128 256), losses := [] }

theorem u5821 : Upper (D 1) (R 1) [22,9,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5821
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5822 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 100 42 464 496 464 464 464), lower := (rows 23 11 100 42 16 32 64 128 256), losses := [] }

theorem u5822 : Upper (D 1) (R 1) [22,9,96,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5822
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5823 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 11 100 56 466 482 450 450 450), lower := (rows 23 11 100 56 16 32 64 128 256), losses := [] }

theorem u5823 : Upper (D 1) (R 1) [22,9,96,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5823
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5824 : PairBound 9 := { available := 402, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 23 11 100 104 402 434 466 402 402), lower := (rows 23 11 100 104 16 32 64 128 256), losses := [] }

theorem u5824 : Upper (D 1) (R 1) [22,9,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5824
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5825 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 100 138 496 496 496 496 496), lower := (rows 23 11 100 138 16 32 64 128 256), losses := [] }

theorem u5825 : Upper (D 1) (R 1) [22,9,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5825
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5826 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 11 100 152 498 482 482 482 482), lower := (rows 23 11 100 152 16 32 64 128 256), losses := [] }

theorem u5826 : Upper (D 1) (R 1) [22,9,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5826
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5827 : Route 9 := (fun mask => (mask,id))

def c5827 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u5827 : Upper (D 1) (R 1) [22,9,96,160] 13 := by
  apply FastRouting.sound _ _ [22,9,96,160] 13 (by decide) (choices 1) [2,64,128,256] r5827 c5827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2087
  · exact u2088
  · exact u2089
  · exact u2090

def b5828 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 100 266 240 240 240 240 496), lower := (rows 23 11 100 266 16 32 64 128 256), losses := [] }

theorem u5828 : Upper (D 1) (R 1) [22,9,96,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5828
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5829 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 23 11 100 280 242 226 226 226 482), lower := (rows 23 11 100 280 16 32 64 128 256), losses := [] }

theorem u5829 : Upper (D 1) (R 1) [22,9,96,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5829
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5830 : Route 9 := (fun mask => (mask,id))

def c5830 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5830 : Upper (D 1) (R 1) [22,9,96,288] 13 := by
  apply FastRouting.sound _ _ [22,9,96,288] 13 (by decide) (choices 1) [2,64,128] r5830 c5830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2091
  · exact u2092
  · exact u2093

def r5831 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c5831 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5831 : Upper (D 1) (R 1) [22,9,96,384] 13 := by
  apply FastRouting.sound _ _ [22,9,96,384] 13 (by decide) (choices 1) [2,32,128] r5831 c5831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2094
  · exact u2095
  · exact u2096

def b5832 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 23 11 292 26 240 224 224 224 480), lower := (rows 23 11 292 26 16 32 64 128 256), losses := [] }

theorem u5832 : Upper (D 1) (R 1) [22,9,288,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5832
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5833 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 292 42 208 240 208 208 464), lower := (rows 23 11 292 42 16 32 64 128 256), losses := [] }

theorem u5833 : Upper (D 1) (R 1) [22,9,288,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5833
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5834 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 11 292 56 210 226 194 194 450), lower := (rows 23 11 292 56 16 32 64 128 256), losses := [] }

theorem u5834 : Upper (D 1) (R 1) [22,9,288,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5834
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5835 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 292 74 240 240 240 240 496), lower := (rows 23 11 292 74 16 32 64 128 256), losses := [] }

theorem u5835 : Upper (D 1) (R 1) [22,9,288,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5835
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5836 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 11 292 88 242 226 226 226 482), lower := (rows 23 11 292 88 16 32 64 128 256), losses := [] }

theorem u5836 : Upper (D 1) (R 1) [22,9,288,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5836
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5837 : Route 9 := (fun mask => (mask,id))

def c5837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5837 : Upper (D 1) (R 1) [22,9,288,96] 13 := by
  apply FastRouting.sound _ _ [22,9,288,96] 13 (by decide) (choices 1) [2,64,128] r5837 c5837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2097
  · exact u2098
  · exact u2099

def r5838 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5838 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5838 : Upper (D 1) (R 1) [22,9,288,192] 13 := by
  apply FastRouting.sound _ _ [22,9,288,192] 13 (by decide) (choices 1) [2,32,64] r5838 c5838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2100
  · exact u2101
  · exact u2102

def b5839 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 76 26 496 480 480 480 480), lower := (rows 23 35 76 26 16 32 64 128 256), losses := [] }

theorem u5839 : Upper (D 1) (R 1) [22,33,72,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5839
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5840 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 35 76 42 464 496 464 464 464), lower := (rows 23 35 76 42 16 32 64 128 256), losses := [] }

theorem u5840 : Upper (D 1) (R 1) [22,33,72,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5840
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5841 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 76 56 466 482 450 450 450), lower := (rows 23 35 76 56 16 32 64 128 256), losses := [] }

theorem u5841 : Upper (D 1) (R 1) [22,33,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5841
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5842 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 23 35 76 74 432 432 496 432 432), lower := (rows 23 35 76 74 16 32 64 128 256), losses := [] }

theorem u5842 : Upper (D 1) (R 1) [22,33,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5842
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5843 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 76 88 434 418 482 418 418), lower := (rows 23 35 76 88 16 32 64 128 256), losses := [] }

theorem u5843 : Upper (D 1) (R 1) [22,33,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5843
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5844 : PairBound 9 := { available := 402, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 76 104 402 434 466 402 402), lower := (rows 23 35 76 104 16 32 64 128 256), losses := [] }

theorem u5844 : Upper (D 1) (R 1) [22,33,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5844
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5845 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 372, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 76 138 496 496 496 496 496), lower := (rows 23 35 76 138 16 32 64 128 256), losses := [] }

theorem u5845 : Upper (D 1) (R 1) [22,33,72,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5845
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5846 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 76 152 498 482 482 482 482), lower := (rows 23 35 76 152 16 32 64 128 256), losses := [] }

theorem u5846 : Upper (D 1) (R 1) [22,33,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5846
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5847 : Route 9 := (fun mask => (mask,id))

def c5847 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u5847 : Upper (D 1) (R 1) [22,33,72,160] 13 := by
  apply FastRouting.sound _ _ [22,33,72,160] 13 (by decide) (choices 1) [2,64,128,256] r5847 c5847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2103
  · exact u2104
  · exact u2105
  · exact u2106

def b5848 : PairBound 9 := { available := 434, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 76 200 434 434 498 434 434), lower := (rows 23 35 76 200 16 32 64 128 256), losses := [] }

theorem u5848 : Upper (D 1) (R 1) [22,33,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5848
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5849 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 76 266 240 240 240 240 496), lower := (rows 23 35 76 266 16 32 64 128 256), losses := [] }

theorem u5849 : Upper (D 1) (R 1) [22,33,72,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5849
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5850 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 76 280 242 226 226 226 482), lower := (rows 23 35 76 280 16 32 64 128 256), losses := [] }

theorem u5850 : Upper (D 1) (R 1) [22,33,72,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5850
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5851 : Route 9 := (fun mask => (mask,id))

def c5851 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5851 : Upper (D 1) (R 1) [22,33,72,288] 13 := by
  apply FastRouting.sound _ _ [22,33,72,288] 13 (by decide) (choices 1) [2,64,128] r5851 c5851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2107
  · exact u2108
  · exact u2109

def b5852 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 76 328 178 178 242 178 434), lower := (rows 23 35 76 328 16 32 64 128 256), losses := [] }

theorem u5852 : Upper (D 1) (R 1) [22,33,72,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5852
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5853 : Route 9 := (fun mask => (mask,id))

def c5853 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5853 : Upper (D 1) (R 1) [22,33,72,384] 13 := by
  apply FastRouting.sound _ _ [22,33,72,384] 13 (by decide) (choices 1) [2,32,64,128] r5853 c5853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2110
  · exact u2111
  · exact u2112
  · exact u2113

def b5854 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 196 26 504 488 488 488 488), lower := (rows 23 35 196 26 16 32 64 128 256), losses := [] }

theorem u5854 : Upper (D 1) (R 1) [22,33,192,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5854
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5855 : PairBound 9 := { available := 472, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 35 196 42 472 504 472 472 472), lower := (rows 23 35 196 42 16 32 64 128 256), losses := [] }

theorem u5855 : Upper (D 1) (R 1) [22,33,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5855
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5856 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5856 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | _ => 0)

theorem u5856 : Upper (D 1) (R 1) [22,33,192,48] 13 := by
  apply FastRouting.sound _ _ [22,33,192,48] 13 (by decide) (choices 1) [2,8,64,256] r5856 c5856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2114
  · exact u2115
  · exact u2116
  · exact u2117

def b5857 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 436, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 196 74 440 440 504 440 440), lower := (rows 23 35 196 74 16 32 64 128 256), losses := [] }

theorem u5857 : Upper (D 1) (R 1) [22,33,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5857
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5858 : Route 9 := (fun mask => (mask,id))

def c5858 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | _ => 0)

theorem u5858 : Upper (D 1) (R 1) [22,33,192,80] 13 := by
  apply FastRouting.sound _ _ [22,33,192,80] 13 (by decide) (choices 1) [2,8,32,128,256] r5858 c5858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2118
  · exact u2119
  · exact u2120
  · exact u2121
  · exact u2122

def r5859 : Route 9 := (fun mask => (mask,id))

def c5859 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0)

theorem u5859 : Upper (D 1) (R 1) [22,33,192,96] 13 := by
  apply FastRouting.sound _ _ [22,33,192,96] 13 (by decide) (choices 1) [2,8,128,256] r5859 c5859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2123
  · exact u2124
  · exact u2125
  · exact u2126

def b5860 : PairBound 9 := { available := 314, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 23 35 196 200 314 314 378 442 314), lower := (rows 23 35 196 200 16 32 64 128 256), losses := [] }

theorem u5860 : Upper (D 1) (R 1) [22,33,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5860
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5861 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 196 266 248 248 248 248 504), lower := (rows 23 35 196 266 16 32 64 128 256), losses := [] }

theorem u5861 : Upper (D 1) (R 1) [22,33,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5861
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5862 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5862 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u5862 : Upper (D 1) (R 1) [22,33,192,272] 13 := by
  apply FastRouting.sound _ _ [22,33,192,272] 13 (by decide) (choices 1) [2,8,32,64] r5862 c5862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2127
  · exact u2128
  · exact u2129
  · exact u2130

def r5863 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5863 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5863 : Upper (D 1) (R 1) [22,33,192,288] 13 := by
  apply FastRouting.sound _ _ [22,33,192,288] 13 (by decide) (choices 1) [2,8,64] r5863 c5863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2131
  · exact u2132
  · exact u2133

def r5864 : Route 9 := (fun mask => (mask,id))

def c5864 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5864 : Upper (D 1) (R 1) [22,33,192,320] 13 := by
  apply FastRouting.sound _ _ [22,33,192,320] 13 (by decide) (choices 1) [2,8,32,128] r5864 c5864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2134
  · exact u2135
  · exact u2136
  · exact u2137

def b5865 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 268 26 240 224 224 224 480), lower := (rows 23 35 268 26 16 32 64 128 256), losses := [] }

theorem u5865 : Upper (D 1) (R 1) [22,33,264,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5865
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5866 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 35 268 42 208 240 208 208 464), lower := (rows 23 35 268 42 16 32 64 128 256), losses := [] }

theorem u5866 : Upper (D 1) (R 1) [22,33,264,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5866
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5867 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 268 56 210 226 194 194 450), lower := (rows 23 35 268 56 16 32 64 128 256), losses := [] }

theorem u5867 : Upper (D 1) (R 1) [22,33,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5867
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5868 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 436, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 268 74 240 240 240 240 496), lower := (rows 23 35 268 74 16 32 64 128 256), losses := [] }

theorem u5868 : Upper (D 1) (R 1) [22,33,264,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5868
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5869 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 268 88 242 226 226 226 482), lower := (rows 23 35 268 88 16 32 64 128 256), losses := [] }

theorem u5869 : Upper (D 1) (R 1) [22,33,264,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5869
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5870 : Route 9 := (fun mask => (mask,id))

def c5870 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5870 : Upper (D 1) (R 1) [22,33,264,96] 13 := by
  apply FastRouting.sound _ _ [22,33,264,96] 13 (by decide) (choices 1) [2,64,128] r5870 c5870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2138
  · exact u2139
  · exact u2140

def r5871 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c5871 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5871 : Upper (D 1) (R 1) [22,33,264,192] 13 := by
  apply FastRouting.sound _ _ [22,33,264,192] 13 (by decide) (choices 1) [2,32,64] r5871 c5871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2141
  · exact u2142
  · exact u2143

def b5872 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 324 26 248 232 232 232 488), lower := (rows 23 35 324 26 16 32 64 128 256), losses := [] }

theorem u5872 : Upper (D 1) (R 1) [22,33,320,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5872
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5873 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 23 35 324 42 216 248 216 216 472), lower := (rows 23 35 324 42 16 32 64 128 256), losses := [] }

theorem u5873 : Upper (D 1) (R 1) [22,33,320,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5873
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5874 : Route 9 := (fun mask => (mask,id))

def c5874 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5874 : Upper (D 1) (R 1) [22,33,320,48] 13 := by
  apply FastRouting.sound _ _ [22,33,320,48] 13 (by decide) (choices 1) [2,8,64,128] r5874 c5874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2144
  · exact u2145
  · exact u2146
  · exact u2147

def b5875 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 324 74 184 184 248 184 440), lower := (rows 23 35 324 74 16 32 64 128 256), losses := [] }

theorem u5875 : Upper (D 1) (R 1) [22,33,320,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5875
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5876 : Route 9 := (fun mask => (mask,id))

def c5876 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5876 : Upper (D 1) (R 1) [22,33,320,80] 13 := by
  apply FastRouting.sound _ _ [22,33,320,80] 13 (by decide) (choices 1) [2,8,32,128] r5876 c5876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2148
  · exact u2149
  · exact u2150
  · exact u2151

def r5877 : Route 9 := (fun mask => (mask,id))

def c5877 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5877 : Upper (D 1) (R 1) [22,33,320,96] 13 := by
  apply FastRouting.sound _ _ [22,33,320,96] 13 (by decide) (choices 1) [2,8,128] r5877 c5877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2152
  · exact u2153
  · exact u2154

def b5878 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 372, targets := 2 }], pairs := [(2,1)], upper := (rows 23 35 324 138 248 248 248 248 504), lower := (rows 23 35 324 138 16 32 64 128 256), losses := [] }

theorem u5878 : Upper (D 1) (R 1) [22,33,320,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5878
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5879 : Route 9 := (fun mask => (mask,id))

def c5879 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u5879 : Upper (D 1) (R 1) [22,33,320,144] 13 := by
  apply FastRouting.sound _ _ [22,33,320,144] 13 (by decide) (choices 1) [2,8,32,64,128] r5879 c5879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2155
  · exact u2156
  · exact u2157
  · exact u2158
  · exact u2159

#print axioms u5879
end Delivery.IrregularNine14.P01
