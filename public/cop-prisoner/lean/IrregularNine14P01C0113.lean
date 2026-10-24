import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0051
import IrregularNine14P01C0052

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6780 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 26 70 73 434 418 482 418 418), lower := (rows 53 26 70 73 16 32 64 128 256), losses := [] }

theorem u6780 : Upper (D 1) (R 1) [52,24,66,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6780
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6781 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 26 70 74 433 417 481 417 417), lower := (rows 53 26 70 74 16 32 64 128 256), losses := [] }

theorem u6781 : Upper (D 1) (R 1) [52,24,66,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6781
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6782 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 53 26 70 104 403 419 451 387 387), lower := (rows 53 26 70 104 16 32 64 128 256), losses := [] }

theorem u6782 : Upper (D 1) (R 1) [52,24,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6782
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6783 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 26 70 137 498 482 482 482 482), lower := (rows 53 26 70 137 16 32 64 128 256), losses := [] }

theorem u6783 : Upper (D 1) (R 1) [52,24,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6783
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6784 : PairBound 9 := { available := 481, camps := [{ cop := 2, region := 433, targets := 2 }], pairs := [(0,1)], upper := (rows 53 26 70 138 497 481 481 481 481), lower := (rows 53 26 70 138 16 32 64 128 256), losses := [] }

theorem u6784 : Upper (D 1) (R 1) [52,24,66,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6784
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6785 : Route 9 := (fun mask => (mask,id))

def c6785 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u6785 : Upper (D 1) (R 1) [52,24,66,160] 13 := by
  apply FastRouting.sound _ _ [52,24,66,160] 13 (by decide) (choices 1) [1,2,64,128,256] r6785 c6785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3078
  · exact u3079
  · exact u3080
  · exact u3081
  · exact u3082

def b6786 : PairBound 9 := { available := 419, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 53 26 70 200 435 419 483 419 419), lower := (rows 53 26 70 200 16 32 64 128 256), losses := [] }

theorem u6786 : Upper (D 1) (R 1) [52,24,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6786
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6787 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 53 26 70 265 242 226 226 226 482), lower := (rows 53 26 70 265 16 32 64 128 256), losses := [] }

theorem u6787 : Upper (D 1) (R 1) [52,24,66,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6787
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6788 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1)], upper := (rows 53 26 70 266 241 225 225 225 481), lower := (rows 53 26 70 266 16 32 64 128 256), losses := [] }

theorem u6788 : Upper (D 1) (R 1) [52,24,66,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6788
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6789 : Route 9 := (fun mask => (mask,id))

def c6789 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6789 : Upper (D 1) (R 1) [52,24,66,288] 13 := by
  apply FastRouting.sound _ _ [52,24,66,288] 13 (by decide) (choices 1) [1,2,64,128] r6789 c6789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3083
  · exact u3084
  · exact u3085
  · exact u3086

def b6790 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 53 26 70 328 179 163 227 163 419), lower := (rows 53 26 70 328 16 32 64 128 256), losses := [] }

theorem u6790 : Upper (D 1) (R 1) [52,24,66,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6790
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6791 : Route 9 := (fun mask => (mask,id))

def c6791 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6791 : Upper (D 1) (R 1) [52,24,66,384] 13 := by
  apply FastRouting.sound _ _ [52,24,66,384] 13 (by decide) (choices 1) [1,2,32,64,128] r6791 c6791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3087
  · exact u3088
  · exact u3089
  · exact u3090
  · exact u3091

def b6792 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 196 11 498 482 482 482 482), lower := (rows 53 26 196 11 16 32 64 128 256), losses := [] }

theorem u6792 : Upper (D 1) (R 1) [52,24,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6792
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6793 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 53 26 196 41 466 482 450 450 450), lower := (rows 53 26 196 41 16 32 64 128 256), losses := [] }

theorem u6793 : Upper (D 1) (R 1) [52,24,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6793
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6794 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 53 26 196 42 467 483 451 451 451), lower := (rows 53 26 196 42 16 32 64 128 256), losses := [] }

theorem u6794 : Upper (D 1) (R 1) [52,24,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6794
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6795 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 26 196 73 434 418 482 418 418), lower := (rows 53 26 196 73 16 32 64 128 256), losses := [] }

theorem u6795 : Upper (D 1) (R 1) [52,24,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6795
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6796 : Route 9 := (fun mask => (mask,id))

def c6796 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6796 : Upper (D 1) (R 1) [52,24,192,66] 13 := by
  apply FastRouting.sound _ _ [52,24,192,66] 13 (by decide) (choices 1) [1,2,32,128,256] r6796 c6796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3092
  · exact u3093
  · exact u3094
  · exact u3095
  · exact u3096

def r6797 : Route 9 := (fun mask => (mask,id))

def c6797 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | _ => 0)

theorem u6797 : Upper (D 1) (R 1) [52,24,192,96] 13 := by
  apply FastRouting.sound _ _ [52,24,192,96] 13 (by decide) (choices 1) [1,2,128,256] r6797 c6797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3097
  · exact u3098
  · exact u3099
  · exact u3100

def b6798 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 26 196 200 307 291 355 419 291), lower := (rows 53 26 196 200 16 32 64 128 256), losses := [] }

theorem u6798 : Upper (D 1) (R 1) [52,24,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6798
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6799 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 53 26 196 265 242 226 226 226 482), lower := (rows 53 26 196 265 16 32 64 128 256), losses := [] }

theorem u6799 : Upper (D 1) (R 1) [52,24,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6799
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6800 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6800 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6800 : Upper (D 1) (R 1) [52,24,192,258] 13 := by
  apply FastRouting.sound _ _ [52,24,192,258] 13 (by decide) (choices 1) [1,2,32,64] r6800 c6800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3101
  · exact u3102
  · exact u3103
  · exact u3104

def r6801 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6801 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6801 : Upper (D 1) (R 1) [52,24,192,288] 13 := by
  apply FastRouting.sound _ _ [52,24,192,288] 13 (by decide) (choices 1) [1,2,64] r6801 c6801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3105
  · exact u3106
  · exact u3107

def r6802 : Route 9 := (fun mask => (mask,id))

def c6802 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6802 : Upper (D 1) (R 1) [52,24,192,320] 13 := by
  apply FastRouting.sound _ _ [52,24,192,320] 13 (by decide) (choices 1) [1,2,32,128] r6802 c6802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3108
  · exact u3109
  · exact u3110
  · exact u3111

def b6803 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 262 11 240 224 224 224 480), lower := (rows 53 26 262 11 16 32 64 128 256), losses := [] }

theorem u6803 : Upper (D 1) (R 1) [52,24,258,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6803
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6804 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 53 26 262 41 210 226 194 194 450), lower := (rows 53 26 262 41 16 32 64 128 256), losses := [] }

theorem u6804 : Upper (D 1) (R 1) [52,24,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6804
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6805 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 53 26 262 42 209 225 193 193 449), lower := (rows 53 26 262 42 16 32 64 128 256), losses := [] }

theorem u6805 : Upper (D 1) (R 1) [52,24,258,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6805
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6806 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 26 262 73 242 226 226 226 482), lower := (rows 53 26 262 73 16 32 64 128 256), losses := [] }

theorem u6806 : Upper (D 1) (R 1) [52,24,258,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6806
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6807 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 53 26 262 74 241 225 225 225 481), lower := (rows 53 26 262 74 16 32 64 128 256), losses := [] }

theorem u6807 : Upper (D 1) (R 1) [52,24,258,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6807
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6808 : Route 9 := (fun mask => (mask,id))

def c6808 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6808 : Upper (D 1) (R 1) [52,24,258,96] 13 := by
  apply FastRouting.sound _ _ [52,24,258,96] 13 (by decide) (choices 1) [1,2,64,128] r6808 c6808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3112
  · exact u3113
  · exact u3114
  · exact u3115

def r6809 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6809 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6809 : Upper (D 1) (R 1) [52,24,258,192] 13 := by
  apply FastRouting.sound _ _ [52,24,258,192] 13 (by decide) (choices 1) [1,2,32,64] r6809 c6809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3116
  · exact u3117
  · exact u3118
  · exact u3119

def b6810 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 324 11 242 226 226 226 482), lower := (rows 53 26 324 11 16 32 64 128 256), losses := [] }

theorem u6810 : Upper (D 1) (R 1) [52,24,320,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6810
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6811 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 53 26 324 41 210 226 194 194 450), lower := (rows 53 26 324 41 16 32 64 128 256), losses := [] }

theorem u6811 : Upper (D 1) (R 1) [52,24,320,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6811
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6812 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 53 26 324 42 211 227 195 195 451), lower := (rows 53 26 324 42 16 32 64 128 256), losses := [] }

theorem u6812 : Upper (D 1) (R 1) [52,24,320,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6812
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6813 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 26 324 73 178 162 226 162 418), lower := (rows 53 26 324 73 16 32 64 128 256), losses := [] }

theorem u6813 : Upper (D 1) (R 1) [52,24,320,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6813
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6814 : Route 9 := (fun mask => (mask,id))

def c6814 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6814 : Upper (D 1) (R 1) [52,24,320,66] 13 := by
  apply FastRouting.sound _ _ [52,24,320,66] 13 (by decide) (choices 1) [1,2,32,128] r6814 c6814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3120
  · exact u3121
  · exact u3122
  · exact u3123

def r6815 : Route 9 := (fun mask => (mask,id))

def c6815 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6815 : Upper (D 1) (R 1) [52,24,320,96] 13 := by
  apply FastRouting.sound _ _ [52,24,320,96] 13 (by decide) (choices 1) [1,2,128] r6815 c6815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3124
  · exact u3125
  · exact u3126

def b6816 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 26 324 137 242 226 226 226 482), lower := (rows 53 26 324 137 16 32 64 128 256), losses := [] }

theorem u6816 : Upper (D 1) (R 1) [52,24,320,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6816
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6817 : Route 9 := (fun mask => (mask,id))

def c6817 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6817 : Upper (D 1) (R 1) [52,24,320,130] 13 := by
  apply FastRouting.sound _ _ [52,24,320,130] 13 (by decide) (choices 1) [1,2,32,64,128] r6817 c6817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3127
  · exact u3128
  · exact u3129
  · exact u3130
  · exact u3131

def r6818 : Route 9 := (fun mask => (mask,id))

def c6818 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6818 : Upper (D 1) (R 1) [52,24,320,160] 13 := by
  apply FastRouting.sound _ _ [52,24,320,160] 13 (by decide) (choices 1) [1,2,64,128] r6818 c6818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3132
  · exact u3133
  · exact u3134
  · exact u3135

def r6819 : Route 9 := (fun mask => (mask,id))

def c6819 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6819 : Upper (D 1) (R 1) [52,24,320,192] 13 := by
  apply FastRouting.sound _ _ [52,24,320,192] 13 (by decide) (choices 1) [1,2,32,128] r6819 c6819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3136
  · exact u3137
  · exact u3138
  · exact u3139

def b6820 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 53 67 14 26 496 480 480 480 480), lower := (rows 53 67 14 26 16 32 64 128 256), losses := [] }

theorem u6820 : Upper (D 1) (R 1) [52,65,10,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6820
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6821 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 14 56 466 482 450 450 450), lower := (rows 53 67 14 56 16 32 64 128 256), losses := [] }

theorem u6821 : Upper (D 1) (R 1) [52,65,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6821
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6822 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 53 67 14 74 432 432 496 432 432), lower := (rows 53 67 14 74 16 32 64 128 256), losses := [] }

theorem u6822 : Upper (D 1) (R 1) [52,65,10,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6822
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6823 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 14 88 434 418 482 418 418), lower := (rows 53 67 14 88 16 32 64 128 256), losses := [] }

theorem u6823 : Upper (D 1) (R 1) [52,65,10,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6823
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6824 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 67 14 138 496 496 496 496 496), lower := (rows 53 67 14 138 16 32 64 128 256), losses := [] }

theorem u6824 : Upper (D 1) (R 1) [52,65,10,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6824
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6825 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 14 152 498 482 482 482 482), lower := (rows 53 67 14 152 16 32 64 128 256), losses := [] }

theorem u6825 : Upper (D 1) (R 1) [52,65,10,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6825
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6826 : PairBound 9 := { available := 434, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 53 67 14 200 434 434 498 434 434), lower := (rows 53 67 14 200 16 32 64 128 256), losses := [] }

theorem u6826 : Upper (D 1) (R 1) [52,65,10,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6826
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6827 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 67 14 266 240 240 240 240 496), lower := (rows 53 67 14 266 16 32 64 128 256), losses := [] }

theorem u6827 : Upper (D 1) (R 1) [52,65,10,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6827
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6828 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 14 280 242 226 226 226 482), lower := (rows 53 67 14 280 16 32 64 128 256), losses := [] }

theorem u6828 : Upper (D 1) (R 1) [52,65,10,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6828
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6829 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 53 67 14 328 178 178 242 178 434), lower := (rows 53 67 14 328 16 32 64 128 256), losses := [] }

theorem u6829 : Upper (D 1) (R 1) [52,65,10,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6829
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6830 : Route 9 := (fun mask => (mask,id))

def c6830 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6830 : Upper (D 1) (R 1) [52,65,10,384] 13 := by
  apply FastRouting.sound _ _ [52,65,10,384] 13 (by decide) (choices 1) [2,32,64,128] r6830 c6830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3140
  · exact u3141
  · exact u3142
  · exact u3143

def b6831 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 67 134 26 504 488 488 488 488), lower := (rows 53 67 134 26 16 32 64 128 256), losses := [] }

theorem u6831 : Upper (D 1) (R 1) [52,65,130,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6831
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6832 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 134 56 474 490 458 458 458), lower := (rows 53 67 134 56 16 32 64 128 256), losses := [] }

theorem u6832 : Upper (D 1) (R 1) [52,65,130,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6832
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6833 : PairBound 9 := { available := 440, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 67 134 74 440 440 504 440 440), lower := (rows 53 67 134 74 16 32 64 128 256), losses := [] }

theorem u6833 : Upper (D 1) (R 1) [52,65,130,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6833
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6834 : Route 9 := (fun mask => (mask,id))

def c6834 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | _ => 0)

theorem u6834 : Upper (D 1) (R 1) [52,65,130,80] 13 := by
  apply FastRouting.sound _ _ [52,65,130,80] 13 (by decide) (choices 1) [2,8,32,128,256] r6834 c6834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3144
  · exact u3145
  · exact u3146
  · exact u3147
  · exact u3148

def b6835 : PairBound 9 := { available := 376, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 67 134 138 376 376 376 504 376), lower := (rows 53 67 134 138 16 32 64 128 256), losses := [] }

theorem u6835 : Upper (D 1) (R 1) [52,65,130,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6835
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6836 : Route 9 := (fun mask => (mask,id))

def c6836 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | _ => 0)

theorem u6836 : Upper (D 1) (R 1) [52,65,130,144] 13 := by
  apply FastRouting.sound _ _ [52,65,130,144] 13 (by decide) (choices 1) [2,8,32,64,256] r6836 c6836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3149
  · exact u3150
  · exact u3151
  · exact u3152
  · exact u3153

def r6837 : Route 9 := (fun mask => (mask,id))

def c6837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6837 : Upper (D 1) (R 1) [52,65,130,192] 13 := by
  apply FastRouting.sound _ _ [52,65,130,192] 13 (by decide) (choices 1) [2,8,32,256] r6837 c6837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3154
  · exact u3155
  · exact u3156
  · exact u3157

def r6838 : Route 9 := (fun mask => (mask,id))

def c6838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u6838 : Upper (D 1) (R 1) [52,65,130,258] 13 := by
  apply FastRouting.sound _ _ [52,65,130,258] 13 (by decide) (choices 1) [8,32,64,128] r6838 c6838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3158
  · exact u3159
  · exact u3160
  · exact u3161

def r6839 : Route 9 := (fun mask => (mask,id))

def c6839 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u6839 : Upper (D 1) (R 1) [52,65,130,272] 13 := by
  apply FastRouting.sound _ _ [52,65,130,272] 13 (by decide) (choices 1) [2,8,32,64,128] r6839 c6839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3162
  · exact u3163
  · exact u3164
  · exact u3165
  · exact u3166

#print axioms u6839
end Delivery.IrregularNine14.P01
