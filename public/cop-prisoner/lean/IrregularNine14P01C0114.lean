import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0052
import IrregularNine14P01C0053

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6840 : Route 9 := (fun mask => (mask,id))

def c6840 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6840 : Upper (D 1) (R 1) [52,65,130,320] 13 := by
  apply FastRouting.sound _ _ [52,65,130,320] 13 (by decide) (choices 1) [2,8,32,128] r6840 c6840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3167
  · exact u3168
  · exact u3169
  · exact u3170

def r6841 : Route 9 := (fun mask => (mask,id))

def c6841 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6841 : Upper (D 1) (R 1) [52,65,130,384] 13 := by
  apply FastRouting.sound _ _ [52,65,130,384] 13 (by decide) (choices 1) [2,8,32,64] r6841 c6841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3171
  · exact u3172
  · exact u3173
  · exact u3174

def b6842 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 140 26 498 482 482 482 482), lower := (rows 53 67 140 26 16 32 64 128 256), losses := [] }

theorem u6842 : Upper (D 1) (R 1) [52,65,136,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6842
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6843 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 140 56 466 482 450 450 450), lower := (rows 53 67 140 56 16 32 64 128 256), losses := [] }

theorem u6843 : Upper (D 1) (R 1) [52,65,136,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6843
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6844 : PairBound 9 := { available := 434, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 67 140 74 434 434 498 434 434), lower := (rows 53 67 140 74 16 32 64 128 256), losses := [] }

theorem u6844 : Upper (D 1) (R 1) [52,65,136,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6844
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6845 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 140 88 434 418 482 418 418), lower := (rows 53 67 140 88 16 32 64 128 256), losses := [] }

theorem u6845 : Upper (D 1) (R 1) [52,65,136,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6845
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6846 : PairBound 9 := { available := 370, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 67 140 138 370 370 370 498 370), lower := (rows 53 67 140 138 16 32 64 128 256), losses := [] }

theorem u6846 : Upper (D 1) (R 1) [52,65,136,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6846
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6847 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 67 140 152 370 354 354 482 354), lower := (rows 53 67 140 152 16 32 64 128 256), losses := [] }

theorem u6847 : Upper (D 1) (R 1) [52,65,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6847
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6848 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 67 140 200 306 306 370 434 306), lower := (rows 53 67 140 200 16 32 64 128 256), losses := [] }

theorem u6848 : Upper (D 1) (R 1) [52,65,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6848
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6849 : Route 9 := (fun mask => (mask,id))

def c6849 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6849 : Upper (D 1) (R 1) [52,65,136,258] 13 := by
  apply FastRouting.sound _ _ [52,65,136,258] 13 (by decide) (choices 1) [2,32,64,128] r6849 c6849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3175
  · exact u3176
  · exact u3177
  · exact u3178

def b6850 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 140 280 242 226 226 226 482), lower := (rows 53 67 140 280 16 32 64 128 256), losses := [] }

theorem u6850 : Upper (D 1) (R 1) [52,65,136,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6850
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6851 : Route 9 := (fun mask => (mask,id))

def c6851 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6851 : Upper (D 1) (R 1) [52,65,136,320] 13 := by
  apply FastRouting.sound _ _ [52,65,136,320] 13 (by decide) (choices 1) [2,32,128] r6851 c6851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3179
  · exact u3180
  · exact u3181

def b6852 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 67 140 392 114 114 114 242 370), lower := (rows 53 67 140 392 16 32 64 128 256), losses := [] }

theorem u6852 : Upper (D 1) (R 1) [52,65,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6852
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6853 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 67 262 26 248 232 232 232 488), lower := (rows 53 67 262 26 16 32 64 128 256), losses := [] }

theorem u6853 : Upper (D 1) (R 1) [52,65,258,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6853
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6854 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 262 56 218 234 202 202 458), lower := (rows 53 67 262 56 16 32 64 128 256), losses := [] }

theorem u6854 : Upper (D 1) (R 1) [52,65,258,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6854
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6855 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 67 262 74 184 184 248 184 440), lower := (rows 53 67 262 74 16 32 64 128 256), losses := [] }

theorem u6855 : Upper (D 1) (R 1) [52,65,258,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6855
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6856 : Route 9 := (fun mask => (mask,id))

def c6856 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6856 : Upper (D 1) (R 1) [52,65,258,80] 13 := by
  apply FastRouting.sound _ _ [52,65,258,80] 13 (by decide) (choices 1) [2,8,32,128] r6856 c6856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3182
  · exact u3183
  · exact u3184
  · exact u3185

def r6857 : Route 9 := (fun mask => (mask,id))

def c6857 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u6857 : Upper (D 1) (R 1) [52,65,258,130] 13 := by
  apply FastRouting.sound _ _ [52,65,258,130] 13 (by decide) (choices 1) [8,32,64,128] r6857 c6857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3186
  · exact u3187
  · exact u3188
  · exact u3189

def r6858 : Route 9 := (fun mask => (mask,id))

def c6858 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u6858 : Upper (D 1) (R 1) [52,65,258,144] 13 := by
  apply FastRouting.sound _ _ [52,65,258,144] 13 (by decide) (choices 1) [2,8,32,64,128] r6858 c6858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3190
  · exact u3191
  · exact u3192
  · exact u3193
  · exact u3194

def r6859 : Route 9 := (fun mask => (mask,id))

def c6859 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6859 : Upper (D 1) (R 1) [52,65,258,192] 13 := by
  apply FastRouting.sound _ _ [52,65,258,192] 13 (by decide) (choices 1) [2,8,32,128] r6859 c6859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3195
  · exact u3196
  · exact u3197
  · exact u3198

def b6860 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 268 26 242 226 226 226 482), lower := (rows 53 67 268 26 16 32 64 128 256), losses := [] }

theorem u6860 : Upper (D 1) (R 1) [52,65,264,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6860
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6861 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 268 56 210 226 194 194 450), lower := (rows 53 67 268 56 16 32 64 128 256), losses := [] }

theorem u6861 : Upper (D 1) (R 1) [52,65,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6861
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6862 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 67 268 74 178 178 242 178 434), lower := (rows 53 67 268 74 16 32 64 128 256), losses := [] }

theorem u6862 : Upper (D 1) (R 1) [52,65,264,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6862
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6863 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 268 88 178 162 226 162 418), lower := (rows 53 67 268 88 16 32 64 128 256), losses := [] }

theorem u6863 : Upper (D 1) (R 1) [52,65,264,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6863
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6864 : Route 9 := (fun mask => (mask,id))

def c6864 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6864 : Upper (D 1) (R 1) [52,65,264,130] 13 := by
  apply FastRouting.sound _ _ [52,65,264,130] 13 (by decide) (choices 1) [2,32,64,128] r6864 c6864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3199
  · exact u3200
  · exact u3201
  · exact u3202

def b6865 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 268 152 242 226 226 226 482), lower := (rows 53 67 268 152 16 32 64 128 256), losses := [] }

theorem u6865 : Upper (D 1) (R 1) [52,65,264,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6865
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6866 : Route 9 := (fun mask => (mask,id))

def c6866 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6866 : Upper (D 1) (R 1) [52,65,264,192] 13 := by
  apply FastRouting.sound _ _ [52,65,264,192] 13 (by decide) (choices 1) [2,32,128] r6866 c6866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3203
  · exact u3204
  · exact u3205

def b6867 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 67 388 26 250 234 234 234 490), lower := (rows 53 67 388 26 16 32 64 128 256), losses := [] }

theorem u6867 : Upper (D 1) (R 1) [52,65,384,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6867
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6868 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 67 388 56 218 234 202 202 458), lower := (rows 53 67 388 56 16 32 64 128 256), losses := [] }

theorem u6868 : Upper (D 1) (R 1) [52,65,384,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6868
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6869 : PairBound 9 := { available := 186, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 67 388 74 186 186 250 186 442), lower := (rows 53 67 388 74 16 32 64 128 256), losses := [] }

theorem u6869 : Upper (D 1) (R 1) [52,65,384,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6869
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6870 : Route 9 := (fun mask => (mask,id))

def c6870 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6870 : Upper (D 1) (R 1) [52,65,384,80] 13 := by
  apply FastRouting.sound _ _ [52,65,384,80] 13 (by decide) (choices 1) [2,8,32,128] r6870 c6870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3206
  · exact u3207
  · exact u3208
  · exact u3209

def r6871 : Route 9 := (fun mask => (mask,id))

def c6871 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6871 : Upper (D 1) (R 1) [52,65,384,130] 13 := by
  apply FastRouting.sound _ _ [52,65,384,130] 13 (by decide) (choices 1) [2,8,32,64] r6871 c6871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3210
  · exact u3211
  · exact u3212
  · exact u3213

def r6872 : Route 9 := (fun mask => (mask,id))

def c6872 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6872 : Upper (D 1) (R 1) [52,65,384,144] 13 := by
  apply FastRouting.sound _ _ [52,65,384,144] 13 (by decide) (choices 1) [2,8,32,64] r6872 c6872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3214
  · exact u3215
  · exact u3216
  · exact u3217

def r6873 : Route 9 := (fun mask => (mask,id))

def c6873 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6873 : Upper (D 1) (R 1) [52,65,384,192] 13 := by
  apply FastRouting.sound _ _ [52,65,384,192] 13 (by decide) (choices 1) [2,8,32] r6873 c6873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3218
  · exact u3219
  · exact u3220

def b6874 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 7 26 496 480 480 480 480), lower := (rows 53 74 7 26 16 32 64 128 256), losses := [] }

theorem u6874 : Upper (D 1) (R 1) [52,72,3,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6874
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6875 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 7 56 466 482 450 450 450), lower := (rows 53 74 7 56 16 32 64 128 256), losses := [] }

theorem u6875 : Upper (D 1) (R 1) [52,72,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6875
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6876 : PairBound 9 := { available := 432, camps := [{ cop := 6, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 7 74 432 432 496 432 432), lower := (rows 53 74 7 74 16 32 64 128 256), losses := [] }

theorem u6876 : Upper (D 1) (R 1) [52,72,3,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6876
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6877 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 53 74 7 88 434 418 482 418 418), lower := (rows 53 74 7 88 16 32 64 128 256), losses := [] }

theorem u6877 : Upper (D 1) (R 1) [52,72,3,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6877
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6878 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 7 138 496 496 496 496 496), lower := (rows 53 74 7 138 16 32 64 128 256), losses := [] }

theorem u6878 : Upper (D 1) (R 1) [52,72,3,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6878
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6879 : PairBound 9 := { available := 482, camps := [{ cop := 3, region := 354, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 7 152 498 482 482 482 482), lower := (rows 53 74 7 152 16 32 64 128 256), losses := [] }

theorem u6879 : Upper (D 1) (R 1) [52,72,3,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6879
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6880 : PairBound 9 := { available := 434, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 7 200 434 434 498 434 434), lower := (rows 53 74 7 200 16 32 64 128 256), losses := [] }

theorem u6880 : Upper (D 1) (R 1) [52,72,3,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6880
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6881 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 7 266 240 240 240 240 496), lower := (rows 53 74 7 266 16 32 64 128 256), losses := [] }

theorem u6881 : Upper (D 1) (R 1) [52,72,3,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6881
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6882 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 7 280 242 226 226 226 482), lower := (rows 53 74 7 280 16 32 64 128 256), losses := [] }

theorem u6882 : Upper (D 1) (R 1) [52,72,3,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6882
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6883 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 7 328 178 178 242 178 434), lower := (rows 53 74 7 328 16 32 64 128 256), losses := [] }

theorem u6883 : Upper (D 1) (R 1) [52,72,3,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6883
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6884 : Route 9 := (fun mask => (mask,id))

def c6884 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6884 : Upper (D 1) (R 1) [52,72,3,384] 13 := by
  apply FastRouting.sound _ _ [52,72,3,384] 13 (by decide) (choices 1) [2,32,64,128] r6884 c6884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3221
  · exact u3222
  · exact u3223
  · exact u3224

def b6885 : PairBound 9 := { available := 482, camps := [{ cop := 3, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 133 26 498 482 482 482 482), lower := (rows 53 74 133 26 16 32 64 128 256), losses := [] }

theorem u6885 : Upper (D 1) (R 1) [52,72,129,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6885
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6886 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 133 56 466 482 450 450 450), lower := (rows 53 74 133 56 16 32 64 128 256), losses := [] }

theorem u6886 : Upper (D 1) (R 1) [52,72,129,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6886
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6887 : PairBound 9 := { available := 434, camps := [{ cop := 6, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 133 74 434 434 498 434 434), lower := (rows 53 74 133 74 16 32 64 128 256), losses := [] }

theorem u6887 : Upper (D 1) (R 1) [52,72,129,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6887
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6888 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 53 74 133 88 434 418 482 418 418), lower := (rows 53 74 133 88 16 32 64 128 256), losses := [] }

theorem u6888 : Upper (D 1) (R 1) [52,72,129,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6888
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6889 : PairBound 9 := { available := 370, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 133 138 370 370 370 498 370), lower := (rows 53 74 133 138 16 32 64 128 256), losses := [] }

theorem u6889 : Upper (D 1) (R 1) [52,72,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6889
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6890 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 354, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 133 152 370 354 354 482 354), lower := (rows 53 74 133 152 16 32 64 128 256), losses := [] }

theorem u6890 : Upper (D 1) (R 1) [52,72,129,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6890
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6891 : PairBound 9 := { available := 306, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 53 74 133 200 306 306 370 434 306), lower := (rows 53 74 133 200 16 32 64 128 256), losses := [] }

theorem u6891 : Upper (D 1) (R 1) [52,72,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6891
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6892 : Route 9 := (fun mask => (mask,id))

def c6892 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6892 : Upper (D 1) (R 1) [52,72,129,258] 13 := by
  apply FastRouting.sound _ _ [52,72,129,258] 13 (by decide) (choices 1) [2,32,64,128] r6892 c6892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3225
  · exact u3226
  · exact u3227
  · exact u3228

def b6893 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 133 280 242 226 226 226 482), lower := (rows 53 74 133 280 16 32 64 128 256), losses := [] }

theorem u6893 : Upper (D 1) (R 1) [52,72,129,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6893
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6894 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 133 328 178 178 242 178 434), lower := (rows 53 74 133 328 16 32 64 128 256), losses := [] }

theorem u6894 : Upper (D 1) (R 1) [52,72,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6894
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6895 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 114, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 133 392 114 114 114 242 370), lower := (rows 53 74 133 392 16 32 64 128 256), losses := [] }

theorem u6895 : Upper (D 1) (R 1) [52,72,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6895
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6896 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 369, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 134 11 496 496 496 496 496), lower := (rows 53 74 134 11 16 32 64 128 256), losses := [] }

theorem u6896 : Upper (D 1) (R 1) [52,72,130,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6896
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6897 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 134 25 498 482 482 482 482), lower := (rows 53 74 134 25 16 32 64 128 256), losses := [] }

theorem u6897 : Upper (D 1) (R 1) [52,72,130,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6897
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6898 : PairBound 9 := { available := 481, camps := [{ cop := 2, region := 369, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 134 26 497 481 481 481 481), lower := (rows 53 74 134 26 16 32 64 128 256), losses := [] }

theorem u6898 : Upper (D 1) (R 1) [52,72,130,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6898
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6899 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 134 56 467 483 451 451 451), lower := (rows 53 74 134 56 16 32 64 128 256), losses := [] }

theorem u6899 : Upper (D 1) (R 1) [52,72,130,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6899
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u6899
end Delivery.IrregularNine14.P01
