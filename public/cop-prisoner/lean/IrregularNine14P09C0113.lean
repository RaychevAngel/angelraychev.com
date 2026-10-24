import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0052
import IrregularNine14P09C0053
import IrregularNine14P09C0054

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6780 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6780 : Upper (D 9) (R 9) [6,33,72,17,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,384] 13 (by decide) (choices 1) [64,128] r6780 c6780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3133
  · exact u3134

def b6781 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 4, region := 428, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(1,6),(2,0),(3,0),(4,5)], upper := (rows 7 35 76 56 81 416 448 384 384), lower := (rows 7 35 76 56 81 32 64 128 256), losses := [] }

theorem u6781 : Upper (D 9) (R 9) [6,33,72,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6781 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6782 : Route 9 := (fun mask => (mask,id))

def c6782 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6782 : Upper (D 9) (R 9) [6,33,72,48,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,129] 13 (by decide) (choices 1) [64,128,256] r6782 c6782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3135
  · exact u3136
  · exact u3137

def r6783 : Route 9 := (fun mask => (mask,id))

def c6783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6783 : Upper (D 9) (R 9) [6,33,72,48,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,192] 13 (by decide) (choices 1) [1,128,256] r6783 c6783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3138
  · exact u3139
  · exact u3140

def r6784 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6784 : Upper (D 9) (R 9) [6,33,72,48,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,384] 13 (by decide) (choices 1) [1,64,128] r6784 c6784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3141
  · exact u3142
  · exact u3143

def r6785 : Route 9 := (fun mask => (mask,id))

def c6785 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6785 : Upper (D 9) (R 9) [6,33,72,129,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,96] 13 (by decide) (choices 1) [16,128,256] r6785 c6785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3144
  · exact u3145
  · exact u3146

def r6786 : Route 9 := (fun mask => (mask,id))

def c6786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u6786 : Upper (D 9) (R 9) [6,33,72,129,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,160] 13 (by decide) (choices 1) [16,64,256] r6786 c6786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3147
  · exact u3148
  · exact u3149

def r6787 : Route 9 := (fun mask => (mask,id))

def c6787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6787 : Upper (D 9) (R 9) [6,33,72,129,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,192] 13 (by decide) (choices 1) [16,256] r6787 c6787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3150
  · exact u3151

def r6788 : Route 9 := (fun mask => (mask,id))

def c6788 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u6788 : Upper (D 9) (R 9) [6,33,72,129,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,288] 13 (by decide) (choices 1) [16,64,128,256] r6788 c6788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3152
  · exact u3153
  · exact u3154
  · exact u3155

def r6789 : Route 9 := (fun mask => (mask,id))

def c6789 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6789 : Upper (D 9) (R 9) [6,33,72,129,320] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,320] 13 (by decide) (choices 1) [16,128,256] r6789 c6789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3156
  · exact u3157
  · exact u3158

def r6790 : Route 9 := (fun mask => (mask,id))

def c6790 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u6790 : Upper (D 9) (R 9) [6,33,72,129,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,384] 13 (by decide) (choices 1) [16,64,256] r6790 c6790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3159
  · exact u3160
  · exact u3161

def b6791 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 16, targets := 448 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7),(4,8)], upper := (rows 7 35 76 152 49 480 448 448 448), lower := (rows 7 35 76 152 49 32 64 128 256), losses := [] }

theorem u6791 : Upper (D 9) (R 9) [6,33,72,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6791 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6792 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 4, region := 428, targets := 1 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,6),(1,6),(2,0),(3,0),(3,6)], upper := (rows 7 35 76 152 81 416 480 416 416), lower := (rows 7 35 76 152 81 32 64 128 256), losses := [] }

theorem u6792 : Upper (D 9) (R 9) [6,33,72,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6792 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6793 : Route 9 := (fun mask => (mask,id))

def c6793 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6793 : Upper (D 9) (R 9) [6,33,72,144,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,96] 13 (by decide) (choices 1) [1,128,256] r6793 c6793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3162
  · exact u3163
  · exact u3164

def b6794 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 96 }], pairs := [(0,7),(1,7),(2,7),(3,5),(3,6)], upper := (rows 7 35 76 152 145 352 352 480 352), lower := (rows 7 35 76 152 145 32 64 128 256), losses := [] }

theorem u6794 : Upper (D 9) (R 9) [6,33,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6794 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6795 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 7 35 76 152 176 353 321 449 321), lower := (rows 7 35 76 152 176 32 64 128 256), losses := [] }

theorem u6795 : Upper (D 9) (R 9) [6,33,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6795 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6796 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 12, targets := 289 }], pairs := [(2,0),(2,5),(2,8),(3,0),(3,5)], upper := (rows 7 35 76 152 208 289 353 417 289), lower := (rows 7 35 76 152 208 32 64 128 256), losses := [] }

theorem u6796 : Upper (D 9) (R 9) [6,33,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6796 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6797 : Route 9 := (fun mask => (mask,id))

def c6797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6797 : Upper (D 9) (R 9) [6,33,72,144,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,257] 13 (by decide) (choices 1) [64,128,256] r6797 c6797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3165
  · exact u3166
  · exact u3167

def r6798 : Route 9 := (fun mask => (mask,id))

def c6798 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6798 : Upper (D 9) (R 9) [6,33,72,144,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,288] 13 (by decide) (choices 1) [1,64,128,256] r6798 c6798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3168
  · exact u3169
  · exact u3170
  · exact u3171

def r6799 : Route 9 := (fun mask => (mask,id))

def c6799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6799 : Upper (D 9) (R 9) [6,33,72,144,320] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,320] 13 (by decide) (choices 1) [1,128,256] r6799 c6799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3172
  · exact u3173
  · exact u3174

def b6800 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 7 35 76 152 400 353 353 481 353), lower := (rows 7 35 76 152 400 32 64 128 256), losses := [] }

theorem u6800 : Upper (D 9) (R 9) [6,33,72,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6800 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6801 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 428, targets := 1 },{ cop := 4, region := 426, targets := 64 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,6),(2,0),(3,0),(3,6),(4,5)], upper := (rows 7 35 76 168 81 432 464 400 400), lower := (rows 7 35 76 168 81 32 64 128 256), losses := [] }

theorem u6801 : Upper (D 9) (R 9) [6,33,72,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6801 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6802 : Route 9 := (fun mask => (mask,id))

def c6802 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u6802 : Upper (D 9) (R 9) [6,33,72,160,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,129] 13 (by decide) (choices 1) [16,64,256] r6802 c6802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3175
  · exact u3176
  · exact u3177

def r6803 : Route 9 := (fun mask => (mask,id))

def c6803 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6803 : Upper (D 9) (R 9) [6,33,72,160,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,192] 13 (by decide) (choices 1) [1,16,256] r6803 c6803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3178
  · exact u3179
  · exact u3180

def r6804 : Route 9 := (fun mask => (mask,id))

def c6804 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u6804 : Upper (D 9) (R 9) [6,33,72,160,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,257] 13 (by decide) (choices 1) [16,64,128,256] r6804 c6804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3181
  · exact u3182
  · exact u3183
  · exact u3184

def r6805 : Route 9 := (fun mask => (mask,id))

def c6805 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6805 : Upper (D 9) (R 9) [6,33,72,160,320] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,320] 13 (by decide) (choices 1) [1,16,128,256] r6805 c6805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3185
  · exact u3186
  · exact u3187
  · exact u3188

def r6806 : Route 9 := (fun mask => (mask,id))

def c6806 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u6806 : Upper (D 9) (R 9) [6,33,72,160,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,384] 13 (by decide) (choices 1) [1,16,64,256] r6806 c6806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3189
  · exact u3190
  · exact u3191
  · exact u3192

def b6807 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 16, targets := 448 },{ cop := 4, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7),(4,8)], upper := (rows 7 35 76 392 49 496 464 464 464), lower := (rows 7 35 76 392 49 32 64 128 256), losses := [] }

theorem u6807 : Upper (D 9) (R 9) [6,33,72,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6807 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6808 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6808 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6808 : Upper (D 9) (R 9) [6,33,72,384,65] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,65] 13 (by decide) (choices 1) [16,128] r6808 c6808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3193
  · exact u3194

def r6809 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6809 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6809 : Upper (D 9) (R 9) [6,33,72,384,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,96] 13 (by decide) (choices 1) [1,16,128] r6809 c6809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3195
  · exact u3196
  · exact u3197

def r6810 : Route 9 := (fun mask => (mask,id))

def c6810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u6810 : Upper (D 9) (R 9) [6,33,72,384,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,129] 13 (by decide) (choices 1) [16,64,256] r6810 c6810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3198
  · exact u3199
  · exact u3200

def r6811 : Route 9 := (fun mask => (mask,id))

def c6811 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u6811 : Upper (D 9) (R 9) [6,33,72,384,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,160] 13 (by decide) (choices 1) [1,16,64,256] r6811 c6811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3201
  · exact u3202
  · exact u3203
  · exact u3204

def r6812 : Route 9 := (fun mask => (mask,id))

def c6812 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6812 : Upper (D 9) (R 9) [6,33,72,384,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,192] 13 (by decide) (choices 1) [1,16,256] r6812 c6812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3205
  · exact u3206
  · exact u3207

def b6813 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 7 35 76 392 400 113 113 241 369), lower := (rows 7 35 76 392 400 32 64 128 256), losses := [] }

theorem u6813 : Upper (D 9) (R 9) [6,33,72,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6813 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6814 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 24, targets := 448 }], pairs := [(3,6),(3,7),(3,8),(4,6),(4,7)], upper := (rows 7 35 196 25 56 480 448 448 448), lower := (rows 7 35 196 25 56 32 64 128 256), losses := [] }

theorem u6814 : Upper (D 9) (R 9) [6,33,192,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6814 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6815 : Route 9 := (fun mask => (mask,id))

def c6815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6815 : Upper (D 9) (R 9) [6,33,192,17,72] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,72] 13 (by decide) (choices 1) [128,256] r6815 c6815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3208
  · exact u3209

def r6816 : Route 9 := (fun mask => (mask,id))

def c6816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6816 : Upper (D 9) (R 9) [6,33,192,17,96] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,96] 13 (by decide) (choices 1) [8,128,256] r6816 c6816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3210
  · exact u3211
  · exact u3212

def b6817 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 16, targets := 289 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,8)], upper := (rows 7 35 196 25 208 296 360 424 296), lower := (rows 7 35 196 25 208 32 64 128 256), losses := [] }

theorem u6817 : Upper (D 9) (R 9) [6,33,192,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6817 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6818 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6818 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6818 : Upper (D 9) (R 9) [6,33,192,17,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,264] 13 (by decide) (choices 1) [64,256] r6818 c6818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3213
  · exact u3214

def r6819 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6819 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | _ => 0)

theorem u6819 : Upper (D 9) (R 9) [6,33,192,17,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,288] 13 (by decide) (choices 1) [8,64,256] r6819 c6819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3215
  · exact u3216
  · exact u3217

def r6820 : Route 9 := (fun mask => (mask,id))

def c6820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6820 : Upper (D 9) (R 9) [6,33,192,17,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,320] 13 (by decide) (choices 1) [8,128,256] r6820 c6820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3218
  · exact u3219
  · exact u3220

def b6821 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 8, targets := 448 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7),(3,8)], upper := (rows 7 35 196 41 88 432 464 400 400), lower := (rows 7 35 196 41 88 32 64 128 256), losses := [] }

theorem u6821 : Upper (D 9) (R 9) [6,33,192,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6821 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6822 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 8, targets := 448 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7),(3,8)], upper := (rows 7 35 196 41 280 496 464 464 464), lower := (rows 7 35 196 41 280 32 64 128 256), losses := [] }

theorem u6822 : Upper (D 9) (R 9) [6,33,192,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6822 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6823 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 8, targets := 448 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7),(3,8)], upper := (rows 7 35 196 41 336 440 472 408 408), lower := (rows 7 35 196 41 336 32 64 128 256), losses := [] }

theorem u6823 : Upper (D 9) (R 9) [6,33,192,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6823 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6824 : PairBound 9 := { available := 392, camps := [{ cop := 4, region := 428, targets := 1 },{ cop := 4, region := 426, targets := 64 },{ cop := 3, region := 452, targets := 32 }], pairs := [(1,6),(2,0),(2,5),(3,0),(3,6)], upper := (rows 7 35 196 56 81 424 456 392 392), lower := (rows 7 35 196 56 81 32 64 128 256), losses := [] }

theorem u6824 : Upper (D 9) (R 9) [6,33,192,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6824 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6825 : Route 9 := (fun mask => (mask,id))

def c6825 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6825 : Upper (D 9) (R 9) [6,33,192,48,72] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,72] 13 (by decide) (choices 1) [1,128,256] r6825 c6825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3221
  · exact u3222
  · exact u3223

def b6826 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 16, targets := 289 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,8)], upper := (rows 7 35 196 56 208 297 329 393 265), lower := (rows 7 35 196 56 208 32 64 128 256), losses := [] }

theorem u6826 : Upper (D 9) (R 9) [6,33,192,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6826 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6827 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | _ => 0)

theorem u6827 : Upper (D 9) (R 9) [6,33,192,48,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,257] 13 (by decide) (choices 1) [8,64,256] r6827 c6827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3224
  · exact u3225
  · exact u3226

def r6828 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6828 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6828 : Upper (D 9) (R 9) [6,33,192,48,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,264] 13 (by decide) (choices 1) [1,64,256] r6828 c6828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3227
  · exact u3228
  · exact u3229

def r6829 : Route 9 := (fun mask => (mask,id))

def c6829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6829 : Upper (D 9) (R 9) [6,33,192,48,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,320] 13 (by decide) (choices 1) [1,8,128,256] r6829 c6829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3230
  · exact u3231
  · exact u3232
  · exact u3233

def r6830 : Route 9 := (fun mask => (mask,id))

def c6830 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6830 : Upper (D 9) (R 9) [6,33,192,65,136] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,136] 13 (by decide) (choices 1) [16,256] r6830 c6830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3234
  · exact u3235

def r6831 : Route 9 := (fun mask => (mask,id))

def c6831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6831 : Upper (D 9) (R 9) [6,33,192,65,160] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,160] 13 (by decide) (choices 1) [8,16,256] r6831 c6831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3236
  · exact u3237
  · exact u3238

def r6832 : Route 9 := (fun mask => (mask,id))

def c6832 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6832 : Upper (D 9) (R 9) [6,33,192,65,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,264] 13 (by decide) (choices 1) [16,128,256] r6832 c6832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3239
  · exact u3240
  · exact u3241

def r6833 : Route 9 := (fun mask => (mask,id))

def c6833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u6833 : Upper (D 9) (R 9) [6,33,192,65,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,288] 13 (by decide) (choices 1) [8,16,128,256] r6833 c6833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3242
  · exact u3243
  · exact u3244
  · exact u3245

def r6834 : Route 9 := (fun mask => (mask,id))

def c6834 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6834 : Upper (D 9) (R 9) [6,33,192,65,384] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,384] 13 (by decide) (choices 1) [8,16,256] r6834 c6834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3246
  · exact u3247
  · exact u3248

def b6835 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 24, targets := 289 }], pairs := [(3,0),(3,5),(3,8),(4,0),(4,5)], upper := (rows 7 35 196 88 152 289 353 417 289), lower := (rows 7 35 196 88 152 32 64 128 256), losses := [] }

theorem u6835 : Upper (D 9) (R 9) [6,33,192,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6835 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6836 : Route 9 := (fun mask => (mask,id))

def c6836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6836 : Upper (D 9) (R 9) [6,33,192,80,160] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,160] 13 (by decide) (choices 1) [1,8,256] r6836 c6836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3249
  · exact u3250
  · exact u3251

def r6837 : Route 9 := (fun mask => (mask,id))

def c6837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6837 : Upper (D 9) (R 9) [6,33,192,80,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,257] 13 (by decide) (choices 1) [8,128,256] r6837 c6837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3252
  · exact u3253
  · exact u3254

def r6838 : Route 9 := (fun mask => (mask,id))

def c6838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6838 : Upper (D 9) (R 9) [6,33,192,80,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,264] 13 (by decide) (choices 1) [1,128,256] r6838 c6838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3255
  · exact u3256
  · exact u3257

def r6839 : Route 9 := (fun mask => (mask,id))

def c6839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6839 : Upper (D 9) (R 9) [6,33,192,80,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,288] 13 (by decide) (choices 1) [1,8,128,256] r6839 c6839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3258
  · exact u3259
  · exact u3260
  · exact u3261

#print axioms u6839
end Delivery.IrregularNine14.P09
