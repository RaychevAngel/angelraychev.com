import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0052
import IrregularNine14P08C0053

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r10800 : Route 9 := (fun mask => (mask,id))

def c10800 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10800 : Upper (D 8) (R 8) [66,36,129,192,288] 13 := by
  apply FastRouting.sound _ _ [66,36,129,192,288] 13 (by decide) (choices 1) [1,8,16] r10800 c10800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3129
  · exact u3130
  · exact u3131

def b10801 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 140 25 49 480 480 480 480), lower := (rows 67 38 140 25 49 32 64 128 256), losses := [] }

theorem u10801 : Upper (D 8) (R 8) [66,36,136,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10801 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10802 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 140 25 81 416 480 416 416), lower := (rows 67 38 140 25 81 32 64 128 256), losses := [] }

theorem u10802 : Upper (D 8) (R 8) [66,36,136,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10802 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10803 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 140 25 112 417 481 417 417), lower := (rows 67 38 140 25 112 32 64 128 256), losses := [] }

theorem u10803 : Upper (D 8) (R 8) [66,36,136,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10803 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10804 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 38 140 25 145 352 352 480 352), lower := (rows 67 38 140 25 145 32 64 128 256), losses := [] }

theorem u10804 : Upper (D 8) (R 8) [66,36,136,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10804 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10805 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 25 176 353 353 481 353), lower := (rows 67 38 140 25 176 32 64 128 256), losses := [] }

theorem u10805 : Upper (D 8) (R 8) [66,36,136,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10806 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 25 208 289 353 417 289), lower := (rows 67 38 140 25 208 32 64 128 256), losses := [] }

theorem u10806 : Upper (D 8) (R 8) [66,36,136,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10806 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10807 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 140 25 273 224 224 224 480), lower := (rows 67 38 140 25 273 32 64 128 256), losses := [] }

theorem u10807 : Upper (D 8) (R 8) [66,36,136,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10807 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10808 : Route 9 := (fun mask => (mask,id))

def c10808 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10808 : Upper (D 8) (R 8) [66,36,136,17,288] 13 := by
  apply FastRouting.sound _ _ [66,36,136,17,288] 13 (by decide) (choices 1) [1,64,128] r10808 c10808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3132
  · exact u3133
  · exact u3134

def b10809 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 140 25 336 161 225 161 417), lower := (rows 67 38 140 25 336 32 64 128 256), losses := [] }

theorem u10809 : Upper (D 8) (R 8) [66,36,136,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10809 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10810 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 25 400 97 97 225 353), lower := (rows 67 38 140 25 400 32 64 128 256), losses := [] }

theorem u10810 : Upper (D 8) (R 8) [66,36,136,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10810 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10811 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 140 41 49 496 464 464 464), lower := (rows 67 38 140 41 49 32 64 128 256), losses := [] }

theorem u10811 : Upper (D 8) (R 8) [66,36,136,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10811 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10812 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 140 41 81 432 496 432 432), lower := (rows 67 38 140 41 81 32 64 128 256), losses := [] }

theorem u10812 : Upper (D 8) (R 8) [66,36,136,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10812 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10813 : Route 9 := (fun mask => (mask,id))

def c10813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u10813 : Upper (D 8) (R 8) [66,36,136,33,96] 13 := by
  apply FastRouting.sound _ _ [66,36,136,33,96] 13 (by decide) (choices 1) [1,16,128,256] r10813 c10813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3135
  · exact u3136
  · exact u3137
  · exact u3138

def b10814 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 360, targets := 128 }], pairs := [(3,7)], upper := (rows 67 38 140 41 145 368 368 496 368), lower := (rows 67 38 140 41 145 32 64 128 256), losses := [] }

theorem u10814 : Upper (D 8) (R 8) [66,36,136,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10815 : Route 9 := (fun mask => (mask,id))

def c10815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u10815 : Upper (D 8) (R 8) [66,36,136,33,160] 13 := by
  apply FastRouting.sound _ _ [66,36,136,33,160] 13 (by decide) (choices 1) [1,16,64,256] r10815 c10815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3139
  · exact u3140
  · exact u3141
  · exact u3142

def r10816 : Route 9 := (fun mask => (mask,id))

def c10816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u10816 : Upper (D 8) (R 8) [66,36,136,33,192] 13 := by
  apply FastRouting.sound _ _ [66,36,136,33,192] 13 (by decide) (choices 1) [1,16,256] r10816 c10816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3143
  · exact u3144
  · exact u3145

def r10817 : Route 9 := (fun mask => (mask,id))

def c10817 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u10817 : Upper (D 8) (R 8) [66,36,136,33,257] 13 := by
  apply FastRouting.sound _ _ [66,36,136,33,257] 13 (by decide) (choices 1) [16,64,128] r10817 c10817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3146
  · exact u3147
  · exact u3148

def r10818 : Route 9 := (fun mask => (mask,id))

def c10818 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u10818 : Upper (D 8) (R 8) [66,36,136,33,288] 13 := by
  apply FastRouting.sound _ _ [66,36,136,33,288] 13 (by decide) (choices 1) [1,16,64,128] r10818 c10818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3149
  · exact u3150
  · exact u3151
  · exact u3152

def r10819 : Route 9 := (fun mask => (mask,id))

def c10819 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10819 : Upper (D 8) (R 8) [66,36,136,33,320] 13 := by
  apply FastRouting.sound _ _ [66,36,136,33,320] 13 (by decide) (choices 1) [1,16,128] r10819 c10819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3153
  · exact u3154
  · exact u3155

def r10820 : Route 9 := (fun mask => (mask,id))

def c10820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10820 : Upper (D 8) (R 8) [66,36,136,33,384] 13 := by
  apply FastRouting.sound _ _ [66,36,136,33,384] 13 (by decide) (choices 1) [1,16,64] r10820 c10820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3156
  · exact u3157
  · exact u3158

def b10821 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 140 56 49 481 449 449 449), lower := (rows 67 38 140 56 49 32 64 128 256), losses := [] }

theorem u10821 : Upper (D 8) (R 8) [66,36,136,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10821 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10822 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 140 56 81 417 481 417 417), lower := (rows 67 38 140 56 81 32 64 128 256), losses := [] }

theorem u10822 : Upper (D 8) (R 8) [66,36,136,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10822 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10823 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 140 56 112 417 449 385 385), lower := (rows 67 38 140 56 112 32 64 128 256), losses := [] }

theorem u10823 : Upper (D 8) (R 8) [66,36,136,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10824 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 56 145 353 353 481 353), lower := (rows 67 38 140 56 145 32 64 128 256), losses := [] }

theorem u10824 : Upper (D 8) (R 8) [66,36,136,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10824 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10825 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 140 56 176 353 321 449 321), lower := (rows 67 38 140 56 176 32 64 128 256), losses := [] }

theorem u10825 : Upper (D 8) (R 8) [66,36,136,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10825 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10826 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 56 208 289 353 417 289), lower := (rows 67 38 140 56 208 32 64 128 256), losses := [] }

theorem u10826 : Upper (D 8) (R 8) [66,36,136,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10826 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10827 : Route 9 := (fun mask => (mask,id))

def c10827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10827 : Upper (D 8) (R 8) [66,36,136,48,257] 13 := by
  apply FastRouting.sound _ _ [66,36,136,48,257] 13 (by decide) (choices 1) [1,64,128] r10827 c10827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3159
  · exact u3160
  · exact u3161

def b10828 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 140 56 304 225 193 193 449), lower := (rows 67 38 140 56 304 32 64 128 256), losses := [] }

theorem u10828 : Upper (D 8) (R 8) [66,36,136,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10828 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10829 : Route 9 := (fun mask => (mask,id))

def c10829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10829 : Upper (D 8) (R 8) [66,36,136,48,320] 13 := by
  apply FastRouting.sound _ _ [66,36,136,48,320] 13 (by decide) (choices 1) [1,128] r10829 c10829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3162
  · exact u3163

def b10830 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 56 400 97 97 225 353), lower := (rows 67 38 140 56 400 32 64 128 256), losses := [] }

theorem u10830 : Upper (D 8) (R 8) [66,36,136,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10830 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10831 : Route 9 := (fun mask => (mask,id))

def c10831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u10831 : Upper (D 8) (R 8) [66,36,136,257,33] 13 := by
  apply FastRouting.sound _ _ [66,36,136,257,33] 13 (by decide) (choices 1) [16,64,128] r10831 c10831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3164
  · exact u3165
  · exact u3166

def b10832 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 140 265 81 176 240 176 432), lower := (rows 67 38 140 265 81 32 64 128 256), losses := [] }

theorem u10832 : Upper (D 8) (R 8) [66,36,136,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10833 : Route 9 := (fun mask => (mask,id))

def c10833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10833 : Upper (D 8) (R 8) [66,36,136,257,96] 13 := by
  apply FastRouting.sound _ _ [66,36,136,257,96] 13 (by decide) (choices 1) [1,16,128] r10833 c10833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3167
  · exact u3168
  · exact u3169

def b10834 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 360, targets := 128 }], pairs := [(3,7)], upper := (rows 67 38 140 265 145 112 112 240 368), lower := (rows 67 38 140 265 145 32 64 128 256), losses := [] }

theorem u10834 : Upper (D 8) (R 8) [66,36,136,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10834 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10835 : Route 9 := (fun mask => (mask,id))

def c10835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10835 : Upper (D 8) (R 8) [66,36,136,257,160] 13 := by
  apply FastRouting.sound _ _ [66,36,136,257,160] 13 (by decide) (choices 1) [1,16,64] r10835 c10835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3170
  · exact u3171
  · exact u3172

def r10836 : Route 9 := (fun mask => (mask,id))

def c10836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10836 : Upper (D 8) (R 8) [66,36,136,257,192] 13 := by
  apply FastRouting.sound _ _ [66,36,136,257,192] 13 (by decide) (choices 1) [1,16] r10836 c10836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3173
  · exact u3174

def r10837 : Route 9 := (fun mask => (mask,id))

def c10837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10837 : Upper (D 8) (R 8) [66,36,136,272,33] 13 := by
  apply FastRouting.sound _ _ [66,36,136,272,33] 13 (by decide) (choices 1) [1,64,128] r10837 c10837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3175
  · exact u3176
  · exact u3177

def b10838 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 140 280 81 161 225 161 417), lower := (rows 67 38 140 280 81 32 64 128 256), losses := [] }

theorem u10838 : Upper (D 8) (R 8) [66,36,136,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10838 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10839 : Route 9 := (fun mask => (mask,id))

def c10839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10839 : Upper (D 8) (R 8) [66,36,136,272,96] 13 := by
  apply FastRouting.sound _ _ [66,36,136,272,96] 13 (by decide) (choices 1) [1,128] r10839 c10839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3178
  · exact u3179

def b10840 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 280 145 97 97 225 353), lower := (rows 67 38 140 280 145 32 64 128 256), losses := [] }

theorem u10840 : Upper (D 8) (R 8) [66,36,136,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10840 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10841 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 280 176 97 97 225 353), lower := (rows 67 38 140 280 176 32 64 128 256), losses := [] }

theorem u10841 : Upper (D 8) (R 8) [66,36,136,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10841 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10842 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 280 208 33 97 161 289), lower := (rows 67 38 140 280 208 32 64 128 256), losses := [] }

theorem u10842 : Upper (D 8) (R 8) [66,36,136,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10843 : Route 9 := (fun mask => (mask,id))

def c10843 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u10843 : Upper (D 8) (R 8) [66,36,136,288,33] 13 := by
  apply FastRouting.sound _ _ [66,36,136,288,33] 13 (by decide) (choices 1) [1,16,64,128] r10843 c10843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3180
  · exact u3181
  · exact u3182
  · exact u3183

def b10844 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 140 296 81 177 241 177 433), lower := (rows 67 38 140 296 81 32 64 128 256), losses := [] }

theorem u10844 : Upper (D 8) (R 8) [66,36,136,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10845 : Route 9 := (fun mask => (mask,id))

def c10845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10845 : Upper (D 8) (R 8) [66,36,136,288,96] 13 := by
  apply FastRouting.sound _ _ [66,36,136,288,96] 13 (by decide) (choices 1) [1,16,128] r10845 c10845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3184
  · exact u3185
  · exact u3186

def b10846 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 360, targets := 128 }], pairs := [(3,7)], upper := (rows 67 38 140 296 145 113 113 241 369), lower := (rows 67 38 140 296 145 32 64 128 256), losses := [] }

theorem u10846 : Upper (D 8) (R 8) [66,36,136,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10846 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10847 : Route 9 := (fun mask => (mask,id))

def c10847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10847 : Upper (D 8) (R 8) [66,36,136,288,160] 13 := by
  apply FastRouting.sound _ _ [66,36,136,288,160] 13 (by decide) (choices 1) [1,16,64] r10847 c10847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3187
  · exact u3188
  · exact u3189

def r10848 : Route 9 := (fun mask => (mask,id))

def c10848 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10848 : Upper (D 8) (R 8) [66,36,136,288,192] 13 := by
  apply FastRouting.sound _ _ [66,36,136,288,192] 13 (by decide) (choices 1) [1,16] r10848 c10848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3190
  · exact u3191

def b10849 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 261 25 56 224 224 224 480), lower := (rows 67 38 261 25 56 32 64 128 256), losses := [] }

theorem u10849 : Upper (D 8) (R 8) [66,36,257,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10850 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 261 25 88 160 224 160 416), lower := (rows 67 38 261 25 88 32 64 128 256), losses := [] }

theorem u10850 : Upper (D 8) (R 8) [66,36,257,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10851 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 261 25 112 168 232 168 424), lower := (rows 67 38 261 25 112 32 64 128 256), losses := [] }

theorem u10851 : Upper (D 8) (R 8) [66,36,257,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10851 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10852 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 261 25 152 224 224 224 480), lower := (rows 67 38 261 25 152 32 64 128 256), losses := [] }

theorem u10852 : Upper (D 8) (R 8) [66,36,257,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10853 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 261 25 176 232 232 232 488), lower := (rows 67 38 261 25 176 32 64 128 256), losses := [] }

theorem u10853 : Upper (D 8) (R 8) [66,36,257,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10854 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 261 25 208 168 232 168 424), lower := (rows 67 38 261 25 208 32 64 128 256), losses := [] }

theorem u10854 : Upper (D 8) (R 8) [66,36,257,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10855 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 261 41 56 240 208 208 464), lower := (rows 67 38 261 41 56 32 64 128 256), losses := [] }

theorem u10855 : Upper (D 8) (R 8) [66,36,257,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10856 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 261 41 88 176 240 176 432), lower := (rows 67 38 261 41 88 32 64 128 256), losses := [] }

theorem u10856 : Upper (D 8) (R 8) [66,36,257,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10856 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10857 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 261 41 112 184 216 152 408), lower := (rows 67 38 261 41 112 32 64 128 256), losses := [] }

theorem u10857 : Upper (D 8) (R 8) [66,36,257,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10858 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 261 41 152 240 240 240 496), lower := (rows 67 38 261 41 152 32 64 128 256), losses := [] }

theorem u10858 : Upper (D 8) (R 8) [66,36,257,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10858 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10859 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 261 41 176 248 216 216 472), lower := (rows 67 38 261 41 176 32 64 128 256), losses := [] }

theorem u10859 : Upper (D 8) (R 8) [66,36,257,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u10859
end Delivery.IrregularNine14.P08
