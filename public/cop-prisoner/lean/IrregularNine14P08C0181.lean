import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0053
import IrregularNine14P08C0054

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10860 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 261 41 208 184 248 184 440), lower := (rows 67 38 261 41 208 32 64 128 256), losses := [] }

theorem u10860 : Upper (D 8) (R 8) [66,36,257,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10860 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10861 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 261 56 56 225 193 193 449), lower := (rows 67 38 261 56 56 32 64 128 256), losses := [] }

theorem u10861 : Upper (D 8) (R 8) [66,36,257,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10861 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10862 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 261 56 81 168 232 168 424), lower := (rows 67 38 261 56 81 32 64 128 256), losses := [] }

theorem u10862 : Upper (D 8) (R 8) [66,36,257,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10863 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 261 56 88 161 225 161 417), lower := (rows 67 38 261 56 88 32 64 128 256), losses := [] }

theorem u10863 : Upper (D 8) (R 8) [66,36,257,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10863 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10864 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 261 56 112 169 201 137 393), lower := (rows 67 38 261 56 112 32 64 128 256), losses := [] }

theorem u10864 : Upper (D 8) (R 8) [66,36,257,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10865 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 261 56 145 232 232 232 488), lower := (rows 67 38 261 56 145 32 64 128 256), losses := [] }

theorem u10865 : Upper (D 8) (R 8) [66,36,257,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10865 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10866 : Route 9 := (fun mask => (mask,id))

def c10866 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10866 : Upper (D 8) (R 8) [66,36,257,48,136] 13 := by
  apply FastRouting.sound _ _ [66,36,257,48,136] 13 (by decide) (choices 1) [1,64,128] r10866 c10866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3192
  · exact u3193
  · exact u3194

def b10867 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 261 56 176 233 201 201 457), lower := (rows 67 38 261 56 176 32 64 128 256), losses := [] }

theorem u10867 : Upper (D 8) (R 8) [66,36,257,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10868 : Route 9 := (fun mask => (mask,id))

def c10868 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10868 : Upper (D 8) (R 8) [66,36,257,48,192] 13 := by
  apply FastRouting.sound _ _ [66,36,257,48,192] 13 (by decide) (choices 1) [1,8,128] r10868 c10868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3195
  · exact u3196
  · exact u3197

def b10869 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 261 73 152 176 240 176 432), lower := (rows 67 38 261 73 152 32 64 128 256), losses := [] }

theorem u10869 : Upper (D 8) (R 8) [66,36,257,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10869 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10870 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 261 73 176 184 248 184 440), lower := (rows 67 38 261 73 176 32 64 128 256), losses := [] }

theorem u10870 : Upper (D 8) (R 8) [66,36,257,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10871 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 261 88 145 168 232 168 424), lower := (rows 67 38 261 88 145 32 64 128 256), losses := [] }

theorem u10871 : Upper (D 8) (R 8) [66,36,257,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10872 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 261 88 152 161 225 161 417), lower := (rows 67 38 261 88 152 32 64 128 256), losses := [] }

theorem u10872 : Upper (D 8) (R 8) [66,36,257,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10873 : Route 9 := (fun mask => (mask,id))

def c10873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10873 : Upper (D 8) (R 8) [66,36,257,80,160] 13 := by
  apply FastRouting.sound _ _ [66,36,257,80,160] 13 (by decide) (choices 1) [1,8,128] r10873 c10873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3198
  · exact u3199
  · exact u3200

def b10874 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 261 104 145 184 248 184 440), lower := (rows 67 38 261 104 145 32 64 128 256), losses := [] }

theorem u10874 : Upper (D 8) (R 8) [66,36,257,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10875 : Route 9 := (fun mask => (mask,id))

def c10875 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10875 : Upper (D 8) (R 8) [66,36,257,96,136] 13 := by
  apply FastRouting.sound _ _ [66,36,257,96,136] 13 (by decide) (choices 1) [1,16,128] r10875 c10875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3201
  · exact u3202
  · exact u3203

def r10876 : Route 9 := (fun mask => (mask,id))

def c10876 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10876 : Upper (D 8) (R 8) [66,36,257,96,160] 13 := by
  apply FastRouting.sound _ _ [66,36,257,96,160] 13 (by decide) (choices 1) [1,8,16,128] r10876 c10876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3204
  · exact u3205
  · exact u3206
  · exact u3207

def b10877 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 261 137 152 112 112 240 368), lower := (rows 67 38 261 137 152 32 64 128 256), losses := [] }

theorem u10877 : Upper (D 8) (R 8) [66,36,257,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10877 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10878 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 261 137 176 120 120 248 376), lower := (rows 67 38 261 137 176 32 64 128 256), losses := [] }

theorem u10878 : Upper (D 8) (R 8) [66,36,257,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10878 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10879 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 261 137 208 56 120 184 312), lower := (rows 67 38 261 137 208 32 64 128 256), losses := [] }

theorem u10879 : Upper (D 8) (R 8) [66,36,257,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10879 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10880 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 261 152 152 97 97 225 353), lower := (rows 67 38 261 152 152 32 64 128 256), losses := [] }

theorem u10880 : Upper (D 8) (R 8) [66,36,257,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10881 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 261 152 176 105 105 233 361), lower := (rows 67 38 261 152 176 32 64 128 256), losses := [] }

theorem u10881 : Upper (D 8) (R 8) [66,36,257,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10882 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 261 152 208 41 105 169 297), lower := (rows 67 38 261 152 208 32 64 128 256), losses := [] }

theorem u10882 : Upper (D 8) (R 8) [66,36,257,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10882 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10883 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 261 168 176 121 89 217 345), lower := (rows 67 38 261 168 176 32 64 128 256), losses := [] }

theorem u10883 : Upper (D 8) (R 8) [66,36,257,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10883 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10884 : Route 9 := (fun mask => (mask,id))

def c10884 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10884 : Upper (D 8) (R 8) [66,36,257,160,192] 13 := by
  apply FastRouting.sound _ _ [66,36,257,160,192] 13 (by decide) (choices 1) [1,8,16] r10884 c10884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3208
  · exact u3209
  · exact u3210

def b10885 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 268 25 49 224 224 224 480), lower := (rows 67 38 268 25 49 32 64 128 256), losses := [] }

theorem u10885 : Upper (D 8) (R 8) [66,36,264,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10885 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10886 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 268 25 81 160 224 160 416), lower := (rows 67 38 268 25 81 32 64 128 256), losses := [] }

theorem u10886 : Upper (D 8) (R 8) [66,36,264,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10886 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10887 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 268 25 112 161 225 161 417), lower := (rows 67 38 268 25 112 32 64 128 256), losses := [] }

theorem u10887 : Upper (D 8) (R 8) [66,36,264,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10888 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 268 25 145 224 224 224 480), lower := (rows 67 38 268 25 145 32 64 128 256), losses := [] }

theorem u10888 : Upper (D 8) (R 8) [66,36,264,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10888 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10889 : Route 9 := (fun mask => (mask,id))

def c10889 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10889 : Upper (D 8) (R 8) [66,36,264,17,160] 13 := by
  apply FastRouting.sound _ _ [66,36,264,17,160] 13 (by decide) (choices 1) [1,64,128] r10889 c10889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3211
  · exact u3212
  · exact u3213

def b10890 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 268 25 208 161 225 161 417), lower := (rows 67 38 268 25 208 32 64 128 256), losses := [] }

theorem u10890 : Upper (D 8) (R 8) [66,36,264,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10890 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10891 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 268 41 49 240 208 208 464), lower := (rows 67 38 268 41 49 32 64 128 256), losses := [] }

theorem u10891 : Upper (D 8) (R 8) [66,36,264,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10892 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 268 41 81 176 240 176 432), lower := (rows 67 38 268 41 81 32 64 128 256), losses := [] }

theorem u10892 : Upper (D 8) (R 8) [66,36,264,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10892 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10893 : Route 9 := (fun mask => (mask,id))

def c10893 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10893 : Upper (D 8) (R 8) [66,36,264,33,96] 13 := by
  apply FastRouting.sound _ _ [66,36,264,33,96] 13 (by decide) (choices 1) [1,16,128] r10893 c10893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3214
  · exact u3215
  · exact u3216

def r10894 : Route 9 := (fun mask => (mask,id))

def c10894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u10894 : Upper (D 8) (R 8) [66,36,264,33,129] 13 := by
  apply FastRouting.sound _ _ [66,36,264,33,129] 13 (by decide) (choices 1) [16,64,128] r10894 c10894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3217
  · exact u3218
  · exact u3219

def r10895 : Route 9 := (fun mask => (mask,id))

def c10895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u10895 : Upper (D 8) (R 8) [66,36,264,33,160] 13 := by
  apply FastRouting.sound _ _ [66,36,264,33,160] 13 (by decide) (choices 1) [1,16,64,128] r10895 c10895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3220
  · exact u3221
  · exact u3222
  · exact u3223

def r10896 : Route 9 := (fun mask => (mask,id))

def c10896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10896 : Upper (D 8) (R 8) [66,36,264,33,192] 13 := by
  apply FastRouting.sound _ _ [66,36,264,33,192] 13 (by decide) (choices 1) [1,16,128] r10896 c10896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3224
  · exact u3225
  · exact u3226

def b10897 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 268 56 49 225 193 193 449), lower := (rows 67 38 268 56 49 32 64 128 256), losses := [] }

theorem u10897 : Upper (D 8) (R 8) [66,36,264,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10897 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10898 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 268 56 81 161 225 161 417), lower := (rows 67 38 268 56 81 32 64 128 256), losses := [] }

theorem u10898 : Upper (D 8) (R 8) [66,36,264,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10898 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10899 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 268 56 112 161 193 129 385), lower := (rows 67 38 268 56 112 32 64 128 256), losses := [] }

theorem u10899 : Upper (D 8) (R 8) [66,36,264,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10900 : Route 9 := (fun mask => (mask,id))

def c10900 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10900 : Upper (D 8) (R 8) [66,36,264,48,129] 13 := by
  apply FastRouting.sound _ _ [66,36,264,48,129] 13 (by decide) (choices 1) [1,64,128] r10900 c10900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3227
  · exact u3228
  · exact u3229

def b10901 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 268 56 176 225 193 193 449), lower := (rows 67 38 268 56 176 32 64 128 256), losses := [] }

theorem u10901 : Upper (D 8) (R 8) [66,36,264,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10901 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10902 : Route 9 := (fun mask => (mask,id))

def c10902 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10902 : Upper (D 8) (R 8) [66,36,264,48,192] 13 := by
  apply FastRouting.sound _ _ [66,36,264,48,192] 13 (by decide) (choices 1) [1,128] r10902 c10902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3230
  · exact u3231

def r10903 : Route 9 := (fun mask => (mask,id))

def c10903 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u10903 : Upper (D 8) (R 8) [66,36,264,129,33] 13 := by
  apply FastRouting.sound _ _ [66,36,264,129,33] 13 (by decide) (choices 1) [16,64,128] r10903 c10903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3232
  · exact u3233
  · exact u3234

def b10904 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 268 137 81 176 240 176 432), lower := (rows 67 38 268 137 81 32 64 128 256), losses := [] }

theorem u10904 : Upper (D 8) (R 8) [66,36,264,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10905 : Route 9 := (fun mask => (mask,id))

def c10905 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10905 : Upper (D 8) (R 8) [66,36,264,129,96] 13 := by
  apply FastRouting.sound _ _ [66,36,264,129,96] 13 (by decide) (choices 1) [1,16,128] r10905 c10905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3235
  · exact u3236
  · exact u3237

def b10906 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 38 268 137 145 112 112 240 368), lower := (rows 67 38 268 137 145 32 64 128 256), losses := [] }

theorem u10906 : Upper (D 8) (R 8) [66,36,264,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10907 : Route 9 := (fun mask => (mask,id))

def c10907 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10907 : Upper (D 8) (R 8) [66,36,264,129,160] 13 := by
  apply FastRouting.sound _ _ [66,36,264,129,160] 13 (by decide) (choices 1) [1,16,64] r10907 c10907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3238
  · exact u3239
  · exact u3240

def r10908 : Route 9 := (fun mask => (mask,id))

def c10908 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10908 : Upper (D 8) (R 8) [66,36,264,129,192] 13 := by
  apply FastRouting.sound _ _ [66,36,264,129,192] 13 (by decide) (choices 1) [1,16] r10908 c10908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3241
  · exact u3242

def r10909 : Route 9 := (fun mask => (mask,id))

def c10909 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10909 : Upper (D 8) (R 8) [66,36,264,144,33] 13 := by
  apply FastRouting.sound _ _ [66,36,264,144,33] 13 (by decide) (choices 1) [1,64,128] r10909 c10909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3243
  · exact u3244
  · exact u3245

def b10910 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 268 152 81 161 225 161 417), lower := (rows 67 38 268 152 81 32 64 128 256), losses := [] }

theorem u10910 : Upper (D 8) (R 8) [66,36,264,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10910 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10911 : Route 9 := (fun mask => (mask,id))

def c10911 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10911 : Upper (D 8) (R 8) [66,36,264,144,96] 13 := by
  apply FastRouting.sound _ _ [66,36,264,144,96] 13 (by decide) (choices 1) [1,128] r10911 c10911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3246
  · exact u3247

def b10912 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 152 145 97 97 225 353), lower := (rows 67 38 268 152 145 32 64 128 256), losses := [] }

theorem u10912 : Upper (D 8) (R 8) [66,36,264,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10912 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10913 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 152 176 97 97 225 353), lower := (rows 67 38 268 152 176 32 64 128 256), losses := [] }

theorem u10913 : Upper (D 8) (R 8) [66,36,264,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10913 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10914 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 152 208 33 97 161 289), lower := (rows 67 38 268 152 208 32 64 128 256), losses := [] }

theorem u10914 : Upper (D 8) (R 8) [66,36,264,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10914 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10915 : Route 9 := (fun mask => (mask,id))

def c10915 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u10915 : Upper (D 8) (R 8) [66,36,264,160,33] 13 := by
  apply FastRouting.sound _ _ [66,36,264,160,33] 13 (by decide) (choices 1) [1,16,64,128] r10915 c10915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3248
  · exact u3249
  · exact u3250
  · exact u3251

def b10916 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 268 168 81 177 241 177 433), lower := (rows 67 38 268 168 81 32 64 128 256), losses := [] }

theorem u10916 : Upper (D 8) (R 8) [66,36,264,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10916 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10917 : Route 9 := (fun mask => (mask,id))

def c10917 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10917 : Upper (D 8) (R 8) [66,36,264,160,96] 13 := by
  apply FastRouting.sound _ _ [66,36,264,160,96] 13 (by decide) (choices 1) [1,16,128] r10917 c10917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3252
  · exact u3253
  · exact u3254

def r10918 : Route 9 := (fun mask => (mask,id))

def c10918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10918 : Upper (D 8) (R 8) [66,36,264,160,129] 13 := by
  apply FastRouting.sound _ _ [66,36,264,160,129] 13 (by decide) (choices 1) [1,16,64] r10918 c10918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3255
  · exact u3256
  · exact u3257

def b10919 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 268 168 176 113 81 209 337), lower := (rows 67 38 268 168 176 32 64 128 256), losses := [] }

theorem u10919 : Upper (D 8) (R 8) [66,36,264,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u10919
end Delivery.IrregularNine14.P08
