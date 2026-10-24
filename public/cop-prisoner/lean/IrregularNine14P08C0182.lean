import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0054

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r10920 : Route 9 := (fun mask => (mask,id))

def c10920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10920 : Upper (D 8) (R 8) [66,36,264,160,192] 13 := by
  apply FastRouting.sound _ _ [66,36,264,160,192] 13 (by decide) (choices 1) [1,16] r10920 c10920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3258
  · exact u3259

def b10921 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 388 25 25 224 224 224 480), lower := (rows 67 38 388 25 25 32 64 128 256), losses := [] }

theorem u10921 : Upper (D 8) (R 8) [66,36,384,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10921 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10922 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 388 25 49 232 232 232 488), lower := (rows 67 38 388 25 49 32 64 128 256), losses := [] }

theorem u10922 : Upper (D 8) (R 8) [66,36,384,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10922 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10923 : Route 9 := (fun mask => (mask,id))

def c10923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10923 : Upper (D 8) (R 8) [66,36,384,17,40] 13 := by
  apply FastRouting.sound _ _ [66,36,384,17,40] 13 (by decide) (choices 1) [1,64,128] r10923 c10923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3260
  · exact u3261
  · exact u3262

def b10924 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 388 25 81 168 232 168 424), lower := (rows 67 38 388 25 81 32 64 128 256), losses := [] }

theorem u10924 : Upper (D 8) (R 8) [66,36,384,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10924 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10925 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 388 25 88 161 225 161 417), lower := (rows 67 38 388 25 88 32 64 128 256), losses := [] }

theorem u10925 : Upper (D 8) (R 8) [66,36,384,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10925 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10926 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 388 25 112 169 233 169 425), lower := (rows 67 38 388 25 112 32 64 128 256), losses := [] }

theorem u10926 : Upper (D 8) (R 8) [66,36,384,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10926 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10927 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 388 25 145 104 104 232 360), lower := (rows 67 38 388 25 145 32 64 128 256), losses := [] }

theorem u10927 : Upper (D 8) (R 8) [66,36,384,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10927 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10928 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 388 25 152 97 97 225 353), lower := (rows 67 38 388 25 152 32 64 128 256), losses := [] }

theorem u10928 : Upper (D 8) (R 8) [66,36,384,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10928 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10929 : Route 9 := (fun mask => (mask,id))

def c10929 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10929 : Upper (D 8) (R 8) [66,36,384,17,160] 13 := by
  apply FastRouting.sound _ _ [66,36,384,17,160] 13 (by decide) (choices 1) [1,8,64] r10929 c10929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3263
  · exact u3264
  · exact u3265

def b10930 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 388 25 208 41 105 169 297), lower := (rows 67 38 388 25 208 32 64 128 256), losses := [] }

theorem u10930 : Upper (D 8) (R 8) [66,36,384,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10930 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10931 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 67 38 388 41 49 248 216 216 472), lower := (rows 67 38 388 41 49 32 64 128 256), losses := [] }

theorem u10931 : Upper (D 8) (R 8) [66,36,384,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10931 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10932 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 388 41 56 241 209 209 465), lower := (rows 67 38 388 41 56 32 64 128 256), losses := [] }

theorem u10932 : Upper (D 8) (R 8) [66,36,384,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10932 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10933 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 388 41 81 184 248 184 440), lower := (rows 67 38 388 41 81 32 64 128 256), losses := [] }

theorem u10933 : Upper (D 8) (R 8) [66,36,384,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10933 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10934 : Route 9 := (fun mask => (mask,id))

def c10934 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10934 : Upper (D 8) (R 8) [66,36,384,33,72] 13 := by
  apply FastRouting.sound _ _ [66,36,384,33,72] 13 (by decide) (choices 1) [1,16,128] r10934 c10934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3266
  · exact u3267
  · exact u3268

def r10935 : Route 9 := (fun mask => (mask,id))

def c10935 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10935 : Upper (D 8) (R 8) [66,36,384,33,96] 13 := by
  apply FastRouting.sound _ _ [66,36,384,33,96] 13 (by decide) (choices 1) [1,8,16,128] r10935 c10935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3269
  · exact u3270
  · exact u3271
  · exact u3272

def b10936 : PairBound 9 := { available := 120, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 67 38 388 41 145 120 120 248 376), lower := (rows 67 38 388 41 145 32 64 128 256), losses := [] }

theorem u10936 : Upper (D 8) (R 8) [66,36,384,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10936 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10937 : Route 9 := (fun mask => (mask,id))

def c10937 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10937 : Upper (D 8) (R 8) [66,36,384,33,136] 13 := by
  apply FastRouting.sound _ _ [66,36,384,33,136] 13 (by decide) (choices 1) [1,16,64] r10937 c10937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3273
  · exact u3274
  · exact u3275

def r10938 : Route 9 := (fun mask => (mask,id))

def c10938 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10938 : Upper (D 8) (R 8) [66,36,384,33,160] 13 := by
  apply FastRouting.sound _ _ [66,36,384,33,160] 13 (by decide) (choices 1) [1,8,16,64] r10938 c10938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3276
  · exact u3277
  · exact u3278
  · exact u3279

def r10939 : Route 9 := (fun mask => (mask,id))

def c10939 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10939 : Upper (D 8) (R 8) [66,36,384,33,192] 13 := by
  apply FastRouting.sound _ _ [66,36,384,33,192] 13 (by decide) (choices 1) [1,8,16] r10939 c10939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3280
  · exact u3281
  · exact u3282

def b10940 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 388 56 56 225 193 193 449), lower := (rows 67 38 388 56 56 32 64 128 256), losses := [] }

theorem u10940 : Upper (D 8) (R 8) [66,36,384,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10940 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10941 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 388 56 81 169 233 169 425), lower := (rows 67 38 388 56 81 32 64 128 256), losses := [] }

theorem u10941 : Upper (D 8) (R 8) [66,36,384,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10941 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10942 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 388 56 88 161 225 161 417), lower := (rows 67 38 388 56 88 32 64 128 256), losses := [] }

theorem u10942 : Upper (D 8) (R 8) [66,36,384,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10942 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10943 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 388 56 112 169 201 137 393), lower := (rows 67 38 388 56 112 32 64 128 256), losses := [] }

theorem u10943 : Upper (D 8) (R 8) [66,36,384,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10944 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 67 38 388 56 145 105 105 233 361), lower := (rows 67 38 388 56 145 32 64 128 256), losses := [] }

theorem u10944 : Upper (D 8) (R 8) [66,36,384,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10944 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10945 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 388 56 152 97 97 225 353), lower := (rows 67 38 388 56 152 32 64 128 256), losses := [] }

theorem u10945 : Upper (D 8) (R 8) [66,36,384,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10946 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 388 56 176 105 73 201 329), lower := (rows 67 38 388 56 176 32 64 128 256), losses := [] }

theorem u10946 : Upper (D 8) (R 8) [66,36,384,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10947 : Route 9 := (fun mask => (mask,id))

def c10947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10947 : Upper (D 8) (R 8) [66,36,384,48,192] 13 := by
  apply FastRouting.sound _ _ [66,36,384,48,192] 13 (by decide) (choices 1) [1,8] r10947 c10947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3283
  · exact u3284

def b10948 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 388 73 152 49 113 177 305), lower := (rows 67 38 388 73 152 32 64 128 256), losses := [] }

theorem u10948 : Upper (D 8) (R 8) [66,36,384,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10949 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 388 73 176 57 121 185 313), lower := (rows 67 38 388 73 176 32 64 128 256), losses := [] }

theorem u10949 : Upper (D 8) (R 8) [66,36,384,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10950 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 67 38 388 88 145 41 105 169 297), lower := (rows 67 38 388 88 145 32 64 128 256), losses := [] }

theorem u10950 : Upper (D 8) (R 8) [66,36,384,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10950 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10951 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 38 388 88 152 33 97 161 289), lower := (rows 67 38 388 88 152 32 64 128 256), losses := [] }

theorem u10951 : Upper (D 8) (R 8) [66,36,384,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10952 : Route 9 := (fun mask => (mask,id))

def c10952 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10952 : Upper (D 8) (R 8) [66,36,384,80,160] 13 := by
  apply FastRouting.sound _ _ [66,36,384,80,160] 13 (by decide) (choices 1) [1,8] r10952 c10952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3285
  · exact u3286

def b10953 : PairBound 9 := { available := 57, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 67 38 388 104 145 57 121 185 313), lower := (rows 67 38 388 104 145 32 64 128 256), losses := [] }

theorem u10953 : Upper (D 8) (R 8) [66,36,384,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10954 : Route 9 := (fun mask => (mask,id))

def c10954 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10954 : Upper (D 8) (R 8) [66,36,384,96,136] 13 := by
  apply FastRouting.sound _ _ [66,36,384,96,136] 13 (by decide) (choices 1) [1,16] r10954 c10954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3287
  · exact u3288

def r10955 : Route 9 := (fun mask => (mask,id))

def c10955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10955 : Upper (D 8) (R 8) [66,36,384,96,160] 13 := by
  apply FastRouting.sound _ _ [66,36,384,96,160] 13 (by decide) (choices 1) [1,8,16] r10955 c10955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3289
  · exact u3290
  · exact u3291

def b10956 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 28 112 416 480 416 416), lower := (rows 67 131 13 28 112 32 64 128 256), losses := [] }

theorem u10956 : Upper (D 8) (R 8) [66,129,9,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10957 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 28 176 352 352 480 352), lower := (rows 67 131 13 28 176 32 64 128 256), losses := [] }

theorem u10957 : Upper (D 8) (R 8) [66,129,9,20,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10958 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 28 304 224 224 224 480), lower := (rows 67 131 13 28 304 32 64 128 256), losses := [] }

theorem u10958 : Upper (D 8) (R 8) [66,129,9,20,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10959 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 28 336 160 224 160 416), lower := (rows 67 131 13 28 336 32 64 128 256), losses := [] }

theorem u10959 : Upper (D 8) (R 8) [66,129,9,20,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10960 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 28 400 96 96 224 352), lower := (rows 67 131 13 28 400 32 64 128 256), losses := [] }

theorem u10960 : Upper (D 8) (R 8) [66,129,9,20,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10961 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 44 112 432 496 432 432), lower := (rows 67 131 13 44 112 32 64 128 256), losses := [] }

theorem u10961 : Upper (D 8) (R 8) [66,129,9,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10961 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10962 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 44 176 368 368 496 368), lower := (rows 67 131 13 44 176 32 64 128 256), losses := [] }

theorem u10962 : Upper (D 8) (R 8) [66,129,9,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10963 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 44 304 240 240 240 496), lower := (rows 67 131 13 44 304 32 64 128 256), losses := [] }

theorem u10963 : Upper (D 8) (R 8) [66,129,9,36,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10964 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 44 336 176 240 176 432), lower := (rows 67 131 13 44 336 32 64 128 256), losses := [] }

theorem u10964 : Upper (D 8) (R 8) [66,129,9,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10964 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10965 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 44 400 112 112 240 368), lower := (rows 67 131 13 44 400 32 64 128 256), losses := [] }

theorem u10965 : Upper (D 8) (R 8) [66,129,9,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10966 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 56 84 416 480 416 416), lower := (rows 67 131 13 56 84 32 64 128 256), losses := [] }

theorem u10966 : Upper (D 8) (R 8) [66,129,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10967 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 56 148 352 352 480 352), lower := (rows 67 131 13 56 148 32 64 128 256), losses := [] }

theorem u10967 : Upper (D 8) (R 8) [66,129,9,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10968 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 56 276 224 224 224 480), lower := (rows 67 131 13 56 276 32 64 128 256), losses := [] }

theorem u10968 : Upper (D 8) (R 8) [66,129,9,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10969 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 56 336 164 228 164 420), lower := (rows 67 131 13 56 336 32 64 128 256), losses := [] }

theorem u10969 : Upper (D 8) (R 8) [66,129,9,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10970 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 56 400 100 100 228 356), lower := (rows 67 131 13 56 400 32 64 128 256), losses := [] }

theorem u10970 : Upper (D 8) (R 8) [66,129,9,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10970 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10971 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 131 13 76 176 304 368 432 304), lower := (rows 67 131 13 76 176 32 64 128 256), losses := [] }

theorem u10971 : Upper (D 8) (R 8) [66,129,9,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10972 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 131 13 76 304 176 240 176 432), lower := (rows 67 131 13 76 304 32 64 128 256), losses := [] }

theorem u10972 : Upper (D 8) (R 8) [66,129,9,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10972 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10973 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 131 13 76 400 48 112 176 304), lower := (rows 67 131 13 76 400 32 64 128 256), losses := [] }

theorem u10973 : Upper (D 8) (R 8) [66,129,9,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10974 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 88 52 416 480 416 416), lower := (rows 67 131 13 88 52 32 64 128 256), losses := [] }

theorem u10974 : Upper (D 8) (R 8) [66,129,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10975 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 88 148 288 352 416 288), lower := (rows 67 131 13 88 148 32 64 128 256), losses := [] }

theorem u10975 : Upper (D 8) (R 8) [66,129,9,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10975 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10976 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 88 176 292 356 420 292), lower := (rows 67 131 13 88 176 32 64 128 256), losses := [] }

theorem u10976 : Upper (D 8) (R 8) [66,129,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10976 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10977 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 88 276 160 224 160 416), lower := (rows 67 131 13 88 276 32 64 128 256), losses := [] }

theorem u10977 : Upper (D 8) (R 8) [66,129,9,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10978 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 88 304 164 228 164 420), lower := (rows 67 131 13 88 304 32 64 128 256), losses := [] }

theorem u10978 : Upper (D 8) (R 8) [66,129,9,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10978 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10979 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 131 13 88 400 36 100 164 292), lower := (rows 67 131 13 88 400 32 64 128 256), losses := [] }

theorem u10979 : Upper (D 8) (R 8) [66,129,9,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u10979
end Delivery.IrregularNine14.P08
