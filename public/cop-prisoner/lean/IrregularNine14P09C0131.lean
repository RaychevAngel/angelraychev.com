import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0086
import IrregularNine14P09C0087
import IrregularNine14P09C0088
import IrregularNine14P09C0089

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7860 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 227, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 194 44 280 276 225 193 193 449), lower := (rows 35 194 44 280 276 32 64 128 256), losses := [] }

theorem u7860 : Upper (D 9) (R 9) [34,192,40,272,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7860 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7861 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 194 44 280 336 165 197 133 389), lower := (rows 35 194 44 280 336 32 64 128 256), losses := [] }

theorem u7861 : Upper (D 9) (R 9) [34,192,40,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7861 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7862 : Route 9 := (fun mask => (mask,id))

def c7862 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7862 : Upper (D 9) (R 9) [34,192,40,320,129] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,129] 13 (by decide) (choices 1) [1,4,16,256] r7862 c7862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5204
  · exact u5205
  · exact u5206
  · exact u5207

def r7863 : Route 9 := (fun mask => (mask,id))

def c7863 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7863 : Upper (D 9) (R 9) [34,192,40,320,132] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,132] 13 (by decide) (choices 1) [1,16,256] r7863 c7863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5208
  · exact u5209
  · exact u5210

def r7864 : Route 9 := (fun mask => (mask,id))

def c7864 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7864 : Upper (D 9) (R 9) [34,192,40,320,257] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,257] 13 (by decide) (choices 1) [1,4,16,128] r7864 c7864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5211
  · exact u5212
  · exact u5213
  · exact u5214

def r7865 : Route 9 := (fun mask => (mask,id))

def c7865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7865 : Upper (D 9) (R 9) [34,192,40,320,260] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,260] 13 (by decide) (choices 1) [1,16,128] r7865 c7865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5215
  · exact u5216
  · exact u5217

def r7866 : Route 9 := (fun mask => (mask,id))

def c7866 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7866 : Upper (D 9) (R 9) [34,192,40,320,384] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,384] 13 (by decide) (choices 1) [1,4,16] r7866 c7866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5218
  · exact u5219
  · exact u5220

def r7867 : Route 9 := (fun mask => (mask,id))

def c7867 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7867 : Upper (D 9) (R 9) [34,192,65,129,260] 13 := by
  apply FastRouting.sound _ _ [34,192,65,129,260] 13 (by decide) (choices 1) [8,16,256] r7867 c7867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5221
  · exact u5222
  · exact u5223

theorem m7868_8 : Upper (D 9) (R 9) [34,192,65,129,288,8] 13 :=
  permutation_upper _ _ _ [34,192,65,129,288,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5224

def r7868 : Route 9 := (fun mask => (mask,id))

def c7868 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7868 : Upper (D 9) (R 9) [34,192,65,129,288] 13 := by
  apply FastRouting.sound _ _ [34,192,65,129,288] 13 (by decide) (choices 1) [4,8,16,256] r7868 c7868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5224
  · exact m7868_8
  · exact u5225
  · exact u5226

def r7869 : Route 9 := (fun mask => (mask,id))

def c7869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7869 : Upper (D 9) (R 9) [34,192,65,132,257] 13 := by
  apply FastRouting.sound _ _ [34,192,65,132,257] 13 (by decide) (choices 1) [8,16,256] r7869 c7869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5227
  · exact u5228
  · exact u5229

def r7870 : Route 9 := (fun mask => (mask,id))

def c7870 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7870 : Upper (D 9) (R 9) [34,192,65,132,264] 13 := by
  apply FastRouting.sound _ _ [34,192,65,132,264] 13 (by decide) (choices 1) [1,16,256] r7870 c7870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5230
  · exact u5231
  · exact u5232

def r7871 : Route 9 := (fun mask => (mask,id))

def c7871 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7871 : Upper (D 9) (R 9) [34,192,65,132,288] 13 := by
  apply FastRouting.sound _ _ [34,192,65,132,288] 13 (by decide) (choices 1) [1,8,16,256] r7871 c7871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5233
  · exact u5234
  · exact u5235
  · exact u5236

def r7872 : Route 9 := (fun mask => (mask,id))

def c7872 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7872 : Upper (D 9) (R 9) [34,192,65,144,257] 13 := by
  apply FastRouting.sound _ _ [34,192,65,144,257] 13 (by decide) (choices 1) [4,8,256] r7872 c7872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5237
  · exact u5238
  · exact u5239

def r7873 : Route 9 := (fun mask => (mask,id))

def c7873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7873 : Upper (D 9) (R 9) [34,192,65,144,260] 13 := by
  apply FastRouting.sound _ _ [34,192,65,144,260] 13 (by decide) (choices 1) [1,8,256] r7873 c7873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5240
  · exact u5241
  · exact u5242

def r7874 : Route 9 := (fun mask => (mask,id))

def c7874 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7874 : Upper (D 9) (R 9) [34,192,65,144,264] 13 := by
  apply FastRouting.sound _ _ [34,192,65,144,264] 13 (by decide) (choices 1) [1,4,256] r7874 c7874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5243
  · exact u5244
  · exact u5245

def r7875 : Route 9 := (fun mask => (mask,id))

def c7875 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7875 : Upper (D 9) (R 9) [34,192,65,144,288] 13 := by
  apply FastRouting.sound _ _ [34,192,65,144,288] 13 (by decide) (choices 1) [1,4,8,256] r7875 c7875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5246
  · exact u5247
  · exact u5248
  · exact u5249

def r7876 : Route 9 := (fun mask => (mask,id))

def c7876 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7876 : Upper (D 9) (R 9) [34,192,65,160,257] 13 := by
  apply FastRouting.sound _ _ [34,192,65,160,257] 13 (by decide) (choices 1) [4,8,16,256] r7876 c7876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5250
  · exact u5251
  · exact u5252
  · exact u5253

def r7877 : Route 9 := (fun mask => (mask,id))

def c7877 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7877 : Upper (D 9) (R 9) [34,192,65,160,260] 13 := by
  apply FastRouting.sound _ _ [34,192,65,160,260] 13 (by decide) (choices 1) [1,8,16,256] r7877 c7877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5254
  · exact u5255
  · exact u5256
  · exact u5257

def r7878 : Route 9 := (fun mask => (mask,id))

def c7878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7878 : Upper (D 9) (R 9) [34,192,65,160,264] 13 := by
  apply FastRouting.sound _ _ [34,192,65,160,264] 13 (by decide) (choices 1) [1,4,16,256] r7878 c7878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5258
  · exact u5259
  · exact u5260
  · exact u5261

def r7879 : Route 9 := (fun mask => (mask,id))

def c7879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7879 : Upper (D 9) (R 9) [34,192,65,257,260] 13 := by
  apply FastRouting.sound _ _ [34,192,65,257,260] 13 (by decide) (choices 1) [8,16,128] r7879 c7879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5262
  · exact u5263
  · exact u5264

def b7880 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 16, targets := 225 },{ cop := 4, region := 231, targets := 256 }], pairs := [(0,8),(4,0),(4,5),(4,6),(4,7)], upper := (rows 35 194 69 265 280 180 244 180 436), lower := (rows 35 194 69 265 280 32 64 128 256), losses := [] }

theorem u7880 : Upper (D 9) (R 9) [34,192,65,257,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7880 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7881 : Route 9 := (fun mask => (mask,id))

def c7881 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7881 : Upper (D 9) (R 9) [34,192,65,257,288] 13 := by
  apply FastRouting.sound _ _ [34,192,65,257,288] 13 (by decide) (choices 1) [4,8,16,128] r7881 c7881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5265
  · exact u5266
  · exact u5267
  · exact u5268

def r7882 : Route 9 := (fun mask => (mask,id))

def c7882 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7882 : Upper (D 9) (R 9) [34,192,65,257,384] 13 := by
  apply FastRouting.sound _ _ [34,192,65,257,384] 13 (by decide) (choices 1) [4,8,16] r7882 c7882
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5269
  · exact u5270
  · exact u5271

def b7883 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 16, targets := 225 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,8),(4,0),(4,5),(4,6),(4,7)], upper := (rows 35 194 69 268 280 177 241 177 433), lower := (rows 35 194 69 268 280 32 64 128 256), losses := [] }

theorem u7883 : Upper (D 9) (R 9) [34,192,65,260,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7883 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7884 : Route 9 := (fun mask => (mask,id))

def c7884 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7884 : Upper (D 9) (R 9) [34,192,65,260,288] 13 := by
  apply FastRouting.sound _ _ [34,192,65,260,288] 13 (by decide) (choices 1) [1,8,16,128] r7884 c7884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5272
  · exact u5273
  · exact u5274
  · exact u5275

def r7885 : Route 9 := (fun mask => (mask,id))

def c7885 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7885 : Upper (D 9) (R 9) [34,192,65,260,384] 13 := by
  apply FastRouting.sound _ _ [34,192,65,260,384] 13 (by decide) (choices 1) [1,8,16] r7885 c7885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5276
  · exact u5277
  · exact u5278

def b7886 : PairBound 9 := { available := 165, camps := [{ cop := 8, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7),(4,0)], upper := (rows 35 194 69 280 280 165 229 165 421), lower := (rows 35 194 69 280 280 32 64 128 256), losses := [] }

theorem u7886 : Upper (D 9) (R 9) [34,192,65,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7886 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7887 : PairBound 9 := { available := 141, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 194 69 280 304 173 205 141 397), lower := (rows 35 194 69 280 304 32 64 128 256), losses := [] }

theorem u7887 : Upper (D 9) (R 9) [34,192,65,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7887 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7888 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 194 69 280 400 45 109 173 301), lower := (rows 35 194 69 280 400 32 64 128 256), losses := [] }

theorem u7888 : Upper (D 9) (R 9) [34,192,65,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7888 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7889 : Route 9 := (fun mask => (mask,id))

def c7889 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7889 : Upper (D 9) (R 9) [34,192,65,288,384] 13 := by
  apply FastRouting.sound _ _ [34,192,65,288,384] 13 (by decide) (choices 1) [1,4,8,16] r7889 c7889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5279
  · exact u5280
  · exact u5281
  · exact u5282

def b7890 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 12, targets := 289 }], pairs := [(2,0),(2,5),(2,8),(3,0),(3,5)], upper := (rows 35 194 76 140 273 305 369 433 305), lower := (rows 35 194 76 140 273 32 64 128 256), losses := [] }

theorem u7890 : Upper (D 9) (R 9) [34,192,72,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7890 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7891 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 12, targets := 289 }], pairs := [(2,0),(2,5),(2,8),(3,0),(3,5)], upper := (rows 35 194 76 140 304 305 337 401 273), lower := (rows 35 194 76 140 304 32 64 128 256), losses := [] }

theorem u7891 : Upper (D 9) (R 9) [34,192,72,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7891 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7892 : Route 9 := (fun mask => (mask,id))

def c7892 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7892 : Upper (D 9) (R 9) [34,192,72,144,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,257] 13 (by decide) (choices 1) [1,4,256] r7892 c7892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5283
  · exact u5284
  · exact u5285

def r7893 : Route 9 := (fun mask => (mask,id))

def c7893 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7893 : Upper (D 9) (R 9) [34,192,72,144,260] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,260] 13 (by decide) (choices 1) [1,256] r7893 c7893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5286
  · exact u5287

def r7894 : Route 9 := (fun mask => (mask,id))

def c7894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7894 : Upper (D 9) (R 9) [34,192,72,144,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,288] 13 (by decide) (choices 1) [1,4,256] r7894 c7894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5288
  · exact u5289
  · exact u5290

def r7895 : Route 9 := (fun mask => (mask,id))

def c7895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7895 : Upper (D 9) (R 9) [34,192,72,160,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,257] 13 (by decide) (choices 1) [1,4,16,256] r7895 c7895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5291
  · exact u5292
  · exact u5293
  · exact u5294

def r7896 : Route 9 := (fun mask => (mask,id))

def c7896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7896 : Upper (D 9) (R 9) [34,192,72,160,260] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,260] 13 (by decide) (choices 1) [1,16,256] r7896 c7896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5295
  · exact u5296
  · exact u5297

def r7897 : Route 9 := (fun mask => (mask,id))

def c7897 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7897 : Upper (D 9) (R 9) [34,192,72,257,160] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,160] 13 (by decide) (choices 1) [1,4,16,256] r7897 c7897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5298
  · exact u5299
  · exact u5300
  · exact u5301

def b7898 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 8, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6),(4,7)], upper := (rows 35 194 76 265 273 180 244 180 436), lower := (rows 35 194 76 265 273 32 64 128 256), losses := [] }

theorem u7898 : Upper (D 9) (R 9) [34,192,72,257,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7898 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7899 : Route 9 := (fun mask => (mask,id))

def c7899 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7899 : Upper (D 9) (R 9) [34,192,72,257,260] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,260] 13 (by decide) (choices 1) [1,16,128] r7899 c7899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5302
  · exact u5303
  · exact u5304

def r7900 : Route 9 := (fun mask => (mask,id))

def c7900 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7900 : Upper (D 9) (R 9) [34,192,72,257,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,288] 13 (by decide) (choices 1) [1,4,16,128] r7900 c7900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5305
  · exact u5306
  · exact u5307
  · exact u5308

def r7901 : Route 9 := (fun mask => (mask,id))

def c7901 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7901 : Upper (D 9) (R 9) [34,192,72,257,384] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,384] 13 (by decide) (choices 1) [1,4,16] r7901 c7901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5309
  · exact u5310
  · exact u5311

def r7902 : Route 9 := (fun mask => (mask,id))

def c7902 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7902 : Upper (D 9) (R 9) [34,192,72,260,160] 13 := by
  apply FastRouting.sound _ _ [34,192,72,260,160] 13 (by decide) (choices 1) [1,16,256] r7902 c7902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5312
  · exact u5313
  · exact u5314

def r7903 : Route 9 := (fun mask => (mask,id))

def c7903 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7903 : Upper (D 9) (R 9) [34,192,72,260,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,260,257] 13 (by decide) (choices 1) [1,16,128] r7903 c7903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5315
  · exact u5316
  · exact u5317

def r7904 : Route 9 := (fun mask => (mask,id))

def c7904 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7904 : Upper (D 9) (R 9) [34,192,72,260,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,260,288] 13 (by decide) (choices 1) [1,16,128] r7904 c7904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5318
  · exact u5319
  · exact u5320

def r7905 : Route 9 := (fun mask => (mask,id))

def c7905 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7905 : Upper (D 9) (R 9) [34,192,72,260,384] 13 := by
  apply FastRouting.sound _ _ [34,192,72,260,384] 13 (by decide) (choices 1) [1,16] r7905 c7905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5321
  · exact u5322

def r7906 : Route 9 := (fun mask => (mask,id))

def c7906 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7906 : Upper (D 9) (R 9) [34,192,72,272,160] 13 := by
  apply FastRouting.sound _ _ [34,192,72,272,160] 13 (by decide) (choices 1) [1,4,256] r7906 c7906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5323
  · exact u5324
  · exact u5325

def b7907 : PairBound 9 := { available := 165, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 194 76 280 273 165 229 165 421), lower := (rows 35 194 76 280 273 32 64 128 256), losses := [] }

theorem u7907 : Upper (D 9) (R 9) [34,192,72,272,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7907 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7908 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 227, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 194 76 280 276 161 225 161 417), lower := (rows 35 194 76 280 276 32 64 128 256), losses := [] }

theorem u7908 : Upper (D 9) (R 9) [34,192,72,272,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7908 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7909 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 194 76 280 304 165 197 133 389), lower := (rows 35 194 76 280 304 32 64 128 256), losses := [] }

theorem u7909 : Upper (D 9) (R 9) [34,192,72,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7909 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7910 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 194 76 280 400 37 101 165 293), lower := (rows 35 194 76 280 400 32 64 128 256), losses := [] }

theorem u7910 : Upper (D 9) (R 9) [34,192,72,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7910 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7911 : Route 9 := (fun mask => (mask,id))

def c7911 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7911 : Upper (D 9) (R 9) [34,192,72,288,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288,257] 13 (by decide) (choices 1) [1,4,16,128] r7911 c7911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5326
  · exact u5327
  · exact u5328
  · exact u5329

def r7912 : Route 9 := (fun mask => (mask,id))

def c7912 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7912 : Upper (D 9) (R 9) [34,192,72,288,260] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288,260] 13 (by decide) (choices 1) [1,16,128] r7912 c7912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5330
  · exact u5331
  · exact u5332

def r7913 : Route 9 := (fun mask => (mask,id))

def c7913 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7913 : Upper (D 9) (R 9) [34,192,72,288,384] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288,384] 13 (by decide) (choices 1) [1,4,16] r7913 c7913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5333
  · exact u5334
  · exact u5335

def r7914 : Route 9 := (fun mask => (mask,id))

def c7914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7914 : Upper (D 9) (R 9) [34,192,72,384,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,384,257] 13 (by decide) (choices 1) [1,4,16] r7914 c7914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5336
  · exact u5337
  · exact u5338

def r7915 : Route 9 := (fun mask => (mask,id))

def c7915 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7915 : Upper (D 9) (R 9) [34,192,72,384,260] 13 := by
  apply FastRouting.sound _ _ [34,192,72,384,260] 13 (by decide) (choices 1) [1,16] r7915 c7915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5339
  · exact u5340

def r7916 : Route 9 := (fun mask => (mask,id))

def c7916 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7916 : Upper (D 9) (R 9) [34,192,72,384,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,384,288] 13 (by decide) (choices 1) [1,4,16] r7916 c7916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5341
  · exact u5342
  · exact u5343

def b7917 : PairBound 9 := { available := 156, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 8, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6),(4,7)], upper := (rows 35 194 100 265 273 188 220 156 412), lower := (rows 35 194 100 265 273 32 64 128 256), losses := [] }

theorem u7917 : Upper (D 9) (R 9) [34,192,96,257,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7917 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r7918 : Route 9 := (fun mask => (mask,id))

def c7918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7918 : Upper (D 9) (R 9) [34,192,96,257,260] 13 := by
  apply FastRouting.sound _ _ [34,192,96,257,260] 13 (by decide) (choices 1) [1,8,16,128] r7918 c7918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5344
  · exact u5345
  · exact u5346
  · exact u5347

def b7919 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 16, targets := 225 },{ cop := 4, region := 231, targets := 256 }], pairs := [(0,8),(4,0),(4,5),(4,6),(4,7)], upper := (rows 35 194 100 265 280 181 213 149 405), lower := (rows 35 194 100 265 280 32 64 128 256), losses := [] }

theorem u7919 : Upper (D 9) (R 9) [34,192,96,257,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7919 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u7919
end Delivery.IrregularNine14.P09
