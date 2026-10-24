import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0169
import IrregularNine14P08C0170
import IrregularNine14P08C0171

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19920 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 176, targets := 1 }], pairs := [(4,0)], upper := (rows 67 14 37 265 240 240 240 240 496), lower := (rows 67 14 37 265 16 32 64 128 256), losses := [] }

theorem u19920 : Upper (D 8) (R 8) [66,12,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19920 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19921 : Route 9 := (fun mask => (mask,id))

def c19921 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19921 : Upper (D 8) (R 8) [66,12,33,272] 13 := by
  apply FastRouting.sound _ _ [66,12,33,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19921 c19921
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10195
  · exact u10196
  · exact u10197
  · exact u10198
  · exact u10199
  · exact u10200

def r19922 : Route 9 := (fun mask => (mask,id))

def c19922 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19922 : Upper (D 8) (R 8) [66,12,33,288] 13 := by
  apply FastRouting.sound _ _ [66,12,33,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19922 c19922
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10201
  · exact u10202
  · exact u10203
  · exact u10204
  · exact u10205
  · exact u10206

def b19923 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 37 328 177 177 241 177 433), lower := (rows 67 14 37 328 16 32 64 128 256), losses := [] }

theorem u19923 : Upper (D 8) (R 8) [66,12,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19923 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19924 : Route 9 := (fun mask => (mask,id))

def c19924 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19924 : Upper (D 8) (R 8) [66,12,33,384] 13 := by
  apply FastRouting.sound _ _ [66,12,33,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19924 c19924
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10207
  · exact u10208
  · exact u10209
  · exact u10210
  · exact u10211
  · exact u10212

def b19925 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 52 73 433 417 481 417 417), lower := (rows 67 14 52 73 16 32 64 128 256), losses := [] }

theorem u19925 : Upper (D 8) (R 8) [66,12,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19925 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19926 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 52 104 433 417 481 417 417), lower := (rows 67 14 52 104 16 32 64 128 256), losses := [] }

theorem u19926 : Upper (D 8) (R 8) [66,12,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19926 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19927 : Route 9 := (fun mask => (mask,id))

def c19927 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19927 : Upper (D 8) (R 8) [66,12,48,129] 13 := by
  apply FastRouting.sound _ _ [66,12,48,129] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19927 c19927
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10213
  · exact u10214
  · exact u10215
  · exact u10216
  · exact u10217
  · exact u10218
  · exact u10219
  · exact u10220
  · exact u10221
  · exact u10222

def r19928 : Route 9 := (fun mask => (mask,id))

def c19928 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19928 : Upper (D 8) (R 8) [66,12,48,160] 13 := by
  apply FastRouting.sound _ _ [66,12,48,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19928 c19928
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10223
  · exact u10224
  · exact u10225
  · exact u10226
  · exact u10227
  · exact u10228
  · exact u10229
  · exact u10230
  · exact u10231
  · exact u10232

def b19929 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 52 200 433 417 481 417 417), lower := (rows 67 14 52 200 16 32 64 128 256), losses := [] }

theorem u19929 : Upper (D 8) (R 8) [66,12,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19929 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19930 : Route 9 := (fun mask => (mask,id))

def c19930 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19930 : Upper (D 8) (R 8) [66,12,48,257] 13 := by
  apply FastRouting.sound _ _ [66,12,48,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19930 c19930
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10233
  · exact u10234
  · exact u10235
  · exact u10236
  · exact u10237
  · exact u10238

def r19931 : Route 9 := (fun mask => (mask,id))

def c19931 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19931 : Upper (D 8) (R 8) [66,12,48,288] 13 := by
  apply FastRouting.sound _ _ [66,12,48,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19931 c19931
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10239
  · exact u10240
  · exact u10241
  · exact u10242
  · exact u10243
  · exact u10244

def b19932 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 52 328 177 161 225 161 417), lower := (rows 67 14 52 328 16 32 64 128 256), losses := [] }

theorem u19932 : Upper (D 8) (R 8) [66,12,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19932 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19933 : Route 9 := (fun mask => (mask,id))

def c19933 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19933 : Upper (D 8) (R 8) [66,12,48,384] 13 := by
  apply FastRouting.sound _ _ [66,12,48,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19933 c19933
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10245
  · exact u10246
  · exact u10247
  · exact u10248
  · exact u10249
  · exact u10250

def b19934 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 69 137 432 432 496 432 432), lower := (rows 67 14 69 137 16 32 64 128 256), losses := [] }

theorem u19934 : Upper (D 8) (R 8) [66,12,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19934 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19935 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 69 152 433 417 481 417 417), lower := (rows 67 14 69 152 16 32 64 128 256), losses := [] }

theorem u19935 : Upper (D 8) (R 8) [66,12,65,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19935 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19936 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 69 168 433 433 497 433 433), lower := (rows 67 14 69 168 16 32 64 128 256), losses := [] }

theorem u19936 : Upper (D 8) (R 8) [66,12,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19936 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19937 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 69 265 176 176 240 176 432), lower := (rows 67 14 69 265 16 32 64 128 256), losses := [] }

theorem u19937 : Upper (D 8) (R 8) [66,12,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19938 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 69 280 177 161 225 161 417), lower := (rows 67 14 69 280 16 32 64 128 256), losses := [] }

theorem u19938 : Upper (D 8) (R 8) [66,12,65,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19938 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19939 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 69 296 177 177 241 177 433), lower := (rows 67 14 69 296 16 32 64 128 256), losses := [] }

theorem u19939 : Upper (D 8) (R 8) [66,12,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19939 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19940 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 69 392 177 177 241 177 433), lower := (rows 67 14 69 392 16 32 64 128 256), losses := [] }

theorem u19940 : Upper (D 8) (R 8) [66,12,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19940 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19941 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 84 137 433 417 481 417 417), lower := (rows 67 14 84 137 16 32 64 128 256), losses := [] }

theorem u19941 : Upper (D 8) (R 8) [66,12,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19941 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19942 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 84 168 433 417 481 417 417), lower := (rows 67 14 84 168 16 32 64 128 256), losses := [] }

theorem u19942 : Upper (D 8) (R 8) [66,12,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19942 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19943 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 84 265 177 161 225 161 417), lower := (rows 67 14 84 265 16 32 64 128 256), losses := [] }

theorem u19943 : Upper (D 8) (R 8) [66,12,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19944 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 84 296 177 161 225 161 417), lower := (rows 67 14 84 296 16 32 64 128 256), losses := [] }

theorem u19944 : Upper (D 8) (R 8) [66,12,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19944 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19945 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 84 392 177 161 225 161 417), lower := (rows 67 14 84 392 16 32 64 128 256), losses := [] }

theorem u19945 : Upper (D 8) (R 8) [66,12,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19946 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 100 137 433 433 497 433 433), lower := (rows 67 14 100 137 16 32 64 128 256), losses := [] }

theorem u19946 : Upper (D 8) (R 8) [66,12,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19947 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 100 152 433 417 481 417 417), lower := (rows 67 14 100 152 16 32 64 128 256), losses := [] }

theorem u19947 : Upper (D 8) (R 8) [66,12,96,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19947 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19948 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 100 168 433 433 497 433 433), lower := (rows 67 14 100 168 16 32 64 128 256), losses := [] }

theorem u19948 : Upper (D 8) (R 8) [66,12,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19949 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 100 265 177 177 241 177 433), lower := (rows 67 14 100 265 16 32 64 128 256), losses := [] }

theorem u19949 : Upper (D 8) (R 8) [66,12,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19950 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 100 280 177 161 225 161 417), lower := (rows 67 14 100 280 16 32 64 128 256), losses := [] }

theorem u19950 : Upper (D 8) (R 8) [66,12,96,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19950 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19951 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 100 296 177 177 241 177 433), lower := (rows 67 14 100 296 16 32 64 128 256), losses := [] }

theorem u19951 : Upper (D 8) (R 8) [66,12,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19952 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 100 392 177 177 241 177 433), lower := (rows 67 14 100 392 16 32 64 128 256), losses := [] }

theorem u19952 : Upper (D 8) (R 8) [66,12,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19953 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 67 14 133 137 368 368 368 496 368), lower := (rows 67 14 133 137 16 32 64 128 256), losses := [] }

theorem u19953 : Upper (D 8) (R 8) [66,12,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19954 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 133 152 369 353 353 481 353), lower := (rows 67 14 133 152 16 32 64 128 256), losses := [] }

theorem u19954 : Upper (D 8) (R 8) [66,12,129,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19954 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19955 : PairBound 9 := { available := 369, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 133 168 369 369 369 497 369), lower := (rows 67 14 133 168 16 32 64 128 256), losses := [] }

theorem u19955 : Upper (D 8) (R 8) [66,12,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19955 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19956 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 7, targets := 32 }], pairs := [(0,5)], upper := (rows 67 14 133 200 305 305 369 433 305), lower := (rows 67 14 133 200 16 32 64 128 256), losses := [] }

theorem u19956 : Upper (D 8) (R 8) [66,12,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19957 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 176, targets := 1 }], pairs := [(4,0)], upper := (rows 67 14 133 265 240 240 240 240 496), lower := (rows 67 14 133 265 16 32 64 128 256), losses := [] }

theorem u19957 : Upper (D 8) (R 8) [66,12,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19958 : Route 9 := (fun mask => (mask,id))

def c19958 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19958 : Upper (D 8) (R 8) [66,12,129,272] 13 := by
  apply FastRouting.sound _ _ [66,12,129,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19958 c19958
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10251
  · exact u10252
  · exact u10253
  · exact u10254
  · exact u10255
  · exact u10256

def r19959 : Route 9 := (fun mask => (mask,id))

def c19959 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19959 : Upper (D 8) (R 8) [66,12,129,288] 13 := by
  apply FastRouting.sound _ _ [66,12,129,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19959 c19959
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10257
  · exact u10258
  · exact u10259
  · exact u10260
  · exact u10261
  · exact u10262

def b19960 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 133 328 177 177 241 177 433), lower := (rows 67 14 133 328 16 32 64 128 256), losses := [] }

theorem u19960 : Upper (D 8) (R 8) [66,12,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19961 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 133 392 113 113 113 241 369), lower := (rows 67 14 133 392 16 32 64 128 256), losses := [] }

theorem u19961 : Upper (D 8) (R 8) [66,12,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19961 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19962 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 148 168 369 353 353 481 353), lower := (rows 67 14 148 168 16 32 64 128 256), losses := [] }

theorem u19962 : Upper (D 8) (R 8) [66,12,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19963 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 148 200 305 289 353 417 289), lower := (rows 67 14 148 200 16 32 64 128 256), losses := [] }

theorem u19963 : Upper (D 8) (R 8) [66,12,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19964 : Route 9 := (fun mask => (mask,id))

def c19964 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19964 : Upper (D 8) (R 8) [66,12,144,257] 13 := by
  apply FastRouting.sound _ _ [66,12,144,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19964 c19964
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10263
  · exact u10264
  · exact u10265
  · exact u10266
  · exact u10267
  · exact u10268

def r19965 : Route 9 := (fun mask => (mask,id))

def c19965 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19965 : Upper (D 8) (R 8) [66,12,144,288] 13 := by
  apply FastRouting.sound _ _ [66,12,144,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19965 c19965
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10269
  · exact u10270
  · exact u10271
  · exact u10272
  · exact u10273
  · exact u10274

def b19966 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 148 328 177 161 225 161 417), lower := (rows 67 14 148 328 16 32 64 128 256), losses := [] }

theorem u19966 : Upper (D 8) (R 8) [66,12,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19967 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 148 392 113 97 97 225 353), lower := (rows 67 14 148 392 16 32 64 128 256), losses := [] }

theorem u19967 : Upper (D 8) (R 8) [66,12,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19968 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 164 168 369 369 369 497 369), lower := (rows 67 14 164 168 16 32 64 128 256), losses := [] }

theorem u19968 : Upper (D 8) (R 8) [66,12,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19969 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 164 200 305 305 369 433 305), lower := (rows 67 14 164 200 16 32 64 128 256), losses := [] }

theorem u19969 : Upper (D 8) (R 8) [66,12,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19970 : Route 9 := (fun mask => (mask,id))

def c19970 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19970 : Upper (D 8) (R 8) [66,12,160,257] 13 := by
  apply FastRouting.sound _ _ [66,12,160,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19970 c19970
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10275
  · exact u10276
  · exact u10277
  · exact u10278
  · exact u10279
  · exact u10280

def r19971 : Route 9 := (fun mask => (mask,id))

def c19971 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19971 : Upper (D 8) (R 8) [66,12,160,272] 13 := by
  apply FastRouting.sound _ _ [66,12,160,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19971 c19971
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10281
  · exact u10282
  · exact u10283
  · exact u10284
  · exact u10285
  · exact u10286

def r19972 : Route 9 := (fun mask => (mask,id))

def c19972 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19972 : Upper (D 8) (R 8) [66,12,160,288] 13 := by
  apply FastRouting.sound _ _ [66,12,160,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19972 c19972
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u10287
  · exact u10288
  · exact u10289
  · exact u10290
  · exact u10291
  · exact u10292

def b19973 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 164 328 177 177 241 177 433), lower := (rows 67 14 164 328 16 32 64 128 256), losses := [] }

theorem u19973 : Upper (D 8) (R 8) [66,12,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19974 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 164 392 113 113 113 241 369), lower := (rows 67 14 164 392 16 32 64 128 256), losses := [] }

theorem u19974 : Upper (D 8) (R 8) [66,12,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19975 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 196 265 177 177 241 177 433), lower := (rows 67 14 196 265 16 32 64 128 256), losses := [] }

theorem u19975 : Upper (D 8) (R 8) [66,12,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19975 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19976 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 196 280 177 161 225 161 417), lower := (rows 67 14 196 280 16 32 64 128 256), losses := [] }

theorem u19976 : Upper (D 8) (R 8) [66,12,192,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19976 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19977 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 196 296 177 177 241 177 433), lower := (rows 67 14 196 296 16 32 64 128 256), losses := [] }

theorem u19977 : Upper (D 8) (R 8) [66,12,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19978 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 196 392 49 49 113 177 305), lower := (rows 67 14 196 392 16 32 64 128 256), losses := [] }

theorem u19978 : Upper (D 8) (R 8) [66,12,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19978 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19979 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 28 496 480 480 480 480), lower := (rows 67 35 13 28 16 32 64 128 256), losses := [] }

theorem u19979 : Upper (D 8) (R 8) [66,33,9,20] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u19979
end Delivery.IrregularNine14.P08
