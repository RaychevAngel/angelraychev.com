import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0470
import IrregularNine14P07C0471
import IrregularNine14P07C0472

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r39900 : Route 9 := (fun mask => (mask,id))

def c39900 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39900 : Upper (D 7) (R 7) [96,160,9,258,68] 13 := by
  apply FastRouting.sound _ _ [96,160,9,258,68] 13 (by decide) (choices 1) [1,2,16,128] r39900 c39900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28248
  · exact u28249
  · exact u28250
  · exact u28251

def r39901 : Route 9 := (fun mask => (mask,id))

def c39901 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39901 : Upper (D 7) (R 7) [96,160,9,258,129] 13 := by
  apply FastRouting.sound _ _ [96,160,9,258,129] 13 (by decide) (choices 1) [2,4,16,64] r39901 c39901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28252
  · exact u28253
  · exact u28254
  · exact u28255

def b39902 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 162 13 266 146 117 85 213 341), lower := (rows 97 162 13 266 146 32 64 128 256), losses := [] }

theorem u39902 : Upper (D 7) (R 7) [96,160,9,258,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39903 : Route 9 := (fun mask => (mask,id))

def c39903 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39903 : Upper (D 7) (R 7) [96,160,9,258,132] 13 := by
  apply FastRouting.sound _ _ [96,160,9,258,132] 13 (by decide) (choices 1) [1,2,16,64] r39903 c39903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28256
  · exact u28257
  · exact u28258
  · exact u28259

def r39904 : Route 9 := (fun mask => (mask,id))

def c39904 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39904 : Upper (D 7) (R 7) [96,160,9,258,192] 13 := by
  apply FastRouting.sound _ _ [96,160,9,258,192] 13 (by decide) (choices 1) [1,2,4,16] r39904 c39904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28260
  · exact u28261
  · exact u28262
  · exact u28263

def b39905 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 162 13 268 81 178 210 146 402), lower := (rows 97 162 13 268 81 32 64 128 256), losses := [] }

theorem u39905 : Upper (D 7) (R 7) [96,160,9,260,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39906 : Route 9 := (fun mask => (mask,id))

def c39906 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39906 : Upper (D 7) (R 7) [96,160,9,260,66] 13 := by
  apply FastRouting.sound _ _ [96,160,9,260,66] 13 (by decide) (choices 1) [1,2,16,128] r39906 c39906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28264
  · exact u28265
  · exact u28266
  · exact u28267

def r39907 : Route 9 := (fun mask => (mask,id))

def c39907 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39907 : Upper (D 7) (R 7) [96,160,9,260,129] 13 := by
  apply FastRouting.sound _ _ [96,160,9,260,129] 13 (by decide) (choices 1) [2,16,64] r39907 c39907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28268
  · exact u28269
  · exact u28270

def b39908 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 162 13 268 146 115 83 211 339), lower := (rows 97 162 13 268 146 32 64 128 256), losses := [] }

theorem u39908 : Upper (D 7) (R 7) [96,160,9,260,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39909 : Route 9 := (fun mask => (mask,id))

def c39909 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39909 : Upper (D 7) (R 7) [96,160,9,260,192] 13 := by
  apply FastRouting.sound _ _ [96,160,9,260,192] 13 (by decide) (choices 1) [1,2,16] r39909 c39909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28271
  · exact u28272
  · exact u28273

def b39910 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 162 13 280 81 166 198 134 390), lower := (rows 97 162 13 280 81 32 64 128 256), losses := [] }

theorem u39910 : Upper (D 7) (R 7) [96,160,9,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39911 : Route 9 := (fun mask => (mask,id))

def c39911 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39911 : Upper (D 7) (R 7) [96,160,9,272,66] 13 := by
  apply FastRouting.sound _ _ [96,160,9,272,66] 13 (by decide) (choices 1) [1,2,4,128] r39911 c39911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28274
  · exact u28275
  · exact u28276
  · exact u28277

def r39912 : Route 9 := (fun mask => (mask,id))

def c39912 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39912 : Upper (D 7) (R 7) [96,160,9,272,68] 13 := by
  apply FastRouting.sound _ _ [96,160,9,272,68] 13 (by decide) (choices 1) [1,2,128] r39912 c39912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28278
  · exact u28279
  · exact u28280

def r39913 : Route 9 := (fun mask => (mask,id))

def c39913 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39913 : Upper (D 7) (R 7) [96,160,9,272,129] 13 := by
  apply FastRouting.sound _ _ [96,160,9,272,129] 13 (by decide) (choices 1) [2,4,64] r39913 c39913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28281
  · exact u28282
  · exact u28283

def b39914 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 162 13 280 146 103 71 199 327), lower := (rows 97 162 13 280 146 32 64 128 256), losses := [] }

theorem u39914 : Upper (D 7) (R 7) [96,160,9,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39915 : Route 9 := (fun mask => (mask,id))

def c39915 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39915 : Upper (D 7) (R 7) [96,160,9,272,132] 13 := by
  apply FastRouting.sound _ _ [96,160,9,272,132] 13 (by decide) (choices 1) [1,2,64] r39915 c39915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28284
  · exact u28285
  · exact u28286

def r39916 : Route 9 := (fun mask => (mask,id))

def c39916 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39916 : Upper (D 7) (R 7) [96,160,9,272,192] 13 := by
  apply FastRouting.sound _ _ [96,160,9,272,192] 13 (by decide) (choices 1) [1,2,4] r39916 c39916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28287
  · exact u28288
  · exact u28289

def r39917 : Route 9 := (fun mask => (mask,id))

def c39917 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39917 : Upper (D 7) (R 7) [96,160,9,320,129] 13 := by
  apply FastRouting.sound _ _ [96,160,9,320,129] 13 (by decide) (choices 1) [2,4,16] r39917 c39917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28290
  · exact u28291
  · exact u28292

def b39918 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 162 13 328 146 55 87 151 279), lower := (rows 97 162 13 328 146 32 64 128 256), losses := [] }

theorem u39918 : Upper (D 7) (R 7) [96,160,9,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39919 : Route 9 := (fun mask => (mask,id))

def c39919 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39919 : Upper (D 7) (R 7) [96,160,9,320,132] 13 := by
  apply FastRouting.sound _ _ [96,160,9,320,132] 13 (by decide) (choices 1) [1,2,16] r39919 c39919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28293
  · exact u28294
  · exact u28295

def b39920 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 162 13 392 81 54 86 150 278), lower := (rows 97 162 13 392 81 32 64 128 256), losses := [] }

theorem u39920 : Upper (D 7) (R 7) [96,160,9,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39921 : Route 9 := (fun mask => (mask,id))

def c39921 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39921 : Upper (D 7) (R 7) [96,160,9,384,66] 13 := by
  apply FastRouting.sound _ _ [96,160,9,384,66] 13 (by decide) (choices 1) [1,2,4,16] r39921 c39921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28296
  · exact u28297
  · exact u28298
  · exact u28299

def r39922 : Route 9 := (fun mask => (mask,id))

def c39922 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39922 : Upper (D 7) (R 7) [96,160,9,384,68] 13 := by
  apply FastRouting.sound _ _ [96,160,9,384,68] 13 (by decide) (choices 1) [1,2,16] r39922 c39922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28300
  · exact u28301
  · exact u28302

def b39923 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 162 28 73 145 294 326 390 262), lower := (rows 97 162 28 73 145 32 64 128 256), losses := [] }

theorem u39923 : Upper (D 7) (R 7) [96,160,24,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39924 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 162 28 73 148 291 323 387 259), lower := (rows 97 162 28 73 148 32 64 128 256), losses := [] }

theorem u39924 : Upper (D 7) (R 7) [96,160,24,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39924 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39925 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 162 28 73 273 166 198 134 390), lower := (rows 97 162 28 73 273 32 64 128 256), losses := [] }

theorem u39925 : Upper (D 7) (R 7) [96,160,24,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39926 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 162 28 73 274 167 199 135 391), lower := (rows 97 162 28 73 274 32 64 128 256), losses := [] }

theorem u39926 : Upper (D 7) (R 7) [96,160,24,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39927 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 162 28 73 276 163 195 131 387), lower := (rows 97 162 28 73 276 32 64 128 256), losses := [] }

theorem u39927 : Upper (D 7) (R 7) [96,160,24,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39928 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 162 28 73 400 39 71 135 263), lower := (rows 97 162 28 73 400 32 64 128 256), losses := [] }

theorem u39928 : Upper (D 7) (R 7) [96,160,24,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39928 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m39929_2 : Upper (D 7) (R 7) [96,160,24,66,129,2] 13 :=
  permutation_upper _ _ _ [96,160,24,66,129,1] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28303

def r39929 : Route 9 := (fun mask => (mask,id))

def c39929 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39929 : Upper (D 7) (R 7) [96,160,24,66,129] 13 := by
  apply FastRouting.sound _ _ [96,160,24,66,129] 13 (by decide) (choices 1) [1,2,4,256] r39929 c39929
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28303
  · exact m39929_2
  · exact u28304
  · exact u28305

def r39930 : Route 9 := (fun mask => (mask,id))

def c39930 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39930 : Upper (D 7) (R 7) [96,160,24,66,132] 13 := by
  apply FastRouting.sound _ _ [96,160,24,66,132] 13 (by decide) (choices 1) [1,2,256] r39930 c39930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28306
  · exact u28307
  · exact u28308

def r39931 : Route 9 := (fun mask => (mask,id))

def c39931 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39931 : Upper (D 7) (R 7) [96,160,24,66,257] 13 := by
  apply FastRouting.sound _ _ [96,160,24,66,257] 13 (by decide) (choices 1) [1,2,4,128] r39931 c39931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28309
  · exact u28310
  · exact u28311
  · exact u28312

def r39932 : Route 9 := (fun mask => (mask,id))

def c39932 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39932 : Upper (D 7) (R 7) [96,160,24,66,258] 13 := by
  apply FastRouting.sound _ _ [96,160,24,66,258] 13 (by decide) (choices 1) [1,4,128] r39932 c39932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28313
  · exact u28314
  · exact u28315

def r39933 : Route 9 := (fun mask => (mask,id))

def c39933 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39933 : Upper (D 7) (R 7) [96,160,24,66,260] 13 := by
  apply FastRouting.sound _ _ [96,160,24,66,260] 13 (by decide) (choices 1) [1,2,128] r39933 c39933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28316
  · exact u28317
  · exact u28318

def r39934 : Route 9 := (fun mask => (mask,id))

def c39934 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39934 : Upper (D 7) (R 7) [96,160,24,66,384] 13 := by
  apply FastRouting.sound _ _ [96,160,24,66,384] 13 (by decide) (choices 1) [1,2,4] r39934 c39934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28319
  · exact u28320
  · exact u28321

def r39935 : Route 9 := (fun mask => (mask,id))

def c39935 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39935 : Upper (D 7) (R 7) [96,160,24,68,257] 13 := by
  apply FastRouting.sound _ _ [96,160,24,68,257] 13 (by decide) (choices 1) [1,2,128] r39935 c39935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28322
  · exact u28323
  · exact u28324

def r39936 : Route 9 := (fun mask => (mask,id))

def c39936 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39936 : Upper (D 7) (R 7) [96,160,24,68,258] 13 := by
  apply FastRouting.sound _ _ [96,160,24,68,258] 13 (by decide) (choices 1) [1,2,128] r39936 c39936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28325
  · exact u28326
  · exact u28327

def r39937 : Route 9 := (fun mask => (mask,id))

def c39937 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39937 : Upper (D 7) (R 7) [96,160,24,68,384] 13 := by
  apply FastRouting.sound _ _ [96,160,24,68,384] 13 (by decide) (choices 1) [1,2] r39937 c39937
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u28328
  · exact u28329

def r39938 : Route 9 := (fun mask => (mask,id))

def c39938 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39938 : Upper (D 7) (R 7) [96,160,24,192,257] 13 := by
  apply FastRouting.sound _ _ [96,160,24,192,257] 13 (by decide) (choices 1) [1,2,4] r39938 c39938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28330
  · exact u28331
  · exact u28332

theorem m39939_2 : Upper (D 7) (R 7) [96,160,24,192,260,2] 13 :=
  permutation_upper _ _ _ [96,160,24,192,260,1] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28333

def r39939 : Route 9 := (fun mask => (mask,id))

def c39939 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39939 : Upper (D 7) (R 7) [96,160,24,192,260] 13 := by
  apply FastRouting.sound _ _ [96,160,24,192,260] 13 (by decide) (choices 1) [1,2] r39939 c39939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u28333
  · exact m39939_2

def b39940 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 4, targets := 162 },{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(2,7)], upper := (rows 97 162 69 137 274 62 94 158 286), lower := (rows 97 162 69 137 274 32 64 128 256), losses := [] }

theorem u39940 : Upper (D 7) (R 7) [96,160,65,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39941 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 4, targets := 162 },{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(2,7)], upper := (rows 97 162 69 137 276 58 90 154 282), lower := (rows 97 162 69 137 276 32 64 128 256), losses := [] }

theorem u39941 : Upper (D 7) (R 7) [96,160,65,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39942 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 4, targets := 162 },{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(2,7)], upper := (rows 97 162 69 137 280 54 86 150 278), lower := (rows 97 162 69 137 280 32 64 128 256), losses := [] }

theorem u39942 : Upper (D 7) (R 7) [96,160,65,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39943 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 4, targets := 162 },{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(2,7)], upper := (rows 97 162 69 140 273 58 90 154 282), lower := (rows 97 162 69 140 273 32 64 128 256), losses := [] }

theorem u39943 : Upper (D 7) (R 7) [96,160,65,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39944 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 4, targets := 162 },{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(2,7)], upper := (rows 97 162 69 140 274 59 91 155 283), lower := (rows 97 162 69 140 274 32 64 128 256), losses := [] }

theorem u39944 : Upper (D 7) (R 7) [96,160,65,132,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39945 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 4, targets := 162 },{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(2,7)], upper := (rows 97 162 69 140 280 51 83 147 275), lower := (rows 97 162 69 140 280 32 64 128 256), losses := [] }

theorem u39945 : Upper (D 7) (R 7) [96,160,65,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39946 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 4, targets := 162 },{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(2,7)], upper := (rows 97 162 69 152 273 46 78 142 270), lower := (rows 97 162 69 152 273 32 64 128 256), losses := [] }

theorem u39946 : Upper (D 7) (R 7) [96,160,65,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39947 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 4, targets := 162 },{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(2,7)], upper := (rows 97 162 69 152 274 47 79 143 271), lower := (rows 97 162 69 152 274 32 64 128 256), losses := [] }

theorem u39947 : Upper (D 7) (R 7) [96,160,65,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39948 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 4, targets := 162 },{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(2,7)], upper := (rows 97 162 69 152 276 43 75 139 267), lower := (rows 97 162 69 152 276 32 64 128 256), losses := [] }

theorem u39948 : Upper (D 7) (R 7) [96,160,65,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39949 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 4, targets := 162 },{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(2,7)], upper := (rows 97 162 69 152 280 39 71 135 263), lower := (rows 97 162 69 152 280 32 64 128 256), losses := [] }

theorem u39949 : Upper (D 7) (R 7) [96,160,65,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39950 : Route 9 := (fun mask => (mask,id))

def c39950 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39950 : Upper (D 7) (R 7) [96,160,66,129,257] 13 := by
  apply FastRouting.sound _ _ [96,160,66,129,257] 13 (by decide) (choices 1) [2,4,8,16] r39950 c39950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28334
  · exact u28335
  · exact u28336
  · exact u28337

def r39951 : Route 9 := (fun mask => (mask,id))

def c39951 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39951 : Upper (D 7) (R 7) [96,160,66,129,260] 13 := by
  apply FastRouting.sound _ _ [96,160,66,129,260] 13 (by decide) (choices 1) [1,2,8,16] r39951 c39951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28338
  · exact u28339
  · exact u28340
  · exact u28341

def r39952 : Route 9 := (fun mask => (mask,id))

def c39952 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39952 : Upper (D 7) (R 7) [96,160,66,132,257] 13 := by
  apply FastRouting.sound _ _ [96,160,66,132,257] 13 (by decide) (choices 1) [1,2,8,16] r39952 c39952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28342
  · exact u28343
  · exact u28344
  · exact u28345

def r39953 : Route 9 := (fun mask => (mask,id))

def c39953 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39953 : Upper (D 7) (R 7) [96,160,66,132,258] 13 := by
  apply FastRouting.sound _ _ [96,160,66,132,258] 13 (by decide) (choices 1) [1,8,16] r39953 c39953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28346
  · exact u28347
  · exact u28348

def r39954 : Route 9 := (fun mask => (mask,id))

def c39954 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39954 : Upper (D 7) (R 7) [96,160,66,132,264] 13 := by
  apply FastRouting.sound _ _ [96,160,66,132,264] 13 (by decide) (choices 1) [1,2,16] r39954 c39954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28349
  · exact u28350
  · exact u28351

def r39955 : Route 9 := (fun mask => (mask,id))

def c39955 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39955 : Upper (D 7) (R 7) [96,160,66,144,257] 13 := by
  apply FastRouting.sound _ _ [96,160,66,144,257] 13 (by decide) (choices 1) [1,2,4,8] r39955 c39955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28352
  · exact u28353
  · exact u28354
  · exact u28355

def r39956 : Route 9 := (fun mask => (mask,id))

def c39956 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39956 : Upper (D 7) (R 7) [96,160,66,144,258] 13 := by
  apply FastRouting.sound _ _ [96,160,66,144,258] 13 (by decide) (choices 1) [1,4,8] r39956 c39956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28356
  · exact u28357
  · exact u28358

def r39957 : Route 9 := (fun mask => (mask,id))

def c39957 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39957 : Upper (D 7) (R 7) [96,160,66,144,260] 13 := by
  apply FastRouting.sound _ _ [96,160,66,144,260] 13 (by decide) (choices 1) [1,2,8] r39957 c39957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28359
  · exact u28360
  · exact u28361

def r39958 : Route 9 := (fun mask => (mask,id))

def c39958 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39958 : Upper (D 7) (R 7) [96,160,66,144,264] 13 := by
  apply FastRouting.sound _ _ [96,160,66,144,264] 13 (by decide) (choices 1) [1,2,4] r39958 c39958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28362
  · exact u28363
  · exact u28364

def b39959 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(1,6),(4,6),(4,7)], upper := (rows 97 162 76 140 273 51 83 147 275), lower := (rows 97 162 76 140 273 32 64 128 256), losses := [] }

theorem u39959 : Upper (D 7) (R 7) [96,160,72,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u39959
end Delivery.IrregularNine14.P07
