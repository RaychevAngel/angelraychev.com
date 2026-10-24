import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0039
import IrregularNine14P09C0040

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5880 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 164 152 280 96 323 387 259), lower := (rows 97 7 164 152 280 96 64 128 256), losses := [] }

theorem u5880 : Upper (D 9) (R 9) [96,5,160,144,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5880 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5881 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 97 7 164 152 280 288 67 195 323), lower := (rows 97 7 164 152 280 288 64 128 256), losses := [] }

theorem u5881 : Upper (D 9) (R 9) [96,5,160,144,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5881 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5882 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 152 336 33 330 394 266), lower := (rows 97 7 164 152 336 33 64 128 256), losses := [] }

theorem u5882 : Upper (D 9) (R 9) [96,5,160,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5882 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5883 : Route 9 := (fun mask => (mask,id))

def c5883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5883 : Upper (D 9) (R 9) [96,5,160,144,320,2] 13 := by
  apply FastRouting.sound _ _ [96,5,160,144,320,2] 13 (by decide) (choices 1) [1,8,256] r5883 c5883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2371
  · exact u2372
  · exact u2373

def b5884 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 7 164 152 336 40 323 387 259), lower := (rows 97 7 164 152 336 40 64 128 256), losses := [] }

theorem u5884 : Upper (D 9) (R 9) [96,5,160,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5884 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5885 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(2,0),(2,6),(3,5),(4,5)], upper := (rows 97 7 164 152 336 288 75 139 267), lower := (rows 97 7 164 152 336 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 304 64 128 256), good := (rows 96 6 164 188 368 288 64 128 288) },{ target := 6, region := (rows 1 2 12 8 16 304 0 128 256), good := (rows 33 7 164 188 304 288 0 128 288) }] }

theorem u5885 : Upper (D 9) (R 9) [96,5,160,144,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5885 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5886 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5)], upper := (rows 97 7 164 200 273 34 344 408 280), lower := (rows 97 7 164 200 273 34 64 128 256), losses := [] }

theorem u5886 : Upper (D 9) (R 9) [96,5,160,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5886 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5887 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(4,6)], upper := (rows 97 7 164 200 273 40 338 402 274), lower := (rows 97 7 164 200 273 40 64 128 256), losses := [] }

theorem u5887 : Upper (D 9) (R 9) [96,5,160,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5887 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5888 : Route 9 := (fun mask => (mask,id))

def c5888 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5888 : Upper (D 9) (R 9) [96,5,160,192,257,16] 13 := by
  apply FastRouting.sound _ _ [96,5,160,192,257,16] 13 (by decide) (choices 1) [2,8,256] r5888 c5888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2374
  · exact u2375
  · exact u2376

def r5889 : Route 9 := (fun mask => (mask,id))

def c5889 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5889 : Upper (D 9) (R 9) [96,5,160,192,257,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,192,257,256] 13 (by decide) (choices 1) [2,8,16] r5889 c5889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2377
  · exact u2378
  · exact u2379

def b5890 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 3, region := 33, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 200 274 33 344 408 280), lower := (rows 97 7 164 200 274 33 64 128 256), losses := [] }

theorem u5890 : Upper (D 9) (R 9) [96,5,160,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5890 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5891 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(4,6)], upper := (rows 97 7 164 200 274 40 337 401 273), lower := (rows 97 7 164 200 274 40 64 128 256), losses := [] }

theorem u5891 : Upper (D 9) (R 9) [96,5,160,192,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5891 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5892 : Route 9 := (fun mask => (mask,id))

def c5892 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5892 : Upper (D 9) (R 9) [96,5,160,192,258,16] 13 := by
  apply FastRouting.sound _ _ [96,5,160,192,258,16] 13 (by decide) (choices 1) [1,8,256] r5892 c5892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2380
  · exact u2381
  · exact u2382

def r5893 : Route 9 := (fun mask => (mask,id))

def c5893 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5893 : Upper (D 9) (R 9) [96,5,160,192,258,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,192,258,256] 13 (by decide) (choices 1) [1,8,16] r5893 c5893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2383
  · exact u2384
  · exact u2385

def b5894 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 3, region := 33, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 200 280 33 338 402 274), lower := (rows 97 7 164 200 280 33 64 128 256), losses := [] }

theorem u5894 : Upper (D 9) (R 9) [96,5,160,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5894 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5895 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5)], upper := (rows 97 7 164 200 280 34 337 401 273), lower := (rows 97 7 164 200 280 34 64 128 256), losses := [] }

theorem u5895 : Upper (D 9) (R 9) [96,5,160,192,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5895 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5896 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 7 164 200 280 48 323 387 259), lower := (rows 97 7 164 200 280 48 64 128 256), losses := [] }

theorem u5896 : Upper (D 9) (R 9) [96,5,160,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5896 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5897 : Route 9 := (fun mask => (mask,id))

def c5897 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5897 : Upper (D 9) (R 9) [96,5,160,192,264,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,192,264,256] 13 (by decide) (choices 1) [1,2,16] r5897 c5897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2386
  · exact u2387
  · exact u2388

def r5898 : Route 9 := (fun mask => (mask,id))

def c5898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5898 : Upper (D 9) (R 9) [96,5,160,257,258,8] 13 := by
  apply FastRouting.sound _ _ [96,5,160,257,258,8] 13 (by decide) (choices 1) [16,128] r5898 c5898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2389
  · exact u2390

def r5899 : Route 9 := (fun mask => (mask,id))

def c5899 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5899 : Upper (D 9) (R 9) [96,5,160,257,258,16] 13 := by
  apply FastRouting.sound _ _ [96,5,160,257,258,16] 13 (by decide) (choices 1) [8,128] r5899 c5899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2391
  · exact u2392

def b5900 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 164 265 274 96 216 152 408), lower := (rows 97 7 164 265 274 96 64 128 256), losses := [] }

theorem u5900 : Upper (D 9) (R 9) [96,5,160,257,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5900 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5901 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 97 7 164 265 274 160 88 216 344), lower := (rows 97 7 164 265 274 160 64 128 256), losses := [] }

theorem u5901 : Upper (D 9) (R 9) [96,5,160,257,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5901 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5902 : Route 9 := (fun mask => (mask,id))

def c5902 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5902 : Upper (D 9) (R 9) [96,5,160,257,320,2] 13 := by
  apply FastRouting.sound _ _ [96,5,160,257,320,2] 13 (by decide) (choices 1) [8,16,128] r5902 c5902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2393
  · exact u2394
  · exact u2395

def b5903 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 4, region := 41, targets := 128 }], pairs := [(0,7),(3,5),(3,7),(4,5)], upper := (rows 97 7 164 265 336 40 210 146 402), lower := (rows 97 7 164 265 336 40 64 128 256), losses := [] }

theorem u5903 : Upper (D 9) (R 9) [96,5,160,257,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5903 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5904 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6)], upper := (rows 97 7 164 265 336 48 202 138 394), lower := (rows 97 7 164 265 336 48 64 128 256), losses := [] }

theorem u5904 : Upper (D 9) (R 9) [96,5,160,257,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5904 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5905 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 97 7 164 265 336 160 90 154 282), lower := (rows 97 7 164 265 336 160 64 128 256), losses := [] }

theorem u5905 : Upper (D 9) (R 9) [96,5,160,257,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5905 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5906 : Route 9 := (fun mask => (mask,id))

def c5906 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5906 : Upper (D 9) (R 9) [96,5,160,257,384,2] 13 := by
  apply FastRouting.sound _ _ [96,5,160,257,384,2] 13 (by decide) (choices 1) [8,16] r5906 c5906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2396
  · exact u2397

def r5907 : Route 9 := (fun mask => (mask,id))

def c5907 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5907 : Upper (D 9) (R 9) [96,5,160,257,384,8] 13 := by
  apply FastRouting.sound _ _ [96,5,160,257,384,8] 13 (by decide) (choices 1) [2,16] r5907 c5907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2398
  · exact u2399

def b5908 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 97 7 164 265 400 48 74 202 330), lower := (rows 97 7 164 265 400 48 64 128 256), losses := [] }

theorem u5908 : Upper (D 9) (R 9) [96,5,160,257,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5908 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5909 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 164 265 400 96 90 154 282), lower := (rows 97 7 164 265 400 96 64 128 256), losses := [] }

theorem u5909 : Upper (D 9) (R 9) [96,5,160,257,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5909 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5910 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 266 336 33 216 152 408), lower := (rows 97 7 164 266 336 33 64 128 256), losses := [] }

theorem u5910 : Upper (D 9) (R 9) [96,5,160,258,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5910 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5911 : Route 9 := (fun mask => (mask,id))

def c5911 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5911 : Upper (D 9) (R 9) [96,5,160,258,320,8] 13 := by
  apply FastRouting.sound _ _ [96,5,160,258,320,8] 13 (by decide) (choices 1) [1,16,128] r5911 c5911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2400
  · exact u2401
  · exact u2402

def b5912 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6)], upper := (rows 97 7 164 266 336 48 201 137 393), lower := (rows 97 7 164 266 336 48 64 128 256), losses := [] }

theorem u5912 : Upper (D 9) (R 9) [96,5,160,258,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5912 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5913 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 97 7 164 266 336 160 89 153 281), lower := (rows 97 7 164 266 336 160 64 128 256), losses := [] }

theorem u5913 : Upper (D 9) (R 9) [96,5,160,258,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5913 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5914 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 266 400 33 88 216 344), lower := (rows 97 7 164 266 400 33 64 128 256), losses := [] }

theorem u5914 : Upper (D 9) (R 9) [96,5,160,258,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5914 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5915 : Route 9 := (fun mask => (mask,id))

def c5915 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5915 : Upper (D 9) (R 9) [96,5,160,258,384,8] 13 := by
  apply FastRouting.sound _ _ [96,5,160,258,384,8] 13 (by decide) (choices 1) [1,16] r5915 c5915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2403
  · exact u2404

def b5916 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 97 7 164 266 400 48 73 201 329), lower := (rows 97 7 164 266 400 48 64 128 256), losses := [] }

theorem u5916 : Upper (D 9) (R 9) [96,5,160,258,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5916 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5917 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 164 266 400 96 89 153 281), lower := (rows 97 7 164 266 400 96 64 128 256), losses := [] }

theorem u5917 : Upper (D 9) (R 9) [96,5,160,258,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5917 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5918 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 328 400 33 90 154 282), lower := (rows 97 7 164 328 400 33 64 128 256), losses := [] }

theorem u5918 : Upper (D 9) (R 9) [96,5,160,320,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5918 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5919 : Route 9 := (fun mask => (mask,id))

def c5919 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5919 : Upper (D 9) (R 9) [96,5,160,320,384,2] 13 := by
  apply FastRouting.sound _ _ [96,5,160,320,384,2] 13 (by decide) (choices 1) [1,8,16] r5919 c5919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2405
  · exact u2406
  · exact u2407

def b5920 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,6)], upper := (rows 97 7 164 328 400 40 83 147 275), lower := (rows 97 7 164 328 400 40 64 128 256), losses := [] }

theorem u5920 : Upper (D 9) (R 9) [96,5,160,320,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5920 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5921 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 97 7 164 328 400 48 75 139 267), lower := (rows 97 7 164 328 400 48 64 128 256), losses := [] }

theorem u5921 : Upper (D 9) (R 9) [96,5,160,320,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5921 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5922 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 56, targets := 448 }], pairs := [(3,6),(3,7),(3,8),(4,6),(4,7)], upper := (rows 97 7 388 26 56 33 448 448 448), lower := (rows 97 7 388 26 56 33 64 128 256), losses := [] }

theorem u5922 : Upper (D 9) (R 9) [96,5,384,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5922 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5923 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 388 26 56 96 449 385 385), lower := (rows 97 7 388 26 56 96 64 128 256), losses := [] }

theorem u5923 : Upper (D 9) (R 9) [96,5,384,18,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5923 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5924 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,0),(4,0)], upper := (rows 97 7 388 26 56 160 321 449 321), lower := (rows 97 7 388 26 56 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 18 164 64 128 256), good := (rows 96 62 420 26 56 160 64 160 256) }] }

theorem u5924 : Upper (D 9) (R 9) [96,5,384,18,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5924 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5925 : Route 9 := (fun mask => (mask,id))

def c5925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u5925 : Upper (D 9) (R 9) [96,5,384,18,129,8] 13 := by
  apply FastRouting.sound _ _ [96,5,384,18,129,8] 13 (by decide) (choices 1) [32,256] r5925 c5925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2408
  · exact u2409

def b5926 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 388 26 145 96 360 424 296), lower := (rows 97 7 388 26 145 96 64 128 256), losses := [] }

theorem u5926 : Upper (D 9) (R 9) [96,5,384,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5926 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5927_8 : Upper (D 9) (R 9) [96,5,384,18,129,256,8] 13 :=
  permutation_upper _ _ _ [96,5,384,18,129,8,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2409

theorem m5927_32 : Upper (D 9) (R 9) [96,5,384,18,129,256,32] 13 :=
  permutation_upper _ _ _ [96,5,384,18,129,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2410

def r5927 : Route 9 := (fun mask => (mask,id))

def c5927 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5927 : Upper (D 9) (R 9) [96,5,384,18,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,384,18,129,256] 13 (by decide) (choices 1) [8,32] r5927 c5927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5927_8
  · exact m5927_32

def b5928 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 388, targets := 1 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(2,0),(3,0)], upper := (rows 97 7 388 26 152 33 352 480 352), lower := (rows 97 7 388 26 152 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 39 10 18 32 97 161 289), good := (rows 484 478 388 30 152 484 64 128 256) }] }

theorem u5928 : Upper (D 9) (R 9) [96,5,384,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5928 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5929 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 388 26 152 96 353 417 289), lower := (rows 97 7 388 26 152 96 64 128 256), losses := [] }

theorem u5929 : Upper (D 9) (R 9) [96,5,384,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5929 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5930 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 5, region := 65, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(3,8),(4,8)], upper := (rows 97 7 388 26 152 288 97 225 353), lower := (rows 97 7 388 26 152 288 64 128 256), losses := [{ target := 8, region := (rows 33 2 4 10 18 32 97 161 0), good := (rows 225 223 132 26 152 225 64 128 0) }] }

theorem u5930 : Upper (D 9) (R 9) [96,5,384,18,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5930 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5931 : Route 9 := (fun mask => (mask,id))

def c5931 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5931 : Upper (D 9) (R 9) [96,5,384,18,160,1] 13 := by
  apply FastRouting.sound _ _ [96,5,384,18,160,1] 13 (by decide) (choices 1) [8,256] r5931 c5931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2411
  · exact u2412

def r5932 : Route 9 := (fun mask => (mask,id))

def c5932 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5932 : Upper (D 9) (R 9) [96,5,384,18,160,8] 13 := by
  apply FastRouting.sound _ _ [96,5,384,18,160,8] 13 (by decide) (choices 1) [1,256] r5932 c5932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2413
  · exact u2414

def b5933 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 388 26 176 96 329 393 265), lower := (rows 97 7 388 26 176 96 64 128 256), losses := [] }

theorem u5933 : Upper (D 9) (R 9) [96,5,384,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5933 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5934 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 48, targets := 65 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(3,0),(3,6),(4,0),(4,6)], upper := (rows 97 7 388 26 176 288 73 201 329), lower := (rows 97 7 388 26 176 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 20 292 64 128 256), good := (rows 96 62 436 26 176 288 64 128 288) },{ target := 6, region := (rows 1 2 4 10 20 292 0 128 256), good := (rows 33 63 436 26 176 288 0 128 288) }] }

theorem u5934 : Upper (D 9) (R 9) [96,5,384,18,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5934 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5935 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 468, targets := 33 },{ cop := 1, region := 40, targets := 64 }], pairs := [(2,0),(2,5),(3,6),(4,0),(4,5)], upper := (rows 97 7 388 42 88 33 464 400 400), lower := (rows 97 7 388 42 88 33 64 128 256), losses := [] }

theorem u5935 : Upper (D 9) (R 9) [96,5,384,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5935 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5936 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5),(1,6),(2,6),(3,6)], upper := (rows 97 7 388 42 88 48 449 385 385), lower := (rows 97 7 388 42 88 48 64 128 256), losses := [] }

theorem u5936 : Upper (D 9) (R 9) [96,5,384,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5936 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5937 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7),(3,0),(3,6),(3,8),(4,7)], upper := (rows 97 7 388 42 88 160 337 401 273), lower := (rows 97 7 388 42 88 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 164 64 128 256), good := (rows 96 46 420 42 88 160 64 160 256) },{ target := 6, region := (rows 1 2 4 10 16 164 0 128 256), good := (rows 33 47 420 42 24 160 0 160 256) },{ target := 8, region := (rows 1 2 4 10 16 164 64 128 0), good := (rows 97 47 164 42 88 160 64 160 0) }] }

theorem u5937 : Upper (D 9) (R 9) [96,5,384,34,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5937 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5938 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 40, targets := 449 }], pairs := [(3,0),(3,6),(3,7),(3,8)], upper := (rows 97 7 388 42 145 40 336 464 336), lower := (rows 97 7 388 42 145 40 64 128 256), losses := [] }

theorem u5938 : Upper (D 9) (R 9) [96,5,384,34,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5938 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5939 : Route 9 := (fun mask => (mask,id))

def c5939 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5939 : Upper (D 9) (R 9) [96,5,384,34,129,16] 13 := by
  apply FastRouting.sound _ _ [96,5,384,34,129,16] 13 (by decide) (choices 1) [8,256] r5939 c5939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2415
  · exact u2416

#print axioms u5939
end Delivery.IrregularNine14.P09
