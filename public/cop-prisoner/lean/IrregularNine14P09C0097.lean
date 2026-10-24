import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0038
import IrregularNine14P09C0039

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5820 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 74 400 33 344 408 280), lower := (rows 97 7 164 74 400 33 64 128 256), losses := [] }

theorem u5820 : Upper (D 9) (R 9) [96,5,160,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5820 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5821 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,6)], upper := (rows 97 7 164 74 400 40 337 401 273), lower := (rows 97 7 164 74 400 40 64 128 256), losses := [] }

theorem u5821 : Upper (D 9) (R 9) [96,5,160,66,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5821 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5822 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 97 7 164 74 400 48 329 393 265), lower := (rows 97 7 164 74 400 48 64 128 256), losses := [] }

theorem u5822 : Upper (D 9) (R 9) [96,5,160,66,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5822 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5823 : Route 9 := (fun mask => (mask,id))

def c5823 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5823 : Upper (D 9) (R 9) [96,5,160,66,384,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,66,384,256] 13 (by decide) (choices 1) [1,8,16] r5823 c5823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2330
  · exact u2331
  · exact u2332

def b5824 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 38, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 164 88 145 34 328 392 264), lower := (rows 97 7 164 88 145 34 64 128 256), losses := [] }

theorem u5824 : Upper (D 9) (R 9) [96,5,160,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5824 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5825 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,6)], upper := (rows 97 7 164 88 145 40 322 386 258), lower := (rows 97 7 164 88 145 40 64 128 256), losses := [] }

theorem u5825 : Upper (D 9) (R 9) [96,5,160,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5825 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5826 : Route 9 := (fun mask => (mask,id))

def c5826 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5826 : Upper (D 9) (R 9) [96,5,160,80,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,129,256] 13 (by decide) (choices 1) [2,8,256] r5826 c5826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2333
  · exact u2334
  · exact u2335

def b5827 : PairBound 9 := { available := 264, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 88 146 33 328 392 264), lower := (rows 97 7 164 88 146 33 64 128 256), losses := [] }

theorem u5827 : Upper (D 9) (R 9) [96,5,160,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5827 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5828 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,6)], upper := (rows 97 7 164 88 146 40 321 385 257), lower := (rows 97 7 164 88 146 40 64 128 256), losses := [] }

theorem u5828 : Upper (D 9) (R 9) [96,5,160,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5828 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5829 : Route 9 := (fun mask => (mask,id))

def c5829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5829 : Upper (D 9) (R 9) [96,5,160,80,130,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,130,256] 13 (by decide) (choices 1) [1,8,256] r5829 c5829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2336
  · exact u2337
  · exact u2338

def r5830 : Route 9 := (fun mask => (mask,id))

def c5830 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5830 : Upper (D 9) (R 9) [96,5,160,80,257,2] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,257,2] 13 (by decide) (choices 1) [8,128,256] r5830 c5830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2339
  · exact u2340
  · exact u2341

def b5831 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,6)], upper := (rows 97 7 164 88 273 40 450 386 386), lower := (rows 97 7 164 88 273 40 64 128 256), losses := [] }

theorem u5831 : Upper (D 9) (R 9) [96,5,160,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5831 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5832 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 97 7 164 88 273 160 330 394 266), lower := (rows 97 7 164 88 273 160 64 128 256), losses := [] }

theorem u5832 : Upper (D 9) (R 9) [96,5,160,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5832 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5833 : Route 9 := (fun mask => (mask,id))

def c5833 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5833 : Upper (D 9) (R 9) [96,5,160,80,257,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,257,256] 13 (by decide) (choices 1) [2,8,128] r5833 c5833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2342
  · exact u2343
  · exact u2344

def b5834 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 88 274 33 456 392 392), lower := (rows 97 7 164 88 274 33 64 128 256), losses := [] }

theorem u5834 : Upper (D 9) (R 9) [96,5,160,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5834 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5835 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,6)], upper := (rows 97 7 164 88 274 40 449 385 385), lower := (rows 97 7 164 88 274 40 64 128 256), losses := [] }

theorem u5835 : Upper (D 9) (R 9) [96,5,160,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5835 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5836 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 97 7 164 88 274 160 329 393 265), lower := (rows 97 7 164 88 274 160 64 128 256), losses := [] }

theorem u5836 : Upper (D 9) (R 9) [96,5,160,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5836 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5837 : Route 9 := (fun mask => (mask,id))

def c5837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5837 : Upper (D 9) (R 9) [96,5,160,80,258,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,258,256] 13 (by decide) (choices 1) [1,8,128] r5837 c5837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2345
  · exact u2346
  · exact u2347

def b5838 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 88 280 33 450 386 386), lower := (rows 97 7 164 88 280 33 64 128 256), losses := [] }

theorem u5838 : Upper (D 9) (R 9) [96,5,160,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5838 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5839 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 7 164 88 280 34 449 385 385), lower := (rows 97 7 164 88 280 34 64 128 256), losses := [] }

theorem u5839 : Upper (D 9) (R 9) [96,5,160,80,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5839 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5840 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 347, targets := 128 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 97 7 164 88 280 160 323 387 259), lower := (rows 97 7 164 88 280 160 64 128 256), losses := [] }

theorem u5840 : Upper (D 9) (R 9) [96,5,160,80,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5840 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5841 : PairBound 9 := { available := 131, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 0, region := 134, targets := 64 }], pairs := [(0,8),(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 164 88 280 288 195 131 387), lower := (rows 97 7 164 88 280 288 64 128 256), losses := [] }

theorem u5841 : Upper (D 9) (R 9) [96,5,160,80,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5841 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5842 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 88 400 33 330 394 266), lower := (rows 97 7 164 88 400 33 64 128 256), losses := [] }

theorem u5842 : Upper (D 9) (R 9) [96,5,160,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5842 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5843 : Route 9 := (fun mask => (mask,id))

def c5843 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5843 : Upper (D 9) (R 9) [96,5,160,80,384,2] 13 := by
  apply FastRouting.sound _ _ [96,5,160,80,384,2] 13 (by decide) (choices 1) [1,8,256] r5843 c5843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2348
  · exact u2349
  · exact u2350

def b5844 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,6)], upper := (rows 97 7 164 88 400 40 323 387 259), lower := (rows 97 7 164 88 400 40 64 128 256), losses := [] }

theorem u5844 : Upper (D 9) (R 9) [96,5,160,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5844 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5845 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,7),(2,0),(2,6),(3,5),(4,5)], upper := (rows 97 7 164 88 400 288 75 139 267), lower := (rows 97 7 164 88 400 288 64 128 256), losses := [{ target := 7, region := (rows 9 2 4 8 16 304 64 0 256), good := (rows 97 7 36 121 304 288 64 0 288) }] }

theorem u5845 : Upper (D 9) (R 9) [96,5,160,80,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5845 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5846 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 38, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 164 137 274 40 336 464 336), lower := (rows 97 7 164 137 274 40 64 128 256), losses := [] }

theorem u5846 : Upper (D 9) (R 9) [96,5,160,129,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5846 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5847 : Route 9 := (fun mask => (mask,id))

def c5847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5847 : Upper (D 9) (R 9) [96,5,160,129,258,16] 13 := by
  apply FastRouting.sound _ _ [96,5,160,129,258,16] 13 (by decide) (choices 1) [8,256] r5847 c5847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2351
  · exact u2352

def b5848 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 164 137 274 96 344 408 280), lower := (rows 97 7 164 137 274 96 64 128 256), losses := [] }

theorem u5848 : Upper (D 9) (R 9) [96,5,160,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5848 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5849 : Route 9 := (fun mask => (mask,id))

def c5849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5849 : Upper (D 9) (R 9) [96,5,160,129,258,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,129,258,256] 13 (by decide) (choices 1) [8,16] r5849 c5849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2353
  · exact u2354

def b5850 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 38, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 164 137 280 34 336 464 336), lower := (rows 97 7 164 137 280 34 64 128 256), losses := [] }

theorem u5850 : Upper (D 9) (R 9) [96,5,160,129,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5850 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5851 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 97 7 164 137 280 48 322 450 322), lower := (rows 97 7 164 137 280 48 64 128 256), losses := [] }

theorem u5851 : Upper (D 9) (R 9) [96,5,160,129,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5851 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5852 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 164 137 280 96 338 402 274), lower := (rows 97 7 164 137 280 96 64 128 256), losses := [] }

theorem u5852 : Upper (D 9) (R 9) [96,5,160,129,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5852 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5853 : Route 9 := (fun mask => (mask,id))

def c5853 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5853 : Upper (D 9) (R 9) [96,5,160,129,264,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,129,264,256] 13 (by decide) (choices 1) [2,16] r5853 c5853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2355
  · exact u2356

def b5854 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 38, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 164 137 336 34 344 408 280), lower := (rows 97 7 164 137 336 34 64 128 256), losses := [] }

theorem u5854 : Upper (D 9) (R 9) [96,5,160,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5854 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5855 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 38, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 164 137 336 40 338 402 274), lower := (rows 97 7 164 137 336 40 64 128 256), losses := [] }

theorem u5855 : Upper (D 9) (R 9) [96,5,160,129,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5855 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5856 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6)], upper := (rows 97 7 164 137 336 48 330 394 266), lower := (rows 97 7 164 137 336 48 64 128 256), losses := [] }

theorem u5856 : Upper (D 9) (R 9) [96,5,160,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5856 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5857 : Route 9 := (fun mask => (mask,id))

def c5857 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5857 : Upper (D 9) (R 9) [96,5,160,129,320,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,129,320,256] 13 (by decide) (choices 1) [2,8,16] r5857 c5857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2357
  · exact u2358
  · exact u2359

def b5858 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 7 164 138 273 40 336 464 336), lower := (rows 97 7 164 138 273 40 64 128 256), losses := [] }

theorem u5858 : Upper (D 9) (R 9) [96,5,160,130,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5858 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5859 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(3,5),(4,5),(4,7)], upper := (rows 97 7 164 138 273 48 328 456 328), lower := (rows 97 7 164 138 273 48 64 128 256), losses := [] }

theorem u5859 : Upper (D 9) (R 9) [96,5,160,130,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5859 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5860 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 164 138 273 96 344 408 280), lower := (rows 97 7 164 138 273 96 64 128 256), losses := [] }

theorem u5860 : Upper (D 9) (R 9) [96,5,160,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5860 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5861 : Route 9 := (fun mask => (mask,id))

def c5861 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5861 : Upper (D 9) (R 9) [96,5,160,130,257,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,130,257,256] 13 (by decide) (choices 1) [8,16] r5861 c5861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2360
  · exact u2361

def b5862 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 138 280 33 336 464 336), lower := (rows 97 7 164 138 280 33 64 128 256), losses := [] }

theorem u5862 : Upper (D 9) (R 9) [96,5,160,130,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5862 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5863 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 97 7 164 138 280 48 321 449 321), lower := (rows 97 7 164 138 280 48 64 128 256), losses := [] }

theorem u5863 : Upper (D 9) (R 9) [96,5,160,130,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5863 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5864 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 164 138 280 96 337 401 273), lower := (rows 97 7 164 138 280 96 64 128 256), losses := [] }

theorem u5864 : Upper (D 9) (R 9) [96,5,160,130,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5864 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5865 : Route 9 := (fun mask => (mask,id))

def c5865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5865 : Upper (D 9) (R 9) [96,5,160,130,264,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,130,264,256] 13 (by decide) (choices 1) [1,16] r5865 c5865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2362
  · exact u2363

def b5866 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 138 336 33 344 408 280), lower := (rows 97 7 164 138 336 33 64 128 256), losses := [] }

theorem u5866 : Upper (D 9) (R 9) [96,5,160,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5866 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5867 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 7 164 138 336 40 337 401 273), lower := (rows 97 7 164 138 336 40 64 128 256), losses := [] }

theorem u5867 : Upper (D 9) (R 9) [96,5,160,130,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5867 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5868 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6)], upper := (rows 97 7 164 138 336 48 329 393 265), lower := (rows 97 7 164 138 336 48 64 128 256), losses := [] }

theorem u5868 : Upper (D 9) (R 9) [96,5,160,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5868 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5869 : Route 9 := (fun mask => (mask,id))

def c5869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5869 : Upper (D 9) (R 9) [96,5,160,130,320,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,130,320,256] 13 (by decide) (choices 1) [1,8,16] r5869 c5869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2364
  · exact u2365
  · exact u2366

def r5870 : Route 9 := (fun mask => (mask,id))

def c5870 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5870 : Upper (D 9) (R 9) [96,5,160,144,257,2] 13 := by
  apply FastRouting.sound _ _ [96,5,160,144,257,2] 13 (by decide) (choices 1) [8,256] r5870 c5870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2367
  · exact u2368

def b5871 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 7 164 152 273 40 322 450 322), lower := (rows 97 7 164 152 273 40 64 128 256), losses := [] }

theorem u5871 : Upper (D 9) (R 9) [96,5,160,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5871 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5872 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 164 152 273 96 330 394 266), lower := (rows 97 7 164 152 273 96 64 128 256), losses := [] }

theorem u5872 : Upper (D 9) (R 9) [96,5,160,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5872 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5873 : Route 9 := (fun mask => (mask,id))

def c5873 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5873 : Upper (D 9) (R 9) [96,5,160,144,257,256] 13 := by
  apply FastRouting.sound _ _ [96,5,160,144,257,256] 13 (by decide) (choices 1) [2,8] r5873 c5873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2369
  · exact u2370

def b5874 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 152 274 33 328 456 328), lower := (rows 97 7 164 152 274 33 64 128 256), losses := [] }

theorem u5874 : Upper (D 9) (R 9) [96,5,160,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5874 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5875 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 7 164 152 274 40 321 449 321), lower := (rows 97 7 164 152 274 40 64 128 256), losses := [] }

theorem u5875 : Upper (D 9) (R 9) [96,5,160,144,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5875 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5876 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 7 164 152 274 96 329 393 265), lower := (rows 97 7 164 152 274 96 64 128 256), losses := [] }

theorem u5876 : Upper (D 9) (R 9) [96,5,160,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5876 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5877 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(2,0),(2,6),(3,5),(4,5)], upper := (rows 97 7 164 152 274 288 73 201 329), lower := (rows 97 7 164 152 274 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 304 64 128 256), good := (rows 96 6 164 188 306 288 64 128 288) },{ target := 6, region := (rows 1 2 12 8 16 304 0 128 256), good := (rows 33 7 164 188 306 288 0 128 288) }] }

theorem u5877 : Upper (D 9) (R 9) [96,5,160,144,258,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5877 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5878 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 7 164 152 280 33 322 450 322), lower := (rows 97 7 164 152 280 33 64 128 256), losses := [] }

theorem u5878 : Upper (D 9) (R 9) [96,5,160,144,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5878 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5879 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 97 7 164 152 280 34 321 449 321), lower := (rows 97 7 164 152 280 34 64 128 256), losses := [] }

theorem u5879 : Upper (D 9) (R 9) [96,5,160,144,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5879 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u5879
end Delivery.IrregularNine14.P09
