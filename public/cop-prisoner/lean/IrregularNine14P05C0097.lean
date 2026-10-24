import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0038
import IrregularNine14P05C0039

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5820 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 35 196 25 26 300 364 428 300), lower := (rows 7 35 196 25 26 32 64 128 256), losses := [] }

theorem u5820 : Upper (D 5) (R 5) [6,33,192,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5820
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5821 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 35 196 25 28 298 362 426 298), lower := (rows 7 35 196 25 28 32 64 128 256), losses := [] }

theorem u5821 : Upper (D 5) (R 5) [6,33,192,17,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5821
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5822 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 25 50 300 332 396 268), lower := (rows 7 35 196 25 50 32 64 128 256), losses := [] }

theorem u5822 : Upper (D 5) (R 5) [6,33,192,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5822
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5823 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 3, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 196 25 52 298 330 394 266), lower := (rows 7 35 196 25 52 32 64 128 256), losses := [] }

theorem u5823 : Upper (D 5) (R 5) [6,33,192,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5823
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5824 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 24, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 196 25 56 302 334 398 270), lower := (rows 7 35 196 25 56 32 64 128 256), losses := [] }

theorem u5824 : Upper (D 5) (R 5) [6,33,192,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5824
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5825 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 228, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 25 274 44 108 172 300), lower := (rows 7 35 196 25 274 32 64 128 256), losses := [] }

theorem u5825 : Upper (D 5) (R 5) [6,33,192,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5825
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5826 : Route 9 := (fun mask => (mask,id))

def c5826 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5826 : Upper (D 5) (R 5) [6,33,192,17,260] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,260] 13 (by decide) (choices 1) [2,8] r5826 c5826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2317
  · exact u2318

def r5827 : Route 9 := (fun mask => (mask,id))

def c5827 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5827 : Upper (D 5) (R 5) [6,33,192,17,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,264] 13 (by decide) (choices 1) [2,4,8] r5827 c5827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2319
  · exact u2320
  · exact u2321

def r5828 : Route 9 := (fun mask => (mask,id))

def c5828 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5828 : Upper (D 5) (R 5) [6,33,192,17,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,288] 13 (by decide) (choices 1) [2,4,8] r5828 c5828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2322
  · exact u2323
  · exact u2324

def b5829 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 35 196 26 21 296 360 424 296), lower := (rows 7 35 196 26 21 32 64 128 256), losses := [] }

theorem u5829 : Upper (D 5) (R 5) [6,33,192,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5829
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5830 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 35 196 26 25 300 364 428 300), lower := (rows 7 35 196 26 25 32 64 128 256), losses := [] }

theorem u5830 : Upper (D 5) (R 5) [6,33,192,18,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5830
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5831 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 196 26 28 297 361 425 297), lower := (rows 7 35 196 26 28 32 64 128 256), losses := [] }

theorem u5831 : Upper (D 5) (R 5) [6,33,192,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5831
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5832 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 24, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 196 26 49 300 332 396 268), lower := (rows 7 35 196 26 49 32 64 128 256), losses := [] }

theorem u5832 : Upper (D 5) (R 5) [6,33,192,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5832
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5833 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 26 52 297 329 393 265), lower := (rows 7 35 196 26 52 32 64 128 256), losses := [] }

theorem u5833 : Upper (D 5) (R 5) [6,33,192,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5833
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5834 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 24, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 35 196 26 56 301 333 397 269), lower := (rows 7 35 196 26 56 32 64 128 256), losses := [] }

theorem u5834 : Upper (D 5) (R 5) [6,33,192,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5834
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5835 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 228, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 26 273 44 108 172 300), lower := (rows 7 35 196 26 273 32 64 128 256), losses := [] }

theorem u5835 : Upper (D 5) (R 5) [6,33,192,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5835
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5836 : Route 9 := (fun mask => (mask,id))

def c5836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5836 : Upper (D 5) (R 5) [6,33,192,18,260] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,260] 13 (by decide) (choices 1) [1,8] r5836 c5836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2325
  · exact u2326

def r5837 : Route 9 := (fun mask => (mask,id))

def c5837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5837 : Upper (D 5) (R 5) [6,33,192,18,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,264] 13 (by decide) (choices 1) [1,4,8] r5837 c5837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2327
  · exact u2328
  · exact u2329

def b5838 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 26 304 45 77 141 269), lower := (rows 7 35 196 26 304 32 64 128 256), losses := [] }

theorem u5838 : Upper (D 5) (R 5) [6,33,192,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5838
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5839 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 28 19 296 360 424 296), lower := (rows 7 35 196 28 19 32 64 128 256), losses := [] }

theorem u5839 : Upper (D 5) (R 5) [6,33,192,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5839
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5840 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 35 196 28 25 298 362 426 298), lower := (rows 7 35 196 28 25 32 64 128 256), losses := [] }

theorem u5840 : Upper (D 5) (R 5) [6,33,192,20,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5840
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5841 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 196 28 26 297 361 425 297), lower := (rows 7 35 196 28 26 32 64 128 256), losses := [] }

theorem u5841 : Upper (D 5) (R 5) [6,33,192,20,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5841
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5842 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 196 28 49 298 330 394 266), lower := (rows 7 35 196 28 49 32 64 128 256), losses := [] }

theorem u5842 : Upper (D 5) (R 5) [6,33,192,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5842
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5843 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 35 196 28 50 297 329 393 265), lower := (rows 7 35 196 28 50 32 64 128 256), losses := [] }

theorem u5843 : Upper (D 5) (R 5) [6,33,192,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5843
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5844 : PairBound 9 := { available := 267, camps := [], pairs := [(3,0),(4,0)], upper := (rows 7 35 196 28 56 299 331 395 267), lower := (rows 7 35 196 28 56 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 18 32 64 128 256), good := (rows 30 58 196 28 56 32 64 128 256) }] }

theorem u5844 : Upper (D 5) (R 5) [6,33,192,20,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5844
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5845 : Route 9 := (fun mask => (mask,id))

def c5845 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5845 : Upper (D 5) (R 5) [6,33,192,20,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,257] 13 (by decide) (choices 1) [2,8] r5845 c5845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2330
  · exact u2331

def r5846 : Route 9 := (fun mask => (mask,id))

def c5846 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5846 : Upper (D 5) (R 5) [6,33,192,20,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,258] 13 (by decide) (choices 1) [1,8] r5846 c5846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2332
  · exact u2333

def r5847 : Route 9 := (fun mask => (mask,id))

def c5847 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5847 : Upper (D 5) (R 5) [6,33,192,20,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,264] 13 (by decide) (choices 1) [1,2,8] r5847 c5847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2334
  · exact u2335
  · exact u2336

def r5848 : Route 9 := (fun mask => (mask,id))

def c5848 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5848 : Upper (D 5) (R 5) [6,33,192,20,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,288] 13 (by decide) (choices 1) [1,2,8] r5848 c5848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2337
  · exact u2338
  · exact u2339

def b5849 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 56 19 300 332 396 268), lower := (rows 7 35 196 56 19 32 64 128 256), losses := [] }

theorem u5849 : Upper (D 5) (R 5) [6,33,192,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5849
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5850 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 35 196 56 21 298 330 394 266), lower := (rows 7 35 196 56 21 32 64 128 256), losses := [] }

theorem u5850 : Upper (D 5) (R 5) [6,33,192,48,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5850
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5851 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 35 196 56 22 297 329 393 265), lower := (rows 7 35 196 56 22 32 64 128 256), losses := [] }

theorem u5851 : Upper (D 5) (R 5) [6,33,192,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5851
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5852 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 24, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 196 56 25 302 334 398 270), lower := (rows 7 35 196 56 25 32 64 128 256), losses := [] }

theorem u5852 : Upper (D 5) (R 5) [6,33,192,48,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5852
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5853 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 24, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 35 196 56 26 301 333 397 269), lower := (rows 7 35 196 56 26 32 64 128 256), losses := [] }

theorem u5853 : Upper (D 5) (R 5) [6,33,192,48,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5853
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5854 : PairBound 9 := { available := 267, camps := [], pairs := [(3,0),(4,0)], upper := (rows 7 35 196 56 28 299 331 395 267), lower := (rows 7 35 196 56 28 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 17 32 64 128 256), good := (rows 30 58 196 56 28 32 64 128 256) }] }

theorem u5854 : Upper (D 5) (R 5) [6,33,192,48,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5854
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5855 : Route 9 := (fun mask => (mask,id))

def c5855 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5855 : Upper (D 5) (R 5) [6,33,192,48,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,257] 13 (by decide) (choices 1) [2,4,8] r5855 c5855
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2340
  · exact u2341
  · exact u2342

def r5856 : Route 9 := (fun mask => (mask,id))

def c5856 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5856 : Upper (D 5) (R 5) [6,33,192,48,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,258] 13 (by decide) (choices 1) [1,4,8] r5856 c5856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2343
  · exact u2344
  · exact u2345

def r5857 : Route 9 := (fun mask => (mask,id))

def c5857 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5857 : Upper (D 5) (R 5) [6,33,192,48,260] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,260] 13 (by decide) (choices 1) [1,2,8] r5857 c5857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2346
  · exact u2347
  · exact u2348

def r5858 : Route 9 := (fun mask => (mask,id))

def c5858 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5858 : Upper (D 5) (R 5) [6,33,192,48,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,264] 13 (by decide) (choices 1) [1,2,4,8] r5858 c5858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2349
  · exact u2350
  · exact u2351
  · exact u2352

def b5859 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 35 196 265 22 56 120 184 312), lower := (rows 7 35 196 265 22 32 64 128 256), losses := [] }

theorem u5859 : Upper (D 5) (R 5) [6,33,192,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5859
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5860 : PairBound 9 := { available := 60, camps := [{ cop := 4, region := 228, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 265 26 60 124 188 316), lower := (rows 7 35 196 265 26 32 64 128 256), losses := [] }

theorem u5860 : Upper (D 5) (R 5) [6,33,192,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5860
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5861 : Route 9 := (fun mask => (mask,id))

def c5861 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5861 : Upper (D 5) (R 5) [6,33,192,257,12] 13 := by
  apply FastRouting.sound _ _ [6,33,192,257,12] 13 (by decide) (choices 1) [2,8,16] r5861 c5861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2353
  · exact u2354
  · exact u2355

def b5862 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 35 196 265 50 60 92 156 284), lower := (rows 7 35 196 265 50 32 64 128 256), losses := [] }

theorem u5862 : Upper (D 5) (R 5) [6,33,192,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5862
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5863 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 3, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 196 265 52 58 90 154 282), lower := (rows 7 35 196 265 52 32 64 128 256), losses := [] }

theorem u5863 : Upper (D 5) (R 5) [6,33,192,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5863
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5864 : Route 9 := (fun mask => (mask,id))

def c5864 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5864 : Upper (D 5) (R 5) [6,33,192,257,40] 13 := by
  apply FastRouting.sound _ _ [6,33,192,257,40] 13 (by decide) (choices 1) [2,4,8,16] r5864 c5864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2356
  · exact u2357
  · exact u2358
  · exact u2359

def b5865 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 35 196 266 21 56 120 184 312), lower := (rows 7 35 196 266 21 32 64 128 256), losses := [] }

theorem u5865 : Upper (D 5) (R 5) [6,33,192,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5865
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5866 : PairBound 9 := { available := 60, camps := [{ cop := 4, region := 228, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 266 25 60 124 188 316), lower := (rows 7 35 196 266 25 32 64 128 256), losses := [] }

theorem u5866 : Upper (D 5) (R 5) [6,33,192,258,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5866
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5867 : Route 9 := (fun mask => (mask,id))

def c5867 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5867 : Upper (D 5) (R 5) [6,33,192,258,12] 13 := by
  apply FastRouting.sound _ _ [6,33,192,258,12] 13 (by decide) (choices 1) [1,8,16] r5867 c5867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2360
  · exact u2361
  · exact u2362

def b5868 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 196 266 49 60 92 156 284), lower := (rows 7 35 196 266 49 32 64 128 256), losses := [] }

theorem u5868 : Upper (D 5) (R 5) [6,33,192,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5868
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5869 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 3, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 196 266 52 57 89 153 281), lower := (rows 7 35 196 266 52 32 64 128 256), losses := [] }

theorem u5869 : Upper (D 5) (R 5) [6,33,192,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5869
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5870 : Route 9 := (fun mask => (mask,id))

def c5870 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5870 : Upper (D 5) (R 5) [6,33,192,258,40] 13 := by
  apply FastRouting.sound _ _ [6,33,192,258,40] 13 (by decide) (choices 1) [1,4,8,16] r5870 c5870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2363
  · exact u2364
  · exact u2365
  · exact u2366

def b5871 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 268 19 56 120 184 312), lower := (rows 7 35 196 268 19 32 64 128 256), losses := [] }

theorem u5871 : Upper (D 5) (R 5) [6,33,192,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5871
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5872 : Route 9 := (fun mask => (mask,id))

def c5872 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5872 : Upper (D 5) (R 5) [6,33,192,260,9] 13 := by
  apply FastRouting.sound _ _ [6,33,192,260,9] 13 (by decide) (choices 1) [2,8,16] r5872 c5872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2367
  · exact u2368
  · exact u2369

def r5873 : Route 9 := (fun mask => (mask,id))

def c5873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5873 : Upper (D 5) (R 5) [6,33,192,260,10] 13 := by
  apply FastRouting.sound _ _ [6,33,192,260,10] 13 (by decide) (choices 1) [1,8,16] r5873 c5873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2370
  · exact u2371
  · exact u2372

def b5874 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 196 268 49 58 90 154 282), lower := (rows 7 35 196 268 49 32 64 128 256), losses := [] }

theorem u5874 : Upper (D 5) (R 5) [6,33,192,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5874
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5875 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 35 196 268 50 57 89 153 281), lower := (rows 7 35 196 268 50 32 64 128 256), losses := [] }

theorem u5875 : Upper (D 5) (R 5) [6,33,192,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5875
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5876 : Route 9 := (fun mask => (mask,id))

def c5876 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5876 : Upper (D 5) (R 5) [6,33,192,260,40] 13 := by
  apply FastRouting.sound _ _ [6,33,192,260,40] 13 (by decide) (choices 1) [1,2,8,16] r5876 c5876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2373
  · exact u2374
  · exact u2375
  · exact u2376

def b5877 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 280 19 44 108 172 300), lower := (rows 7 35 196 280 19 32 64 128 256), losses := [] }

theorem u5877 : Upper (D 5) (R 5) [6,33,192,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5877
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5878 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 35 196 280 21 42 106 170 298), lower := (rows 7 35 196 280 21 32 64 128 256), losses := [] }

theorem u5878 : Upper (D 5) (R 5) [6,33,192,272,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5878
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5879 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 35 196 280 22 41 105 169 297), lower := (rows 7 35 196 280 22 32 64 128 256), losses := [] }

theorem u5879 : Upper (D 5) (R 5) [6,33,192,272,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5879
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u5879
end Delivery.IrregularNine14.P05
