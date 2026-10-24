import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0046

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6420 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 133 265 400 34 88 216 344), lower := (rows 97 38 133 265 400 34 64 128 256), losses := [] }

theorem u6420 : Upper (D 9) (R 9) [96,36,129,257,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6420 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6421 : Route 9 := (fun mask => (mask,id))

def c6421 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6421 : Upper (D 9) (R 9) [96,36,129,257,384,8] 13 := by
  apply FastRouting.sound _ _ [96,36,129,257,384,8] 13 (by decide) (choices 1) [2,16] r6421 c6421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2760
  · exact u2761

def r6422 : Route 9 := (fun mask => (mask,id))

def c6422 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6422 : Upper (D 9) (R 9) [96,36,129,257,384,16] 13 := by
  apply FastRouting.sound _ _ [96,36,129,257,384,16] 13 (by decide) (choices 1) [2,8] r6422 c6422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2762
  · exact u2763

def b6423 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 133 265 400 96 90 154 282), lower := (rows 97 38 133 265 400 96 64 128 256), losses := [] }

theorem u6423 : Upper (D 9) (R 9) [96,36,129,257,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6423 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6424 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 38 133 266 336 33 216 152 408), lower := (rows 97 38 133 266 336 33 64 128 256), losses := [] }

theorem u6424 : Upper (D 9) (R 9) [96,36,129,258,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6424 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6425 : Route 9 := (fun mask => (mask,id))

def c6425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u6425 : Upper (D 9) (R 9) [96,36,129,258,320,8] 13 := by
  apply FastRouting.sound _ _ [96,36,129,258,320,8] 13 (by decide) (choices 1) [1,16,128] r6425 c6425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2764
  · exact u2765
  · exact u2766

def b6426 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 38 133 266 336 48 201 137 393), lower := (rows 97 38 133 266 336 48 64 128 256), losses := [] }

theorem u6426 : Upper (D 9) (R 9) [96,36,129,258,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6426 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6427 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 345, targets := 128 },{ cop := 2, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7),(4,7)], upper := (rows 97 38 133 266 336 160 89 153 281), lower := (rows 97 38 133 266 336 160 64 128 256), losses := [] }

theorem u6427 : Upper (D 9) (R 9) [96,36,129,258,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6427 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6428 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 38 133 266 400 33 88 216 344), lower := (rows 97 38 133 266 400 33 64 128 256), losses := [] }

theorem u6428 : Upper (D 9) (R 9) [96,36,129,258,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6428 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6429 : Route 9 := (fun mask => (mask,id))

def c6429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6429 : Upper (D 9) (R 9) [96,36,129,258,384,8] 13 := by
  apply FastRouting.sound _ _ [96,36,129,258,384,8] 13 (by decide) (choices 1) [1,16] r6429 c6429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2767
  · exact u2768

def r6430 : Route 9 := (fun mask => (mask,id))

def c6430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6430 : Upper (D 9) (R 9) [96,36,129,258,384,16] 13 := by
  apply FastRouting.sound _ _ [96,36,129,258,384,16] 13 (by decide) (choices 1) [1,8] r6430 c6430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2769
  · exact u2770

def b6431 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 133 266 400 96 89 153 281), lower := (rows 97 38 133 266 400 96 64 128 256), losses := [] }

theorem u6431 : Upper (D 9) (R 9) [96,36,129,258,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6431 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6432 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 472, targets := 33 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 38 133 328 400 33 90 154 282), lower := (rows 97 38 133 328 400 33 64 128 256), losses := [] }

theorem u6432 : Upper (D 9) (R 9) [96,36,129,320,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6432 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6433 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 133 328 400 34 89 153 281), lower := (rows 97 38 133 328 400 34 64 128 256), losses := [] }

theorem u6433 : Upper (D 9) (R 9) [96,36,129,320,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6433 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6434 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(4,6)], upper := (rows 97 38 133 328 400 40 83 147 275), lower := (rows 97 38 133 328 400 40 64 128 256), losses := [] }

theorem u6434 : Upper (D 9) (R 9) [96,36,129,320,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6434 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6435 : Route 9 := (fun mask => (mask,id))

def c6435 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6435 : Upper (D 9) (R 9) [96,36,129,320,384,16] 13 := by
  apply FastRouting.sound _ _ [96,36,129,320,384,16] 13 (by decide) (choices 1) [1,2,8] r6435 c6435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2771
  · exact u2772
  · exact u2773

def b6436 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 390, targets := 64 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 38 134 88 280 33 449 385 385), lower := (rows 97 38 134 88 280 33 64 128 256), losses := [] }

theorem u6436 : Upper (D 9) (R 9) [96,36,130,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6436 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6437 : PairBound 9 := { available := 257, camps := [{ cop := 5, region := 6, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(2,0),(2,6)], upper := (rows 97 38 134 88 280 160 321 385 257), lower := (rows 97 38 134 88 280 160 64 128 256), losses := [] }

theorem u6437 : Upper (D 9) (R 9) [96,36,130,80,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6437 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6438 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 97 38 134 88 280 288 193 129 385), lower := (rows 97 38 134 88 280 288 64 128 256), losses := [] }

theorem u6438 : Upper (D 9) (R 9) [96,36,130,80,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6438 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6439 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 4, region := 105, targets := 128 },{ cop := 3, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(3,5),(3,7),(4,5)], upper := (rows 97 38 134 88 400 33 329 393 265), lower := (rows 97 38 134 88 400 33 64 128 256), losses := [] }

theorem u6439 : Upper (D 9) (R 9) [96,36,130,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6439 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6440 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,6)], upper := (rows 97 38 134 88 400 40 321 385 257), lower := (rows 97 38 134 88 400 40 64 128 256), losses := [] }

theorem u6440 : Upper (D 9) (R 9) [96,36,130,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6440 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6441 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 38, targets := 65 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,0),(1,6),(2,0),(2,6),(3,5)], upper := (rows 97 38 134 88 400 288 73 137 265), lower := (rows 97 38 134 88 400 288 64 128 256), losses := [] }

theorem u6441 : Upper (D 9) (R 9) [96,36,130,80,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6441 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6442 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 38, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(2,0)], upper := (rows 97 38 134 137 273 40 336 464 336), lower := (rows 97 38 134 137 273 40 64 128 256), losses := [] }

theorem u6442 : Upper (D 9) (R 9) [96,36,130,129,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6442 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6443 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(3,5),(4,5),(4,7)], upper := (rows 97 38 134 137 273 48 328 456 328), lower := (rows 97 38 134 137 273 48 64 128 256), losses := [] }

theorem u6443 : Upper (D 9) (R 9) [96,36,130,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6443 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6444 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 38 134 137 273 96 344 408 280), lower := (rows 97 38 134 137 273 96 64 128 256), losses := [] }

theorem u6444 : Upper (D 9) (R 9) [96,36,130,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6444 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6445 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 3, region := 369, targets := 128 },{ cop := 4, region := 200, targets := 256 }], pairs := [(0,7),(3,5),(3,8),(4,5),(4,7)], upper := (rows 97 38 134 137 273 288 88 216 344), lower := (rows 97 38 134 137 273 288 64 128 256), losses := [] }

theorem u6445 : Upper (D 9) (R 9) [96,36,130,129,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6445 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6446 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 38, targets := 320 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,6),(1,8),(2,6),(2,8),(3,5)], upper := (rows 97 38 134 137 280 33 336 464 336), lower := (rows 97 38 134 137 280 33 64 128 256), losses := [] }

theorem u6446 : Upper (D 9) (R 9) [96,36,130,129,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6446 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6447 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(3,5),(4,5),(4,7)], upper := (rows 97 38 134 137 280 48 321 449 321), lower := (rows 97 38 134 137 280 48 64 128 256), losses := [] }

theorem u6447 : Upper (D 9) (R 9) [96,36,130,129,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6447 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6448 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 38 134 137 280 96 337 401 273), lower := (rows 97 38 134 137 280 96 64 128 256), losses := [] }

theorem u6448 : Upper (D 9) (R 9) [96,36,130,129,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6448 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6449 : Route 9 := (fun mask => (mask,id))

def c6449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6449 : Upper (D 9) (R 9) [96,36,130,129,264,256] 13 := by
  apply FastRouting.sound _ _ [96,36,130,129,264,256] 13 (by decide) (choices 1) [1,16] r6449 c6449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2774
  · exact u2775

def b6450 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 38, targets := 320 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,6),(1,8),(2,6),(2,8),(3,5)], upper := (rows 97 38 134 137 336 33 344 408 280), lower := (rows 97 38 134 137 336 33 64 128 256), losses := [] }

theorem u6450 : Upper (D 9) (R 9) [96,36,130,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6450 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6451 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 38, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(2,0)], upper := (rows 97 38 134 137 336 40 337 401 273), lower := (rows 97 38 134 137 336 40 64 128 256), losses := [] }

theorem u6451 : Upper (D 9) (R 9) [96,36,130,129,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6451 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6452 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 0, region := 392, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6)], upper := (rows 97 38 134 137 336 48 329 393 265), lower := (rows 97 38 134 137 336 48 64 128 256), losses := [] }

theorem u6452 : Upper (D 9) (R 9) [96,36,130,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6452 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6453 : Route 9 := (fun mask => (mask,id))

def c6453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6453 : Upper (D 9) (R 9) [96,36,130,129,320,256] 13 := by
  apply FastRouting.sound _ _ [96,36,130,129,320,256] 13 (by decide) (choices 1) [1,8,16] r6453 c6453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2776
  · exact u2777
  · exact u2778

def b6454 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 3, region := 369, targets := 128 },{ cop := 4, region := 200, targets := 1 }], pairs := [(0,7),(3,0),(3,5),(4,5),(4,7)], upper := (rows 97 38 134 152 273 33 328 456 328), lower := (rows 97 38 134 152 273 33 64 128 256), losses := [] }

theorem u6454 : Upper (D 9) (R 9) [96,36,130,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6454 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6455 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 38, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(2,0)], upper := (rows 97 38 134 152 273 40 321 449 321), lower := (rows 97 38 134 152 273 40 64 128 256), losses := [] }

theorem u6455 : Upper (D 9) (R 9) [96,36,130,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6455 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6456 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 38 134 152 273 96 329 393 265), lower := (rows 97 38 134 152 273 96 64 128 256), losses := [] }

theorem u6456 : Upper (D 9) (R 9) [96,36,130,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6456 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6457 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 3, region := 369, targets := 128 },{ cop := 4, region := 200, targets := 256 }], pairs := [(0,7),(3,5),(3,8),(4,5),(4,7)], upper := (rows 97 38 134 152 273 288 73 201 329), lower := (rows 97 38 134 152 273 288 64 128 256), losses := [] }

theorem u6457 : Upper (D 9) (R 9) [96,36,130,144,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6457 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6458 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 3, region := 369, targets := 128 },{ cop := 4, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(3,5),(4,5),(4,7)], upper := (rows 97 38 134 152 336 33 329 393 265), lower := (rows 97 38 134 152 336 33 64 128 256), losses := [] }

theorem u6458 : Upper (D 9) (R 9) [96,36,130,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6458 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6459 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 38, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(2,0)], upper := (rows 97 38 134 152 336 40 321 385 257), lower := (rows 97 38 134 152 336 40 64 128 256), losses := [] }

theorem u6459 : Upper (D 9) (R 9) [96,36,130,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6459 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6460 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,0),(3,5),(4,5),(4,7)], upper := (rows 97 38 134 152 336 288 73 137 265), lower := (rows 97 38 134 152 336 288 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 304 64 128 256), good := (rows 96 38 134 190 368 288 64 128 288) }] }

theorem u6460 : Upper (D 9) (R 9) [96,36,130,144,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6460 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6461 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 97 38 134 200 273 33 344 408 280), lower := (rows 97 38 134 200 273 33 64 128 256), losses := [] }

theorem u6461 : Upper (D 9) (R 9) [96,36,130,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6461 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6462 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 38 134 200 273 40 337 401 273), lower := (rows 97 38 134 200 273 40 64 128 256), losses := [] }

theorem u6462 : Upper (D 9) (R 9) [96,36,130,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6462 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6463 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 3, region := 305, targets := 128 }], pairs := [(0,7),(3,5),(4,5),(4,7)], upper := (rows 97 38 134 200 273 48 329 393 265), lower := (rows 97 38 134 200 273 48 64 128 256), losses := [] }

theorem u6463 : Upper (D 9) (R 9) [96,36,130,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6463 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6464 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 3, region := 305, targets := 128 },{ cop := 4, region := 200, targets := 256 }], pairs := [(0,7),(3,5),(3,8),(4,5),(4,7)], upper := (rows 97 38 134 200 273 288 89 153 281), lower := (rows 97 38 134 200 273 288 64 128 256), losses := [] }

theorem u6464 : Upper (D 9) (R 9) [96,36,130,192,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6464 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6465 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 97 38 134 200 280 33 337 401 273), lower := (rows 97 38 134 200 280 33 64 128 256), losses := [] }

theorem u6465 : Upper (D 9) (R 9) [96,36,130,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6465 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6466 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 38 134 200 280 48 321 385 257), lower := (rows 97 38 134 200 280 48 64 128 256), losses := [] }

theorem u6466 : Upper (D 9) (R 9) [96,36,130,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6466 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6467 : Route 9 := (fun mask => (mask,id))

def c6467 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6467 : Upper (D 9) (R 9) [96,36,130,192,264,256] 13 := by
  apply FastRouting.sound _ _ [96,36,130,192,264,256] 13 (by decide) (choices 1) [1,16] r6467 c6467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2779
  · exact u2780

def b6468 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 4, region := 41, targets := 128 },{ cop := 3, region := 208, targets := 1 }], pairs := [(0,7),(3,5),(3,7),(4,0),(4,5)], upper := (rows 97 38 134 265 336 33 216 152 408), lower := (rows 97 38 134 265 336 33 64 128 256), losses := [] }

theorem u6468 : Upper (D 9) (R 9) [96,36,130,257,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6468 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6469 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 4, region := 41, targets := 128 }], pairs := [(0,7),(3,5),(3,7),(4,5)], upper := (rows 97 38 134 265 336 40 209 145 401), lower := (rows 97 38 134 265 336 40 64 128 256), losses := [] }

theorem u6469 : Upper (D 9) (R 9) [96,36,130,257,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6469 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6470 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 0, region := 392, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6)], upper := (rows 97 38 134 265 336 48 201 137 393), lower := (rows 97 38 134 265 336 48 64 128 256), losses := [] }

theorem u6470 : Upper (D 9) (R 9) [96,36,130,257,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6470 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6471 : PairBound 9 := { available := 25, camps := [{ cop := 5, region := 6, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(2,0),(2,6)], upper := (rows 97 38 134 265 336 160 89 153 281), lower := (rows 97 38 134 265 336 160 64 128 256), losses := [] }

theorem u6471 : Upper (D 9) (R 9) [96,36,130,257,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6471 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6472 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 4, region := 105, targets := 128 },{ cop := 3, region := 208, targets := 1 }], pairs := [(0,7),(3,5),(3,7),(4,0),(4,5)], upper := (rows 97 38 134 265 400 33 88 216 344), lower := (rows 97 38 134 265 400 33 64 128 256), losses := [] }

theorem u6472 : Upper (D 9) (R 9) [96,36,130,257,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6472 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6473 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(3,5),(3,7),(4,5)], upper := (rows 97 38 134 265 400 40 81 209 337), lower := (rows 97 38 134 265 400 40 64 128 256), losses := [] }

theorem u6473 : Upper (D 9) (R 9) [96,36,130,257,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6473 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6474 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 38, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(2,0)], upper := (rows 97 38 134 265 400 48 73 201 329), lower := (rows 97 38 134 265 400 48 64 128 256), losses := [] }

theorem u6474 : Upper (D 9) (R 9) [96,36,130,257,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6474 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6475 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,6)], upper := (rows 97 38 134 265 400 96 89 153 281), lower := (rows 97 38 134 265 400 96 64 128 256), losses := [] }

theorem u6475 : Upper (D 9) (R 9) [96,36,130,257,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6475 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6476 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 3, region := 33, targets := 384 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(0,8),(3,5),(3,7),(4,5)], upper := (rows 97 38 134 328 400 33 89 153 281), lower := (rows 97 38 134 328 400 33 64 128 256), losses := [] }

theorem u6476 : Upper (D 9) (R 9) [96,36,130,320,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6476 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6477 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,6)], upper := (rows 97 38 134 328 400 40 81 145 273), lower := (rows 97 38 134 328 400 40 64 128 256), losses := [] }

theorem u6477 : Upper (D 9) (R 9) [96,36,130,320,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6477 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6478 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 38, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(2,0)], upper := (rows 97 38 134 328 400 48 73 137 265), lower := (rows 97 38 134 328 400 48 64 128 256), losses := [] }

theorem u6478 : Upper (D 9) (R 9) [96,36,130,320,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6478 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6479 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 33, targets := 256 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(2,5),(3,7)], upper := (rows 97 38 140 88 146 33 321 385 257), lower := (rows 97 38 140 88 146 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 22 10 18 0 97 161 289), good := (rows 449 478 140 92 158 449 64 128 256) }] }

theorem u6479 : Upper (D 9) (R 9) [96,36,136,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6479 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u6479
end Delivery.IrregularNine14.P09
