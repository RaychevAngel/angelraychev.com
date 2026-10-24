import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0075
import IrregularNine14P01C0076

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7800 : PairBound 9 := { available := 109, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 386 22 138 125 109 109 237 365), lower := (rows 113 386 22 138 16 32 64 128 256), losses := [] }

theorem u7800 : Upper (D 1) (R 1) [112,384,18,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7800
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7801 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7801 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7801 : Upper (D 1) (R 1) [112,384,18,132] 13 := by
  apply FastRouting.sound _ _ [112,384,18,132] 13 (by decide) (choices 1) [1,2,8,32] r7801 c7801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4505
  · exact u4506
  · exact u4507
  · exact u4508

def r7802 : Route 9 := (fun mask => (mask,id))

def c7802 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7802 : Upper (D 1) (R 1) [112,384,18,160] 13 := by
  apply FastRouting.sound _ _ [112,384,18,160] 13 (by decide) (choices 1) [1,2,4,8,64] r7802 c7802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4509
  · exact u4510
  · exact u4511
  · exact u4512
  · exact u4513

def b7803 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 386 28 44 211 227 195 195 451), lower := (rows 113 386 28 44 16 32 64 128 256), losses := [] }

theorem u7803 : Upper (D 1) (R 1) [112,384,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7803
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7804 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 386 28 104 151 167 199 135 391), lower := (rows 113 386 28 104 16 32 64 128 256), losses := [] }

theorem u7804 : Upper (D 1) (R 1) [112,384,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7804
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7805 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 113 386 28 137 118 102 102 230 358), lower := (rows 113 386 28 137 16 32 64 128 256), losses := [] }

theorem u7805 : Upper (D 1) (R 1) [112,384,24,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7805
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7806 : PairBound 9 := { available := 103, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 386 28 138 119 103 103 231 359), lower := (rows 113 386 28 138 16 32 64 128 256), losses := [] }

theorem u7806 : Upper (D 1) (R 1) [112,384,24,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7806
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7807 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 386, targets := 16 }], pairs := [(1,4)], upper := (rows 113 386 28 140 115 99 99 227 355), lower := (rows 113 386 28 140 16 32 64 128 256), losses := [] }

theorem u7807 : Upper (D 1) (R 1) [112,384,24,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7807
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7808 : Route 9 := (fun mask => (mask,id))

def c7808 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7808 : Upper (D 1) (R 1) [112,384,24,160] 13 := by
  apply FastRouting.sound _ _ [112,384,24,160] 13 (by decide) (choices 1) [1,2,4,64] r7808 c7808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4514
  · exact u4515
  · exact u4516
  · exact u4517

def b7809 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 386 52 137 94 110 78 206 334), lower := (rows 113 386 52 137 16 32 64 128 256), losses := [] }

theorem u7809 : Upper (D 1) (R 1) [112,384,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7809
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7810 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 386 52 140 91 107 75 203 331), lower := (rows 113 386 52 140 16 32 64 128 256), losses := [] }

theorem u7810 : Upper (D 1) (R 1) [112,384,48,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7810
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7811 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 386 52 200 31 47 79 143 271), lower := (rows 113 386 52 200 16 32 64 128 256), losses := [] }

theorem u7811 : Upper (D 1) (R 1) [112,384,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7811
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7812 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 263 11 52 26 240 224 224 224 480), lower := (rows 263 11 52 26 16 32 64 128 256), losses := [] }

theorem u7812 : Upper (D 1) (R 1) [262,9,48,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7812
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7813 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 263 11 52 56 210 226 194 194 450), lower := (rows 263 11 52 56 16 32 64 128 256), losses := [] }

theorem u7813 : Upper (D 1) (R 1) [262,9,48,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7813
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7814 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 263 11 52 74 240 240 240 240 496), lower := (rows 263 11 52 74 16 32 64 128 256), losses := [] }

theorem u7814 : Upper (D 1) (R 1) [262,9,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7814
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7815 : Route 9 := (fun mask => (mask,id))

def c7815 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7815 : Upper (D 1) (R 1) [262,9,48,80] 13 := by
  apply FastRouting.sound _ _ [262,9,48,80] 13 (by decide) (choices 1) [2,32,64,128] r7815 c7815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4518
  · exact u4519
  · exact u4520
  · exact u4521

def r7816 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7816 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7816 : Upper (D 1) (R 1) [262,9,48,192] 13 := by
  apply FastRouting.sound _ _ [262,9,48,192] 13 (by decide) (choices 1) [2,32,64] r7816 c7816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4522
  · exact u4523
  · exact u4524

def b7817 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 263 19 44 26 240 224 224 224 480), lower := (rows 263 19 44 26 16 32 64 128 256), losses := [] }

theorem u7817 : Upper (D 1) (R 1) [262,17,40,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7817
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7818 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 263 19 44 42 208 240 208 208 464), lower := (rows 263 19 44 42 16 32 64 128 256), losses := [] }

theorem u7818 : Upper (D 1) (R 1) [262,17,40,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7818
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7819 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 263 19 44 56 210 226 194 194 450), lower := (rows 263 19 44 56 16 32 64 128 256), losses := [] }

theorem u7819 : Upper (D 1) (R 1) [262,17,40,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7819
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7820 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 180, targets := 2 }], pairs := [(2,1)], upper := (rows 263 19 44 74 240 240 240 240 496), lower := (rows 263 19 44 74 16 32 64 128 256), losses := [] }

theorem u7820 : Upper (D 1) (R 1) [262,17,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7820
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7821 : Route 9 := (fun mask => (mask,id))

def c7821 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7821 : Upper (D 1) (R 1) [262,17,40,80] 13 := by
  apply FastRouting.sound _ _ [262,17,40,80] 13 (by decide) (choices 1) [2,32,64,128] r7821 c7821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4525
  · exact u4526
  · exact u4527
  · exact u4528

def b7822 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 263 19 44 104 210 242 210 210 466), lower := (rows 263 19 44 104 16 32 64 128 256), losses := [] }

theorem u7822 : Upper (D 1) (R 1) [262,17,40,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7822
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7823 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7823 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7823 : Upper (D 1) (R 1) [262,17,40,192] 13 := by
  apply FastRouting.sound _ _ [262,17,40,192] 13 (by decide) (choices 1) [2,32,64] r7823 c7823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4529
  · exact u4530
  · exact u4531

def b7824 : PairBound 9 := { available := 232, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 263 19 100 26 248 232 232 232 488), lower := (rows 263 19 100 26 16 32 64 128 256), losses := [] }

theorem u7824 : Upper (D 1) (R 1) [262,17,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7824
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7825 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 212, targets := 2 }], pairs := [(2,1)], upper := (rows 263 19 100 42 216 248 216 216 472), lower := (rows 263 19 100 42 16 32 64 128 256), losses := [] }

theorem u7825 : Upper (D 1) (R 1) [262,17,96,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7825
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7826 : Route 9 := (fun mask => (mask,id))

def c7826 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7826 : Upper (D 1) (R 1) [262,17,96,48] 13 := by
  apply FastRouting.sound _ _ [262,17,96,48] 13 (by decide) (choices 1) [2,8,64,128] r7826 c7826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4532
  · exact u4533
  · exact u4534
  · exact u4535

def b7827 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 263 19 100 104 154 186 218 154 410), lower := (rows 263 19 100 104 16 32 64 128 256), losses := [] }

theorem u7827 : Upper (D 1) (R 1) [262,17,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7827
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7828 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 116, targets := 2 }], pairs := [(2,1)], upper := (rows 263 19 100 138 248 248 248 248 504), lower := (rows 263 19 100 138 16 32 64 128 256), losses := [] }

theorem u7828 : Upper (D 1) (R 1) [262,17,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7828
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7829 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7829 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7829 : Upper (D 1) (R 1) [262,17,96,144] 13 := by
  apply FastRouting.sound _ _ [262,17,96,144] 13 (by decide) (choices 1) [2,8,32,128] r7829 c7829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4536
  · exact u4537
  · exact u4538
  · exact u4539

def r7830 : Route 9 := (fun mask => (mask,id))

def c7830 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7830 : Upper (D 1) (R 1) [262,17,96,160] 13 := by
  apply FastRouting.sound _ _ [262,17,96,160] 13 (by decide) (choices 1) [2,8,64,128] r7830 c7830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4540
  · exact u4541
  · exact u4542
  · exact u4543

def b7831 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 263 26 37 26 240 224 224 224 480), lower := (rows 263 26 37 26 16 32 64 128 256), losses := [] }

theorem u7831 : Upper (D 1) (R 1) [262,24,33,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7831
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7832 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 263 26 37 42 208 240 208 208 464), lower := (rows 263 26 37 42 16 32 64 128 256), losses := [] }

theorem u7832 : Upper (D 1) (R 1) [262,24,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7832
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7833 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 485, targets := 16 }], pairs := [(0,4)], upper := (rows 263 26 37 56 210 226 194 194 450), lower := (rows 263 26 37 56 16 32 64 128 256), losses := [] }

theorem u7833 : Upper (D 1) (R 1) [262,24,33,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7833
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7834 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 263 26 37 74 240 240 240 240 496), lower := (rows 263 26 37 74 16 32 64 128 256), losses := [] }

theorem u7834 : Upper (D 1) (R 1) [262,24,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7834
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7835 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 263 26 37 88 242 226 226 226 482), lower := (rows 263 26 37 88 16 32 64 128 256), losses := [] }

theorem u7835 : Upper (D 1) (R 1) [262,24,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7835
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7836 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 146, targets := 32 }], pairs := [(1,5)], upper := (rows 263 26 37 104 210 242 210 210 466), lower := (rows 263 26 37 104 16 32 64 128 256), losses := [] }

theorem u7836 : Upper (D 1) (R 1) [262,24,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7836
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7837 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7837 : Upper (D 1) (R 1) [262,24,33,192] 13 := by
  apply FastRouting.sound _ _ [262,24,33,192] 13 (by decide) (choices 1) [2,32,64] r7837 c7837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4544
  · exact u4545
  · exact u4546

def b7838 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 263 26 100 11 240 240 240 240 496), lower := (rows 263 26 100 11 16 32 64 128 256), losses := [] }

theorem u7838 : Upper (D 1) (R 1) [262,24,96,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7838
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7839 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 263 26 100 25 242 226 226 226 482), lower := (rows 263 26 100 25 16 32 64 128 256), losses := [] }

theorem u7839 : Upper (D 1) (R 1) [262,24,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7839
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7840 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 263 26 100 26 241 225 225 225 481), lower := (rows 263 26 100 26 16 32 64 128 256), losses := [] }

theorem u7840 : Upper (D 1) (R 1) [262,24,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7840
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7841 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 263 26 100 41 210 242 210 210 466), lower := (rows 263 26 100 41 16 32 64 128 256), losses := [] }

theorem u7841 : Upper (D 1) (R 1) [262,24,96,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7841
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7842 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 263 26 100 42 209 241 209 209 465), lower := (rows 263 26 100 42 16 32 64 128 256), losses := [] }

theorem u7842 : Upper (D 1) (R 1) [262,24,96,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7842
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7843 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 263 26 100 56 211 227 195 195 451), lower := (rows 263 26 100 56 16 32 64 128 256), losses := [] }

theorem u7843 : Upper (D 1) (R 1) [262,24,96,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7843
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7844 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 263 26 100 104 147 179 211 147 403), lower := (rows 263 26 100 104 16 32 64 128 256), losses := [] }

theorem u7844 : Upper (D 1) (R 1) [262,24,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7844
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7845 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7845 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7845 : Upper (D 1) (R 1) [262,24,96,129] 13 := by
  apply FastRouting.sound _ _ [262,24,96,129] 13 (by decide) (choices 1) [2,32,128] r7845 c7845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4547
  · exact u4548
  · exact u4549

def b7846 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1)], upper := (rows 263 26 100 138 241 241 241 241 497), lower := (rows 263 26 100 138 16 32 64 128 256), losses := [] }

theorem u7846 : Upper (D 1) (R 1) [262,24,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7846
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7847 : PairBound 9 := { available := 227, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 263 26 100 152 243 227 227 227 483), lower := (rows 263 26 100 152 16 32 64 128 256), losses := [] }

theorem u7847 : Upper (D 1) (R 1) [262,24,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7847
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7848 : Route 9 := (fun mask => (mask,id))

def c7848 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7848 : Upper (D 1) (R 1) [262,24,96,160] 13 := by
  apply FastRouting.sound _ _ [262,24,96,160] 13 (by decide) (choices 1) [1,2,64,128] r7848 c7848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4550
  · exact u4551
  · exact u4552
  · exact u4553

def b7849 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 263 50 13 26 240 224 224 224 480), lower := (rows 263 50 13 26 16 32 64 128 256), losses := [] }

theorem u7849 : Upper (D 1) (R 1) [262,48,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7849
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7850 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 263 50 13 56 210 226 194 194 450), lower := (rows 263 50 13 56 16 32 64 128 256), losses := [] }

theorem u7850 : Upper (D 1) (R 1) [262,48,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7850
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7851 : Route 9 := (fun mask => (mask,id))

def c7851 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7851 : Upper (D 1) (R 1) [262,48,9,66] 13 := by
  apply FastRouting.sound _ _ [262,48,9,66] 13 (by decide) (choices 1) [32,64,128] r7851 c7851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4554
  · exact u4555
  · exact u4556

def r7852 : Route 9 := (fun mask => (mask,id))

def c7852 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7852 : Upper (D 1) (R 1) [262,48,9,80] 13 := by
  apply FastRouting.sound _ _ [262,48,9,80] 13 (by decide) (choices 1) [2,32,64,128] r7852 c7852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4557
  · exact u4558
  · exact u4559
  · exact u4560

def r7853 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7853 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7853 : Upper (D 1) (R 1) [262,48,9,192] 13 := by
  apply FastRouting.sound _ _ [262,48,9,192] 13 (by decide) (choices 1) [2,32,64] r7853 c7853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4561
  · exact u4562
  · exact u4563

def b7854 : PairBound 9 := { available := 232, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 263 50 69 26 248 232 232 232 488), lower := (rows 263 50 69 26 16 32 64 128 256), losses := [] }

theorem u7854 : Upper (D 1) (R 1) [262,48,65,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7854
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7855 : PairBound 9 := { available := 202, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 263 50 69 56 218 234 202 202 458), lower := (rows 263 50 69 56 16 32 64 128 256), losses := [] }

theorem u7855 : Upper (D 1) (R 1) [262,48,65,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7855
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7856 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 69 74 184 184 248 184 440), lower := (rows 263 50 69 74 16 32 64 128 256), losses := [] }

theorem u7856 : Upper (D 1) (R 1) [262,48,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7856
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7857 : PairBound 9 := { available := 170, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 69 88 186 170 234 170 426), lower := (rows 263 50 69 88 16 32 64 128 256), losses := [] }

theorem u7857 : Upper (D 1) (R 1) [262,48,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7857
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7858 : Route 9 := (fun mask => (mask,id))

def c7858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u7858 : Upper (D 1) (R 1) [262,48,65,130] 13 := by
  apply FastRouting.sound _ _ [262,48,65,130] 13 (by decide) (choices 1) [8,32,64,128] r7858 c7858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4564
  · exact u4565
  · exact u4566
  · exact u4567

def r7859 : Route 9 := (fun mask => (mask,id))

def c7859 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7859 : Upper (D 1) (R 1) [262,48,65,144] 13 := by
  apply FastRouting.sound _ _ [262,48,65,144] 13 (by decide) (choices 1) [2,8,32,64,128] r7859 c7859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4568
  · exact u4569
  · exact u4570
  · exact u4571
  · exact u4572

#print axioms u7859
end Delivery.IrregularNine14.P01
