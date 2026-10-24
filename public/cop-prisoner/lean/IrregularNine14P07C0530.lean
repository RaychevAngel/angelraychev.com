import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0243
import IrregularNine14P07C0244
import IrregularNine14P07C0245

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r31800 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31800 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31800 : Upper (D 7) (R 7) [6,257,33,18,192] 13 := by
  apply FastRouting.sound _ _ [6,257,33,18,192] 13 (by decide) (choices 1) [8,64] r31800 c31800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14620
  · exact u14621

def b31801 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 259 37 42 88 240 208 208 464), lower := (rows 7 259 37 42 88 32 64 128 256), losses := [] }

theorem u31801 : Upper (D 7) (R 7) [6,257,33,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31802 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 259 37 42 208 248 216 216 472), lower := (rows 7 259 37 42 208 32 64 128 256), losses := [] }

theorem u31802 : Upper (D 7) (R 7) [6,257,33,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31803 : Route 9 := (fun mask => (mask,id))

def c31803 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31803 : Upper (D 7) (R 7) [6,257,33,48,66] 13 := by
  apply FastRouting.sound _ _ [6,257,33,48,66] 13 (by decide) (choices 1) [8,64,128] r31803 c31803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14622
  · exact u14623
  · exact u14624

def b31804 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 2, region := 451, targets := 32 }], pairs := [(0,5),(1,5),(3,0),(4,0)], upper := (rows 7 259 37 56 88 226 194 194 450), lower := (rows 7 259 37 56 88 32 64 128 256), losses := [] }

theorem u31804 : Upper (D 7) (R 7) [6,257,33,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31805 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31805 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31805 : Upper (D 7) (R 7) [6,257,33,48,192] 13 := by
  apply FastRouting.sound _ _ [6,257,33,48,192] 13 (by decide) (choices 1) [2,8,64] r31805 c31805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14625
  · exact u14626
  · exact u14627

def b31806 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 423, targets := 64 },{ cop := 0, region := 248, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 259 37 74 88 176 240 176 432), lower := (rows 7 259 37 74 88 32 64 128 256), losses := [] }

theorem u31806 : Upper (D 7) (R 7) [6,257,33,66,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31807 : Route 9 := (fun mask => (mask,id))

def c31807 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31807 : Upper (D 7) (R 7) [6,257,33,66,96] 13 := by
  apply FastRouting.sound _ _ [6,257,33,66,96] 13 (by decide) (choices 1) [8,16,128] r31807 c31807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14628
  · exact u14629
  · exact u14630

def r31808 : Route 9 := (fun mask => (mask,id))

def c31808 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31808 : Upper (D 7) (R 7) [6,257,33,66,136] 13 := by
  apply FastRouting.sound _ _ [6,257,33,66,136] 13 (by decide) (choices 1) [16,64,128] r31808 c31808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14631
  · exact u14632
  · exact u14633

def r31809 : Route 9 := (fun mask => (mask,id))

def c31809 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u31809 : Upper (D 7) (R 7) [6,257,33,66,160] 13 := by
  apply FastRouting.sound _ _ [6,257,33,66,160] 13 (by decide) (choices 1) [8,16,64,128] r31809 c31809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14634
  · exact u14635
  · exact u14636
  · exact u14637

def r31810 : Route 9 := (fun mask => (mask,id))

def c31810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31810 : Upper (D 7) (R 7) [6,257,33,66,192] 13 := by
  apply FastRouting.sound _ _ [6,257,33,66,192] 13 (by decide) (choices 1) [8,16,128] r31810 c31810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14638
  · exact u14639
  · exact u14640

def b31811 : PairBound 9 := { available := 162, camps := [{ cop := 6, region := 24, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 259 37 88 88 162 226 162 418), lower := (rows 7 259 37 88 88 32 64 128 256), losses := [] }

theorem u31811 : Upper (D 7) (R 7) [6,257,33,80,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31812 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 259 37 88 112 170 202 138 394), lower := (rows 7 259 37 88 112 32 64 128 256), losses := [] }

theorem u31812 : Upper (D 7) (R 7) [6,257,33,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m31813_128 : Upper (D 7) (R 7) [6,257,33,80,136,128] 13 :=
  permutation_upper _ _ _ [6,257,33,80,136,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14642

def r31813 : Route 9 := (fun mask => (mask,id))

def c31813 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31813 : Upper (D 7) (R 7) [6,257,33,80,136] 13 := by
  apply FastRouting.sound _ _ [6,257,33,80,136] 13 (by decide) (choices 1) [2,64,128] r31813 c31813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14641
  · exact u14642
  · exact m31813_128

def r31814 : Route 9 := (fun mask => (mask,id))

def c31814 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31814 : Upper (D 7) (R 7) [6,257,33,80,160] 13 := by
  apply FastRouting.sound _ _ [6,257,33,80,160] 13 (by decide) (choices 1) [2,8,64,128] r31814 c31814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14643
  · exact u14644
  · exact u14645
  · exact u14646

def b31815 : PairBound 9 := { available := 170, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 259 37 88 208 170 234 170 426), lower := (rows 7 259 37 88 208 32 64 128 256), losses := [] }

theorem u31815 : Upper (D 7) (R 7) [6,257,33,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31816 : Route 9 := (fun mask => (mask,id))

def c31816 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31816 : Upper (D 7) (R 7) [6,257,33,96,192] 13 := by
  apply FastRouting.sound _ _ [6,257,33,96,192] 13 (by decide) (choices 1) [2,8,16,128] r31816 c31816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14647
  · exact u14648
  · exact u14649
  · exact u14650

def b31817 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 259 37 200 208 58 122 186 314), lower := (rows 7 259 37 200 208 32 64 128 256), losses := [] }

theorem u31817 : Upper (D 7) (R 7) [6,257,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31818 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 259 44 25 50 224 192 192 448), lower := (rows 7 259 44 25 50 32 64 128 256), losses := [] }

theorem u31818 : Upper (D 7) (R 7) [6,257,40,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31819 : Route 9 := (fun mask => (mask,id))

def c31819 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31819 : Upper (D 7) (R 7) [6,257,40,17,66] 13 := by
  apply FastRouting.sound _ _ [6,257,40,17,66] 13 (by decide) (choices 1) [64,128] r31819 c31819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14651
  · exact u14652

def b31820 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 451, targets := 32 },{ cop := 0, region := 240, targets := 1 }], pairs := [(0,5),(1,5),(2,0),(4,0)], upper := (rows 7 259 44 25 112 226 194 194 450), lower := (rows 7 259 44 25 112 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 35 67 131 259), good := (rows 502 498 60 508 112 32 64 128 256) }] }

theorem u31820 : Upper (D 7) (R 7) [6,257,40,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31821 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31821 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31821 : Upper (D 7) (R 7) [6,257,40,17,192] 13 := by
  apply FastRouting.sound _ _ [6,257,40,17,192] 13 (by decide) (choices 1) [2,64] r31821 c31821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14653
  · exact u14654

def b31822 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 451, targets := 32 },{ cop := 3, region := 228, targets := 3 }], pairs := [(0,5),(1,5),(2,0),(2,1)], upper := (rows 7 259 44 26 49 224 192 192 448), lower := (rows 7 259 44 26 49 32 64 128 256), losses := [] }

theorem u31822 : Upper (D 7) (R 7) [6,257,40,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31823 : Route 9 := (fun mask => (mask,id))

def c31823 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31823 : Upper (D 7) (R 7) [6,257,40,18,65] 13 := by
  apply FastRouting.sound _ _ [6,257,40,18,65] 13 (by decide) (choices 1) [64,128] r31823 c31823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14655
  · exact u14656

def b31824 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 451, targets := 32 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,5),(1,5),(2,1),(4,1)], upper := (rows 7 259 44 26 112 225 193 193 449), lower := (rows 7 259 44 26 112 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 35 67 131 259), good := (rows 501 497 60 508 112 32 64 128 256) }] }

theorem u31824 : Upper (D 7) (R 7) [6,257,40,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31825 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31825 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31825 : Upper (D 7) (R 7) [6,257,40,18,192] 13 := by
  apply FastRouting.sound _ _ [6,257,40,18,192] 13 (by decide) (choices 1) [1,64] r31825 c31825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14657
  · exact u14658

def r31826 : Route 9 := (fun mask => (mask,id))

def c31826 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31826 : Upper (D 7) (R 7) [6,257,40,65,34] 13 := by
  apply FastRouting.sound _ _ [6,257,40,65,34] 13 (by decide) (choices 1) [16,64,128] r31826 c31826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14659
  · exact u14660
  · exact u14661

def r31827 : Route 9 := (fun mask => (mask,id))

def c31827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31827 : Upper (D 7) (R 7) [6,257,40,65,66] 13 := by
  apply FastRouting.sound _ _ [6,257,40,65,66] 13 (by decide) (choices 1) [16,128] r31827 c31827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14662
  · exact u14663

def r31828 : Route 9 := (fun mask => (mask,id))

def c31828 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31828 : Upper (D 7) (R 7) [6,257,40,65,96] 13 := by
  apply FastRouting.sound _ _ [6,257,40,65,96] 13 (by decide) (choices 1) [2,16,128] r31828 c31828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14664
  · exact u14665
  · exact u14666

def r31829 : Route 9 := (fun mask => (mask,id))

def c31829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31829 : Upper (D 7) (R 7) [6,257,40,65,130] 13 := by
  apply FastRouting.sound _ _ [6,257,40,65,130] 13 (by decide) (choices 1) [16,64,128] r31829 c31829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14667
  · exact u14668
  · exact u14669

def r31830 : Route 9 := (fun mask => (mask,id))

def c31830 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31830 : Upper (D 7) (R 7) [6,257,40,65,160] 13 := by
  apply FastRouting.sound _ _ [6,257,40,65,160] 13 (by decide) (choices 1) [2,16,64,128] r31830 c31830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14670
  · exact u14671
  · exact u14672
  · exact u14673

def r31831 : Route 9 := (fun mask => (mask,id))

def c31831 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31831 : Upper (D 7) (R 7) [6,257,40,65,192] 13 := by
  apply FastRouting.sound _ _ [6,257,40,65,192] 13 (by decide) (choices 1) [2,16,128] r31831 c31831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14674
  · exact u14675
  · exact u14676

def b31832 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 0, region := 240, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,1)], upper := (rows 7 259 44 74 49 240 208 208 464), lower := (rows 7 259 44 74 49 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 19 59 91 155 283), good := (rows 501 497 492 508 497 32 64 128 256) }] }

theorem u31832 : Upper (D 7) (R 7) [6,257,40,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31833 : Route 9 := (fun mask => (mask,id))

def c31833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31833 : Upper (D 7) (R 7) [6,257,40,66,65] 13 := by
  apply FastRouting.sound _ _ [6,257,40,66,65] 13 (by decide) (choices 1) [16,128] r31833 c31833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14677
  · exact u14678

def r31834 : Route 9 := (fun mask => (mask,id))

def c31834 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31834 : Upper (D 7) (R 7) [6,257,40,66,96] 13 := by
  apply FastRouting.sound _ _ [6,257,40,66,96] 13 (by decide) (choices 1) [1,16,128] r31834 c31834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14679
  · exact u14680
  · exact u14681

def r31835 : Route 9 := (fun mask => (mask,id))

def c31835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31835 : Upper (D 7) (R 7) [6,257,40,66,129] 13 := by
  apply FastRouting.sound _ _ [6,257,40,66,129] 13 (by decide) (choices 1) [16,64,128] r31835 c31835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14682
  · exact u14683
  · exact u14684

def r31836 : Route 9 := (fun mask => (mask,id))

def c31836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31836 : Upper (D 7) (R 7) [6,257,40,66,160] 13 := by
  apply FastRouting.sound _ _ [6,257,40,66,160] 13 (by decide) (choices 1) [1,16,64,128] r31836 c31836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14685
  · exact u14686
  · exact u14687
  · exact u14688

def r31837 : Route 9 := (fun mask => (mask,id))

def c31837 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31837 : Upper (D 7) (R 7) [6,257,40,66,192] 13 := by
  apply FastRouting.sound _ _ [6,257,40,66,192] 13 (by decide) (choices 1) [1,16,128] r31837 c31837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14689
  · exact u14690
  · exact u14691

def b31838 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 259 44 88 19 224 224 224 480), lower := (rows 7 259 44 88 19 32 64 128 256), losses := [] }

theorem u31838 : Upper (D 7) (R 7) [6,257,40,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31839 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 451, targets := 32 },{ cop := 4, region := 458, targets := 32 }], pairs := [(0,5),(1,5),(2,0),(3,5)], upper := (rows 7 259 44 88 49 226 194 194 450), lower := (rows 7 259 44 88 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 67 131 259), good := (rows 486 482 44 92 508 32 64 128 256) }] }

theorem u31839 : Upper (D 7) (R 7) [6,257,40,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31840 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 451, targets := 32 }], pairs := [(0,5),(1,5),(2,1),(3,1)], upper := (rows 7 259 44 88 50 225 193 193 449), lower := (rows 7 259 44 88 50 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 485 481 44 92 508 32 64 128 256) }] }

theorem u31840 : Upper (D 7) (R 7) [6,257,40,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31841 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 259 44 88 81 162 226 162 418), lower := (rows 7 259 44 88 81 32 64 128 256), losses := [] }

theorem u31841 : Upper (D 7) (R 7) [6,257,40,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31842 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 259 44 88 82 161 225 161 417), lower := (rows 7 259 44 88 82 32 64 128 256), losses := [] }

theorem u31842 : Upper (D 7) (R 7) [6,257,40,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31843 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 12, targets := 131 }], pairs := [(2,0),(2,1),(2,7),(3,0)], upper := (rows 7 259 44 88 112 163 195 131 387), lower := (rows 7 259 44 88 112 32 64 128 256), losses := [] }

theorem u31843 : Upper (D 7) (R 7) [6,257,40,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31844 : Route 9 := (fun mask => (mask,id))

def c31844 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31844 : Upper (D 7) (R 7) [6,257,40,80,129] 13 := by
  apply FastRouting.sound _ _ [6,257,40,80,129] 13 (by decide) (choices 1) [2,64,128] r31844 c31844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14692
  · exact u14693
  · exact u14694

def r31845 : Route 9 := (fun mask => (mask,id))

def c31845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31845 : Upper (D 7) (R 7) [6,257,40,80,130] 13 := by
  apply FastRouting.sound _ _ [6,257,40,80,130] 13 (by decide) (choices 1) [1,64,128] r31845 c31845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14695
  · exact u14696
  · exact u14697

def r31846 : Route 9 := (fun mask => (mask,id))

def c31846 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31846 : Upper (D 7) (R 7) [6,257,40,80,160] 13 := by
  apply FastRouting.sound _ _ [6,257,40,80,160] 13 (by decide) (choices 1) [1,2,64,128] r31846 c31846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14698
  · exact u14699
  · exact u14700
  · exact u14701

def b31847 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 259 44 88 208 163 227 163 419), lower := (rows 7 259 44 88 208 32 64 128 256), losses := [] }

theorem u31847 : Upper (D 7) (R 7) [6,257,40,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31848 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 236, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 259 44 200 19 240 240 240 496), lower := (rows 7 259 44 200 19 32 64 128 256), losses := [] }

theorem u31848 : Upper (D 7) (R 7) [6,257,40,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31849 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31849 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31849 : Upper (D 7) (R 7) [6,257,40,192,33] 13 := by
  apply FastRouting.sound _ _ [6,257,40,192,33] 13 (by decide) (choices 1) [2,16,64] r31849 c31849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14702
  · exact u14703
  · exact u14704

def r31850 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c31850 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31850 : Upper (D 7) (R 7) [6,257,40,192,34] 13 := by
  apply FastRouting.sound _ _ [6,257,40,192,34] 13 (by decide) (choices 1) [1,16,64] r31850 c31850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14705
  · exact u14706
  · exact u14707

def r31851 : Route 9 := (fun mask => (mask,id))

def c31851 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31851 : Upper (D 7) (R 7) [6,257,40,192,65] 13 := by
  apply FastRouting.sound _ _ [6,257,40,192,65] 13 (by decide) (choices 1) [2,16,128] r31851 c31851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14708
  · exact u14709
  · exact u14710

def r31852 : Route 9 := (fun mask => (mask,id))

def c31852 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31852 : Upper (D 7) (R 7) [6,257,40,192,66] 13 := by
  apply FastRouting.sound _ _ [6,257,40,192,66] 13 (by decide) (choices 1) [1,16,128] r31852 c31852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14711
  · exact u14712
  · exact u14713

def r31853 : Route 9 := (fun mask => (mask,id))

def c31853 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31853 : Upper (D 7) (R 7) [6,257,40,192,96] 13 := by
  apply FastRouting.sound _ _ [6,257,40,192,96] 13 (by decide) (choices 1) [1,2,16,128] r31853 c31853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14714
  · exact u14715
  · exact u14716
  · exact u14717

def b31854 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 259 44 200 208 51 115 179 307), lower := (rows 7 259 44 200 208 32 64 128 256), losses := [] }

theorem u31854 : Upper (D 7) (R 7) [6,257,40,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31855 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 244, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 100 11 56 240 208 208 464), lower := (rows 7 259 100 11 56 32 64 128 256), losses := [] }

theorem u31855 : Upper (D 7) (R 7) [6,257,96,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31856 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 244, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 100 11 152 240 240 240 496), lower := (rows 7 259 100 11 152 32 64 128 256), losses := [] }

theorem u31856 : Upper (D 7) (R 7) [6,257,96,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31857 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 244, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 100 11 176 248 216 216 472), lower := (rows 7 259 100 11 176 32 64 128 256), losses := [] }

theorem u31857 : Upper (D 7) (R 7) [6,257,96,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31858 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 259 100 25 26 224 224 224 480), lower := (rows 7 259 100 25 26 32 64 128 256), losses := [] }

theorem u31858 : Upper (D 7) (R 7) [6,257,96,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31859 : Route 9 := (fun mask => (mask,id))

def c31859 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31859 : Upper (D 7) (R 7) [6,257,96,17,34] 13 := by
  apply FastRouting.sound _ _ [6,257,96,17,34] 13 (by decide) (choices 1) [8,64,128] r31859 c31859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14718
  · exact u14719
  · exact u14720

#print axioms u31859
end Delivery.IrregularNine14.P07
