import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0077
import IrregularNine14P01C0078
import IrregularNine14P01C0079

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7980 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 184, targets := 2 }], pairs := [(3,1)], upper := (rows 275 35 70 104 156 188 220 156 412), lower := (rows 275 35 70 104 16 32 64 128 256), losses := [] }

theorem u7980 : Upper (D 1) (R 1) [274,33,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7980
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7981 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 184, targets := 2 }], pairs := [(3,1)], upper := (rows 275 35 70 140 248 248 248 248 504), lower := (rows 275 35 70 140 16 32 64 128 256), losses := [] }

theorem u7981 : Upper (D 1) (R 1) [274,33,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7981
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7982 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 184, targets := 2 }], pairs := [(3,1)], upper := (rows 275 35 70 152 252 236 236 236 492), lower := (rows 275 35 70 152 16 32 64 128 256), losses := [] }

theorem u7982 : Upper (D 1) (R 1) [274,33,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7982
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7983 : PairBound 9 := { available := 220, camps := [{ cop := 2, region := 184, targets := 2 }], pairs := [(3,1)], upper := (rows 275 35 70 168 220 252 220 220 476), lower := (rows 275 35 70 168 16 32 64 128 256), losses := [] }

theorem u7983 : Upper (D 1) (R 1) [274,33,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7983
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7984 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 184, targets := 2 }], pairs := [(3,1)], upper := (rows 275 35 70 200 188 188 252 188 444), lower := (rows 275 35 70 200 16 32 64 128 256), losses := [] }

theorem u7984 : Upper (D 1) (R 1) [274,33,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7984
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7985 : PairBound 9 := { available := 178, camps := [{ cop := 6, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 76 76 178 178 242 178 434), lower := (rows 275 35 76 76 16 32 64 128 256), losses := [] }

theorem u7985 : Upper (D 1) (R 1) [274,33,72,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7985
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7986 : PairBound 9 := { available := 166, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 76 88 182 166 230 166 422), lower := (rows 275 35 76 88 16 32 64 128 256), losses := [] }

theorem u7986 : Upper (D 1) (R 1) [274,33,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7986
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7987 : PairBound 9 := { available := 150, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 76 104 150 182 214 150 406), lower := (rows 275 35 76 104 16 32 64 128 256), losses := [] }

theorem u7987 : Upper (D 1) (R 1) [274,33,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7987
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m7988_128 : Upper (D 1) (R 1) [274,33,72,132,128] 13 :=
  permutation_upper _ _ _ [274,33,72,132,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4681

def r7988 : Route 9 := (fun mask => (mask,id))

def c7988 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7988 : Upper (D 1) (R 1) [274,33,72,132] 13 := by
  apply FastRouting.sound _ _ [274,33,72,132] 13 (by decide) (choices 1) [2,32,64,128] r7988 c7988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4679
  · exact u4680
  · exact u4681
  · exact m7988_128

def r7989 : Route 9 := (fun mask => (mask,id))

def c7989 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u7989 : Upper (D 1) (R 1) [274,33,72,144] 13 := by
  apply FastRouting.sound _ _ [274,33,72,144] 13 (by decide) (choices 1) [2,4,32,64,128] r7989 c7989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4682
  · exact u4683
  · exact u4684
  · exact u4685
  · exact u4686

def r7990 : Route 9 := (fun mask => (mask,id))

def c7990 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7990 : Upper (D 1) (R 1) [274,33,72,160] 13 := by
  apply FastRouting.sound _ _ [274,33,72,160] 13 (by decide) (choices 1) [2,4,64,128] r7990 c7990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4687
  · exact u4688
  · exact u4689
  · exact u4690

def b7991 : PairBound 9 := { available := 182, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 76 200 182 182 246 182 438), lower := (rows 275 35 76 200 16 32 64 128 256), losses := [] }

theorem u7991 : Upper (D 1) (R 1) [274,33,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7991
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7992 : Route 9 := (fun mask => (mask,id))

def c7992 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7992 : Upper (D 1) (R 1) [274,33,80,96] 13 := by
  apply FastRouting.sound _ _ [274,33,80,96] 13 (by decide) (choices 1) [2,4,8,128] r7992 c7992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4691
  · exact u4692
  · exact u4693
  · exact u4694

def r7993 : Route 9 := (fun mask => (mask,id))

def c7993 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 256 => 8 | _ => 0)

theorem u7993 : Upper (D 1) (R 1) [274,33,80,160] 13 := by
  apply FastRouting.sound _ _ [274,33,80,160] 13 (by decide) (choices 1) [2,4,8,64,128] r7993 c7993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4695
  · exact u4696
  · exact u4697
  · exact u4698
  · exact u4699

def r7994 : Route 9 := (fun mask => (mask,id))

def c7994 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 256 => 8 | _ => 0)

theorem u7994 : Upper (D 1) (R 1) [274,33,80,192] 13 := by
  apply FastRouting.sound _ _ [274,33,80,192] 13 (by decide) (choices 1) [2,4,8,32,128] r7994 c7994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4700
  · exact u4701
  · exact u4702
  · exact u4703
  · exact u4704

def r7995 : Route 9 := (fun mask => (mask,id))

def c7995 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7995 : Upper (D 1) (R 1) [274,33,96,192] 13 := by
  apply FastRouting.sound _ _ [274,33,96,192] 13 (by decide) (choices 1) [2,4,8,128] r7995 c7995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4705
  · exact u4706
  · exact u4707
  · exact u4708

def b7996 : PairBound 9 := { available := 62, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 275 35 196 200 62 62 126 190 318), lower := (rows 275 35 196 200 16 32 64 128 256), losses := [] }

theorem u7996 : Upper (D 1) (R 1) [274,33,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7996
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7997 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 13 26 240 224 224 224 480), lower := (rows 275 38 13 26 16 32 64 128 256), losses := [] }

theorem u7997 : Upper (D 1) (R 1) [274,36,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7997
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7998 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 38 13 42 208 240 208 208 464), lower := (rows 275 38 13 42 16 32 64 128 256), losses := [] }

theorem u7998 : Upper (D 1) (R 1) [274,36,9,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7998
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7999 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 38 13 56 210 226 194 194 450), lower := (rows 275 38 13 56 16 32 64 128 256), losses := [] }

theorem u7999 : Upper (D 1) (R 1) [274,36,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7999
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8000 : Route 9 := (fun mask => (mask,id))

def c8000 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8000 : Upper (D 1) (R 1) [274,36,9,66] 13 := by
  apply FastRouting.sound _ _ [274,36,9,66] 13 (by decide) (choices 1) [32,64,128] r8000 c8000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4709
  · exact u4710
  · exact u4711

def b8001 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 13 88 242 226 226 226 482), lower := (rows 275 38 13 88 16 32 64 128 256), losses := [] }

theorem u8001 : Upper (D 1) (R 1) [274,36,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8001
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8002 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 38 13 104 210 242 210 210 466), lower := (rows 275 38 13 104 16 32 64 128 256), losses := [] }

theorem u8002 : Upper (D 1) (R 1) [274,36,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8002
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8003 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8003 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8003 : Upper (D 1) (R 1) [274,36,9,192] 13 := by
  apply FastRouting.sound _ _ [274,36,9,192] 13 (by decide) (choices 1) [2,32,64] r8003 c8003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4712
  · exact u4713
  · exact u4714

def b8004 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 275 38 69 26 248 232 232 232 488), lower := (rows 275 38 69 26 16 32 64 128 256), losses := [] }

theorem u8004 : Upper (D 1) (R 1) [274,36,65,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8004
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8005 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 38 69 42 216 248 216 216 472), lower := (rows 275 38 69 42 16 32 64 128 256), losses := [] }

theorem u8005 : Upper (D 1) (R 1) [274,36,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8005
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8006 : Route 9 := (fun mask => (mask,id))

def c8006 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8006 : Upper (D 1) (R 1) [274,36,65,48] 13 := by
  apply FastRouting.sound _ _ [274,36,65,48] 13 (by decide) (choices 1) [2,8,64,128] r8006 c8006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4715
  · exact u4716
  · exact u4717
  · exact u4718

def b8007 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 275 38 69 74 184 184 248 184 440), lower := (rows 275 38 69 74 16 32 64 128 256), losses := [] }

theorem u8007 : Upper (D 1) (R 1) [274,36,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8007
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8008 : Route 9 := (fun mask => (mask,id))

def c8008 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8008 : Upper (D 1) (R 1) [274,36,65,80] 13 := by
  apply FastRouting.sound _ _ [274,36,65,80] 13 (by decide) (choices 1) [2,8,32,128] r8008 c8008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4719
  · exact u4720
  · exact u4721
  · exact u4722

def r8009 : Route 9 := (fun mask => (mask,id))

def c8009 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8009 : Upper (D 1) (R 1) [274,36,65,96] 13 := by
  apply FastRouting.sound _ _ [274,36,65,96] 13 (by decide) (choices 1) [2,8,128] r8009 c8009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4723
  · exact u4724
  · exact u4725

def r8010 : Route 9 := (fun mask => (mask,id))

def c8010 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u8010 : Upper (D 1) (R 1) [274,36,65,130] 13 := by
  apply FastRouting.sound _ _ [274,36,65,130] 13 (by decide) (choices 1) [8,32,64,128] r8010 c8010
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4726
  · exact u4727
  · exact u4728
  · exact u4729

def r8011 : Route 9 := (fun mask => (mask,id))

def c8011 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u8011 : Upper (D 1) (R 1) [274,36,65,144] 13 := by
  apply FastRouting.sound _ _ [274,36,65,144] 13 (by decide) (choices 1) [2,8,32,64,128] r8011 c8011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4730
  · exact u4731
  · exact u4732
  · exact u4733
  · exact u4734

def r8012 : Route 9 := (fun mask => (mask,id))

def c8012 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8012 : Upper (D 1) (R 1) [274,36,65,160] 13 := by
  apply FastRouting.sound _ _ [274,36,65,160] 13 (by decide) (choices 1) [2,8,64,128] r8012 c8012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4735
  · exact u4736
  · exact u4737
  · exact u4738

def r8013 : Route 9 := (fun mask => (mask,id))

def c8013 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8013 : Upper (D 1) (R 1) [274,36,65,192] 13 := by
  apply FastRouting.sound _ _ [274,36,65,192] 13 (by decide) (choices 1) [2,8,32,128] r8013 c8013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4739
  · exact u4740
  · exact u4741
  · exact u4742

def b8014 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 38 76 11 240 240 240 240 496), lower := (rows 275 38 76 11 16 32 64 128 256), losses := [] }

theorem u8014 : Upper (D 1) (R 1) [274,36,72,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8014
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8015 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 275 38 76 25 242 226 226 226 482), lower := (rows 275 38 76 25 16 32 64 128 256), losses := [] }

theorem u8015 : Upper (D 1) (R 1) [274,36,72,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8015
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8016 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 275 38 76 26 241 225 225 225 481), lower := (rows 275 38 76 26 16 32 64 128 256), losses := [] }

theorem u8016 : Upper (D 1) (R 1) [274,36,72,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8016
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8017 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 38 76 41 210 242 210 210 466), lower := (rows 275 38 76 41 16 32 64 128 256), losses := [] }

theorem u8017 : Upper (D 1) (R 1) [274,36,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8017
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8018 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 38 76 42 209 241 209 209 465), lower := (rows 275 38 76 42 16 32 64 128 256), losses := [] }

theorem u8018 : Upper (D 1) (R 1) [274,36,72,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8018
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8019 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 38 76 56 211 227 195 195 451), lower := (rows 275 38 76 56 16 32 64 128 256), losses := [] }

theorem u8019 : Upper (D 1) (R 1) [274,36,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8019
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8020 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 76 73 178 178 242 178 434), lower := (rows 275 38 76 73 16 32 64 128 256), losses := [] }

theorem u8020 : Upper (D 1) (R 1) [274,36,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8020
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8021 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 76 74 177 177 241 177 433), lower := (rows 275 38 76 74 16 32 64 128 256), losses := [] }

theorem u8021 : Upper (D 1) (R 1) [274,36,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8021
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8022 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 76 88 179 163 227 163 419), lower := (rows 275 38 76 88 16 32 64 128 256), losses := [] }

theorem u8022 : Upper (D 1) (R 1) [274,36,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8022
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8023 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 76 104 147 179 211 147 403), lower := (rows 275 38 76 104 16 32 64 128 256), losses := [] }

theorem u8023 : Upper (D 1) (R 1) [274,36,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8023
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8024 : Route 9 := (fun mask => (mask,id))

def c8024 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8024 : Upper (D 1) (R 1) [274,36,72,129] 13 := by
  apply FastRouting.sound _ _ [274,36,72,129] 13 (by decide) (choices 1) [2,32,64,128] r8024 c8024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4743
  · exact u4744
  · exact u4745
  · exact u4746

def r8025 : Route 9 := (fun mask => (mask,id))

def c8025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8025 : Upper (D 1) (R 1) [274,36,72,130] 13 := by
  apply FastRouting.sound _ _ [274,36,72,130] 13 (by decide) (choices 1) [1,32,64,128] r8025 c8025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4747
  · exact u4748
  · exact u4749
  · exact u4750

def r8026 : Route 9 := (fun mask => (mask,id))

def c8026 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8026 : Upper (D 1) (R 1) [274,36,72,144] 13 := by
  apply FastRouting.sound _ _ [274,36,72,144] 13 (by decide) (choices 1) [1,2,32,64,128] r8026 c8026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4751
  · exact u4752
  · exact u4753
  · exact u4754
  · exact u4755

def b8027 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 465, targets := 32 }], pairs := [(0,5)], upper := (rows 275 38 76 168 211 243 211 211 467), lower := (rows 275 38 76 168 16 32 64 128 256), losses := [] }

theorem u8027 : Upper (D 1) (R 1) [274,36,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8027
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8028 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 76 200 179 179 243 179 435), lower := (rows 275 38 76 200 16 32 64 128 256), losses := [] }

theorem u8028 : Upper (D 1) (R 1) [274,36,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8028
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8029 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 38 196 11 248 248 248 248 504), lower := (rows 275 38 196 11 16 32 64 128 256), losses := [] }

theorem u8029 : Upper (D 1) (R 1) [274,36,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8029
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8030 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 275 38 196 25 250 234 234 234 490), lower := (rows 275 38 196 25 16 32 64 128 256), losses := [] }

theorem u8030 : Upper (D 1) (R 1) [274,36,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8030
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8031 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 275 38 196 26 249 233 233 233 489), lower := (rows 275 38 196 26 16 32 64 128 256), losses := [] }

theorem u8031 : Upper (D 1) (R 1) [274,36,192,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8031
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8032 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8032 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8032 : Upper (D 1) (R 1) [274,36,192,33] 13 := by
  apply FastRouting.sound _ _ [274,36,192,33] 13 (by decide) (choices 1) [2,8,64] r8032 c8032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4756
  · exact u4757
  · exact u4758

def b8033 : PairBound 9 := { available := 217, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 38 196 42 217 249 217 217 473), lower := (rows 275 38 196 42 16 32 64 128 256), losses := [] }

theorem u8033 : Upper (D 1) (R 1) [274,36,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8033
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8034 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8034 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8034 : Upper (D 1) (R 1) [274,36,192,48] 13 := by
  apply FastRouting.sound _ _ [274,36,192,48] 13 (by decide) (choices 1) [1,2,8,64] r8034 c8034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4759
  · exact u4760
  · exact u4761
  · exact u4762

def r8035 : Route 9 := (fun mask => (mask,id))

def c8035 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8035 : Upper (D 1) (R 1) [274,36,192,65] 13 := by
  apply FastRouting.sound _ _ [274,36,192,65] 13 (by decide) (choices 1) [2,8,32,128] r8035 c8035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4763
  · exact u4764
  · exact u4765
  · exact u4766

def b8036 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 275 38 196 74 185 185 249 185 441), lower := (rows 275 38 196 74 16 32 64 128 256), losses := [] }

theorem u8036 : Upper (D 1) (R 1) [274,36,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8036
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8037 : Route 9 := (fun mask => (mask,id))

def c8037 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8037 : Upper (D 1) (R 1) [274,36,192,80] 13 := by
  apply FastRouting.sound _ _ [274,36,192,80] 13 (by decide) (choices 1) [1,2,8,32,128] r8037 c8037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4767
  · exact u4768
  · exact u4769
  · exact u4770
  · exact u4771

def r8038 : Route 9 := (fun mask => (mask,id))

def c8038 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8038 : Upper (D 1) (R 1) [274,36,192,96] 13 := by
  apply FastRouting.sound _ _ [274,36,192,96] 13 (by decide) (choices 1) [1,2,8,128] r8038 c8038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4772
  · exact u4773
  · exact u4774
  · exact u4775

def b8039 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 275 38 196 200 59 59 123 187 315), lower := (rows 275 38 196 200 16 32 64 128 256), losses := [] }

theorem u8039 : Upper (D 1) (R 1) [274,36,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8039
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u8039
end Delivery.IrregularNine14.P01
