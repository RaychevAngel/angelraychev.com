import FiniteExclusionKernel

set_option maxRecDepth 4096
set_option maxHeartbeats 20000000

namespace Delivery.FiniteExclusion.Cycle2x3x4
open FiniteGame Extremal

def a (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 4
  | 4 => 2
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 5
  | _ => 0

theorem node_3 : Excluded a [2,3] :=
  predecessor_excluded a [2,3] 4 3 0 1 (by decide) (by decide +kernel)

theorem node_4 : Excluded a [2,4] :=
  predecessor_excluded a [2,4] 3 2 1 0 (by decide) (by decide +kernel)

theorem node_6 : Excluded a [2,5,0] :=
  predecessor_excluded a [2,5,0] 3 0 0 2 (by decide) (by decide +kernel)

theorem node_7 : Excluded a [2,5,1] :=
  source_excluded a [2,5,1] 0 3 2 (by decide) (by decide +kernel)

theorem node_8 : Excluded a [2,5,4] :=
  source_excluded a [2,5,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_10 : Excluded a [2,5,6,0] :=
  predecessor_excluded a [2,5,6,0] 1 2 3 0 (by decide) (by decide +kernel)

theorem node_12 : Excluded a [2,5,6,1,0] :=
  source_excluded a [2,5,6,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_13 : Excluded a [2,5,6,1,3] :=
  source_excluded a [2,5,6,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_15 : Excluded a [2,5,6,1,7,0] :=
  source_excluded a [2,5,6,1,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_16 : Excluded a [2,5,6,1,7,3] :=
  source_excluded a [2,5,6,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_17 : Excluded a [2,5,6,1,7,4] :=
  predecessor_excluded a [2,5,6,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_20 : Excluded a [2,5,6,1,7,8,0,3] :=
  predecessor_excluded a [2,5,6,1,7,8,0,3] 0 3 4 7 (by decide) (by decide +kernel)

def b_22 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 5
  | 2 => 6
  | 3 => 1
  | 4 => 7
  | 5 => 8
  | 6 => 0
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_22 : LosingRegion (edgeOf a b_22) 0 :=
  losingMask a b_22 0 1548928139457190264046592
    (by decide +kernel) (by decide +kernel)

theorem node_22 : Excluded a [2,5,6,1,7,8,0,4,3] :=
  losing_excluded a [2,5,6,1,7,8,0,4,3] (by decide) b_22 (by decide +kernel) 2 0 6 cert_22 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_22 2 0 ∧ 6 ≠ 2 ∧ maskRegion 1548928139457190264046592 2 6; decide +kernel)

theorem node_21 : Excluded a [2,5,6,1,7,8,0,4] :=
  branch_excluded a [2,5,6,1,7,8,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,6,1,7,8,0,4,0] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,8,0,4,1] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,8,0,4,2] (by decide +kernel))
      node_22
      (invalid_excluded a [2,5,6,1,7,8,0,4,4] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,8,0,4,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,8,0,4,6] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,8,0,4,7] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,8,0,4,8] (by decide +kernel)))

theorem node_19 : Excluded a [2,5,6,1,7,8,0] :=
  branch_excluded a [2,5,6,1,7,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,6,1,7,8,0,0] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,8,0,1] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,8,0,2] (by decide +kernel))
      node_20
      node_21
      (invalid_excluded a [2,5,6,1,7,8,0,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,8,0,6] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,8,0,7] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,8,0,8] (by decide +kernel)))

theorem node_23 : Excluded a [2,5,6,1,7,8,3] :=
  source_excluded a [2,5,6,1,7,8,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_24 : Excluded a [2,5,6,1,7,8,4] :=
  source_excluded a [2,5,6,1,7,8,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_18 : Excluded a [2,5,6,1,7,8] :=
  branch_excluded a [2,5,6,1,7,8] (by decide)
    (fin9_cases _
      node_19
      (invalid_excluded a [2,5,6,1,7,8,1] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,8,2] (by decide +kernel))
      node_23
      node_24
      (invalid_excluded a [2,5,6,1,7,8,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,8,6] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,8,7] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,8,8] (by decide +kernel)))

theorem node_14 : Excluded a [2,5,6,1,7] :=
  branch_excluded a [2,5,6,1,7] (by decide)
    (fin9_cases _
      node_15
      (invalid_excluded a [2,5,6,1,7,1] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,2] (by decide +kernel))
      node_16
      node_17
      (invalid_excluded a [2,5,6,1,7,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,6] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,7,7] (by decide +kernel))
      node_18)

theorem node_26 : Excluded a [2,5,6,1,8,0] :=
  source_excluded a [2,5,6,1,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_27 : Excluded a [2,5,6,1,8,3] :=
  source_excluded a [2,5,6,1,8,3] 2 0 5 (by decide) (by decide +kernel)

def b_31 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 5
  | 2 => 6
  | 3 => 1
  | 4 => 8
  | 5 => 4
  | 6 => 0
  | 7 => 3
  | 8 => 7
  | _ => 0

def cert_31 : LosingRegion (edgeOf a b_31) 0 :=
  losingMask a b_31 0 1772797825535729382458368
    (by decide +kernel) (by decide +kernel)

theorem node_31 : Excluded a [2,5,6,1,8,4,0,3,7] :=
  losing_excluded a [2,5,6,1,8,4,0,3,7] (by decide) b_31 (by decide +kernel) 2 0 6 cert_31 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_31 2 0 ∧ 6 ≠ 2 ∧ maskRegion 1772797825535729382458368 2 6; decide +kernel)

theorem node_30 : Excluded a [2,5,6,1,8,4,0,3] :=
  branch_excluded a [2,5,6,1,8,4,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,6,1,8,4,0,3,0] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,0,3,1] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,0,3,2] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,0,3,3] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,0,3,4] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,0,3,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,0,3,6] (by decide +kernel))
      node_31
      (invalid_excluded a [2,5,6,1,8,4,0,3,8] (by decide +kernel)))

theorem node_29 : Excluded a [2,5,6,1,8,4,0] :=
  branch_excluded a [2,5,6,1,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,6,1,8,4,0,0] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,0,1] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,0,2] (by decide +kernel))
      node_30
      (invalid_excluded a [2,5,6,1,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,0,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,0,6] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,0,8] (by decide +kernel)))

theorem node_32 : Excluded a [2,5,6,1,8,4,3] :=
  source_excluded a [2,5,6,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_28 : Excluded a [2,5,6,1,8,4] :=
  branch_excluded a [2,5,6,1,8,4] (by decide)
    (fin9_cases _
      node_29
      (invalid_excluded a [2,5,6,1,8,4,1] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,2] (by decide +kernel))
      node_32
      (invalid_excluded a [2,5,6,1,8,4,4] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,4,8] (by decide +kernel)))

theorem node_33 : Excluded a [2,5,6,1,8,7] :=
  source_excluded a [2,5,6,1,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_25 : Excluded a [2,5,6,1,8] :=
  branch_excluded a [2,5,6,1,8] (by decide)
    (fin9_cases _
      node_26
      (invalid_excluded a [2,5,6,1,8,1] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,2] (by decide +kernel))
      node_27
      node_28
      (invalid_excluded a [2,5,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,8,6] (by decide +kernel))
      node_33
      (invalid_excluded a [2,5,6,1,8,8] (by decide +kernel)))

theorem node_11 : Excluded a [2,5,6,1] :=
  branch_excluded a [2,5,6,1] (by decide)
    (fin9_cases _
      node_12
      (invalid_excluded a [2,5,6,1,1] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,2] (by decide +kernel))
      node_13
      (invalid_excluded a [2,5,6,1,4] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,1,6] (by decide +kernel))
      node_14
      node_25)

theorem node_34 : Excluded a [2,5,6,7] :=
  predecessor_excluded a [2,5,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_36 : Excluded a [2,5,6,8,0] :=
  source_excluded a [2,5,6,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_37 : Excluded a [2,5,6,8,1] :=
  source_excluded a [2,5,6,8,1] 0 3 4 (by decide) (by decide +kernel)

theorem node_38 : Excluded a [2,5,6,8,3] :=
  source_excluded a [2,5,6,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_40 : Excluded a [2,5,6,8,7,0] :=
  source_excluded a [2,5,6,8,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_41 : Excluded a [2,5,6,8,7,1] :=
  predecessor_excluded a [2,5,6,8,7,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_42 : Excluded a [2,5,6,8,7,3] :=
  source_excluded a [2,5,6,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_43 : Excluded a [2,5,6,8,7,4] :=
  predecessor_excluded a [2,5,6,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_39 : Excluded a [2,5,6,8,7] :=
  branch_excluded a [2,5,6,8,7] (by decide)
    (fin9_cases _
      node_40
      node_41
      (invalid_excluded a [2,5,6,8,7,2] (by decide +kernel))
      node_42
      node_43
      (invalid_excluded a [2,5,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [2,5,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [2,5,6,8,7,8] (by decide +kernel)))

theorem node_35 : Excluded a [2,5,6,8] :=
  branch_excluded a [2,5,6,8] (by decide)
    (fin9_cases _
      node_36
      node_37
      (invalid_excluded a [2,5,6,8,2] (by decide +kernel))
      node_38
      (invalid_excluded a [2,5,6,8,4] (by decide +kernel))
      (invalid_excluded a [2,5,6,8,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,8,6] (by decide +kernel))
      node_39
      (invalid_excluded a [2,5,6,8,8] (by decide +kernel)))

theorem node_9 : Excluded a [2,5,6] :=
  branch_excluded a [2,5,6] (by decide)
    (fin9_cases _
      node_10
      node_11
      (invalid_excluded a [2,5,6,2] (by decide +kernel))
      (invalid_excluded a [2,5,6,3] (by decide +kernel))
      (invalid_excluded a [2,5,6,4] (by decide +kernel))
      (invalid_excluded a [2,5,6,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,6] (by decide +kernel))
      node_34
      node_35)

theorem node_45 : Excluded a [2,5,7,0] :=
  predecessor_excluded a [2,5,7,0] 1 2 3 0 (by decide) (by decide +kernel)

theorem node_47 : Excluded a [2,5,7,1,0] :=
  source_excluded a [2,5,7,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_48 : Excluded a [2,5,7,1,3] :=
  source_excluded a [2,5,7,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_49 : Excluded a [2,5,7,1,6] :=
  predecessor_excluded a [2,5,7,1,6] 0 7 4 2 (by decide) (by decide +kernel)

theorem node_51 : Excluded a [2,5,7,1,8,0] :=
  source_excluded a [2,5,7,1,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_54 : Excluded a [2,5,7,1,8,3,0,4] :=
  source_excluded a [2,5,7,1,8,3,0,4] 7 0 4 (by decide) (by decide +kernel)

def b_56 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 5
  | 2 => 7
  | 3 => 1
  | 4 => 8
  | 5 => 3
  | 6 => 0
  | 7 => 6
  | 8 => 4
  | _ => 0

def cert_56 : LosingRegion (edgeOf a b_56) 0 :=
  losingMask a b_56 0 2278247836413745945904128
    (by decide +kernel) (by decide +kernel)

theorem node_56 : Excluded a [2,5,7,1,8,3,0,6,4] :=
  losing_excluded a [2,5,7,1,8,3,0,6,4] (by decide) b_56 (by decide +kernel) 2 0 1 cert_56 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_56 2 0 ∧ 1 ≠ 2 ∧ maskRegion 2278247836413745945904128 2 1; decide +kernel)

theorem node_55 : Excluded a [2,5,7,1,8,3,0,6] :=
  branch_excluded a [2,5,7,1,8,3,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,1,8,3,0,6,0] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,3,0,6,1] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,3,0,6,2] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,3,0,6,3] (by decide +kernel))
      node_56
      (invalid_excluded a [2,5,7,1,8,3,0,6,5] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,3,0,6,6] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,3,0,6,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,3,0,6,8] (by decide +kernel)))

theorem node_53 : Excluded a [2,5,7,1,8,3,0] :=
  branch_excluded a [2,5,7,1,8,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,1,8,3,0,0] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,3,0,1] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,3,0,2] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,3,0,3] (by decide +kernel))
      node_54
      (invalid_excluded a [2,5,7,1,8,3,0,5] (by decide +kernel))
      node_55
      (invalid_excluded a [2,5,7,1,8,3,0,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,3,0,8] (by decide +kernel)))

theorem node_57 : Excluded a [2,5,7,1,8,3,4] :=
  predecessor_excluded a [2,5,7,1,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_52 : Excluded a [2,5,7,1,8,3] :=
  branch_excluded a [2,5,7,1,8,3] (by decide)
    (fin9_cases _
      node_53
      (invalid_excluded a [2,5,7,1,8,3,1] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,3,2] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,3,3] (by decide +kernel))
      node_57
      (invalid_excluded a [2,5,7,1,8,3,5] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,3,6] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,3,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,3,8] (by decide +kernel)))

theorem node_60 : Excluded a [2,5,7,1,8,4,0,3] :=
  source_excluded a [2,5,7,1,8,4,0,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_62 : Excluded a [2,5,7,1,8,4,0,6,3] :=
  predecessor_excluded a [2,5,7,1,8,4,0,6,3] 0 4 8 5 (by decide) (by decide +kernel)

theorem node_61 : Excluded a [2,5,7,1,8,4,0,6] :=
  branch_excluded a [2,5,7,1,8,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,1,8,4,0,6,0] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,4,0,6,1] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,4,0,6,2] (by decide +kernel))
      node_62
      (invalid_excluded a [2,5,7,1,8,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,4,0,6,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,4,0,6,8] (by decide +kernel)))

theorem node_59 : Excluded a [2,5,7,1,8,4,0] :=
  branch_excluded a [2,5,7,1,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,1,8,4,0,0] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,4,0,1] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,4,0,2] (by decide +kernel))
      node_60
      (invalid_excluded a [2,5,7,1,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,4,0,5] (by decide +kernel))
      node_61
      (invalid_excluded a [2,5,7,1,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,4,0,8] (by decide +kernel)))

theorem node_63 : Excluded a [2,5,7,1,8,4,3] :=
  source_excluded a [2,5,7,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_58 : Excluded a [2,5,7,1,8,4] :=
  branch_excluded a [2,5,7,1,8,4] (by decide)
    (fin9_cases _
      node_59
      (invalid_excluded a [2,5,7,1,8,4,1] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,4,2] (by decide +kernel))
      node_63
      (invalid_excluded a [2,5,7,1,8,4,4] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,4,5] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,4,8] (by decide +kernel)))

theorem node_50 : Excluded a [2,5,7,1,8] :=
  branch_excluded a [2,5,7,1,8] (by decide)
    (fin9_cases _
      node_51
      (invalid_excluded a [2,5,7,1,8,1] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,2] (by decide +kernel))
      node_52
      node_58
      (invalid_excluded a [2,5,7,1,8,5] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,8,8] (by decide +kernel)))

theorem node_46 : Excluded a [2,5,7,1] :=
  branch_excluded a [2,5,7,1] (by decide)
    (fin9_cases _
      node_47
      (invalid_excluded a [2,5,7,1,1] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,2] (by decide +kernel))
      node_48
      (invalid_excluded a [2,5,7,1,4] (by decide +kernel))
      (invalid_excluded a [2,5,7,1,5] (by decide +kernel))
      node_49
      (invalid_excluded a [2,5,7,1,7] (by decide +kernel))
      node_50)

theorem node_65 : Excluded a [2,5,7,6,0] :=
  source_excluded a [2,5,7,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_66 : Excluded a [2,5,7,6,1] :=
  source_excluded a [2,5,7,6,1] 0 3 4 (by decide) (by decide +kernel)

theorem node_67 : Excluded a [2,5,7,6,3] :=
  source_excluded a [2,5,7,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_69 : Excluded a [2,5,7,6,8,0] :=
  source_excluded a [2,5,7,6,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_70 : Excluded a [2,5,7,6,8,1] :=
  predecessor_excluded a [2,5,7,6,8,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_71 : Excluded a [2,5,7,6,8,3] :=
  source_excluded a [2,5,7,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_72 : Excluded a [2,5,7,6,8,4] :=
  source_excluded a [2,5,7,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_68 : Excluded a [2,5,7,6,8] :=
  branch_excluded a [2,5,7,6,8] (by decide)
    (fin9_cases _
      node_69
      node_70
      (invalid_excluded a [2,5,7,6,8,2] (by decide +kernel))
      node_71
      node_72
      (invalid_excluded a [2,5,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [2,5,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [2,5,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,6,8,8] (by decide +kernel)))

theorem node_64 : Excluded a [2,5,7,6] :=
  branch_excluded a [2,5,7,6] (by decide)
    (fin9_cases _
      node_65
      node_66
      (invalid_excluded a [2,5,7,6,2] (by decide +kernel))
      node_67
      (invalid_excluded a [2,5,7,6,4] (by decide +kernel))
      (invalid_excluded a [2,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [2,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [2,5,7,6,7] (by decide +kernel))
      node_68)

theorem node_73 : Excluded a [2,5,7,8] :=
  predecessor_excluded a [2,5,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_44 : Excluded a [2,5,7] :=
  branch_excluded a [2,5,7] (by decide)
    (fin9_cases _
      node_45
      node_46
      (invalid_excluded a [2,5,7,2] (by decide +kernel))
      (invalid_excluded a [2,5,7,3] (by decide +kernel))
      (invalid_excluded a [2,5,7,4] (by decide +kernel))
      (invalid_excluded a [2,5,7,5] (by decide +kernel))
      node_64
      (invalid_excluded a [2,5,7,7] (by decide +kernel))
      node_73)

theorem node_75 : Excluded a [2,5,8,0] :=
  predecessor_excluded a [2,5,8,0] 1 2 3 0 (by decide) (by decide +kernel)

theorem node_77 : Excluded a [2,5,8,1,0] :=
  source_excluded a [2,5,8,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_78 : Excluded a [2,5,8,1,3] :=
  source_excluded a [2,5,8,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_80 : Excluded a [2,5,8,1,6,0] :=
  source_excluded a [2,5,8,1,6,0] 1 2 5 (by decide) (by decide +kernel)

def b_84 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 5
  | 2 => 8
  | 3 => 1
  | 4 => 6
  | 5 => 3
  | 6 => 0
  | 7 => 4
  | 8 => 7
  | _ => 0

def cert_84 : LosingRegion (edgeOf a b_84) 0 :=
  losingMask a b_84 0 1373416590574999696049152
    (by decide +kernel) (by decide +kernel)

theorem node_84 : Excluded a [2,5,8,1,6,3,0,4,7] :=
  losing_excluded a [2,5,8,1,6,3,0,4,7] (by decide) b_84 (by decide +kernel) 2 0 0 cert_84 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_84 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1373416590574999696049152 2 0; decide +kernel)

theorem node_83 : Excluded a [2,5,8,1,6,3,0,4] :=
  branch_excluded a [2,5,8,1,6,3,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,8,1,6,3,0,4,0] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,0,4,1] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,0,4,2] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,0,4,3] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,0,4,4] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,0,4,5] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,0,4,6] (by decide +kernel))
      node_84
      (invalid_excluded a [2,5,8,1,6,3,0,4,8] (by decide +kernel)))

theorem node_82 : Excluded a [2,5,8,1,6,3,0] :=
  branch_excluded a [2,5,8,1,6,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,8,1,6,3,0,0] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,0,1] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,0,2] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,0,3] (by decide +kernel))
      node_83
      (invalid_excluded a [2,5,8,1,6,3,0,5] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,0,6] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,0,7] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,0,8] (by decide +kernel)))

theorem node_85 : Excluded a [2,5,8,1,6,3,4] :=
  predecessor_excluded a [2,5,8,1,6,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_81 : Excluded a [2,5,8,1,6,3] :=
  branch_excluded a [2,5,8,1,6,3] (by decide)
    (fin9_cases _
      node_82
      (invalid_excluded a [2,5,8,1,6,3,1] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,2] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,3] (by decide +kernel))
      node_85
      (invalid_excluded a [2,5,8,1,6,3,5] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,6] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,7] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,3,8] (by decide +kernel)))

theorem node_86 : Excluded a [2,5,8,1,6,4] :=
  source_excluded a [2,5,8,1,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_87 : Excluded a [2,5,8,1,6,7] :=
  source_excluded a [2,5,8,1,6,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_79 : Excluded a [2,5,8,1,6] :=
  branch_excluded a [2,5,8,1,6] (by decide)
    (fin9_cases _
      node_80
      (invalid_excluded a [2,5,8,1,6,1] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,2] (by decide +kernel))
      node_81
      node_86
      (invalid_excluded a [2,5,8,1,6,5] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,6,6] (by decide +kernel))
      node_87
      (invalid_excluded a [2,5,8,1,6,8] (by decide +kernel)))

theorem node_88 : Excluded a [2,5,8,1,7] :=
  predecessor_excluded a [2,5,8,1,7] 0 8 4 2 (by decide) (by decide +kernel)

theorem node_76 : Excluded a [2,5,8,1] :=
  branch_excluded a [2,5,8,1] (by decide)
    (fin9_cases _
      node_77
      (invalid_excluded a [2,5,8,1,1] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,2] (by decide +kernel))
      node_78
      (invalid_excluded a [2,5,8,1,4] (by decide +kernel))
      (invalid_excluded a [2,5,8,1,5] (by decide +kernel))
      node_79
      node_88
      (invalid_excluded a [2,5,8,1,8] (by decide +kernel)))

theorem node_90 : Excluded a [2,5,8,6,0] :=
  source_excluded a [2,5,8,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_91 : Excluded a [2,5,8,6,1] :=
  source_excluded a [2,5,8,6,1] 0 3 4 (by decide) (by decide +kernel)

theorem node_92 : Excluded a [2,5,8,6,3] :=
  source_excluded a [2,5,8,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_93 : Excluded a [2,5,8,6,7] :=
  predecessor_excluded a [2,5,8,6,7] 0 8 4 2 (by decide) (by decide +kernel)

theorem node_89 : Excluded a [2,5,8,6] :=
  branch_excluded a [2,5,8,6] (by decide)
    (fin9_cases _
      node_90
      node_91
      (invalid_excluded a [2,5,8,6,2] (by decide +kernel))
      node_92
      (invalid_excluded a [2,5,8,6,4] (by decide +kernel))
      (invalid_excluded a [2,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [2,5,8,6,6] (by decide +kernel))
      node_93
      (invalid_excluded a [2,5,8,6,8] (by decide +kernel)))

theorem node_95 : Excluded a [2,5,8,7,0] :=
  source_excluded a [2,5,8,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_96 : Excluded a [2,5,8,7,1] :=
  source_excluded a [2,5,8,7,1] 0 3 4 (by decide) (by decide +kernel)

theorem node_97 : Excluded a [2,5,8,7,3] :=
  source_excluded a [2,5,8,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_99 : Excluded a [2,5,8,7,6,0] :=
  source_excluded a [2,5,8,7,6,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_100 : Excluded a [2,5,8,7,6,1] :=
  predecessor_excluded a [2,5,8,7,6,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_101 : Excluded a [2,5,8,7,6,3] :=
  predecessor_excluded a [2,5,8,7,6,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_102 : Excluded a [2,5,8,7,6,4] :=
  source_excluded a [2,5,8,7,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_98 : Excluded a [2,5,8,7,6] :=
  branch_excluded a [2,5,8,7,6] (by decide)
    (fin9_cases _
      node_99
      node_100
      (invalid_excluded a [2,5,8,7,6,2] (by decide +kernel))
      node_101
      node_102
      (invalid_excluded a [2,5,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [2,5,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [2,5,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [2,5,8,7,6,8] (by decide +kernel)))

theorem node_94 : Excluded a [2,5,8,7] :=
  branch_excluded a [2,5,8,7] (by decide)
    (fin9_cases _
      node_95
      node_96
      (invalid_excluded a [2,5,8,7,2] (by decide +kernel))
      node_97
      (invalid_excluded a [2,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [2,5,8,7,5] (by decide +kernel))
      node_98
      (invalid_excluded a [2,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [2,5,8,7,8] (by decide +kernel)))

theorem node_74 : Excluded a [2,5,8] :=
  branch_excluded a [2,5,8] (by decide)
    (fin9_cases _
      node_75
      node_76
      (invalid_excluded a [2,5,8,2] (by decide +kernel))
      (invalid_excluded a [2,5,8,3] (by decide +kernel))
      (invalid_excluded a [2,5,8,4] (by decide +kernel))
      (invalid_excluded a [2,5,8,5] (by decide +kernel))
      node_89
      node_94
      (invalid_excluded a [2,5,8,8] (by decide +kernel)))

theorem node_5 : Excluded a [2,5] :=
  branch_excluded a [2,5] (by decide)
    (fin9_cases _
      node_6
      node_7
      (invalid_excluded a [2,5,2] (by decide +kernel))
      (invalid_excluded a [2,5,3] (by decide +kernel))
      node_8
      (invalid_excluded a [2,5,5] (by decide +kernel))
      node_9
      node_44
      node_74)

theorem node_104 : Excluded a [2,6,0] :=
  predecessor_excluded a [2,6,0] 3 0 0 2 (by decide) (by decide +kernel)

theorem node_105 : Excluded a [2,6,1] :=
  source_excluded a [2,6,1] 0 3 2 (by decide) (by decide +kernel)

theorem node_106 : Excluded a [2,6,4] :=
  source_excluded a [2,6,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_108 : Excluded a [2,6,5,0] :=
  predecessor_excluded a [2,6,5,0] 1 2 3 0 (by decide) (by decide +kernel)

theorem node_110 : Excluded a [2,6,5,1,0] :=
  source_excluded a [2,6,5,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_111 : Excluded a [2,6,5,1,3] :=
  source_excluded a [2,6,5,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_113 : Excluded a [2,6,5,1,7,0] :=
  source_excluded a [2,6,5,1,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_114 : Excluded a [2,6,5,1,7,3] :=
  source_excluded a [2,6,5,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_115 : Excluded a [2,6,5,1,7,4] :=
  predecessor_excluded a [2,6,5,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_117 : Excluded a [2,6,5,1,7,8,0] :=
  source_excluded a [2,6,5,1,7,8,0] 1 2 6 (by decide) (by decide +kernel)

def b_120 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 6
  | 2 => 5
  | 3 => 1
  | 4 => 7
  | 5 => 8
  | 6 => 3
  | 7 => 0
  | 8 => 4
  | _ => 0

def cert_120 : LosingRegion (edgeOf a b_120) 0 :=
  losingMask a b_120 0 1710678414803397064262656
    (by decide +kernel) (by decide +kernel)

theorem node_120 : Excluded a [2,6,5,1,7,8,3,0,4] :=
  losing_excluded a [2,6,5,1,7,8,3,0,4] (by decide) b_120 (by decide +kernel) 2 0 0 cert_120 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_120 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1710678414803397064262656 2 0; decide +kernel)

theorem node_119 : Excluded a [2,6,5,1,7,8,3,0] :=
  branch_excluded a [2,6,5,1,7,8,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,5,1,7,8,3,0,0] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,8,3,0,1] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,8,3,0,2] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,8,3,0,3] (by decide +kernel))
      node_120
      (invalid_excluded a [2,6,5,1,7,8,3,0,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,8,3,0,6] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,8,3,0,7] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,8,3,0,8] (by decide +kernel)))

theorem node_121 : Excluded a [2,6,5,1,7,8,3,4] :=
  predecessor_excluded a [2,6,5,1,7,8,3,4] 0 4 6 7 (by decide) (by decide +kernel)

theorem node_118 : Excluded a [2,6,5,1,7,8,3] :=
  branch_excluded a [2,6,5,1,7,8,3] (by decide)
    (fin9_cases _
      node_119
      (invalid_excluded a [2,6,5,1,7,8,3,1] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,8,3,2] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,8,3,3] (by decide +kernel))
      node_121
      (invalid_excluded a [2,6,5,1,7,8,3,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,8,3,6] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,8,3,7] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,8,3,8] (by decide +kernel)))

theorem node_122 : Excluded a [2,6,5,1,7,8,4] :=
  source_excluded a [2,6,5,1,7,8,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_116 : Excluded a [2,6,5,1,7,8] :=
  branch_excluded a [2,6,5,1,7,8] (by decide)
    (fin9_cases _
      node_117
      (invalid_excluded a [2,6,5,1,7,8,1] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,8,2] (by decide +kernel))
      node_118
      node_122
      (invalid_excluded a [2,6,5,1,7,8,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,8,6] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,8,7] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,8,8] (by decide +kernel)))

theorem node_112 : Excluded a [2,6,5,1,7] :=
  branch_excluded a [2,6,5,1,7] (by decide)
    (fin9_cases _
      node_113
      (invalid_excluded a [2,6,5,1,7,1] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,2] (by decide +kernel))
      node_114
      node_115
      (invalid_excluded a [2,6,5,1,7,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,6] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,7] (by decide +kernel))
      node_116)

theorem node_123 : Excluded a [2,6,5,1,8] :=
  predecessor_excluded a [2,6,5,1,8] 0 5 4 2 (by decide) (by decide +kernel)

theorem node_109 : Excluded a [2,6,5,1] :=
  branch_excluded a [2,6,5,1] (by decide)
    (fin9_cases _
      node_110
      (invalid_excluded a [2,6,5,1,1] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,2] (by decide +kernel))
      node_111
      (invalid_excluded a [2,6,5,1,4] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,6] (by decide +kernel))
      node_112
      node_123)

theorem node_125 : Excluded a [2,6,5,7,0] :=
  source_excluded a [2,6,5,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_126 : Excluded a [2,6,5,7,1] :=
  source_excluded a [2,6,5,7,1] 0 3 4 (by decide) (by decide +kernel)

theorem node_127 : Excluded a [2,6,5,7,3] :=
  source_excluded a [2,6,5,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_128 : Excluded a [2,6,5,7,8] :=
  predecessor_excluded a [2,6,5,7,8] 0 5 4 2 (by decide) (by decide +kernel)

theorem node_124 : Excluded a [2,6,5,7] :=
  branch_excluded a [2,6,5,7] (by decide)
    (fin9_cases _
      node_125
      node_126
      (invalid_excluded a [2,6,5,7,2] (by decide +kernel))
      node_127
      (invalid_excluded a [2,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [2,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [2,6,5,7,7] (by decide +kernel))
      node_128)

theorem node_130 : Excluded a [2,6,5,8,0] :=
  source_excluded a [2,6,5,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_131 : Excluded a [2,6,5,8,1] :=
  source_excluded a [2,6,5,8,1] 0 3 4 (by decide) (by decide +kernel)

theorem node_132 : Excluded a [2,6,5,8,3] :=
  source_excluded a [2,6,5,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_134 : Excluded a [2,6,5,8,7,0] :=
  source_excluded a [2,6,5,8,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_135 : Excluded a [2,6,5,8,7,1] :=
  source_excluded a [2,6,5,8,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_136 : Excluded a [2,6,5,8,7,3] :=
  source_excluded a [2,6,5,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_137 : Excluded a [2,6,5,8,7,4] :=
  predecessor_excluded a [2,6,5,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_133 : Excluded a [2,6,5,8,7] :=
  branch_excluded a [2,6,5,8,7] (by decide)
    (fin9_cases _
      node_134
      node_135
      (invalid_excluded a [2,6,5,8,7,2] (by decide +kernel))
      node_136
      node_137
      (invalid_excluded a [2,6,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [2,6,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [2,6,5,8,7,8] (by decide +kernel)))

theorem node_129 : Excluded a [2,6,5,8] :=
  branch_excluded a [2,6,5,8] (by decide)
    (fin9_cases _
      node_130
      node_131
      (invalid_excluded a [2,6,5,8,2] (by decide +kernel))
      node_132
      (invalid_excluded a [2,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [2,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,8,6] (by decide +kernel))
      node_133
      (invalid_excluded a [2,6,5,8,8] (by decide +kernel)))

theorem node_107 : Excluded a [2,6,5] :=
  branch_excluded a [2,6,5] (by decide)
    (fin9_cases _
      node_108
      node_109
      (invalid_excluded a [2,6,5,2] (by decide +kernel))
      (invalid_excluded a [2,6,5,3] (by decide +kernel))
      (invalid_excluded a [2,6,5,4] (by decide +kernel))
      (invalid_excluded a [2,6,5,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,6] (by decide +kernel))
      node_124
      node_129)

theorem node_139 : Excluded a [2,6,7,0] :=
  predecessor_excluded a [2,6,7,0] 1 2 3 0 (by decide) (by decide +kernel)

theorem node_141 : Excluded a [2,6,7,1,0] :=
  source_excluded a [2,6,7,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_142 : Excluded a [2,6,7,1,3] :=
  source_excluded a [2,6,7,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_144 : Excluded a [2,6,7,1,5,0] :=
  source_excluded a [2,6,7,1,5,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_145 : Excluded a [2,6,7,1,5,3] :=
  predecessor_excluded a [2,6,7,1,5,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_147 : Excluded a [2,6,7,1,5,4,0] :=
  source_excluded a [2,6,7,1,5,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_148 : Excluded a [2,6,7,1,5,4,3] :=
  source_excluded a [2,6,7,1,5,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_149 : Excluded a [2,6,7,1,5,4,8] :=
  source_excluded a [2,6,7,1,5,4,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_146 : Excluded a [2,6,7,1,5,4] :=
  branch_excluded a [2,6,7,1,5,4] (by decide)
    (fin9_cases _
      node_147
      (invalid_excluded a [2,6,7,1,5,4,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,4,2] (by decide +kernel))
      node_148
      (invalid_excluded a [2,6,7,1,5,4,4] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,4,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,4,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,4,7] (by decide +kernel))
      node_149)

theorem node_151 : Excluded a [2,6,7,1,5,8,0] :=
  source_excluded a [2,6,7,1,5,8,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_152 : Excluded a [2,6,7,1,5,8,3] :=
  source_excluded a [2,6,7,1,5,8,3] 2 0 6 (by decide) (by decide +kernel)

def b_155 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 6
  | 2 => 7
  | 3 => 1
  | 4 => 5
  | 5 => 8
  | 6 => 4
  | 7 => 0
  | 8 => 3
  | _ => 0

def cert_155 : LosingRegion (edgeOf a b_155) 0 :=
  losingMask a b_155 0 1885408357812992375522304
    (by decide +kernel) (by decide +kernel)

theorem node_155 : Excluded a [2,6,7,1,5,8,4,0,3] :=
  losing_excluded a [2,6,7,1,5,8,4,0,3] (by decide) b_155 (by decide +kernel) 2 0 7 cert_155 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_155 2 0 ∧ 7 ≠ 2 ∧ maskRegion 1885408357812992375522304 2 7; decide +kernel)

theorem node_154 : Excluded a [2,6,7,1,5,8,4,0] :=
  branch_excluded a [2,6,7,1,5,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,7,1,5,8,4,0,0] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,8,4,0,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,8,4,0,2] (by decide +kernel))
      node_155
      (invalid_excluded a [2,6,7,1,5,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,8,4,0,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,8,4,0,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,8,4,0,8] (by decide +kernel)))

theorem node_156 : Excluded a [2,6,7,1,5,8,4,3] :=
  source_excluded a [2,6,7,1,5,8,4,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_153 : Excluded a [2,6,7,1,5,8,4] :=
  branch_excluded a [2,6,7,1,5,8,4] (by decide)
    (fin9_cases _
      node_154
      (invalid_excluded a [2,6,7,1,5,8,4,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,8,4,2] (by decide +kernel))
      node_156
      (invalid_excluded a [2,6,7,1,5,8,4,4] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,8,4,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,8,4,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,8,4,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,8,4,8] (by decide +kernel)))

theorem node_150 : Excluded a [2,6,7,1,5,8] :=
  branch_excluded a [2,6,7,1,5,8] (by decide)
    (fin9_cases _
      node_151
      (invalid_excluded a [2,6,7,1,5,8,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,8,2] (by decide +kernel))
      node_152
      node_153
      (invalid_excluded a [2,6,7,1,5,8,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,8,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,8,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,8,8] (by decide +kernel)))

theorem node_143 : Excluded a [2,6,7,1,5] :=
  branch_excluded a [2,6,7,1,5] (by decide)
    (fin9_cases _
      node_144
      (invalid_excluded a [2,6,7,1,5,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,2] (by decide +kernel))
      node_145
      node_146
      (invalid_excluded a [2,6,7,1,5,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5,7] (by decide +kernel))
      node_150)

theorem node_158 : Excluded a [2,6,7,1,8,0] :=
  source_excluded a [2,6,7,1,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_160 : Excluded a [2,6,7,1,8,3,0] :=
  source_excluded a [2,6,7,1,8,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_161 : Excluded a [2,6,7,1,8,3,4] :=
  predecessor_excluded a [2,6,7,1,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

def b_164 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 6
  | 2 => 7
  | 3 => 1
  | 4 => 8
  | 5 => 3
  | 6 => 5
  | 7 => 0
  | 8 => 4
  | _ => 0

def cert_164 : LosingRegion (edgeOf a b_164) 0 :=
  losingMask a b_164 0 2414313401079642872349696
    (by decide +kernel) (by decide +kernel)

theorem node_164 : Excluded a [2,6,7,1,8,3,5,0,4] :=
  losing_excluded a [2,6,7,1,8,3,5,0,4] (by decide) b_164 (by decide +kernel) 2 0 7 cert_164 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_164 2 0 ∧ 7 ≠ 2 ∧ maskRegion 2414313401079642872349696 2 7; decide +kernel)

theorem node_163 : Excluded a [2,6,7,1,8,3,5,0] :=
  branch_excluded a [2,6,7,1,8,3,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,7,1,8,3,5,0,0] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,5,0,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,5,0,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,5,0,3] (by decide +kernel))
      node_164
      (invalid_excluded a [2,6,7,1,8,3,5,0,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,5,0,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,5,0,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,5,0,8] (by decide +kernel)))

theorem node_165 : Excluded a [2,6,7,1,8,3,5,4] :=
  source_excluded a [2,6,7,1,8,3,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_162 : Excluded a [2,6,7,1,8,3,5] :=
  branch_excluded a [2,6,7,1,8,3,5] (by decide)
    (fin9_cases _
      node_163
      (invalid_excluded a [2,6,7,1,8,3,5,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,5,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,5,3] (by decide +kernel))
      node_165
      (invalid_excluded a [2,6,7,1,8,3,5,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,5,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,5,8] (by decide +kernel)))

theorem node_159 : Excluded a [2,6,7,1,8,3] :=
  branch_excluded a [2,6,7,1,8,3] (by decide)
    (fin9_cases _
      node_160
      (invalid_excluded a [2,6,7,1,8,3,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,3] (by decide +kernel))
      node_161
      node_162
      (invalid_excluded a [2,6,7,1,8,3,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,8] (by decide +kernel)))

theorem node_167 : Excluded a [2,6,7,1,8,4,0] :=
  source_excluded a [2,6,7,1,8,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_168 : Excluded a [2,6,7,1,8,4,3] :=
  source_excluded a [2,6,7,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_171 : Excluded a [2,6,7,1,8,4,5,0,3] :=
  predecessor_excluded a [2,6,7,1,8,4,5,0,3] 0 4 8 5 (by decide) (by decide +kernel)

theorem node_170 : Excluded a [2,6,7,1,8,4,5,0] :=
  branch_excluded a [2,6,7,1,8,4,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,7,1,8,4,5,0,0] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,5,0,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,5,0,2] (by decide +kernel))
      node_171
      (invalid_excluded a [2,6,7,1,8,4,5,0,4] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,5,0,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,5,0,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,5,0,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,5,0,8] (by decide +kernel)))

theorem node_172 : Excluded a [2,6,7,1,8,4,5,3] :=
  source_excluded a [2,6,7,1,8,4,5,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_169 : Excluded a [2,6,7,1,8,4,5] :=
  branch_excluded a [2,6,7,1,8,4,5] (by decide)
    (fin9_cases _
      node_170
      (invalid_excluded a [2,6,7,1,8,4,5,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,5,2] (by decide +kernel))
      node_172
      (invalid_excluded a [2,6,7,1,8,4,5,4] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,5,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,5,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,5,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,5,8] (by decide +kernel)))

theorem node_166 : Excluded a [2,6,7,1,8,4] :=
  branch_excluded a [2,6,7,1,8,4] (by decide)
    (fin9_cases _
      node_167
      (invalid_excluded a [2,6,7,1,8,4,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,2] (by decide +kernel))
      node_168
      (invalid_excluded a [2,6,7,1,8,4,4] (by decide +kernel))
      node_169
      (invalid_excluded a [2,6,7,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,8] (by decide +kernel)))

theorem node_157 : Excluded a [2,6,7,1,8] :=
  branch_excluded a [2,6,7,1,8] (by decide)
    (fin9_cases _
      node_158
      (invalid_excluded a [2,6,7,1,8,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,2] (by decide +kernel))
      node_159
      node_166
      (invalid_excluded a [2,6,7,1,8,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,8] (by decide +kernel)))

theorem node_140 : Excluded a [2,6,7,1] :=
  branch_excluded a [2,6,7,1] (by decide)
    (fin9_cases _
      node_141
      (invalid_excluded a [2,6,7,1,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,2] (by decide +kernel))
      node_142
      (invalid_excluded a [2,6,7,1,4] (by decide +kernel))
      node_143
      (invalid_excluded a [2,6,7,1,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,7] (by decide +kernel))
      node_157)

theorem node_174 : Excluded a [2,6,7,5,0] :=
  source_excluded a [2,6,7,5,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_175 : Excluded a [2,6,7,5,1] :=
  source_excluded a [2,6,7,5,1] 0 3 4 (by decide) (by decide +kernel)

theorem node_176 : Excluded a [2,6,7,5,3] :=
  source_excluded a [2,6,7,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_178 : Excluded a [2,6,7,5,8,0] :=
  source_excluded a [2,6,7,5,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_179 : Excluded a [2,6,7,5,8,1] :=
  source_excluded a [2,6,7,5,8,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_181 : Excluded a [2,6,7,5,8,3,0] :=
  source_excluded a [2,6,7,5,8,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_182 : Excluded a [2,6,7,5,8,3,1] :=
  predecessor_excluded a [2,6,7,5,8,3,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_183 : Excluded a [2,6,7,5,8,3,4] :=
  predecessor_excluded a [2,6,7,5,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_180 : Excluded a [2,6,7,5,8,3] :=
  branch_excluded a [2,6,7,5,8,3] (by decide)
    (fin9_cases _
      node_181
      node_182
      (invalid_excluded a [2,6,7,5,8,3,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,5,8,3,3] (by decide +kernel))
      node_183
      (invalid_excluded a [2,6,7,5,8,3,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,5,8,3,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,5,8,3,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,5,8,3,8] (by decide +kernel)))

theorem node_184 : Excluded a [2,6,7,5,8,4] :=
  source_excluded a [2,6,7,5,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_177 : Excluded a [2,6,7,5,8] :=
  branch_excluded a [2,6,7,5,8] (by decide)
    (fin9_cases _
      node_178
      node_179
      (invalid_excluded a [2,6,7,5,8,2] (by decide +kernel))
      node_180
      node_184
      (invalid_excluded a [2,6,7,5,8,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,5,8,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,5,8,8] (by decide +kernel)))

theorem node_173 : Excluded a [2,6,7,5] :=
  branch_excluded a [2,6,7,5] (by decide)
    (fin9_cases _
      node_174
      node_175
      (invalid_excluded a [2,6,7,5,2] (by decide +kernel))
      node_176
      (invalid_excluded a [2,6,7,5,4] (by decide +kernel))
      (invalid_excluded a [2,6,7,5,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,5,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,5,7] (by decide +kernel))
      node_177)

theorem node_185 : Excluded a [2,6,7,8] :=
  predecessor_excluded a [2,6,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_138 : Excluded a [2,6,7] :=
  branch_excluded a [2,6,7] (by decide)
    (fin9_cases _
      node_139
      node_140
      (invalid_excluded a [2,6,7,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,3] (by decide +kernel))
      (invalid_excluded a [2,6,7,4] (by decide +kernel))
      node_173
      (invalid_excluded a [2,6,7,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,7] (by decide +kernel))
      node_185)

theorem node_187 : Excluded a [2,6,8,0] :=
  predecessor_excluded a [2,6,8,0] 1 2 3 0 (by decide) (by decide +kernel)

theorem node_189 : Excluded a [2,6,8,1,0] :=
  source_excluded a [2,6,8,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_190 : Excluded a [2,6,8,1,3] :=
  source_excluded a [2,6,8,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_192 : Excluded a [2,6,8,1,5,0] :=
  source_excluded a [2,6,8,1,5,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_193 : Excluded a [2,6,8,1,5,3] :=
  predecessor_excluded a [2,6,8,1,5,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_195 : Excluded a [2,6,8,1,5,4,0] :=
  source_excluded a [2,6,8,1,5,4,0] 1 2 6 (by decide) (by decide +kernel)

def b_198 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 6
  | 2 => 8
  | 3 => 1
  | 4 => 5
  | 5 => 4
  | 6 => 3
  | 7 => 0
  | 8 => 7
  | _ => 0

def cert_198 : LosingRegion (edgeOf a b_198) 0 :=
  losingMask a b_198 0 2116804251704816815309824
    (by decide +kernel) (by decide +kernel)

theorem node_198 : Excluded a [2,6,8,1,5,4,3,0,7] :=
  losing_excluded a [2,6,8,1,5,4,3,0,7] (by decide) b_198 (by decide +kernel) 2 0 1 cert_198 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_198 2 0 ∧ 1 ≠ 2 ∧ maskRegion 2116804251704816815309824 2 1; decide +kernel)

theorem node_197 : Excluded a [2,6,8,1,5,4,3,0] :=
  branch_excluded a [2,6,8,1,5,4,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,8,1,5,4,3,0,0] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,3,0,1] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,3,0,2] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,3,0,3] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,3,0,4] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,3,0,5] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,3,0,6] (by decide +kernel))
      node_198
      (invalid_excluded a [2,6,8,1,5,4,3,0,8] (by decide +kernel)))

theorem node_196 : Excluded a [2,6,8,1,5,4,3] :=
  branch_excluded a [2,6,8,1,5,4,3] (by decide)
    (fin9_cases _
      node_197
      (invalid_excluded a [2,6,8,1,5,4,3,1] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,3,2] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,3,3] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,3,4] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,3,5] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,3,6] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,3,7] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,3,8] (by decide +kernel)))

theorem node_194 : Excluded a [2,6,8,1,5,4] :=
  branch_excluded a [2,6,8,1,5,4] (by decide)
    (fin9_cases _
      node_195
      (invalid_excluded a [2,6,8,1,5,4,1] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,2] (by decide +kernel))
      node_196
      (invalid_excluded a [2,6,8,1,5,4,4] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,5] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,6] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,7] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,4,8] (by decide +kernel)))

theorem node_199 : Excluded a [2,6,8,1,5,7] :=
  source_excluded a [2,6,8,1,5,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_191 : Excluded a [2,6,8,1,5] :=
  branch_excluded a [2,6,8,1,5] (by decide)
    (fin9_cases _
      node_192
      (invalid_excluded a [2,6,8,1,5,1] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,2] (by decide +kernel))
      node_193
      node_194
      (invalid_excluded a [2,6,8,1,5,5] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5,6] (by decide +kernel))
      node_199
      (invalid_excluded a [2,6,8,1,5,8] (by decide +kernel)))

theorem node_200 : Excluded a [2,6,8,1,7] :=
  predecessor_excluded a [2,6,8,1,7] 0 8 4 2 (by decide) (by decide +kernel)

theorem node_188 : Excluded a [2,6,8,1] :=
  branch_excluded a [2,6,8,1] (by decide)
    (fin9_cases _
      node_189
      (invalid_excluded a [2,6,8,1,1] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,2] (by decide +kernel))
      node_190
      (invalid_excluded a [2,6,8,1,4] (by decide +kernel))
      node_191
      (invalid_excluded a [2,6,8,1,6] (by decide +kernel))
      node_200
      (invalid_excluded a [2,6,8,1,8] (by decide +kernel)))

theorem node_201 : Excluded a [2,6,8,5] :=
  predecessor_excluded a [2,6,8,5] 0 5 2 3 (by decide) (by decide +kernel)

theorem node_203 : Excluded a [2,6,8,7,0] :=
  source_excluded a [2,6,8,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_204 : Excluded a [2,6,8,7,1] :=
  source_excluded a [2,6,8,7,1] 0 3 4 (by decide) (by decide +kernel)

theorem node_205 : Excluded a [2,6,8,7,3] :=
  source_excluded a [2,6,8,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_207 : Excluded a [2,6,8,7,5,0] :=
  source_excluded a [2,6,8,7,5,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_208 : Excluded a [2,6,8,7,5,1] :=
  source_excluded a [2,6,8,7,5,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_209 : Excluded a [2,6,8,7,5,3] :=
  predecessor_excluded a [2,6,8,7,5,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_211 : Excluded a [2,6,8,7,5,4,0] :=
  source_excluded a [2,6,8,7,5,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_212 : Excluded a [2,6,8,7,5,4,1] :=
  predecessor_excluded a [2,6,8,7,5,4,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_213 : Excluded a [2,6,8,7,5,4,3] :=
  source_excluded a [2,6,8,7,5,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_210 : Excluded a [2,6,8,7,5,4] :=
  branch_excluded a [2,6,8,7,5,4] (by decide)
    (fin9_cases _
      node_211
      node_212
      (invalid_excluded a [2,6,8,7,5,4,2] (by decide +kernel))
      node_213
      (invalid_excluded a [2,6,8,7,5,4,4] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,5,4,5] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,5,4,6] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,5,4,7] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,5,4,8] (by decide +kernel)))

theorem node_206 : Excluded a [2,6,8,7,5] :=
  branch_excluded a [2,6,8,7,5] (by decide)
    (fin9_cases _
      node_207
      node_208
      (invalid_excluded a [2,6,8,7,5,2] (by decide +kernel))
      node_209
      node_210
      (invalid_excluded a [2,6,8,7,5,5] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,5,6] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,5,7] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,5,8] (by decide +kernel)))

theorem node_202 : Excluded a [2,6,8,7] :=
  branch_excluded a [2,6,8,7] (by decide)
    (fin9_cases _
      node_203
      node_204
      (invalid_excluded a [2,6,8,7,2] (by decide +kernel))
      node_205
      (invalid_excluded a [2,6,8,7,4] (by decide +kernel))
      node_206
      (invalid_excluded a [2,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,8] (by decide +kernel)))

theorem node_186 : Excluded a [2,6,8] :=
  branch_excluded a [2,6,8] (by decide)
    (fin9_cases _
      node_187
      node_188
      (invalid_excluded a [2,6,8,2] (by decide +kernel))
      (invalid_excluded a [2,6,8,3] (by decide +kernel))
      (invalid_excluded a [2,6,8,4] (by decide +kernel))
      node_201
      (invalid_excluded a [2,6,8,6] (by decide +kernel))
      node_202
      (invalid_excluded a [2,6,8,8] (by decide +kernel)))

theorem node_103 : Excluded a [2,6] :=
  branch_excluded a [2,6] (by decide)
    (fin9_cases _
      node_104
      node_105
      (invalid_excluded a [2,6,2] (by decide +kernel))
      (invalid_excluded a [2,6,3] (by decide +kernel))
      node_106
      node_107
      (invalid_excluded a [2,6,6] (by decide +kernel))
      node_138
      node_186)

theorem node_215 : Excluded a [2,7,0] :=
  predecessor_excluded a [2,7,0] 3 0 0 2 (by decide) (by decide +kernel)

theorem node_216 : Excluded a [2,7,1] :=
  source_excluded a [2,7,1] 0 3 2 (by decide) (by decide +kernel)

theorem node_217 : Excluded a [2,7,4] :=
  source_excluded a [2,7,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_219 : Excluded a [2,7,5,0] :=
  predecessor_excluded a [2,7,5,0] 1 2 3 0 (by decide) (by decide +kernel)

theorem node_221 : Excluded a [2,7,5,1,0] :=
  source_excluded a [2,7,5,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_222 : Excluded a [2,7,5,1,3] :=
  source_excluded a [2,7,5,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_225 : Excluded a [2,7,5,1,6,0,3] :=
  predecessor_excluded a [2,7,5,1,6,0,3] 0 3 4 6 (by decide) (by decide +kernel)

theorem node_227 : Excluded a [2,7,5,1,6,0,4,3] :=
  branch_excluded a [2,7,5,1,6,0,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,5,1,6,0,4,3,0] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,4,3,1] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,4,3,2] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,4,3,3] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,4,3,4] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,4,3,5] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,4,3,6] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,4,3,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,4,3,8] (by decide +kernel)))

theorem node_226 : Excluded a [2,7,5,1,6,0,4] :=
  branch_excluded a [2,7,5,1,6,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,5,1,6,0,4,0] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,4,1] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,4,2] (by decide +kernel))
      node_227
      (invalid_excluded a [2,7,5,1,6,0,4,4] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,4,5] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,4,6] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,4,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,4,8] (by decide +kernel)))

theorem node_228 : Excluded a [2,7,5,1,6,0,8] :=
  source_excluded a [2,7,5,1,6,0,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_224 : Excluded a [2,7,5,1,6,0] :=
  branch_excluded a [2,7,5,1,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,5,1,6,0,0] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,1] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,2] (by decide +kernel))
      node_225
      node_226
      (invalid_excluded a [2,7,5,1,6,0,5] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,6] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,0,7] (by decide +kernel))
      node_228)

theorem node_229 : Excluded a [2,7,5,1,6,3] :=
  source_excluded a [2,7,5,1,6,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_230 : Excluded a [2,7,5,1,6,4] :=
  source_excluded a [2,7,5,1,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_232 : Excluded a [2,7,5,1,6,8,0] :=
  source_excluded a [2,7,5,1,6,8,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_233 : Excluded a [2,7,5,1,6,8,3] :=
  predecessor_excluded a [2,7,5,1,6,8,3] 0 3 4 6 (by decide) (by decide +kernel)

theorem node_235 : Excluded a [2,7,5,1,6,8,4,0] :=
  source_excluded a [2,7,5,1,6,8,4,0] 1 2 7 (by decide) (by decide +kernel)

def b_237 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 7
  | 2 => 5
  | 3 => 1
  | 4 => 6
  | 5 => 8
  | 6 => 4
  | 7 => 3
  | 8 => 0
  | _ => 0

def cert_237 : LosingRegion (edgeOf a b_237) 0 :=
  losingMask a b_237 0 1212476292088678999131136
    (by decide +kernel) (by decide +kernel)

theorem node_237 : Excluded a [2,7,5,1,6,8,4,3,0] :=
  losing_excluded a [2,7,5,1,6,8,4,3,0] (by decide) b_237 (by decide +kernel) 2 0 1 cert_237 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_237 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1212476292088678999131136 2 1; decide +kernel)

theorem node_236 : Excluded a [2,7,5,1,6,8,4,3] :=
  branch_excluded a [2,7,5,1,6,8,4,3] (by decide)
    (fin9_cases _
      node_237
      (invalid_excluded a [2,7,5,1,6,8,4,3,1] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,8,4,3,2] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,8,4,3,5] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,8,4,3,6] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,8,4,3,8] (by decide +kernel)))

theorem node_234 : Excluded a [2,7,5,1,6,8,4] :=
  branch_excluded a [2,7,5,1,6,8,4] (by decide)
    (fin9_cases _
      node_235
      (invalid_excluded a [2,7,5,1,6,8,4,1] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,8,4,2] (by decide +kernel))
      node_236
      (invalid_excluded a [2,7,5,1,6,8,4,4] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,8,4,5] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,8,4,6] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,8,4,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,8,4,8] (by decide +kernel)))

theorem node_231 : Excluded a [2,7,5,1,6,8] :=
  branch_excluded a [2,7,5,1,6,8] (by decide)
    (fin9_cases _
      node_232
      (invalid_excluded a [2,7,5,1,6,8,1] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,8,2] (by decide +kernel))
      node_233
      node_234
      (invalid_excluded a [2,7,5,1,6,8,5] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,8,6] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,8,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,8,8] (by decide +kernel)))

theorem node_223 : Excluded a [2,7,5,1,6] :=
  branch_excluded a [2,7,5,1,6] (by decide)
    (fin9_cases _
      node_224
      (invalid_excluded a [2,7,5,1,6,1] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,2] (by decide +kernel))
      node_229
      node_230
      (invalid_excluded a [2,7,5,1,6,5] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,6] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,6,7] (by decide +kernel))
      node_231)

theorem node_238 : Excluded a [2,7,5,1,8] :=
  predecessor_excluded a [2,7,5,1,8] 0 5 4 2 (by decide) (by decide +kernel)

theorem node_220 : Excluded a [2,7,5,1] :=
  branch_excluded a [2,7,5,1] (by decide)
    (fin9_cases _
      node_221
      (invalid_excluded a [2,7,5,1,1] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,2] (by decide +kernel))
      node_222
      (invalid_excluded a [2,7,5,1,4] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,5] (by decide +kernel))
      node_223
      (invalid_excluded a [2,7,5,1,7] (by decide +kernel))
      node_238)

theorem node_239 : Excluded a [2,7,5,6] :=
  predecessor_excluded a [2,7,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_241 : Excluded a [2,7,5,8,0] :=
  source_excluded a [2,7,5,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_242 : Excluded a [2,7,5,8,1] :=
  source_excluded a [2,7,5,8,1] 0 3 4 (by decide) (by decide +kernel)

theorem node_243 : Excluded a [2,7,5,8,3] :=
  source_excluded a [2,7,5,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_246 : Excluded a [2,7,5,8,6,0,1] :=
  source_excluded a [2,7,5,8,6,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_247 : Excluded a [2,7,5,8,6,0,3] :=
  predecessor_excluded a [2,7,5,8,6,0,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_249 : Excluded a [2,7,5,8,6,0,4,1] :=
  predecessor_excluded a [2,7,5,8,6,0,4,1] 2 1 1 7 (by decide) (by decide +kernel)

theorem node_250 : Excluded a [2,7,5,8,6,0,4,3] :=
  source_excluded a [2,7,5,8,6,0,4,3] 7 0 3 (by decide) (by decide +kernel)

theorem node_248 : Excluded a [2,7,5,8,6,0,4] :=
  branch_excluded a [2,7,5,8,6,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,5,8,6,0,4,0] (by decide +kernel))
      node_249
      (invalid_excluded a [2,7,5,8,6,0,4,2] (by decide +kernel))
      node_250
      (invalid_excluded a [2,7,5,8,6,0,4,4] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,6,0,4,5] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,6,0,4,6] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,6,0,4,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,6,0,4,8] (by decide +kernel)))

theorem node_245 : Excluded a [2,7,5,8,6,0] :=
  branch_excluded a [2,7,5,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,5,8,6,0,0] (by decide +kernel))
      node_246
      (invalid_excluded a [2,7,5,8,6,0,2] (by decide +kernel))
      node_247
      node_248
      (invalid_excluded a [2,7,5,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,6,0,8] (by decide +kernel)))

theorem node_251 : Excluded a [2,7,5,8,6,1] :=
  predecessor_excluded a [2,7,5,8,6,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_252 : Excluded a [2,7,5,8,6,3] :=
  source_excluded a [2,7,5,8,6,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_253 : Excluded a [2,7,5,8,6,4] :=
  source_excluded a [2,7,5,8,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_244 : Excluded a [2,7,5,8,6] :=
  branch_excluded a [2,7,5,8,6] (by decide)
    (fin9_cases _
      node_245
      node_251
      (invalid_excluded a [2,7,5,8,6,2] (by decide +kernel))
      node_252
      node_253
      (invalid_excluded a [2,7,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,6,6] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,6,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,6,8] (by decide +kernel)))

theorem node_240 : Excluded a [2,7,5,8] :=
  branch_excluded a [2,7,5,8] (by decide)
    (fin9_cases _
      node_241
      node_242
      (invalid_excluded a [2,7,5,8,2] (by decide +kernel))
      node_243
      (invalid_excluded a [2,7,5,8,4] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,5] (by decide +kernel))
      node_244
      (invalid_excluded a [2,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,8] (by decide +kernel)))

theorem node_218 : Excluded a [2,7,5] :=
  branch_excluded a [2,7,5] (by decide)
    (fin9_cases _
      node_219
      node_220
      (invalid_excluded a [2,7,5,2] (by decide +kernel))
      (invalid_excluded a [2,7,5,3] (by decide +kernel))
      (invalid_excluded a [2,7,5,4] (by decide +kernel))
      (invalid_excluded a [2,7,5,5] (by decide +kernel))
      node_239
      (invalid_excluded a [2,7,5,7] (by decide +kernel))
      node_240)

theorem node_255 : Excluded a [2,7,6,0] :=
  predecessor_excluded a [2,7,6,0] 1 2 3 0 (by decide) (by decide +kernel)

theorem node_257 : Excluded a [2,7,6,1,0] :=
  source_excluded a [2,7,6,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_258 : Excluded a [2,7,6,1,3] :=
  source_excluded a [2,7,6,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_259 : Excluded a [2,7,6,1,5] :=
  predecessor_excluded a [2,7,6,1,5] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_262 : Excluded a [2,7,6,1,8,0,3] :=
  source_excluded a [2,7,6,1,8,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_263 : Excluded a [2,7,6,1,8,0,4] :=
  predecessor_excluded a [2,7,6,1,8,0,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_266 : Excluded a [2,7,6,1,8,0,5,3,4] :=
  predecessor_excluded a [2,7,6,1,8,0,5,3,4] 0 4 7 8 (by decide) (by decide +kernel)

theorem node_265 : Excluded a [2,7,6,1,8,0,5,3] :=
  branch_excluded a [2,7,6,1,8,0,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,1,8,0,5,3,0] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,3,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,3,2] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,3,3] (by decide +kernel))
      node_266
      (invalid_excluded a [2,7,6,1,8,0,5,3,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,3,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,3,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,3,8] (by decide +kernel)))

theorem node_267 : Excluded a [2,7,6,1,8,0,5,4] :=
  source_excluded a [2,7,6,1,8,0,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_264 : Excluded a [2,7,6,1,8,0,5] :=
  branch_excluded a [2,7,6,1,8,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,1,8,0,5,0] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,2] (by decide +kernel))
      node_265
      node_267
      (invalid_excluded a [2,7,6,1,8,0,5,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,8] (by decide +kernel)))

theorem node_261 : Excluded a [2,7,6,1,8,0] :=
  branch_excluded a [2,7,6,1,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,1,8,0,0] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,2] (by decide +kernel))
      node_262
      node_263
      node_264
      (invalid_excluded a [2,7,6,1,8,0,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,8] (by decide +kernel)))

theorem node_268 : Excluded a [2,7,6,1,8,3] :=
  source_excluded a [2,7,6,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_270 : Excluded a [2,7,6,1,8,4,0] :=
  source_excluded a [2,7,6,1,8,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_271 : Excluded a [2,7,6,1,8,4,3] :=
  source_excluded a [2,7,6,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_273 : Excluded a [2,7,6,1,8,4,5,0] :=
  source_excluded a [2,7,6,1,8,4,5,0] 1 2 7 (by decide) (by decide +kernel)

def b_275 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 7
  | 2 => 6
  | 3 => 1
  | 4 => 8
  | 5 => 4
  | 6 => 5
  | 7 => 3
  | 8 => 0
  | _ => 0

def cert_275 : LosingRegion (edgeOf a b_275) 0 :=
  losingMask a b_275 0 1210109914289289664660480
    (by decide +kernel) (by decide +kernel)

theorem node_275 : Excluded a [2,7,6,1,8,4,5,3,0] :=
  losing_excluded a [2,7,6,1,8,4,5,3,0] (by decide) b_275 (by decide +kernel) 2 0 0 cert_275 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_275 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1210109914289289664660480 2 0; decide +kernel)

theorem node_274 : Excluded a [2,7,6,1,8,4,5,3] :=
  branch_excluded a [2,7,6,1,8,4,5,3] (by decide)
    (fin9_cases _
      node_275
      (invalid_excluded a [2,7,6,1,8,4,5,3,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,5,3,2] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,5,3,3] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,5,3,4] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,5,3,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,5,3,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,5,3,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,5,3,8] (by decide +kernel)))

theorem node_272 : Excluded a [2,7,6,1,8,4,5] :=
  branch_excluded a [2,7,6,1,8,4,5] (by decide)
    (fin9_cases _
      node_273
      (invalid_excluded a [2,7,6,1,8,4,5,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,5,2] (by decide +kernel))
      node_274
      (invalid_excluded a [2,7,6,1,8,4,5,4] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,5,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,5,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,5,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,5,8] (by decide +kernel)))

theorem node_269 : Excluded a [2,7,6,1,8,4] :=
  branch_excluded a [2,7,6,1,8,4] (by decide)
    (fin9_cases _
      node_270
      (invalid_excluded a [2,7,6,1,8,4,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,2] (by decide +kernel))
      node_271
      (invalid_excluded a [2,7,6,1,8,4,4] (by decide +kernel))
      node_272
      (invalid_excluded a [2,7,6,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,8] (by decide +kernel)))

theorem node_260 : Excluded a [2,7,6,1,8] :=
  branch_excluded a [2,7,6,1,8] (by decide)
    (fin9_cases _
      node_261
      (invalid_excluded a [2,7,6,1,8,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,2] (by decide +kernel))
      node_268
      node_269
      (invalid_excluded a [2,7,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,8] (by decide +kernel)))

theorem node_256 : Excluded a [2,7,6,1] :=
  branch_excluded a [2,7,6,1] (by decide)
    (fin9_cases _
      node_257
      (invalid_excluded a [2,7,6,1,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,2] (by decide +kernel))
      node_258
      (invalid_excluded a [2,7,6,1,4] (by decide +kernel))
      node_259
      (invalid_excluded a [2,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,7] (by decide +kernel))
      node_260)

theorem node_277 : Excluded a [2,7,6,5,0] :=
  source_excluded a [2,7,6,5,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_278 : Excluded a [2,7,6,5,1] :=
  source_excluded a [2,7,6,5,1] 0 3 4 (by decide) (by decide +kernel)

theorem node_279 : Excluded a [2,7,6,5,3] :=
  source_excluded a [2,7,6,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_282 : Excluded a [2,7,6,5,8,0,1] :=
  source_excluded a [2,7,6,5,8,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_283 : Excluded a [2,7,6,5,8,0,3] :=
  source_excluded a [2,7,6,5,8,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_284 : Excluded a [2,7,6,5,8,0,4] :=
  predecessor_excluded a [2,7,6,5,8,0,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_281 : Excluded a [2,7,6,5,8,0] :=
  branch_excluded a [2,7,6,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,5,8,0,0] (by decide +kernel))
      node_282
      (invalid_excluded a [2,7,6,5,8,0,2] (by decide +kernel))
      node_283
      node_284
      (invalid_excluded a [2,7,6,5,8,0,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,5,8,0,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,5,8,0,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,5,8,0,8] (by decide +kernel)))

theorem node_285 : Excluded a [2,7,6,5,8,1] :=
  predecessor_excluded a [2,7,6,5,8,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_286 : Excluded a [2,7,6,5,8,3] :=
  source_excluded a [2,7,6,5,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_287 : Excluded a [2,7,6,5,8,4] :=
  source_excluded a [2,7,6,5,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_280 : Excluded a [2,7,6,5,8] :=
  branch_excluded a [2,7,6,5,8] (by decide)
    (fin9_cases _
      node_281
      node_285
      (invalid_excluded a [2,7,6,5,8,2] (by decide +kernel))
      node_286
      node_287
      (invalid_excluded a [2,7,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,5,8,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,5,8,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,5,8,8] (by decide +kernel)))

theorem node_276 : Excluded a [2,7,6,5] :=
  branch_excluded a [2,7,6,5] (by decide)
    (fin9_cases _
      node_277
      node_278
      (invalid_excluded a [2,7,6,5,2] (by decide +kernel))
      node_279
      (invalid_excluded a [2,7,6,5,4] (by decide +kernel))
      (invalid_excluded a [2,7,6,5,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,5,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,5,7] (by decide +kernel))
      node_280)

theorem node_289 : Excluded a [2,7,6,8,0] :=
  source_excluded a [2,7,6,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_290 : Excluded a [2,7,6,8,1] :=
  source_excluded a [2,7,6,8,1] 0 3 4 (by decide) (by decide +kernel)

theorem node_291 : Excluded a [2,7,6,8,3] :=
  source_excluded a [2,7,6,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_292 : Excluded a [2,7,6,8,5] :=
  predecessor_excluded a [2,7,6,8,5] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_288 : Excluded a [2,7,6,8] :=
  branch_excluded a [2,7,6,8] (by decide)
    (fin9_cases _
      node_289
      node_290
      (invalid_excluded a [2,7,6,8,2] (by decide +kernel))
      node_291
      (invalid_excluded a [2,7,6,8,4] (by decide +kernel))
      node_292
      (invalid_excluded a [2,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,8] (by decide +kernel)))

theorem node_254 : Excluded a [2,7,6] :=
  branch_excluded a [2,7,6] (by decide)
    (fin9_cases _
      node_255
      node_256
      (invalid_excluded a [2,7,6,2] (by decide +kernel))
      (invalid_excluded a [2,7,6,3] (by decide +kernel))
      (invalid_excluded a [2,7,6,4] (by decide +kernel))
      node_276
      (invalid_excluded a [2,7,6,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,7] (by decide +kernel))
      node_288)

theorem node_294 : Excluded a [2,7,8,0] :=
  predecessor_excluded a [2,7,8,0] 1 2 3 0 (by decide) (by decide +kernel)

theorem node_296 : Excluded a [2,7,8,1,0] :=
  source_excluded a [2,7,8,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_297 : Excluded a [2,7,8,1,3] :=
  source_excluded a [2,7,8,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_301 : Excluded a [2,7,8,1,5,0,3,4] :=
  predecessor_excluded a [2,7,8,1,5,0,3,4] 0 5 7 4 (by decide) (by decide +kernel)

theorem node_303 : Excluded a [2,7,8,1,5,0,3,6,4] :=
  source_excluded a [2,7,8,1,5,0,3,6,4] 8 0 4 (by decide) (by decide +kernel)

theorem node_302 : Excluded a [2,7,8,1,5,0,3,6] :=
  branch_excluded a [2,7,8,1,5,0,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,1,5,0,3,6,0] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,3,6,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,3,6,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,3,6,3] (by decide +kernel))
      node_303
      (invalid_excluded a [2,7,8,1,5,0,3,6,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,3,6,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,3,6,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,3,6,8] (by decide +kernel)))

theorem node_300 : Excluded a [2,7,8,1,5,0,3] :=
  branch_excluded a [2,7,8,1,5,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,1,5,0,3,0] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,3,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,3,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,3,3] (by decide +kernel))
      node_301
      (invalid_excluded a [2,7,8,1,5,0,3,5] (by decide +kernel))
      node_302
      (invalid_excluded a [2,7,8,1,5,0,3,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,3,8] (by decide +kernel)))

theorem node_305 : Excluded a [2,7,8,1,5,0,4,3] :=
  source_excluded a [2,7,8,1,5,0,4,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_307 : Excluded a [2,7,8,1,5,0,4,6,3] :=
  source_excluded a [2,7,8,1,5,0,4,6,3] 2 0 8 (by decide) (by decide +kernel)

theorem node_306 : Excluded a [2,7,8,1,5,0,4,6] :=
  branch_excluded a [2,7,8,1,5,0,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,1,5,0,4,6,0] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,4,6,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,4,6,2] (by decide +kernel))
      node_307
      (invalid_excluded a [2,7,8,1,5,0,4,6,4] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,4,6,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,4,6,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,4,6,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,4,6,8] (by decide +kernel)))

theorem node_304 : Excluded a [2,7,8,1,5,0,4] :=
  branch_excluded a [2,7,8,1,5,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,1,5,0,4,0] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,4,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,4,2] (by decide +kernel))
      node_305
      (invalid_excluded a [2,7,8,1,5,0,4,4] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,4,5] (by decide +kernel))
      node_306
      (invalid_excluded a [2,7,8,1,5,0,4,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,4,8] (by decide +kernel)))

theorem node_299 : Excluded a [2,7,8,1,5,0] :=
  branch_excluded a [2,7,8,1,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,1,5,0,0] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,2] (by decide +kernel))
      node_300
      node_304
      (invalid_excluded a [2,7,8,1,5,0,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,0,8] (by decide +kernel)))

theorem node_308 : Excluded a [2,7,8,1,5,3] :=
  predecessor_excluded a [2,7,8,1,5,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_310 : Excluded a [2,7,8,1,5,4,0] :=
  source_excluded a [2,7,8,1,5,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_312 : Excluded a [2,7,8,1,5,4,3,0] :=
  source_excluded a [2,7,8,1,5,4,3,0] 1 2 7 (by decide) (by decide +kernel)

def b_314 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 7
  | 2 => 8
  | 3 => 1
  | 4 => 5
  | 5 => 4
  | 6 => 3
  | 7 => 6
  | 8 => 0
  | _ => 0

def cert_314 : LosingRegion (edgeOf a b_314) 0 :=
  losingMask a b_314 0 1212510396680288498353152
    (by decide +kernel) (by decide +kernel)

theorem node_314 : Excluded a [2,7,8,1,5,4,3,6,0] :=
  losing_excluded a [2,7,8,1,5,4,3,6,0] (by decide) b_314 (by decide +kernel) 2 0 8 cert_314 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_314 2 0 ∧ 8 ≠ 2 ∧ maskRegion 1212510396680288498353152 2 8; decide +kernel)

theorem node_313 : Excluded a [2,7,8,1,5,4,3,6] :=
  branch_excluded a [2,7,8,1,5,4,3,6] (by decide)
    (fin9_cases _
      node_314
      (invalid_excluded a [2,7,8,1,5,4,3,6,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,3,6,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,3,6,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,3,6,8] (by decide +kernel)))

theorem node_311 : Excluded a [2,7,8,1,5,4,3] :=
  branch_excluded a [2,7,8,1,5,4,3] (by decide)
    (fin9_cases _
      node_312
      (invalid_excluded a [2,7,8,1,5,4,3,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,3,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,3,3] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,3,4] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,3,5] (by decide +kernel))
      node_313
      (invalid_excluded a [2,7,8,1,5,4,3,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,3,8] (by decide +kernel)))

theorem node_309 : Excluded a [2,7,8,1,5,4] :=
  branch_excluded a [2,7,8,1,5,4] (by decide)
    (fin9_cases _
      node_310
      (invalid_excluded a [2,7,8,1,5,4,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,2] (by decide +kernel))
      node_311
      (invalid_excluded a [2,7,8,1,5,4,4] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,4,8] (by decide +kernel)))

theorem node_298 : Excluded a [2,7,8,1,5] :=
  branch_excluded a [2,7,8,1,5] (by decide)
    (fin9_cases _
      node_299
      (invalid_excluded a [2,7,8,1,5,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,2] (by decide +kernel))
      node_308
      node_309
      (invalid_excluded a [2,7,8,1,5,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5,8] (by decide +kernel)))

theorem node_317 : Excluded a [2,7,8,1,6,0,3] :=
  predecessor_excluded a [2,7,8,1,6,0,3] 0 3 4 6 (by decide) (by decide +kernel)

theorem node_319 : Excluded a [2,7,8,1,6,0,4,3] :=
  source_excluded a [2,7,8,1,6,0,4,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_320 : Excluded a [2,7,8,1,6,0,4,5] :=
  source_excluded a [2,7,8,1,6,0,4,5] 7 0 8 (by decide) (by decide +kernel)

theorem node_318 : Excluded a [2,7,8,1,6,0,4] :=
  branch_excluded a [2,7,8,1,6,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,1,6,0,4,0] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,4,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,4,2] (by decide +kernel))
      node_319
      (invalid_excluded a [2,7,8,1,6,0,4,4] (by decide +kernel))
      node_320
      (invalid_excluded a [2,7,8,1,6,0,4,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,4,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,4,8] (by decide +kernel)))

theorem node_322 : Excluded a [2,7,8,1,6,0,5,3] :=
  source_excluded a [2,7,8,1,6,0,5,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_324 : Excluded a [2,7,8,1,6,0,5,4,3] :=
  source_excluded a [2,7,8,1,6,0,5,4,3] 2 0 8 (by decide) (by decide +kernel)

theorem node_323 : Excluded a [2,7,8,1,6,0,5,4] :=
  branch_excluded a [2,7,8,1,6,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,1,6,0,5,4,0] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,5,4,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,5,4,2] (by decide +kernel))
      node_324
      (invalid_excluded a [2,7,8,1,6,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,5,4,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,5,4,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,5,4,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,5,4,8] (by decide +kernel)))

theorem node_321 : Excluded a [2,7,8,1,6,0,5] :=
  branch_excluded a [2,7,8,1,6,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,1,6,0,5,0] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,5,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,5,2] (by decide +kernel))
      node_322
      node_323
      (invalid_excluded a [2,7,8,1,6,0,5,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,5,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,5,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,5,8] (by decide +kernel)))

theorem node_316 : Excluded a [2,7,8,1,6,0] :=
  branch_excluded a [2,7,8,1,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,1,6,0,0] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,2] (by decide +kernel))
      node_317
      node_318
      node_321
      (invalid_excluded a [2,7,8,1,6,0,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,0,8] (by decide +kernel)))

theorem node_326 : Excluded a [2,7,8,1,6,3,0] :=
  source_excluded a [2,7,8,1,6,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_327 : Excluded a [2,7,8,1,6,3,4] :=
  predecessor_excluded a [2,7,8,1,6,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_329 : Excluded a [2,7,8,1,6,3,5,0] :=
  source_excluded a [2,7,8,1,6,3,5,0] 1 2 7 (by decide) (by decide +kernel)

def b_331 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 7
  | 2 => 8
  | 3 => 1
  | 4 => 6
  | 5 => 3
  | 6 => 5
  | 7 => 4
  | 8 => 0
  | _ => 0

def cert_331 : LosingRegion (edgeOf a b_331) 0 :=
  losingMask a b_331 0 1212512983435324469281792
    (by decide +kernel) (by decide +kernel)

theorem node_331 : Excluded a [2,7,8,1,6,3,5,4,0] :=
  losing_excluded a [2,7,8,1,6,3,5,4,0] (by decide) b_331 (by decide +kernel) 2 0 8 cert_331 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_331 2 0 ∧ 8 ≠ 2 ∧ maskRegion 1212512983435324469281792 2 8; decide +kernel)

theorem node_330 : Excluded a [2,7,8,1,6,3,5,4] :=
  branch_excluded a [2,7,8,1,6,3,5,4] (by decide)
    (fin9_cases _
      node_331
      (invalid_excluded a [2,7,8,1,6,3,5,4,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,3,5,4,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,3,5,4,3] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,3,5,4,4] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,3,5,4,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,3,5,4,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,3,5,4,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,3,5,4,8] (by decide +kernel)))

theorem node_328 : Excluded a [2,7,8,1,6,3,5] :=
  branch_excluded a [2,7,8,1,6,3,5] (by decide)
    (fin9_cases _
      node_329
      (invalid_excluded a [2,7,8,1,6,3,5,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,3,5,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,3,5,3] (by decide +kernel))
      node_330
      (invalid_excluded a [2,7,8,1,6,3,5,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,3,5,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,3,5,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,3,5,8] (by decide +kernel)))

theorem node_325 : Excluded a [2,7,8,1,6,3] :=
  branch_excluded a [2,7,8,1,6,3] (by decide)
    (fin9_cases _
      node_326
      (invalid_excluded a [2,7,8,1,6,3,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,3,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,3,3] (by decide +kernel))
      node_327
      node_328
      (invalid_excluded a [2,7,8,1,6,3,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,3,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,3,8] (by decide +kernel)))

theorem node_332 : Excluded a [2,7,8,1,6,4] :=
  source_excluded a [2,7,8,1,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_315 : Excluded a [2,7,8,1,6] :=
  branch_excluded a [2,7,8,1,6] (by decide)
    (fin9_cases _
      node_316
      (invalid_excluded a [2,7,8,1,6,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,2] (by decide +kernel))
      node_325
      node_332
      (invalid_excluded a [2,7,8,1,6,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,6,8] (by decide +kernel)))

theorem node_295 : Excluded a [2,7,8,1] :=
  branch_excluded a [2,7,8,1] (by decide)
    (fin9_cases _
      node_296
      (invalid_excluded a [2,7,8,1,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,2] (by decide +kernel))
      node_297
      (invalid_excluded a [2,7,8,1,4] (by decide +kernel))
      node_298
      node_315
      (invalid_excluded a [2,7,8,1,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,8] (by decide +kernel)))

theorem node_333 : Excluded a [2,7,8,5] :=
  predecessor_excluded a [2,7,8,5] 0 5 2 3 (by decide) (by decide +kernel)

theorem node_335 : Excluded a [2,7,8,6,0] :=
  source_excluded a [2,7,8,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_336 : Excluded a [2,7,8,6,1] :=
  source_excluded a [2,7,8,6,1] 0 3 4 (by decide) (by decide +kernel)

theorem node_337 : Excluded a [2,7,8,6,3] :=
  source_excluded a [2,7,8,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_340 : Excluded a [2,7,8,6,5,0,1] :=
  source_excluded a [2,7,8,6,5,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_342 : Excluded a [2,7,8,6,5,0,3,1] :=
  predecessor_excluded a [2,7,8,6,5,0,3,1] 2 1 1 7 (by decide) (by decide +kernel)

theorem node_343 : Excluded a [2,7,8,6,5,0,3,4] :=
  predecessor_excluded a [2,7,8,6,5,0,3,4] 0 5 7 4 (by decide) (by decide +kernel)

theorem node_341 : Excluded a [2,7,8,6,5,0,3] :=
  branch_excluded a [2,7,8,6,5,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,6,5,0,3,0] (by decide +kernel))
      node_342
      (invalid_excluded a [2,7,8,6,5,0,3,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,5,0,3,3] (by decide +kernel))
      node_343
      (invalid_excluded a [2,7,8,6,5,0,3,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,5,0,3,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,5,0,3,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,5,0,3,8] (by decide +kernel)))

theorem node_344 : Excluded a [2,7,8,6,5,0,4] :=
  source_excluded a [2,7,8,6,5,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_339 : Excluded a [2,7,8,6,5,0] :=
  branch_excluded a [2,7,8,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,6,5,0,0] (by decide +kernel))
      node_340
      (invalid_excluded a [2,7,8,6,5,0,2] (by decide +kernel))
      node_341
      node_344
      (invalid_excluded a [2,7,8,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,5,0,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,5,0,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,5,0,8] (by decide +kernel)))

theorem node_345 : Excluded a [2,7,8,6,5,1] :=
  predecessor_excluded a [2,7,8,6,5,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_346 : Excluded a [2,7,8,6,5,3] :=
  source_excluded a [2,7,8,6,5,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_347 : Excluded a [2,7,8,6,5,4] :=
  source_excluded a [2,7,8,6,5,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_338 : Excluded a [2,7,8,6,5] :=
  branch_excluded a [2,7,8,6,5] (by decide)
    (fin9_cases _
      node_339
      node_345
      (invalid_excluded a [2,7,8,6,5,2] (by decide +kernel))
      node_346
      node_347
      (invalid_excluded a [2,7,8,6,5,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,5,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,5,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,5,8] (by decide +kernel)))

theorem node_334 : Excluded a [2,7,8,6] :=
  branch_excluded a [2,7,8,6] (by decide)
    (fin9_cases _
      node_335
      node_336
      (invalid_excluded a [2,7,8,6,2] (by decide +kernel))
      node_337
      (invalid_excluded a [2,7,8,6,4] (by decide +kernel))
      node_338
      (invalid_excluded a [2,7,8,6,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,8] (by decide +kernel)))

theorem node_293 : Excluded a [2,7,8] :=
  branch_excluded a [2,7,8] (by decide)
    (fin9_cases _
      node_294
      node_295
      (invalid_excluded a [2,7,8,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,3] (by decide +kernel))
      (invalid_excluded a [2,7,8,4] (by decide +kernel))
      node_333
      node_334
      (invalid_excluded a [2,7,8,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,8] (by decide +kernel)))

theorem node_214 : Excluded a [2,7] :=
  branch_excluded a [2,7] (by decide)
    (fin9_cases _
      node_215
      node_216
      (invalid_excluded a [2,7,2] (by decide +kernel))
      (invalid_excluded a [2,7,3] (by decide +kernel))
      node_217
      node_218
      node_254
      (invalid_excluded a [2,7,7] (by decide +kernel))
      node_293)

theorem node_349 : Excluded a [2,8,0] :=
  predecessor_excluded a [2,8,0] 3 0 0 2 (by decide) (by decide +kernel)

theorem node_350 : Excluded a [2,8,1] :=
  source_excluded a [2,8,1] 0 3 2 (by decide) (by decide +kernel)

theorem node_351 : Excluded a [2,8,4] :=
  source_excluded a [2,8,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_353 : Excluded a [2,8,5,0] :=
  predecessor_excluded a [2,8,5,0] 1 2 3 0 (by decide) (by decide +kernel)

theorem node_355 : Excluded a [2,8,5,1,0] :=
  source_excluded a [2,8,5,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_356 : Excluded a [2,8,5,1,3] :=
  source_excluded a [2,8,5,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_359 : Excluded a [2,8,5,1,6,0,3] :=
  predecessor_excluded a [2,8,5,1,6,0,3] 0 3 4 6 (by decide) (by decide +kernel)

def b_362 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 8
  | 2 => 5
  | 3 => 1
  | 4 => 6
  | 5 => 0
  | 6 => 4
  | 7 => 3
  | 8 => 7
  | _ => 0

def cert_362 : LosingRegion (edgeOf a b_362) 0 :=
  losingMask a b_362 0 1380480522632865206240256
    (by decide +kernel) (by decide +kernel)

theorem node_362 : Excluded a [2,8,5,1,6,0,4,3,7] :=
  losing_excluded a [2,8,5,1,6,0,4,3,7] (by decide) b_362 (by decide +kernel) 2 0 5 cert_362 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_362 2 0 ∧ 5 ≠ 2 ∧ maskRegion 1380480522632865206240256 2 5; decide +kernel)

theorem node_361 : Excluded a [2,8,5,1,6,0,4,3] :=
  branch_excluded a [2,8,5,1,6,0,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,5,1,6,0,4,3,0] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,4,3,1] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,4,3,2] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,4,3,3] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,4,3,4] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,4,3,5] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,4,3,6] (by decide +kernel))
      node_362
      (invalid_excluded a [2,8,5,1,6,0,4,3,8] (by decide +kernel)))

theorem node_360 : Excluded a [2,8,5,1,6,0,4] :=
  branch_excluded a [2,8,5,1,6,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,5,1,6,0,4,0] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,4,1] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,4,2] (by decide +kernel))
      node_361
      (invalid_excluded a [2,8,5,1,6,0,4,4] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,4,5] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,4,6] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,4,7] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,4,8] (by decide +kernel)))

theorem node_358 : Excluded a [2,8,5,1,6,0] :=
  branch_excluded a [2,8,5,1,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,5,1,6,0,0] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,1] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,2] (by decide +kernel))
      node_359
      node_360
      (invalid_excluded a [2,8,5,1,6,0,5] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,6] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,7] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,0,8] (by decide +kernel)))

theorem node_363 : Excluded a [2,8,5,1,6,3] :=
  source_excluded a [2,8,5,1,6,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_364 : Excluded a [2,8,5,1,6,4] :=
  source_excluded a [2,8,5,1,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_365 : Excluded a [2,8,5,1,6,7] :=
  source_excluded a [2,8,5,1,6,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_357 : Excluded a [2,8,5,1,6] :=
  branch_excluded a [2,8,5,1,6] (by decide)
    (fin9_cases _
      node_358
      (invalid_excluded a [2,8,5,1,6,1] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,2] (by decide +kernel))
      node_363
      node_364
      (invalid_excluded a [2,8,5,1,6,5] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,6,6] (by decide +kernel))
      node_365
      (invalid_excluded a [2,8,5,1,6,8] (by decide +kernel)))

theorem node_369 : Excluded a [2,8,5,1,7,0,3,4] :=
  predecessor_excluded a [2,8,5,1,7,0,3,4] 0 4 6 7 (by decide) (by decide +kernel)

def b_371 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 8
  | 2 => 5
  | 3 => 1
  | 4 => 7
  | 5 => 0
  | 6 => 3
  | 7 => 6
  | 8 => 4
  | _ => 0

def cert_371 : LosingRegion (edgeOf a b_371) 0 :=
  losingMask a b_371 0 1382982074067485912466432
    (by decide +kernel) (by decide +kernel)

theorem node_371 : Excluded a [2,8,5,1,7,0,3,6,4] :=
  losing_excluded a [2,8,5,1,7,0,3,6,4] (by decide) b_371 (by decide +kernel) 2 0 5 cert_371 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_371 2 0 ∧ 5 ≠ 2 ∧ maskRegion 1382982074067485912466432 2 5; decide +kernel)

theorem node_370 : Excluded a [2,8,5,1,7,0,3,6] :=
  branch_excluded a [2,8,5,1,7,0,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,5,1,7,0,3,6,0] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,0,3,6,1] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,0,3,6,2] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,0,3,6,3] (by decide +kernel))
      node_371
      (invalid_excluded a [2,8,5,1,7,0,3,6,5] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,0,3,6,6] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,0,3,6,7] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,0,3,6,8] (by decide +kernel)))

theorem node_368 : Excluded a [2,8,5,1,7,0,3] :=
  branch_excluded a [2,8,5,1,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,5,1,7,0,3,0] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,0,3,1] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,0,3,2] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,0,3,3] (by decide +kernel))
      node_369
      (invalid_excluded a [2,8,5,1,7,0,3,5] (by decide +kernel))
      node_370
      (invalid_excluded a [2,8,5,1,7,0,3,7] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,0,3,8] (by decide +kernel)))

theorem node_372 : Excluded a [2,8,5,1,7,0,4] :=
  source_excluded a [2,8,5,1,7,0,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_367 : Excluded a [2,8,5,1,7,0] :=
  branch_excluded a [2,8,5,1,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,5,1,7,0,0] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,0,1] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,0,2] (by decide +kernel))
      node_368
      node_372
      (invalid_excluded a [2,8,5,1,7,0,5] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,0,6] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,0,7] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,0,8] (by decide +kernel)))

theorem node_373 : Excluded a [2,8,5,1,7,3] :=
  source_excluded a [2,8,5,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_374 : Excluded a [2,8,5,1,7,4] :=
  predecessor_excluded a [2,8,5,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_366 : Excluded a [2,8,5,1,7] :=
  branch_excluded a [2,8,5,1,7] (by decide)
    (fin9_cases _
      node_367
      (invalid_excluded a [2,8,5,1,7,1] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,2] (by decide +kernel))
      node_373
      node_374
      (invalid_excluded a [2,8,5,1,7,5] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,6] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,7] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,7,8] (by decide +kernel)))

theorem node_354 : Excluded a [2,8,5,1] :=
  branch_excluded a [2,8,5,1] (by decide)
    (fin9_cases _
      node_355
      (invalid_excluded a [2,8,5,1,1] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,2] (by decide +kernel))
      node_356
      (invalid_excluded a [2,8,5,1,4] (by decide +kernel))
      (invalid_excluded a [2,8,5,1,5] (by decide +kernel))
      node_357
      node_366
      (invalid_excluded a [2,8,5,1,8] (by decide +kernel)))

theorem node_375 : Excluded a [2,8,5,6] :=
  predecessor_excluded a [2,8,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_377 : Excluded a [2,8,5,7,0] :=
  source_excluded a [2,8,5,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_378 : Excluded a [2,8,5,7,1] :=
  source_excluded a [2,8,5,7,1] 0 3 4 (by decide) (by decide +kernel)

theorem node_379 : Excluded a [2,8,5,7,3] :=
  source_excluded a [2,8,5,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_382 : Excluded a [2,8,5,7,6,0,1] :=
  predecessor_excluded a [2,8,5,7,6,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_383 : Excluded a [2,8,5,7,6,0,3] :=
  source_excluded a [2,8,5,7,6,0,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_384 : Excluded a [2,8,5,7,6,0,4] :=
  source_excluded a [2,8,5,7,6,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_381 : Excluded a [2,8,5,7,6,0] :=
  branch_excluded a [2,8,5,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,5,7,6,0,0] (by decide +kernel))
      node_382
      (invalid_excluded a [2,8,5,7,6,0,2] (by decide +kernel))
      node_383
      node_384
      (invalid_excluded a [2,8,5,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [2,8,5,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [2,8,5,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [2,8,5,7,6,0,8] (by decide +kernel)))

theorem node_386 : Excluded a [2,8,5,7,6,1,0] :=
  predecessor_excluded a [2,8,5,7,6,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_387 : Excluded a [2,8,5,7,6,1,3] :=
  source_excluded a [2,8,5,7,6,1,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_388 : Excluded a [2,8,5,7,6,1,4] :=
  source_excluded a [2,8,5,7,6,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_385 : Excluded a [2,8,5,7,6,1] :=
  branch_excluded a [2,8,5,7,6,1] (by decide)
    (fin9_cases _
      node_386
      (invalid_excluded a [2,8,5,7,6,1,1] (by decide +kernel))
      (invalid_excluded a [2,8,5,7,6,1,2] (by decide +kernel))
      node_387
      node_388
      (invalid_excluded a [2,8,5,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [2,8,5,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [2,8,5,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [2,8,5,7,6,1,8] (by decide +kernel)))

theorem node_389 : Excluded a [2,8,5,7,6,3] :=
  source_excluded a [2,8,5,7,6,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_390 : Excluded a [2,8,5,7,6,4] :=
  source_excluded a [2,8,5,7,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_380 : Excluded a [2,8,5,7,6] :=
  branch_excluded a [2,8,5,7,6] (by decide)
    (fin9_cases _
      node_381
      node_385
      (invalid_excluded a [2,8,5,7,6,2] (by decide +kernel))
      node_389
      node_390
      (invalid_excluded a [2,8,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [2,8,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [2,8,5,7,6,7] (by decide +kernel))
      (invalid_excluded a [2,8,5,7,6,8] (by decide +kernel)))

theorem node_376 : Excluded a [2,8,5,7] :=
  branch_excluded a [2,8,5,7] (by decide)
    (fin9_cases _
      node_377
      node_378
      (invalid_excluded a [2,8,5,7,2] (by decide +kernel))
      node_379
      (invalid_excluded a [2,8,5,7,4] (by decide +kernel))
      (invalid_excluded a [2,8,5,7,5] (by decide +kernel))
      node_380
      (invalid_excluded a [2,8,5,7,7] (by decide +kernel))
      (invalid_excluded a [2,8,5,7,8] (by decide +kernel)))

theorem node_352 : Excluded a [2,8,5] :=
  branch_excluded a [2,8,5] (by decide)
    (fin9_cases _
      node_353
      node_354
      (invalid_excluded a [2,8,5,2] (by decide +kernel))
      (invalid_excluded a [2,8,5,3] (by decide +kernel))
      (invalid_excluded a [2,8,5,4] (by decide +kernel))
      (invalid_excluded a [2,8,5,5] (by decide +kernel))
      node_375
      node_376
      (invalid_excluded a [2,8,5,8] (by decide +kernel)))

theorem node_392 : Excluded a [2,8,6,0] :=
  predecessor_excluded a [2,8,6,0] 1 2 3 0 (by decide) (by decide +kernel)

theorem node_394 : Excluded a [2,8,6,1,0] :=
  source_excluded a [2,8,6,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_395 : Excluded a [2,8,6,1,3] :=
  source_excluded a [2,8,6,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_396 : Excluded a [2,8,6,1,5] :=
  predecessor_excluded a [2,8,6,1,5] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_399 : Excluded a [2,8,6,1,7,0,3] :=
  source_excluded a [2,8,6,1,7,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_400 : Excluded a [2,8,6,1,7,0,4] :=
  source_excluded a [2,8,6,1,7,0,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_402 : Excluded a [2,8,6,1,7,0,5,3] :=
  predecessor_excluded a [2,8,6,1,7,0,5,3] 0 3 4 7 (by decide) (by decide +kernel)

def b_404 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 8
  | 2 => 6
  | 3 => 1
  | 4 => 7
  | 5 => 0
  | 6 => 5
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_404 : LosingRegion (edgeOf a b_404) 0 :=
  losingMask a b_404 0 1364493554617514274063360
    (by decide +kernel) (by decide +kernel)

theorem node_404 : Excluded a [2,8,6,1,7,0,5,4,3] :=
  losing_excluded a [2,8,6,1,7,0,5,4,3] (by decide) b_404 (by decide +kernel) 2 0 1 cert_404 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_404 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1364493554617514274063360 2 1; decide +kernel)

theorem node_403 : Excluded a [2,8,6,1,7,0,5,4] :=
  branch_excluded a [2,8,6,1,7,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,6,1,7,0,5,4,0] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,0,5,4,1] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,0,5,4,2] (by decide +kernel))
      node_404
      (invalid_excluded a [2,8,6,1,7,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,0,5,4,5] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,0,5,4,6] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,0,5,4,7] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,0,5,4,8] (by decide +kernel)))

theorem node_401 : Excluded a [2,8,6,1,7,0,5] :=
  branch_excluded a [2,8,6,1,7,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,6,1,7,0,5,0] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,0,5,1] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,0,5,2] (by decide +kernel))
      node_402
      node_403
      (invalid_excluded a [2,8,6,1,7,0,5,5] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,0,5,6] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,0,5,7] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,0,5,8] (by decide +kernel)))

theorem node_398 : Excluded a [2,8,6,1,7,0] :=
  branch_excluded a [2,8,6,1,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,6,1,7,0,0] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,0,1] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,0,2] (by decide +kernel))
      node_399
      node_400
      node_401
      (invalid_excluded a [2,8,6,1,7,0,6] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,0,7] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,0,8] (by decide +kernel)))

theorem node_405 : Excluded a [2,8,6,1,7,3] :=
  source_excluded a [2,8,6,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_406 : Excluded a [2,8,6,1,7,4] :=
  predecessor_excluded a [2,8,6,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_397 : Excluded a [2,8,6,1,7] :=
  branch_excluded a [2,8,6,1,7] (by decide)
    (fin9_cases _
      node_398
      (invalid_excluded a [2,8,6,1,7,1] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,2] (by decide +kernel))
      node_405
      node_406
      (invalid_excluded a [2,8,6,1,7,5] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,6] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,7] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,7,8] (by decide +kernel)))

theorem node_393 : Excluded a [2,8,6,1] :=
  branch_excluded a [2,8,6,1] (by decide)
    (fin9_cases _
      node_394
      (invalid_excluded a [2,8,6,1,1] (by decide +kernel))
      (invalid_excluded a [2,8,6,1,2] (by decide +kernel))
      node_395
      (invalid_excluded a [2,8,6,1,4] (by decide +kernel))
      node_396
      (invalid_excluded a [2,8,6,1,6] (by decide +kernel))
      node_397
      (invalid_excluded a [2,8,6,1,8] (by decide +kernel)))

theorem node_408 : Excluded a [2,8,6,5,0] :=
  source_excluded a [2,8,6,5,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_409 : Excluded a [2,8,6,5,1] :=
  source_excluded a [2,8,6,5,1] 0 3 4 (by decide) (by decide +kernel)

theorem node_410 : Excluded a [2,8,6,5,3] :=
  source_excluded a [2,8,6,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_413 : Excluded a [2,8,6,5,7,0,1] :=
  predecessor_excluded a [2,8,6,5,7,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_414 : Excluded a [2,8,6,5,7,0,3] :=
  source_excluded a [2,8,6,5,7,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_415 : Excluded a [2,8,6,5,7,0,4] :=
  source_excluded a [2,8,6,5,7,0,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_412 : Excluded a [2,8,6,5,7,0] :=
  branch_excluded a [2,8,6,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,6,5,7,0,0] (by decide +kernel))
      node_413
      (invalid_excluded a [2,8,6,5,7,0,2] (by decide +kernel))
      node_414
      node_415
      (invalid_excluded a [2,8,6,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [2,8,6,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [2,8,6,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [2,8,6,5,7,0,8] (by decide +kernel)))

theorem node_417 : Excluded a [2,8,6,5,7,1,0] :=
  predecessor_excluded a [2,8,6,5,7,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_418 : Excluded a [2,8,6,5,7,1,3] :=
  source_excluded a [2,8,6,5,7,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_419 : Excluded a [2,8,6,5,7,1,4] :=
  source_excluded a [2,8,6,5,7,1,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_416 : Excluded a [2,8,6,5,7,1] :=
  branch_excluded a [2,8,6,5,7,1] (by decide)
    (fin9_cases _
      node_417
      (invalid_excluded a [2,8,6,5,7,1,1] (by decide +kernel))
      (invalid_excluded a [2,8,6,5,7,1,2] (by decide +kernel))
      node_418
      node_419
      (invalid_excluded a [2,8,6,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [2,8,6,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [2,8,6,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [2,8,6,5,7,1,8] (by decide +kernel)))

theorem node_420 : Excluded a [2,8,6,5,7,3] :=
  source_excluded a [2,8,6,5,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_421 : Excluded a [2,8,6,5,7,4] :=
  source_excluded a [2,8,6,5,7,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_411 : Excluded a [2,8,6,5,7] :=
  branch_excluded a [2,8,6,5,7] (by decide)
    (fin9_cases _
      node_412
      node_416
      (invalid_excluded a [2,8,6,5,7,2] (by decide +kernel))
      node_420
      node_421
      (invalid_excluded a [2,8,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [2,8,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [2,8,6,5,7,7] (by decide +kernel))
      (invalid_excluded a [2,8,6,5,7,8] (by decide +kernel)))

theorem node_407 : Excluded a [2,8,6,5] :=
  branch_excluded a [2,8,6,5] (by decide)
    (fin9_cases _
      node_408
      node_409
      (invalid_excluded a [2,8,6,5,2] (by decide +kernel))
      node_410
      (invalid_excluded a [2,8,6,5,4] (by decide +kernel))
      (invalid_excluded a [2,8,6,5,5] (by decide +kernel))
      (invalid_excluded a [2,8,6,5,6] (by decide +kernel))
      node_411
      (invalid_excluded a [2,8,6,5,8] (by decide +kernel)))

theorem node_422 : Excluded a [2,8,6,7] :=
  predecessor_excluded a [2,8,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_391 : Excluded a [2,8,6] :=
  branch_excluded a [2,8,6] (by decide)
    (fin9_cases _
      node_392
      node_393
      (invalid_excluded a [2,8,6,2] (by decide +kernel))
      (invalid_excluded a [2,8,6,3] (by decide +kernel))
      (invalid_excluded a [2,8,6,4] (by decide +kernel))
      node_407
      (invalid_excluded a [2,8,6,6] (by decide +kernel))
      node_422
      (invalid_excluded a [2,8,6,8] (by decide +kernel)))

theorem node_424 : Excluded a [2,8,7,0] :=
  predecessor_excluded a [2,8,7,0] 1 2 3 0 (by decide) (by decide +kernel)

theorem node_426 : Excluded a [2,8,7,1,0] :=
  source_excluded a [2,8,7,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_427 : Excluded a [2,8,7,1,3] :=
  source_excluded a [2,8,7,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_430 : Excluded a [2,8,7,1,5,0,3] :=
  source_excluded a [2,8,7,1,5,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_432 : Excluded a [2,8,7,1,5,0,4,3] :=
  source_excluded a [2,8,7,1,5,0,4,3] 2 0 7 (by decide) (by decide +kernel)

def b_434 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 8
  | 2 => 7
  | 3 => 1
  | 4 => 5
  | 5 => 0
  | 6 => 4
  | 7 => 6
  | 8 => 3
  | _ => 0

def cert_434 : LosingRegion (edgeOf a b_434) 0 :=
  losingMask a b_434 0 1212494292962164501906432
    (by decide +kernel) (by decide +kernel)

theorem node_434 : Excluded a [2,8,7,1,5,0,4,6,3] :=
  losing_excluded a [2,8,7,1,5,0,4,6,3] (by decide) b_434 (by decide +kernel) 2 0 0 cert_434 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_434 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1212494292962164501906432 2 0; decide +kernel)

theorem node_433 : Excluded a [2,8,7,1,5,0,4,6] :=
  branch_excluded a [2,8,7,1,5,0,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,7,1,5,0,4,6,0] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,0,4,6,1] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,0,4,6,2] (by decide +kernel))
      node_434
      (invalid_excluded a [2,8,7,1,5,0,4,6,4] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,0,4,6,5] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,0,4,6,6] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,0,4,6,7] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,0,4,6,8] (by decide +kernel)))

theorem node_431 : Excluded a [2,8,7,1,5,0,4] :=
  branch_excluded a [2,8,7,1,5,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,7,1,5,0,4,0] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,0,4,1] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,0,4,2] (by decide +kernel))
      node_432
      (invalid_excluded a [2,8,7,1,5,0,4,4] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,0,4,5] (by decide +kernel))
      node_433
      (invalid_excluded a [2,8,7,1,5,0,4,7] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,0,4,8] (by decide +kernel)))

theorem node_429 : Excluded a [2,8,7,1,5,0] :=
  branch_excluded a [2,8,7,1,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,7,1,5,0,0] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,0,1] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,0,2] (by decide +kernel))
      node_430
      node_431
      (invalid_excluded a [2,8,7,1,5,0,5] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,0,6] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,0,7] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,0,8] (by decide +kernel)))

theorem node_435 : Excluded a [2,8,7,1,5,3] :=
  predecessor_excluded a [2,8,7,1,5,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_438 : Excluded a [2,8,7,1,5,4,0,3] :=
  source_excluded a [2,8,7,1,5,4,0,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_440 : Excluded a [2,8,7,1,5,4,0,6,3] :=
  predecessor_excluded a [2,8,7,1,5,4,0,6,3] 0 4 8 5 (by decide) (by decide +kernel)

theorem node_439 : Excluded a [2,8,7,1,5,4,0,6] :=
  branch_excluded a [2,8,7,1,5,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,7,1,5,4,0,6,0] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,4,0,6,1] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,4,0,6,2] (by decide +kernel))
      node_440
      (invalid_excluded a [2,8,7,1,5,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,4,0,6,7] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,4,0,6,8] (by decide +kernel)))

theorem node_437 : Excluded a [2,8,7,1,5,4,0] :=
  branch_excluded a [2,8,7,1,5,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,7,1,5,4,0,0] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,4,0,1] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,4,0,2] (by decide +kernel))
      node_438
      (invalid_excluded a [2,8,7,1,5,4,0,4] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,4,0,5] (by decide +kernel))
      node_439
      (invalid_excluded a [2,8,7,1,5,4,0,7] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,4,0,8] (by decide +kernel)))

theorem node_441 : Excluded a [2,8,7,1,5,4,3] :=
  source_excluded a [2,8,7,1,5,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_436 : Excluded a [2,8,7,1,5,4] :=
  branch_excluded a [2,8,7,1,5,4] (by decide)
    (fin9_cases _
      node_437
      (invalid_excluded a [2,8,7,1,5,4,1] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,4,2] (by decide +kernel))
      node_441
      (invalid_excluded a [2,8,7,1,5,4,4] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,4,5] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,4,6] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,4,7] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,4,8] (by decide +kernel)))

theorem node_428 : Excluded a [2,8,7,1,5] :=
  branch_excluded a [2,8,7,1,5] (by decide)
    (fin9_cases _
      node_429
      (invalid_excluded a [2,8,7,1,5,1] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,2] (by decide +kernel))
      node_435
      node_436
      (invalid_excluded a [2,8,7,1,5,5] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,6] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,7] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,5,8] (by decide +kernel)))

theorem node_442 : Excluded a [2,8,7,1,6] :=
  predecessor_excluded a [2,8,7,1,6] 0 7 4 2 (by decide) (by decide +kernel)

theorem node_425 : Excluded a [2,8,7,1] :=
  branch_excluded a [2,8,7,1] (by decide)
    (fin9_cases _
      node_426
      (invalid_excluded a [2,8,7,1,1] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,2] (by decide +kernel))
      node_427
      (invalid_excluded a [2,8,7,1,4] (by decide +kernel))
      node_428
      node_442
      (invalid_excluded a [2,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [2,8,7,1,8] (by decide +kernel)))

theorem node_444 : Excluded a [2,8,7,5,0] :=
  source_excluded a [2,8,7,5,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_445 : Excluded a [2,8,7,5,1] :=
  source_excluded a [2,8,7,5,1] 0 3 4 (by decide) (by decide +kernel)

theorem node_446 : Excluded a [2,8,7,5,3] :=
  source_excluded a [2,8,7,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_447 : Excluded a [2,8,7,5,6] :=
  predecessor_excluded a [2,8,7,5,6] 0 7 4 2 (by decide) (by decide +kernel)

theorem node_443 : Excluded a [2,8,7,5] :=
  branch_excluded a [2,8,7,5] (by decide)
    (fin9_cases _
      node_444
      node_445
      (invalid_excluded a [2,8,7,5,2] (by decide +kernel))
      node_446
      (invalid_excluded a [2,8,7,5,4] (by decide +kernel))
      (invalid_excluded a [2,8,7,5,5] (by decide +kernel))
      node_447
      (invalid_excluded a [2,8,7,5,7] (by decide +kernel))
      (invalid_excluded a [2,8,7,5,8] (by decide +kernel)))

theorem node_449 : Excluded a [2,8,7,6,0] :=
  source_excluded a [2,8,7,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_450 : Excluded a [2,8,7,6,1] :=
  source_excluded a [2,8,7,6,1] 0 3 4 (by decide) (by decide +kernel)

theorem node_451 : Excluded a [2,8,7,6,3] :=
  source_excluded a [2,8,7,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_454 : Excluded a [2,8,7,6,5,0,1] :=
  predecessor_excluded a [2,8,7,6,5,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_455 : Excluded a [2,8,7,6,5,0,3] :=
  source_excluded a [2,8,7,6,5,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_456 : Excluded a [2,8,7,6,5,0,4] :=
  source_excluded a [2,8,7,6,5,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_453 : Excluded a [2,8,7,6,5,0] :=
  branch_excluded a [2,8,7,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,8,7,6,5,0,0] (by decide +kernel))
      node_454
      (invalid_excluded a [2,8,7,6,5,0,2] (by decide +kernel))
      node_455
      node_456
      (invalid_excluded a [2,8,7,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [2,8,7,6,5,0,6] (by decide +kernel))
      (invalid_excluded a [2,8,7,6,5,0,7] (by decide +kernel))
      (invalid_excluded a [2,8,7,6,5,0,8] (by decide +kernel)))

theorem node_458 : Excluded a [2,8,7,6,5,1,0] :=
  predecessor_excluded a [2,8,7,6,5,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_459 : Excluded a [2,8,7,6,5,1,3] :=
  source_excluded a [2,8,7,6,5,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_460 : Excluded a [2,8,7,6,5,1,4] :=
  source_excluded a [2,8,7,6,5,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_457 : Excluded a [2,8,7,6,5,1] :=
  branch_excluded a [2,8,7,6,5,1] (by decide)
    (fin9_cases _
      node_458
      (invalid_excluded a [2,8,7,6,5,1,1] (by decide +kernel))
      (invalid_excluded a [2,8,7,6,5,1,2] (by decide +kernel))
      node_459
      node_460
      (invalid_excluded a [2,8,7,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [2,8,7,6,5,1,6] (by decide +kernel))
      (invalid_excluded a [2,8,7,6,5,1,7] (by decide +kernel))
      (invalid_excluded a [2,8,7,6,5,1,8] (by decide +kernel)))

theorem node_461 : Excluded a [2,8,7,6,5,3] :=
  source_excluded a [2,8,7,6,5,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_462 : Excluded a [2,8,7,6,5,4] :=
  source_excluded a [2,8,7,6,5,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_452 : Excluded a [2,8,7,6,5] :=
  branch_excluded a [2,8,7,6,5] (by decide)
    (fin9_cases _
      node_453
      node_457
      (invalid_excluded a [2,8,7,6,5,2] (by decide +kernel))
      node_461
      node_462
      (invalid_excluded a [2,8,7,6,5,5] (by decide +kernel))
      (invalid_excluded a [2,8,7,6,5,6] (by decide +kernel))
      (invalid_excluded a [2,8,7,6,5,7] (by decide +kernel))
      (invalid_excluded a [2,8,7,6,5,8] (by decide +kernel)))

theorem node_448 : Excluded a [2,8,7,6] :=
  branch_excluded a [2,8,7,6] (by decide)
    (fin9_cases _
      node_449
      node_450
      (invalid_excluded a [2,8,7,6,2] (by decide +kernel))
      node_451
      (invalid_excluded a [2,8,7,6,4] (by decide +kernel))
      node_452
      (invalid_excluded a [2,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [2,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [2,8,7,6,8] (by decide +kernel)))

theorem node_423 : Excluded a [2,8,7] :=
  branch_excluded a [2,8,7] (by decide)
    (fin9_cases _
      node_424
      node_425
      (invalid_excluded a [2,8,7,2] (by decide +kernel))
      (invalid_excluded a [2,8,7,3] (by decide +kernel))
      (invalid_excluded a [2,8,7,4] (by decide +kernel))
      node_443
      node_448
      (invalid_excluded a [2,8,7,7] (by decide +kernel))
      (invalid_excluded a [2,8,7,8] (by decide +kernel)))

theorem node_348 : Excluded a [2,8] :=
  branch_excluded a [2,8] (by decide)
    (fin9_cases _
      node_349
      node_350
      (invalid_excluded a [2,8,2] (by decide +kernel))
      (invalid_excluded a [2,8,3] (by decide +kernel))
      node_351
      node_352
      node_391
      node_423
      (invalid_excluded a [2,8,8] (by decide +kernel)))

theorem node_2 : Excluded a [2] :=
  branch_excluded a [2] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,0] (by decide +kernel))
      (invalid_excluded a [2,1] (by decide +kernel))
      (invalid_excluded a [2,2] (by decide +kernel))
      node_3
      node_4
      node_5
      node_103
      node_214
      node_348)

theorem node_464 : Excluded a [3,2] :=
  predecessor_excluded a [3,2] 4 3 1 0 (by decide) (by decide +kernel)

theorem node_465 : Excluded a [3,4] :=
  predecessor_excluded a [3,4] 2 4 0 1 (by decide) (by decide +kernel)

theorem node_467 : Excluded a [3,5,0] :=
  source_excluded a [3,5,0] 2 1 0 (by decide) (by decide +kernel)

theorem node_468 : Excluded a [3,5,1] :=
  source_excluded a [3,5,1] 0 2 2 (by decide) (by decide +kernel)

theorem node_469 : Excluded a [3,5,4] :=
  source_excluded a [3,5,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_471 : Excluded a [3,5,6,0] :=
  predecessor_excluded a [3,5,6,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_472 : Excluded a [3,5,6,1] :=
  source_excluded a [3,5,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_473 : Excluded a [3,5,6,2] :=
  source_excluded a [3,5,6,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_474 : Excluded a [3,5,6,7] :=
  predecessor_excluded a [3,5,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_476 : Excluded a [3,5,6,8,0] :=
  predecessor_excluded a [3,5,6,8,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_478 : Excluded a [3,5,6,8,1,0] :=
  source_excluded a [3,5,6,8,1,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_479 : Excluded a [3,5,6,8,1,2] :=
  source_excluded a [3,5,6,8,1,2] 5 0 2 (by decide) (by decide +kernel)

def b_483 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 6
  | 3 => 8
  | 4 => 1
  | 5 => 4
  | 6 => 0
  | 7 => 2
  | 8 => 7
  | _ => 0

def cert_483 : LosingRegion (edgeOf a b_483) 0 :=
  losingMask a b_483 0 1373490377544841494004736
    (by decide +kernel) (by decide +kernel)

theorem node_483 : Excluded a [3,5,6,8,1,4,0,2,7] :=
  losing_excluded a [3,5,6,8,1,4,0,2,7] (by decide) b_483 (by decide +kernel) 2 0 5 cert_483 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_483 2 0 ∧ 5 ≠ 2 ∧ maskRegion 1373490377544841494004736 2 5; decide +kernel)

theorem node_482 : Excluded a [3,5,6,8,1,4,0,2] :=
  branch_excluded a [3,5,6,8,1,4,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,6,8,1,4,0,2,0] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,0,2,1] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,0,2,3] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,0,2,4] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,0,2,6] (by decide +kernel))
      node_483
      (invalid_excluded a [3,5,6,8,1,4,0,2,8] (by decide +kernel)))

theorem node_481 : Excluded a [3,5,6,8,1,4,0] :=
  branch_excluded a [3,5,6,8,1,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,6,8,1,4,0,0] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,0,1] (by decide +kernel))
      node_482
      (invalid_excluded a [3,5,6,8,1,4,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,0,8] (by decide +kernel)))

theorem node_484 : Excluded a [3,5,6,8,1,4,2] :=
  predecessor_excluded a [3,5,6,8,1,4,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_480 : Excluded a [3,5,6,8,1,4] :=
  branch_excluded a [3,5,6,8,1,4] (by decide)
    (fin9_cases _
      node_481
      (invalid_excluded a [3,5,6,8,1,4,1] (by decide +kernel))
      node_484
      (invalid_excluded a [3,5,6,8,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,4] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,4,8] (by decide +kernel)))

theorem node_485 : Excluded a [3,5,6,8,1,7] :=
  source_excluded a [3,5,6,8,1,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_477 : Excluded a [3,5,6,8,1] :=
  branch_excluded a [3,5,6,8,1] (by decide)
    (fin9_cases _
      node_478
      (invalid_excluded a [3,5,6,8,1,1] (by decide +kernel))
      node_479
      (invalid_excluded a [3,5,6,8,1,3] (by decide +kernel))
      node_480
      (invalid_excluded a [3,5,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,1,6] (by decide +kernel))
      node_485
      (invalid_excluded a [3,5,6,8,1,8] (by decide +kernel)))

theorem node_487 : Excluded a [3,5,6,8,7,0] :=
  source_excluded a [3,5,6,8,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_488 : Excluded a [3,5,6,8,7,1] :=
  predecessor_excluded a [3,5,6,8,7,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_489 : Excluded a [3,5,6,8,7,2] :=
  source_excluded a [3,5,6,8,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_490 : Excluded a [3,5,6,8,7,4] :=
  predecessor_excluded a [3,5,6,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_486 : Excluded a [3,5,6,8,7] :=
  branch_excluded a [3,5,6,8,7] (by decide)
    (fin9_cases _
      node_487
      node_488
      node_489
      (invalid_excluded a [3,5,6,8,7,3] (by decide +kernel))
      node_490
      (invalid_excluded a [3,5,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,7,8] (by decide +kernel)))

theorem node_475 : Excluded a [3,5,6,8] :=
  branch_excluded a [3,5,6,8] (by decide)
    (fin9_cases _
      node_476
      node_477
      (invalid_excluded a [3,5,6,8,2] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,4] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,6] (by decide +kernel))
      node_486
      (invalid_excluded a [3,5,6,8,8] (by decide +kernel)))

theorem node_470 : Excluded a [3,5,6] :=
  branch_excluded a [3,5,6] (by decide)
    (fin9_cases _
      node_471
      node_472
      node_473
      (invalid_excluded a [3,5,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,6] (by decide +kernel))
      node_474
      node_475)

theorem node_492 : Excluded a [3,5,7,0] :=
  predecessor_excluded a [3,5,7,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_493 : Excluded a [3,5,7,1] :=
  source_excluded a [3,5,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_494 : Excluded a [3,5,7,2] :=
  source_excluded a [3,5,7,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_496 : Excluded a [3,5,7,6,0] :=
  predecessor_excluded a [3,5,7,6,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_498 : Excluded a [3,5,7,6,1,0] :=
  source_excluded a [3,5,7,6,1,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_499 : Excluded a [3,5,7,6,1,2] :=
  predecessor_excluded a [3,5,7,6,1,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_500 : Excluded a [3,5,7,6,1,4] :=
  source_excluded a [3,5,7,6,1,4] 3 0 5 (by decide) (by decide +kernel)

def b_504 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 7
  | 3 => 6
  | 4 => 1
  | 5 => 8
  | 6 => 0
  | 7 => 2
  | 8 => 4
  | _ => 0

def cert_504 : LosingRegion (edgeOf a b_504) 0 :=
  losingMask a b_504 0 1567817605522680022565888
    (by decide +kernel) (by decide +kernel)

theorem node_504 : Excluded a [3,5,7,6,1,8,0,2,4] :=
  losing_excluded a [3,5,7,6,1,8,0,2,4] (by decide) b_504 (by decide +kernel) 2 0 0 cert_504 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_504 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1567817605522680022565888 2 0; decide +kernel)

theorem node_503 : Excluded a [3,5,7,6,1,8,0,2] :=
  branch_excluded a [3,5,7,6,1,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,6,1,8,0,2,0] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,1,8,0,2,1] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,1,8,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,1,8,0,2,3] (by decide +kernel))
      node_504
      (invalid_excluded a [3,5,7,6,1,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,1,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,1,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,1,8,0,2,8] (by decide +kernel)))

theorem node_505 : Excluded a [3,5,7,6,1,8,0,4] :=
  predecessor_excluded a [3,5,7,6,1,8,0,4] 0 4 2 7 (by decide) (by decide +kernel)

theorem node_502 : Excluded a [3,5,7,6,1,8,0] :=
  branch_excluded a [3,5,7,6,1,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,6,1,8,0,0] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,1,8,0,1] (by decide +kernel))
      node_503
      (invalid_excluded a [3,5,7,6,1,8,0,3] (by decide +kernel))
      node_505
      (invalid_excluded a [3,5,7,6,1,8,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,1,8,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,1,8,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,1,8,0,8] (by decide +kernel)))

theorem node_506 : Excluded a [3,5,7,6,1,8,2] :=
  source_excluded a [3,5,7,6,1,8,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_507 : Excluded a [3,5,7,6,1,8,4] :=
  source_excluded a [3,5,7,6,1,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_501 : Excluded a [3,5,7,6,1,8] :=
  branch_excluded a [3,5,7,6,1,8] (by decide)
    (fin9_cases _
      node_502
      (invalid_excluded a [3,5,7,6,1,8,1] (by decide +kernel))
      node_506
      (invalid_excluded a [3,5,7,6,1,8,3] (by decide +kernel))
      node_507
      (invalid_excluded a [3,5,7,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,1,8,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,1,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,1,8,8] (by decide +kernel)))

theorem node_497 : Excluded a [3,5,7,6,1] :=
  branch_excluded a [3,5,7,6,1] (by decide)
    (fin9_cases _
      node_498
      (invalid_excluded a [3,5,7,6,1,1] (by decide +kernel))
      node_499
      (invalid_excluded a [3,5,7,6,1,3] (by decide +kernel))
      node_500
      (invalid_excluded a [3,5,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,1,7] (by decide +kernel))
      node_501)

theorem node_509 : Excluded a [3,5,7,6,8,0] :=
  source_excluded a [3,5,7,6,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_510 : Excluded a [3,5,7,6,8,1] :=
  predecessor_excluded a [3,5,7,6,8,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_511 : Excluded a [3,5,7,6,8,2] :=
  predecessor_excluded a [3,5,7,6,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_512 : Excluded a [3,5,7,6,8,4] :=
  source_excluded a [3,5,7,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_508 : Excluded a [3,5,7,6,8] :=
  branch_excluded a [3,5,7,6,8] (by decide)
    (fin9_cases _
      node_509
      node_510
      node_511
      (invalid_excluded a [3,5,7,6,8,3] (by decide +kernel))
      node_512
      (invalid_excluded a [3,5,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,8] (by decide +kernel)))

theorem node_495 : Excluded a [3,5,7,6] :=
  branch_excluded a [3,5,7,6] (by decide)
    (fin9_cases _
      node_496
      node_497
      (invalid_excluded a [3,5,7,6,2] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,7] (by decide +kernel))
      node_508)

theorem node_513 : Excluded a [3,5,7,8] :=
  predecessor_excluded a [3,5,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_491 : Excluded a [3,5,7] :=
  branch_excluded a [3,5,7] (by decide)
    (fin9_cases _
      node_492
      node_493
      node_494
      (invalid_excluded a [3,5,7,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,5] (by decide +kernel))
      node_495
      (invalid_excluded a [3,5,7,7] (by decide +kernel))
      node_513)

theorem node_515 : Excluded a [3,5,8,0] :=
  predecessor_excluded a [3,5,8,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_516 : Excluded a [3,5,8,1] :=
  source_excluded a [3,5,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_517 : Excluded a [3,5,8,2] :=
  source_excluded a [3,5,8,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_519 : Excluded a [3,5,8,6,0] :=
  predecessor_excluded a [3,5,8,6,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_521 : Excluded a [3,5,8,6,1,0] :=
  source_excluded a [3,5,8,6,1,0] 1 2 5 (by decide) (by decide +kernel)

def b_525 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 8
  | 3 => 6
  | 4 => 1
  | 5 => 2
  | 6 => 0
  | 7 => 4
  | 8 => 7
  | _ => 0

def cert_525 : LosingRegion (edgeOf a b_525) 0 :=
  losingMask a b_525 0 1735129574271225655723008
    (by decide +kernel) (by decide +kernel)

theorem node_525 : Excluded a [3,5,8,6,1,2,0,4,7] :=
  losing_excluded a [3,5,8,6,1,2,0,4,7] (by decide) b_525 (by decide +kernel) 2 0 0 cert_525 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_525 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1735129574271225655723008 2 0; decide +kernel)

theorem node_524 : Excluded a [3,5,8,6,1,2,0,4] :=
  branch_excluded a [3,5,8,6,1,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,6,1,2,0,4,0] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,0,4,1] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,0,4,2] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,0,4,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,0,4,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,0,4,6] (by decide +kernel))
      node_525
      (invalid_excluded a [3,5,8,6,1,2,0,4,8] (by decide +kernel)))

theorem node_523 : Excluded a [3,5,8,6,1,2,0] :=
  branch_excluded a [3,5,8,6,1,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,6,1,2,0,0] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,0,1] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,0,2] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,0,3] (by decide +kernel))
      node_524
      (invalid_excluded a [3,5,8,6,1,2,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,0,8] (by decide +kernel)))

theorem node_526 : Excluded a [3,5,8,6,1,2,4] :=
  source_excluded a [3,5,8,6,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_522 : Excluded a [3,5,8,6,1,2] :=
  branch_excluded a [3,5,8,6,1,2] (by decide)
    (fin9_cases _
      node_523
      (invalid_excluded a [3,5,8,6,1,2,1] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,3] (by decide +kernel))
      node_526
      (invalid_excluded a [3,5,8,6,1,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,2,8] (by decide +kernel)))

theorem node_527 : Excluded a [3,5,8,6,1,4] :=
  source_excluded a [3,5,8,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_528 : Excluded a [3,5,8,6,1,7] :=
  source_excluded a [3,5,8,6,1,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_520 : Excluded a [3,5,8,6,1] :=
  branch_excluded a [3,5,8,6,1] (by decide)
    (fin9_cases _
      node_521
      (invalid_excluded a [3,5,8,6,1,1] (by decide +kernel))
      node_522
      (invalid_excluded a [3,5,8,6,1,3] (by decide +kernel))
      node_527
      (invalid_excluded a [3,5,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,1,6] (by decide +kernel))
      node_528
      (invalid_excluded a [3,5,8,6,1,8] (by decide +kernel)))

theorem node_529 : Excluded a [3,5,8,6,7] :=
  predecessor_excluded a [3,5,8,6,7] 0 8 4 2 (by decide) (by decide +kernel)

theorem node_518 : Excluded a [3,5,8,6] :=
  branch_excluded a [3,5,8,6] (by decide)
    (fin9_cases _
      node_519
      node_520
      (invalid_excluded a [3,5,8,6,2] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,6] (by decide +kernel))
      node_529
      (invalid_excluded a [3,5,8,6,8] (by decide +kernel)))

theorem node_531 : Excluded a [3,5,8,7,0] :=
  predecessor_excluded a [3,5,8,7,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_533 : Excluded a [3,5,8,7,1,0] :=
  source_excluded a [3,5,8,7,1,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_536 : Excluded a [3,5,8,7,1,2,0,4] :=
  source_excluded a [3,5,8,7,1,2,0,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_538 : Excluded a [3,5,8,7,1,2,0,6,4] :=
  predecessor_excluded a [3,5,8,7,1,2,0,6,4] 0 2 8 5 (by decide) (by decide +kernel)

theorem node_537 : Excluded a [3,5,8,7,1,2,0,6] :=
  branch_excluded a [3,5,8,7,1,2,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,7,1,2,0,6,0] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,2,0,6,1] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,2,0,6,2] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,2,0,6,3] (by decide +kernel))
      node_538
      (invalid_excluded a [3,5,8,7,1,2,0,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,2,0,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,2,0,6,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,2,0,6,8] (by decide +kernel)))

theorem node_535 : Excluded a [3,5,8,7,1,2,0] :=
  branch_excluded a [3,5,8,7,1,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,7,1,2,0,0] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,2,0,1] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,2,0,2] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,2,0,3] (by decide +kernel))
      node_536
      (invalid_excluded a [3,5,8,7,1,2,0,5] (by decide +kernel))
      node_537
      (invalid_excluded a [3,5,8,7,1,2,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,2,0,8] (by decide +kernel)))

theorem node_539 : Excluded a [3,5,8,7,1,2,4] :=
  source_excluded a [3,5,8,7,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_534 : Excluded a [3,5,8,7,1,2] :=
  branch_excluded a [3,5,8,7,1,2] (by decide)
    (fin9_cases _
      node_535
      (invalid_excluded a [3,5,8,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,2,3] (by decide +kernel))
      node_539
      (invalid_excluded a [3,5,8,7,1,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,2,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,2,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,2,8] (by decide +kernel)))

theorem node_542 : Excluded a [3,5,8,7,1,4,0,2] :=
  source_excluded a [3,5,8,7,1,4,0,2] 7 0 2 (by decide) (by decide +kernel)

def b_544 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 8
  | 3 => 7
  | 4 => 1
  | 5 => 4
  | 6 => 0
  | 7 => 6
  | 8 => 2
  | _ => 0

def cert_544 : LosingRegion (edgeOf a b_544) 0 :=
  losingMask a b_544 0 2278247836379948821251072
    (by decide +kernel) (by decide +kernel)

theorem node_544 : Excluded a [3,5,8,7,1,4,0,6,2] :=
  losing_excluded a [3,5,8,7,1,4,0,6,2] (by decide) b_544 (by decide +kernel) 2 0 0 cert_544 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_544 2 0 ∧ 0 ≠ 2 ∧ maskRegion 2278247836379948821251072 2 0; decide +kernel)

theorem node_543 : Excluded a [3,5,8,7,1,4,0,6] :=
  branch_excluded a [3,5,8,7,1,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,7,1,4,0,6,0] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,4,0,6,1] (by decide +kernel))
      node_544
      (invalid_excluded a [3,5,8,7,1,4,0,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,4,0,6,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,4,0,6,8] (by decide +kernel)))

theorem node_541 : Excluded a [3,5,8,7,1,4,0] :=
  branch_excluded a [3,5,8,7,1,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,7,1,4,0,0] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,4,0,1] (by decide +kernel))
      node_542
      (invalid_excluded a [3,5,8,7,1,4,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,4,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,4,0,5] (by decide +kernel))
      node_543
      (invalid_excluded a [3,5,8,7,1,4,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,4,0,8] (by decide +kernel)))

theorem node_545 : Excluded a [3,5,8,7,1,4,2] :=
  predecessor_excluded a [3,5,8,7,1,4,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_540 : Excluded a [3,5,8,7,1,4] :=
  branch_excluded a [3,5,8,7,1,4] (by decide)
    (fin9_cases _
      node_541
      (invalid_excluded a [3,5,8,7,1,4,1] (by decide +kernel))
      node_545
      (invalid_excluded a [3,5,8,7,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,4,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,4,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,4,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,4,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,4,8] (by decide +kernel)))

theorem node_532 : Excluded a [3,5,8,7,1] :=
  branch_excluded a [3,5,8,7,1] (by decide)
    (fin9_cases _
      node_533
      (invalid_excluded a [3,5,8,7,1,1] (by decide +kernel))
      node_534
      (invalid_excluded a [3,5,8,7,1,3] (by decide +kernel))
      node_540
      (invalid_excluded a [3,5,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,1,8] (by decide +kernel)))

theorem node_547 : Excluded a [3,5,8,7,6,0] :=
  source_excluded a [3,5,8,7,6,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_548 : Excluded a [3,5,8,7,6,1] :=
  predecessor_excluded a [3,5,8,7,6,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_549 : Excluded a [3,5,8,7,6,2] :=
  source_excluded a [3,5,8,7,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_550 : Excluded a [3,5,8,7,6,4] :=
  source_excluded a [3,5,8,7,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_546 : Excluded a [3,5,8,7,6] :=
  branch_excluded a [3,5,8,7,6] (by decide)
    (fin9_cases _
      node_547
      node_548
      node_549
      (invalid_excluded a [3,5,8,7,6,3] (by decide +kernel))
      node_550
      (invalid_excluded a [3,5,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,6,8] (by decide +kernel)))

theorem node_530 : Excluded a [3,5,8,7] :=
  branch_excluded a [3,5,8,7] (by decide)
    (fin9_cases _
      node_531
      node_532
      (invalid_excluded a [3,5,8,7,2] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,5] (by decide +kernel))
      node_546
      (invalid_excluded a [3,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,8] (by decide +kernel)))

theorem node_514 : Excluded a [3,5,8] :=
  branch_excluded a [3,5,8] (by decide)
    (fin9_cases _
      node_515
      node_516
      node_517
      (invalid_excluded a [3,5,8,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,5] (by decide +kernel))
      node_518
      node_530
      (invalid_excluded a [3,5,8,8] (by decide +kernel)))

theorem node_466 : Excluded a [3,5] :=
  branch_excluded a [3,5] (by decide)
    (fin9_cases _
      node_467
      node_468
      (invalid_excluded a [3,5,2] (by decide +kernel))
      (invalid_excluded a [3,5,3] (by decide +kernel))
      node_469
      (invalid_excluded a [3,5,5] (by decide +kernel))
      node_470
      node_491
      node_514)

theorem node_552 : Excluded a [3,6,0] :=
  source_excluded a [3,6,0] 2 1 0 (by decide) (by decide +kernel)

theorem node_553 : Excluded a [3,6,1] :=
  source_excluded a [3,6,1] 0 2 2 (by decide) (by decide +kernel)

theorem node_554 : Excluded a [3,6,4] :=
  source_excluded a [3,6,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_556 : Excluded a [3,6,5,0] :=
  predecessor_excluded a [3,6,5,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_557 : Excluded a [3,6,5,1] :=
  source_excluded a [3,6,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_558 : Excluded a [3,6,5,2] :=
  source_excluded a [3,6,5,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_560 : Excluded a [3,6,5,7,0] :=
  predecessor_excluded a [3,6,5,7,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_562 : Excluded a [3,6,5,7,1,0] :=
  source_excluded a [3,6,5,7,1,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_564 : Excluded a [3,6,5,7,1,2,0] :=
  source_excluded a [3,6,5,7,1,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_565 : Excluded a [3,6,5,7,1,2,4] :=
  source_excluded a [3,6,5,7,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_566 : Excluded a [3,6,5,7,1,2,8] :=
  source_excluded a [3,6,5,7,1,2,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_563 : Excluded a [3,6,5,7,1,2] :=
  branch_excluded a [3,6,5,7,1,2] (by decide)
    (fin9_cases _
      node_564
      (invalid_excluded a [3,6,5,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,2,3] (by decide +kernel))
      node_565
      (invalid_excluded a [3,6,5,7,1,2,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,2,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,2,7] (by decide +kernel))
      node_566)

theorem node_567 : Excluded a [3,6,5,7,1,4] :=
  predecessor_excluded a [3,6,5,7,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_569 : Excluded a [3,6,5,7,1,8,0] :=
  source_excluded a [3,6,5,7,1,8,0] 1 2 6 (by decide) (by decide +kernel)

def b_572 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 6
  | 2 => 5
  | 3 => 7
  | 4 => 1
  | 5 => 8
  | 6 => 2
  | 7 => 0
  | 8 => 4
  | _ => 0

def cert_572 : LosingRegion (edgeOf a b_572) 0 :=
  losingMask a b_572 0 1942076827370232397169664
    (by decide +kernel) (by decide +kernel)

theorem node_572 : Excluded a [3,6,5,7,1,8,2,0,4] :=
  losing_excluded a [3,6,5,7,1,8,2,0,4] (by decide) b_572 (by decide +kernel) 2 0 0 cert_572 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_572 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1942076827370232397169664 2 0; decide +kernel)

theorem node_571 : Excluded a [3,6,5,7,1,8,2,0] :=
  branch_excluded a [3,6,5,7,1,8,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,7,1,8,2,0,0] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,8,2,0,1] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,8,2,0,2] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,8,2,0,3] (by decide +kernel))
      node_572
      (invalid_excluded a [3,6,5,7,1,8,2,0,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,8,2,0,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,8,2,0,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,8,2,0,8] (by decide +kernel)))

theorem node_573 : Excluded a [3,6,5,7,1,8,2,4] :=
  source_excluded a [3,6,5,7,1,8,2,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_570 : Excluded a [3,6,5,7,1,8,2] :=
  branch_excluded a [3,6,5,7,1,8,2] (by decide)
    (fin9_cases _
      node_571
      (invalid_excluded a [3,6,5,7,1,8,2,1] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,8,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,8,2,3] (by decide +kernel))
      node_573
      (invalid_excluded a [3,6,5,7,1,8,2,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,8,2,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,8,2,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,8,2,8] (by decide +kernel)))

theorem node_574 : Excluded a [3,6,5,7,1,8,4] :=
  source_excluded a [3,6,5,7,1,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_568 : Excluded a [3,6,5,7,1,8] :=
  branch_excluded a [3,6,5,7,1,8] (by decide)
    (fin9_cases _
      node_569
      (invalid_excluded a [3,6,5,7,1,8,1] (by decide +kernel))
      node_570
      (invalid_excluded a [3,6,5,7,1,8,3] (by decide +kernel))
      node_574
      (invalid_excluded a [3,6,5,7,1,8,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,8,8] (by decide +kernel)))

theorem node_561 : Excluded a [3,6,5,7,1] :=
  branch_excluded a [3,6,5,7,1] (by decide)
    (fin9_cases _
      node_562
      (invalid_excluded a [3,6,5,7,1,1] (by decide +kernel))
      node_563
      (invalid_excluded a [3,6,5,7,1,3] (by decide +kernel))
      node_567
      (invalid_excluded a [3,6,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,1,7] (by decide +kernel))
      node_568)

theorem node_575 : Excluded a [3,6,5,7,8] :=
  predecessor_excluded a [3,6,5,7,8] 0 5 4 2 (by decide) (by decide +kernel)

theorem node_559 : Excluded a [3,6,5,7] :=
  branch_excluded a [3,6,5,7] (by decide)
    (fin9_cases _
      node_560
      node_561
      (invalid_excluded a [3,6,5,7,2] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,7] (by decide +kernel))
      node_575)

theorem node_577 : Excluded a [3,6,5,8,0] :=
  predecessor_excluded a [3,6,5,8,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_579 : Excluded a [3,6,5,8,1,0] :=
  source_excluded a [3,6,5,8,1,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_581 : Excluded a [3,6,5,8,1,2,0] :=
  source_excluded a [3,6,5,8,1,2,0] 1 2 6 (by decide) (by decide +kernel)

def b_584 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 6
  | 2 => 5
  | 3 => 8
  | 4 => 1
  | 5 => 2
  | 6 => 4
  | 7 => 0
  | 8 => 7
  | _ => 0

def cert_584 : LosingRegion (edgeOf a b_584) 0 :=
  losingMask a b_584 0 2116804251671032550392832
    (by decide +kernel) (by decide +kernel)

theorem node_584 : Excluded a [3,6,5,8,1,2,4,0,7] :=
  losing_excluded a [3,6,5,8,1,2,4,0,7] (by decide) b_584 (by decide +kernel) 2 0 0 cert_584 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_584 2 0 ∧ 0 ≠ 2 ∧ maskRegion 2116804251671032550392832 2 0; decide +kernel)

theorem node_583 : Excluded a [3,6,5,8,1,2,4,0] :=
  branch_excluded a [3,6,5,8,1,2,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,8,1,2,4,0,0] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,4,0,1] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,4,0,2] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,4,0,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,4,0,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,4,0,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,4,0,6] (by decide +kernel))
      node_584
      (invalid_excluded a [3,6,5,8,1,2,4,0,8] (by decide +kernel)))

theorem node_582 : Excluded a [3,6,5,8,1,2,4] :=
  branch_excluded a [3,6,5,8,1,2,4] (by decide)
    (fin9_cases _
      node_583
      (invalid_excluded a [3,6,5,8,1,2,4,1] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,4,2] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,4,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,4,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,4,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,4,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,4,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,4,8] (by decide +kernel)))

theorem node_580 : Excluded a [3,6,5,8,1,2] :=
  branch_excluded a [3,6,5,8,1,2] (by decide)
    (fin9_cases _
      node_581
      (invalid_excluded a [3,6,5,8,1,2,1] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,3] (by decide +kernel))
      node_582
      (invalid_excluded a [3,6,5,8,1,2,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,2,8] (by decide +kernel)))

theorem node_585 : Excluded a [3,6,5,8,1,4] :=
  predecessor_excluded a [3,6,5,8,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_586 : Excluded a [3,6,5,8,1,7] :=
  source_excluded a [3,6,5,8,1,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_578 : Excluded a [3,6,5,8,1] :=
  branch_excluded a [3,6,5,8,1] (by decide)
    (fin9_cases _
      node_579
      (invalid_excluded a [3,6,5,8,1,1] (by decide +kernel))
      node_580
      (invalid_excluded a [3,6,5,8,1,3] (by decide +kernel))
      node_585
      (invalid_excluded a [3,6,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,1,6] (by decide +kernel))
      node_586
      (invalid_excluded a [3,6,5,8,1,8] (by decide +kernel)))

theorem node_588 : Excluded a [3,6,5,8,7,0] :=
  source_excluded a [3,6,5,8,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_589 : Excluded a [3,6,5,8,7,1] :=
  source_excluded a [3,6,5,8,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_591 : Excluded a [3,6,5,8,7,2,0] :=
  source_excluded a [3,6,5,8,7,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_592 : Excluded a [3,6,5,8,7,2,1] :=
  predecessor_excluded a [3,6,5,8,7,2,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_593 : Excluded a [3,6,5,8,7,2,4] :=
  source_excluded a [3,6,5,8,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_590 : Excluded a [3,6,5,8,7,2] :=
  branch_excluded a [3,6,5,8,7,2] (by decide)
    (fin9_cases _
      node_591
      node_592
      (invalid_excluded a [3,6,5,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,2,3] (by decide +kernel))
      node_593
      (invalid_excluded a [3,6,5,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,2,8] (by decide +kernel)))

theorem node_594 : Excluded a [3,6,5,8,7,4] :=
  predecessor_excluded a [3,6,5,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_587 : Excluded a [3,6,5,8,7] :=
  branch_excluded a [3,6,5,8,7] (by decide)
    (fin9_cases _
      node_588
      node_589
      node_590
      (invalid_excluded a [3,6,5,8,7,3] (by decide +kernel))
      node_594
      (invalid_excluded a [3,6,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,8] (by decide +kernel)))

theorem node_576 : Excluded a [3,6,5,8] :=
  branch_excluded a [3,6,5,8] (by decide)
    (fin9_cases _
      node_577
      node_578
      (invalid_excluded a [3,6,5,8,2] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,6] (by decide +kernel))
      node_587
      (invalid_excluded a [3,6,5,8,8] (by decide +kernel)))

theorem node_555 : Excluded a [3,6,5] :=
  branch_excluded a [3,6,5] (by decide)
    (fin9_cases _
      node_556
      node_557
      node_558
      (invalid_excluded a [3,6,5,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,6] (by decide +kernel))
      node_559
      node_576)

theorem node_596 : Excluded a [3,6,7,0] :=
  predecessor_excluded a [3,6,7,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_597 : Excluded a [3,6,7,1] :=
  source_excluded a [3,6,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_598 : Excluded a [3,6,7,2] :=
  source_excluded a [3,6,7,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_600 : Excluded a [3,6,7,5,0] :=
  predecessor_excluded a [3,6,7,5,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_602 : Excluded a [3,6,7,5,1,0] :=
  source_excluded a [3,6,7,5,1,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_603 : Excluded a [3,6,7,5,1,2] :=
  predecessor_excluded a [3,6,7,5,1,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_604 : Excluded a [3,6,7,5,1,4] :=
  source_excluded a [3,6,7,5,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_606 : Excluded a [3,6,7,5,1,8,0] :=
  source_excluded a [3,6,7,5,1,8,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_607 : Excluded a [3,6,7,5,1,8,2] :=
  source_excluded a [3,6,7,5,1,8,2] 6 0 2 (by decide) (by decide +kernel)

def b_610 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 6
  | 2 => 7
  | 3 => 5
  | 4 => 1
  | 5 => 8
  | 6 => 4
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_610 : LosingRegion (edgeOf a b_610) 0 :=
  losingMask a b_610 0 1748457346653308427699200
    (by decide +kernel) (by decide +kernel)

theorem node_610 : Excluded a [3,6,7,5,1,8,4,0,2] :=
  losing_excluded a [3,6,7,5,1,8,4,0,2] (by decide) b_610 (by decide +kernel) 2 0 6 cert_610 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_610 2 0 ∧ 6 ≠ 2 ∧ maskRegion 1748457346653308427699200 2 6; decide +kernel)

theorem node_609 : Excluded a [3,6,7,5,1,8,4,0] :=
  branch_excluded a [3,6,7,5,1,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,7,5,1,8,4,0,0] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,1,8,4,0,1] (by decide +kernel))
      node_610
      (invalid_excluded a [3,6,7,5,1,8,4,0,3] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,1,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,1,8,4,0,5] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,1,8,4,0,6] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,1,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,1,8,4,0,8] (by decide +kernel)))

theorem node_611 : Excluded a [3,6,7,5,1,8,4,2] :=
  predecessor_excluded a [3,6,7,5,1,8,4,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_608 : Excluded a [3,6,7,5,1,8,4] :=
  branch_excluded a [3,6,7,5,1,8,4] (by decide)
    (fin9_cases _
      node_609
      (invalid_excluded a [3,6,7,5,1,8,4,1] (by decide +kernel))
      node_611
      (invalid_excluded a [3,6,7,5,1,8,4,3] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,1,8,4,4] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,1,8,4,5] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,1,8,4,8] (by decide +kernel)))

theorem node_605 : Excluded a [3,6,7,5,1,8] :=
  branch_excluded a [3,6,7,5,1,8] (by decide)
    (fin9_cases _
      node_606
      (invalid_excluded a [3,6,7,5,1,8,1] (by decide +kernel))
      node_607
      (invalid_excluded a [3,6,7,5,1,8,3] (by decide +kernel))
      node_608
      (invalid_excluded a [3,6,7,5,1,8,5] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,1,8,6] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,1,8,7] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,1,8,8] (by decide +kernel)))

theorem node_601 : Excluded a [3,6,7,5,1] :=
  branch_excluded a [3,6,7,5,1] (by decide)
    (fin9_cases _
      node_602
      (invalid_excluded a [3,6,7,5,1,1] (by decide +kernel))
      node_603
      (invalid_excluded a [3,6,7,5,1,3] (by decide +kernel))
      node_604
      (invalid_excluded a [3,6,7,5,1,5] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,1,6] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,1,7] (by decide +kernel))
      node_605)

theorem node_613 : Excluded a [3,6,7,5,8,0] :=
  source_excluded a [3,6,7,5,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_614 : Excluded a [3,6,7,5,8,1] :=
  source_excluded a [3,6,7,5,8,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_615 : Excluded a [3,6,7,5,8,2] :=
  predecessor_excluded a [3,6,7,5,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_616 : Excluded a [3,6,7,5,8,4] :=
  source_excluded a [3,6,7,5,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_612 : Excluded a [3,6,7,5,8] :=
  branch_excluded a [3,6,7,5,8] (by decide)
    (fin9_cases _
      node_613
      node_614
      node_615
      (invalid_excluded a [3,6,7,5,8,3] (by decide +kernel))
      node_616
      (invalid_excluded a [3,6,7,5,8,5] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,8,6] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,8,8] (by decide +kernel)))

theorem node_599 : Excluded a [3,6,7,5] :=
  branch_excluded a [3,6,7,5] (by decide)
    (fin9_cases _
      node_600
      node_601
      (invalid_excluded a [3,6,7,5,2] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,3] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,4] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,5] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,6] (by decide +kernel))
      (invalid_excluded a [3,6,7,5,7] (by decide +kernel))
      node_612)

theorem node_617 : Excluded a [3,6,7,8] :=
  predecessor_excluded a [3,6,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_595 : Excluded a [3,6,7] :=
  branch_excluded a [3,6,7] (by decide)
    (fin9_cases _
      node_596
      node_597
      node_598
      (invalid_excluded a [3,6,7,3] (by decide +kernel))
      (invalid_excluded a [3,6,7,4] (by decide +kernel))
      node_599
      (invalid_excluded a [3,6,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,7,7] (by decide +kernel))
      node_617)

theorem node_619 : Excluded a [3,6,8,0] :=
  predecessor_excluded a [3,6,8,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_620 : Excluded a [3,6,8,1] :=
  source_excluded a [3,6,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_621 : Excluded a [3,6,8,2] :=
  source_excluded a [3,6,8,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_622 : Excluded a [3,6,8,5] :=
  predecessor_excluded a [3,6,8,5] 0 5 2 3 (by decide) (by decide +kernel)

theorem node_624 : Excluded a [3,6,8,7,0] :=
  predecessor_excluded a [3,6,8,7,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_626 : Excluded a [3,6,8,7,1,0] :=
  source_excluded a [3,6,8,7,1,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_628 : Excluded a [3,6,8,7,1,2,0] :=
  source_excluded a [3,6,8,7,1,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_629 : Excluded a [3,6,8,7,1,2,4] :=
  source_excluded a [3,6,8,7,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_632 : Excluded a [3,6,8,7,1,2,5,0,4] :=
  predecessor_excluded a [3,6,8,7,1,2,5,0,4] 0 2 8 5 (by decide) (by decide +kernel)

theorem node_631 : Excluded a [3,6,8,7,1,2,5,0] :=
  branch_excluded a [3,6,8,7,1,2,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,7,1,2,5,0,0] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,2,5,0,1] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,2,5,0,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,2,5,0,3] (by decide +kernel))
      node_632
      (invalid_excluded a [3,6,8,7,1,2,5,0,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,2,5,0,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,2,5,0,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,2,5,0,8] (by decide +kernel)))

theorem node_633 : Excluded a [3,6,8,7,1,2,5,4] :=
  source_excluded a [3,6,8,7,1,2,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_630 : Excluded a [3,6,8,7,1,2,5] :=
  branch_excluded a [3,6,8,7,1,2,5] (by decide)
    (fin9_cases _
      node_631
      (invalid_excluded a [3,6,8,7,1,2,5,1] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,2,5,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,2,5,3] (by decide +kernel))
      node_633
      (invalid_excluded a [3,6,8,7,1,2,5,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,2,5,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,2,5,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,2,5,8] (by decide +kernel)))

theorem node_627 : Excluded a [3,6,8,7,1,2] :=
  branch_excluded a [3,6,8,7,1,2] (by decide)
    (fin9_cases _
      node_628
      (invalid_excluded a [3,6,8,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,2,3] (by decide +kernel))
      node_629
      node_630
      (invalid_excluded a [3,6,8,7,1,2,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,2,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,2,8] (by decide +kernel)))

theorem node_635 : Excluded a [3,6,8,7,1,4,0] :=
  source_excluded a [3,6,8,7,1,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_636 : Excluded a [3,6,8,7,1,4,2] :=
  predecessor_excluded a [3,6,8,7,1,4,2] 0 8 6 2 (by decide) (by decide +kernel)

def b_639 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 6
  | 2 => 8
  | 3 => 7
  | 4 => 1
  | 5 => 4
  | 6 => 5
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_639 : LosingRegion (edgeOf a b_639) 0 :=
  losingMask a b_639 0 2414313473264659616498688
    (by decide +kernel) (by decide +kernel)

theorem node_639 : Excluded a [3,6,8,7,1,4,5,0,2] :=
  losing_excluded a [3,6,8,7,1,4,5,0,2] (by decide) b_639 (by decide +kernel) 2 0 0 cert_639 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_639 2 0 ∧ 0 ≠ 2 ∧ maskRegion 2414313473264659616498688 2 0; decide +kernel)

theorem node_638 : Excluded a [3,6,8,7,1,4,5,0] :=
  branch_excluded a [3,6,8,7,1,4,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,7,1,4,5,0,0] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,4,5,0,1] (by decide +kernel))
      node_639
      (invalid_excluded a [3,6,8,7,1,4,5,0,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,4,5,0,4] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,4,5,0,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,4,5,0,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,4,5,0,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,4,5,0,8] (by decide +kernel)))

theorem node_640 : Excluded a [3,6,8,7,1,4,5,2] :=
  source_excluded a [3,6,8,7,1,4,5,2] 7 0 2 (by decide) (by decide +kernel)

theorem node_637 : Excluded a [3,6,8,7,1,4,5] :=
  branch_excluded a [3,6,8,7,1,4,5] (by decide)
    (fin9_cases _
      node_638
      (invalid_excluded a [3,6,8,7,1,4,5,1] (by decide +kernel))
      node_640
      (invalid_excluded a [3,6,8,7,1,4,5,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,4,5,4] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,4,5,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,4,5,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,4,5,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,4,5,8] (by decide +kernel)))

theorem node_634 : Excluded a [3,6,8,7,1,4] :=
  branch_excluded a [3,6,8,7,1,4] (by decide)
    (fin9_cases _
      node_635
      (invalid_excluded a [3,6,8,7,1,4,1] (by decide +kernel))
      node_636
      (invalid_excluded a [3,6,8,7,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,4,4] (by decide +kernel))
      node_637
      (invalid_excluded a [3,6,8,7,1,4,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,4,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,4,8] (by decide +kernel)))

theorem node_625 : Excluded a [3,6,8,7,1] :=
  branch_excluded a [3,6,8,7,1] (by decide)
    (fin9_cases _
      node_626
      (invalid_excluded a [3,6,8,7,1,1] (by decide +kernel))
      node_627
      (invalid_excluded a [3,6,8,7,1,3] (by decide +kernel))
      node_634
      (invalid_excluded a [3,6,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,1,8] (by decide +kernel)))

theorem node_642 : Excluded a [3,6,8,7,5,0] :=
  source_excluded a [3,6,8,7,5,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_643 : Excluded a [3,6,8,7,5,1] :=
  source_excluded a [3,6,8,7,5,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_644 : Excluded a [3,6,8,7,5,2] :=
  source_excluded a [3,6,8,7,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_646 : Excluded a [3,6,8,7,5,4,0] :=
  source_excluded a [3,6,8,7,5,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_647 : Excluded a [3,6,8,7,5,4,1] :=
  predecessor_excluded a [3,6,8,7,5,4,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_648 : Excluded a [3,6,8,7,5,4,2] :=
  predecessor_excluded a [3,6,8,7,5,4,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_645 : Excluded a [3,6,8,7,5,4] :=
  branch_excluded a [3,6,8,7,5,4] (by decide)
    (fin9_cases _
      node_646
      node_647
      node_648
      (invalid_excluded a [3,6,8,7,5,4,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,5,4,4] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,5,4,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,5,4,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,5,4,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,5,4,8] (by decide +kernel)))

theorem node_641 : Excluded a [3,6,8,7,5] :=
  branch_excluded a [3,6,8,7,5] (by decide)
    (fin9_cases _
      node_642
      node_643
      node_644
      (invalid_excluded a [3,6,8,7,5,3] (by decide +kernel))
      node_645
      (invalid_excluded a [3,6,8,7,5,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,5,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,5,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,5,8] (by decide +kernel)))

theorem node_623 : Excluded a [3,6,8,7] :=
  branch_excluded a [3,6,8,7] (by decide)
    (fin9_cases _
      node_624
      node_625
      (invalid_excluded a [3,6,8,7,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,4] (by decide +kernel))
      node_641
      (invalid_excluded a [3,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,8] (by decide +kernel)))

theorem node_618 : Excluded a [3,6,8] :=
  branch_excluded a [3,6,8] (by decide)
    (fin9_cases _
      node_619
      node_620
      node_621
      (invalid_excluded a [3,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,4] (by decide +kernel))
      node_622
      (invalid_excluded a [3,6,8,6] (by decide +kernel))
      node_623
      (invalid_excluded a [3,6,8,8] (by decide +kernel)))

theorem node_551 : Excluded a [3,6] :=
  branch_excluded a [3,6] (by decide)
    (fin9_cases _
      node_552
      node_553
      (invalid_excluded a [3,6,2] (by decide +kernel))
      (invalid_excluded a [3,6,3] (by decide +kernel))
      node_554
      node_555
      (invalid_excluded a [3,6,6] (by decide +kernel))
      node_595
      node_618)

theorem node_650 : Excluded a [3,7,0] :=
  source_excluded a [3,7,0] 2 1 0 (by decide) (by decide +kernel)

theorem node_651 : Excluded a [3,7,1] :=
  source_excluded a [3,7,1] 0 2 2 (by decide) (by decide +kernel)

theorem node_652 : Excluded a [3,7,4] :=
  source_excluded a [3,7,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_654 : Excluded a [3,7,5,0] :=
  predecessor_excluded a [3,7,5,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_655 : Excluded a [3,7,5,1] :=
  source_excluded a [3,7,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_656 : Excluded a [3,7,5,2] :=
  source_excluded a [3,7,5,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_657 : Excluded a [3,7,5,6] :=
  predecessor_excluded a [3,7,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_659 : Excluded a [3,7,5,8,0] :=
  predecessor_excluded a [3,7,5,8,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_663 : Excluded a [3,7,5,8,1,0,2,4] :=
  source_excluded a [3,7,5,8,1,0,2,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_665 : Excluded a [3,7,5,8,1,0,2,6,4] :=
  source_excluded a [3,7,5,8,1,0,2,6,4] 3 0 8 (by decide) (by decide +kernel)

theorem node_664 : Excluded a [3,7,5,8,1,0,2,6] :=
  branch_excluded a [3,7,5,8,1,0,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,8,1,0,2,6,0] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,2,6,1] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,2,6,2] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,2,6,3] (by decide +kernel))
      node_665
      (invalid_excluded a [3,7,5,8,1,0,2,6,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,2,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,2,6,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,2,6,8] (by decide +kernel)))

theorem node_662 : Excluded a [3,7,5,8,1,0,2] :=
  branch_excluded a [3,7,5,8,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,8,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,2,3] (by decide +kernel))
      node_663
      (invalid_excluded a [3,7,5,8,1,0,2,5] (by decide +kernel))
      node_664
      (invalid_excluded a [3,7,5,8,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,2,8] (by decide +kernel)))

theorem node_667 : Excluded a [3,7,5,8,1,0,4,2] :=
  predecessor_excluded a [3,7,5,8,1,0,4,2] 0 5 7 2 (by decide) (by decide +kernel)

theorem node_669 : Excluded a [3,7,5,8,1,0,4,6,2] :=
  source_excluded a [3,7,5,8,1,0,4,6,2] 8 0 2 (by decide) (by decide +kernel)

theorem node_668 : Excluded a [3,7,5,8,1,0,4,6] :=
  branch_excluded a [3,7,5,8,1,0,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,8,1,0,4,6,0] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,6,1] (by decide +kernel))
      node_669
      (invalid_excluded a [3,7,5,8,1,0,4,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,6,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,6,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,6,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,6,8] (by decide +kernel)))

theorem node_666 : Excluded a [3,7,5,8,1,0,4] :=
  branch_excluded a [3,7,5,8,1,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,8,1,0,4,0] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,1] (by decide +kernel))
      node_667
      (invalid_excluded a [3,7,5,8,1,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,5] (by decide +kernel))
      node_668
      (invalid_excluded a [3,7,5,8,1,0,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,4,8] (by decide +kernel)))

theorem node_661 : Excluded a [3,7,5,8,1,0] :=
  branch_excluded a [3,7,5,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,1] (by decide +kernel))
      node_662
      (invalid_excluded a [3,7,5,8,1,0,3] (by decide +kernel))
      node_666
      (invalid_excluded a [3,7,5,8,1,0,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,0,8] (by decide +kernel)))

theorem node_671 : Excluded a [3,7,5,8,1,2,0] :=
  source_excluded a [3,7,5,8,1,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_673 : Excluded a [3,7,5,8,1,2,4,0] :=
  source_excluded a [3,7,5,8,1,2,4,0] 1 2 7 (by decide) (by decide +kernel)

def b_675 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 7
  | 2 => 5
  | 3 => 8
  | 4 => 1
  | 5 => 2
  | 6 => 4
  | 7 => 6
  | 8 => 0
  | _ => 0

def cert_675 : LosingRegion (edgeOf a b_675) 0 :=
  losingMask a b_675 0 1212547362199538230363136
    (by decide +kernel) (by decide +kernel)

theorem node_675 : Excluded a [3,7,5,8,1,2,4,6,0] :=
  losing_excluded a [3,7,5,8,1,2,4,6,0] (by decide) b_675 (by decide +kernel) 2 0 0 cert_675 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_675 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1212547362199538230363136 2 0; decide +kernel)

theorem node_674 : Excluded a [3,7,5,8,1,2,4,6] :=
  branch_excluded a [3,7,5,8,1,2,4,6] (by decide)
    (fin9_cases _
      node_675
      (invalid_excluded a [3,7,5,8,1,2,4,6,1] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,6,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,6,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,6,8] (by decide +kernel)))

theorem node_672 : Excluded a [3,7,5,8,1,2,4] :=
  branch_excluded a [3,7,5,8,1,2,4] (by decide)
    (fin9_cases _
      node_673
      (invalid_excluded a [3,7,5,8,1,2,4,1] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,2] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,5] (by decide +kernel))
      node_674
      (invalid_excluded a [3,7,5,8,1,2,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,8] (by decide +kernel)))

theorem node_670 : Excluded a [3,7,5,8,1,2] :=
  branch_excluded a [3,7,5,8,1,2] (by decide)
    (fin9_cases _
      node_671
      (invalid_excluded a [3,7,5,8,1,2,1] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,3] (by decide +kernel))
      node_672
      (invalid_excluded a [3,7,5,8,1,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,8] (by decide +kernel)))

theorem node_676 : Excluded a [3,7,5,8,1,4] :=
  predecessor_excluded a [3,7,5,8,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_660 : Excluded a [3,7,5,8,1] :=
  branch_excluded a [3,7,5,8,1] (by decide)
    (fin9_cases _
      node_661
      (invalid_excluded a [3,7,5,8,1,1] (by decide +kernel))
      node_670
      (invalid_excluded a [3,7,5,8,1,3] (by decide +kernel))
      node_676
      (invalid_excluded a [3,7,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,8] (by decide +kernel)))

theorem node_679 : Excluded a [3,7,5,8,6,0,1] :=
  source_excluded a [3,7,5,8,6,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_680 : Excluded a [3,7,5,8,6,0,2] :=
  source_excluded a [3,7,5,8,6,0,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_682 : Excluded a [3,7,5,8,6,0,4,1] :=
  predecessor_excluded a [3,7,5,8,6,0,4,1] 2 1 1 7 (by decide) (by decide +kernel)

theorem node_683 : Excluded a [3,7,5,8,6,0,4,2] :=
  predecessor_excluded a [3,7,5,8,6,0,4,2] 0 5 7 2 (by decide) (by decide +kernel)

theorem node_681 : Excluded a [3,7,5,8,6,0,4] :=
  branch_excluded a [3,7,5,8,6,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,8,6,0,4,0] (by decide +kernel))
      node_682
      node_683
      (invalid_excluded a [3,7,5,8,6,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,6,0,4,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,6,0,4,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,6,0,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,6,0,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,6,0,4,8] (by decide +kernel)))

theorem node_678 : Excluded a [3,7,5,8,6,0] :=
  branch_excluded a [3,7,5,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,8,6,0,0] (by decide +kernel))
      node_679
      node_680
      (invalid_excluded a [3,7,5,8,6,0,3] (by decide +kernel))
      node_681
      (invalid_excluded a [3,7,5,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,6,0,8] (by decide +kernel)))

theorem node_684 : Excluded a [3,7,5,8,6,1] :=
  predecessor_excluded a [3,7,5,8,6,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_685 : Excluded a [3,7,5,8,6,2] :=
  source_excluded a [3,7,5,8,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_686 : Excluded a [3,7,5,8,6,4] :=
  source_excluded a [3,7,5,8,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_677 : Excluded a [3,7,5,8,6] :=
  branch_excluded a [3,7,5,8,6] (by decide)
    (fin9_cases _
      node_678
      node_684
      node_685
      (invalid_excluded a [3,7,5,8,6,3] (by decide +kernel))
      node_686
      (invalid_excluded a [3,7,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,6,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,6,8] (by decide +kernel)))

theorem node_658 : Excluded a [3,7,5,8] :=
  branch_excluded a [3,7,5,8] (by decide)
    (fin9_cases _
      node_659
      node_660
      (invalid_excluded a [3,7,5,8,2] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,5] (by decide +kernel))
      node_677
      (invalid_excluded a [3,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,8] (by decide +kernel)))

theorem node_653 : Excluded a [3,7,5] :=
  branch_excluded a [3,7,5] (by decide)
    (fin9_cases _
      node_654
      node_655
      node_656
      (invalid_excluded a [3,7,5,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,5] (by decide +kernel))
      node_657
      (invalid_excluded a [3,7,5,7] (by decide +kernel))
      node_658)

theorem node_688 : Excluded a [3,7,6,0] :=
  predecessor_excluded a [3,7,6,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_689 : Excluded a [3,7,6,1] :=
  source_excluded a [3,7,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_690 : Excluded a [3,7,6,2] :=
  source_excluded a [3,7,6,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_692 : Excluded a [3,7,6,5,0] :=
  predecessor_excluded a [3,7,6,5,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_696 : Excluded a [3,7,6,5,1,0,2,4] :=
  branch_excluded a [3,7,6,5,1,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,5,1,0,2,4,0] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,2,4,1] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,2,4,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,2,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,2,4,4] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,2,4,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,2,4,8] (by decide +kernel)))

theorem node_695 : Excluded a [3,7,6,5,1,0,2] :=
  branch_excluded a [3,7,6,5,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,5,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,2,3] (by decide +kernel))
      node_696
      (invalid_excluded a [3,7,6,5,1,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,2,8] (by decide +kernel)))

theorem node_697 : Excluded a [3,7,6,5,1,0,4] :=
  predecessor_excluded a [3,7,6,5,1,0,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_698 : Excluded a [3,7,6,5,1,0,8] :=
  source_excluded a [3,7,6,5,1,0,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_694 : Excluded a [3,7,6,5,1,0] :=
  branch_excluded a [3,7,6,5,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,5,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,1] (by decide +kernel))
      node_695
      (invalid_excluded a [3,7,6,5,1,0,3] (by decide +kernel))
      node_697
      (invalid_excluded a [3,7,6,5,1,0,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,0,7] (by decide +kernel))
      node_698)

theorem node_699 : Excluded a [3,7,6,5,1,2] :=
  source_excluded a [3,7,6,5,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_700 : Excluded a [3,7,6,5,1,4] :=
  source_excluded a [3,7,6,5,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_702 : Excluded a [3,7,6,5,1,8,0] :=
  source_excluded a [3,7,6,5,1,8,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_704 : Excluded a [3,7,6,5,1,8,2,0] :=
  source_excluded a [3,7,6,5,1,8,2,0] 1 2 7 (by decide) (by decide +kernel)

def b_706 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 7
  | 2 => 6
  | 3 => 5
  | 4 => 1
  | 5 => 8
  | 6 => 2
  | 7 => 4
  | 8 => 0
  | _ => 0

def cert_706 : LosingRegion (edgeOf a b_706) 0 :=
  losingMask a b_706 0 1212476292054920453686272
    (by decide +kernel) (by decide +kernel)

theorem node_706 : Excluded a [3,7,6,5,1,8,2,4,0] :=
  losing_excluded a [3,7,6,5,1,8,2,4,0] (by decide) b_706 (by decide +kernel) 2 0 0 cert_706 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_706 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1212476292054920453686272 2 0; decide +kernel)

theorem node_705 : Excluded a [3,7,6,5,1,8,2,4] :=
  branch_excluded a [3,7,6,5,1,8,2,4] (by decide)
    (fin9_cases _
      node_706
      (invalid_excluded a [3,7,6,5,1,8,2,4,1] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,8,2,4,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,8,2,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,8,2,4,4] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,8,2,4,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,8,2,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,8,2,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,8,2,4,8] (by decide +kernel)))

theorem node_703 : Excluded a [3,7,6,5,1,8,2] :=
  branch_excluded a [3,7,6,5,1,8,2] (by decide)
    (fin9_cases _
      node_704
      (invalid_excluded a [3,7,6,5,1,8,2,1] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,8,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,8,2,3] (by decide +kernel))
      node_705
      (invalid_excluded a [3,7,6,5,1,8,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,8,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,8,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,8,2,8] (by decide +kernel)))

theorem node_707 : Excluded a [3,7,6,5,1,8,4] :=
  predecessor_excluded a [3,7,6,5,1,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_701 : Excluded a [3,7,6,5,1,8] :=
  branch_excluded a [3,7,6,5,1,8] (by decide)
    (fin9_cases _
      node_702
      (invalid_excluded a [3,7,6,5,1,8,1] (by decide +kernel))
      node_703
      (invalid_excluded a [3,7,6,5,1,8,3] (by decide +kernel))
      node_707
      (invalid_excluded a [3,7,6,5,1,8,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,8,8] (by decide +kernel)))

theorem node_693 : Excluded a [3,7,6,5,1] :=
  branch_excluded a [3,7,6,5,1] (by decide)
    (fin9_cases _
      node_694
      (invalid_excluded a [3,7,6,5,1,1] (by decide +kernel))
      node_699
      (invalid_excluded a [3,7,6,5,1,3] (by decide +kernel))
      node_700
      (invalid_excluded a [3,7,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,1,7] (by decide +kernel))
      node_701)

theorem node_710 : Excluded a [3,7,6,5,8,0,1] :=
  source_excluded a [3,7,6,5,8,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_712 : Excluded a [3,7,6,5,8,0,2,1] :=
  predecessor_excluded a [3,7,6,5,8,0,2,1] 2 1 1 7 (by decide) (by decide +kernel)

theorem node_713 : Excluded a [3,7,6,5,8,0,2,4] :=
  source_excluded a [3,7,6,5,8,0,2,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_711 : Excluded a [3,7,6,5,8,0,2] :=
  branch_excluded a [3,7,6,5,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,5,8,0,2,0] (by decide +kernel))
      node_712
      (invalid_excluded a [3,7,6,5,8,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,8,0,2,3] (by decide +kernel))
      node_713
      (invalid_excluded a [3,7,6,5,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,8,0,2,8] (by decide +kernel)))

theorem node_714 : Excluded a [3,7,6,5,8,0,4] :=
  predecessor_excluded a [3,7,6,5,8,0,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_709 : Excluded a [3,7,6,5,8,0] :=
  branch_excluded a [3,7,6,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,5,8,0,0] (by decide +kernel))
      node_710
      node_711
      (invalid_excluded a [3,7,6,5,8,0,3] (by decide +kernel))
      node_714
      (invalid_excluded a [3,7,6,5,8,0,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,8,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,8,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,8,0,8] (by decide +kernel)))

theorem node_715 : Excluded a [3,7,6,5,8,1] :=
  predecessor_excluded a [3,7,6,5,8,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_716 : Excluded a [3,7,6,5,8,2] :=
  source_excluded a [3,7,6,5,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_717 : Excluded a [3,7,6,5,8,4] :=
  source_excluded a [3,7,6,5,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_708 : Excluded a [3,7,6,5,8] :=
  branch_excluded a [3,7,6,5,8] (by decide)
    (fin9_cases _
      node_709
      node_715
      node_716
      (invalid_excluded a [3,7,6,5,8,3] (by decide +kernel))
      node_717
      (invalid_excluded a [3,7,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,8,8] (by decide +kernel)))

theorem node_691 : Excluded a [3,7,6,5] :=
  branch_excluded a [3,7,6,5] (by decide)
    (fin9_cases _
      node_692
      node_693
      (invalid_excluded a [3,7,6,5,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,4] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,5,7] (by decide +kernel))
      node_708)

theorem node_719 : Excluded a [3,7,6,8,0] :=
  predecessor_excluded a [3,7,6,8,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_723 : Excluded a [3,7,6,8,1,0,2,4] :=
  source_excluded a [3,7,6,8,1,0,2,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_724 : Excluded a [3,7,6,8,1,0,2,5] :=
  source_excluded a [3,7,6,8,1,0,2,5] 7 0 8 (by decide) (by decide +kernel)

theorem node_722 : Excluded a [3,7,6,8,1,0,2] :=
  branch_excluded a [3,7,6,8,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,8,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,2,3] (by decide +kernel))
      node_723
      node_724
      (invalid_excluded a [3,7,6,8,1,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,2,8] (by decide +kernel)))

theorem node_725 : Excluded a [3,7,6,8,1,0,4] :=
  predecessor_excluded a [3,7,6,8,1,0,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_728 : Excluded a [3,7,6,8,1,0,5,2,4] :=
  source_excluded a [3,7,6,8,1,0,5,2,4] 3 0 8 (by decide) (by decide +kernel)

theorem node_727 : Excluded a [3,7,6,8,1,0,5,2] :=
  branch_excluded a [3,7,6,8,1,0,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,8,1,0,5,2,0] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,5,2,1] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,5,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,5,2,3] (by decide +kernel))
      node_728
      (invalid_excluded a [3,7,6,8,1,0,5,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,5,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,5,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,5,2,8] (by decide +kernel)))

theorem node_729 : Excluded a [3,7,6,8,1,0,5,4] :=
  source_excluded a [3,7,6,8,1,0,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_726 : Excluded a [3,7,6,8,1,0,5] :=
  branch_excluded a [3,7,6,8,1,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,8,1,0,5,0] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,5,1] (by decide +kernel))
      node_727
      (invalid_excluded a [3,7,6,8,1,0,5,3] (by decide +kernel))
      node_729
      (invalid_excluded a [3,7,6,8,1,0,5,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,5,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,5,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,5,8] (by decide +kernel)))

theorem node_721 : Excluded a [3,7,6,8,1,0] :=
  branch_excluded a [3,7,6,8,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,8,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,1] (by decide +kernel))
      node_722
      (invalid_excluded a [3,7,6,8,1,0,3] (by decide +kernel))
      node_725
      node_726
      (invalid_excluded a [3,7,6,8,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,0,8] (by decide +kernel)))

theorem node_730 : Excluded a [3,7,6,8,1,2] :=
  source_excluded a [3,7,6,8,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_732 : Excluded a [3,7,6,8,1,4,0] :=
  source_excluded a [3,7,6,8,1,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_733 : Excluded a [3,7,6,8,1,4,2] :=
  predecessor_excluded a [3,7,6,8,1,4,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_735 : Excluded a [3,7,6,8,1,4,5,0] :=
  source_excluded a [3,7,6,8,1,4,5,0] 1 2 7 (by decide) (by decide +kernel)

def b_737 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 7
  | 2 => 6
  | 3 => 8
  | 4 => 1
  | 5 => 4
  | 6 => 5
  | 7 => 2
  | 8 => 0
  | _ => 0

def cert_737 : LosingRegion (edgeOf a b_737) 0 :=
  losingMask a b_737 0 1212549733204004552573952
    (by decide +kernel) (by decide +kernel)

theorem node_737 : Excluded a [3,7,6,8,1,4,5,2,0] :=
  losing_excluded a [3,7,6,8,1,4,5,2,0] (by decide) b_737 (by decide +kernel) 2 0 0 cert_737 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_737 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1212549733204004552573952 2 0; decide +kernel)

theorem node_736 : Excluded a [3,7,6,8,1,4,5,2] :=
  branch_excluded a [3,7,6,8,1,4,5,2] (by decide)
    (fin9_cases _
      node_737
      (invalid_excluded a [3,7,6,8,1,4,5,2,1] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,5,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,5,2,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,5,2,4] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,5,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,5,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,5,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,5,2,8] (by decide +kernel)))

theorem node_734 : Excluded a [3,7,6,8,1,4,5] :=
  branch_excluded a [3,7,6,8,1,4,5] (by decide)
    (fin9_cases _
      node_735
      (invalid_excluded a [3,7,6,8,1,4,5,1] (by decide +kernel))
      node_736
      (invalid_excluded a [3,7,6,8,1,4,5,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,5,4] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,5,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,5,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,5,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,5,8] (by decide +kernel)))

theorem node_731 : Excluded a [3,7,6,8,1,4] :=
  branch_excluded a [3,7,6,8,1,4] (by decide)
    (fin9_cases _
      node_732
      (invalid_excluded a [3,7,6,8,1,4,1] (by decide +kernel))
      node_733
      (invalid_excluded a [3,7,6,8,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,4] (by decide +kernel))
      node_734
      (invalid_excluded a [3,7,6,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,8] (by decide +kernel)))

theorem node_720 : Excluded a [3,7,6,8,1] :=
  branch_excluded a [3,7,6,8,1] (by decide)
    (fin9_cases _
      node_721
      (invalid_excluded a [3,7,6,8,1,1] (by decide +kernel))
      node_730
      (invalid_excluded a [3,7,6,8,1,3] (by decide +kernel))
      node_731
      (invalid_excluded a [3,7,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,8] (by decide +kernel)))

theorem node_738 : Excluded a [3,7,6,8,5] :=
  predecessor_excluded a [3,7,6,8,5] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_718 : Excluded a [3,7,6,8] :=
  branch_excluded a [3,7,6,8] (by decide)
    (fin9_cases _
      node_719
      node_720
      (invalid_excluded a [3,7,6,8,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,4] (by decide +kernel))
      node_738
      (invalid_excluded a [3,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,8] (by decide +kernel)))

theorem node_687 : Excluded a [3,7,6] :=
  branch_excluded a [3,7,6] (by decide)
    (fin9_cases _
      node_688
      node_689
      node_690
      (invalid_excluded a [3,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,4] (by decide +kernel))
      node_691
      (invalid_excluded a [3,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,7] (by decide +kernel))
      node_718)

theorem node_740 : Excluded a [3,7,8,0] :=
  predecessor_excluded a [3,7,8,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_741 : Excluded a [3,7,8,1] :=
  source_excluded a [3,7,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_742 : Excluded a [3,7,8,2] :=
  source_excluded a [3,7,8,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_743 : Excluded a [3,7,8,5] :=
  predecessor_excluded a [3,7,8,5] 0 5 2 3 (by decide) (by decide +kernel)

theorem node_745 : Excluded a [3,7,8,6,0] :=
  predecessor_excluded a [3,7,8,6,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_748 : Excluded a [3,7,8,6,1,0,2] :=
  predecessor_excluded a [3,7,8,6,1,0,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_749 : Excluded a [3,7,8,6,1,0,4] :=
  source_excluded a [3,7,8,6,1,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_751 : Excluded a [3,7,8,6,1,0,5,2] :=
  source_excluded a [3,7,8,6,1,0,5,2] 7 0 2 (by decide) (by decide +kernel)

theorem node_753 : Excluded a [3,7,8,6,1,0,5,4,2] :=
  predecessor_excluded a [3,7,8,6,1,0,5,4,2] 0 2 7 8 (by decide) (by decide +kernel)

theorem node_752 : Excluded a [3,7,8,6,1,0,5,4] :=
  branch_excluded a [3,7,8,6,1,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,8,6,1,0,5,4,0] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,0,5,4,1] (by decide +kernel))
      node_753
      (invalid_excluded a [3,7,8,6,1,0,5,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,0,5,4,5] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,0,5,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,0,5,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,0,5,4,8] (by decide +kernel)))

theorem node_750 : Excluded a [3,7,8,6,1,0,5] :=
  branch_excluded a [3,7,8,6,1,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,8,6,1,0,5,0] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,0,5,1] (by decide +kernel))
      node_751
      (invalid_excluded a [3,7,8,6,1,0,5,3] (by decide +kernel))
      node_752
      (invalid_excluded a [3,7,8,6,1,0,5,5] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,0,5,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,0,5,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,0,5,8] (by decide +kernel)))

theorem node_747 : Excluded a [3,7,8,6,1,0] :=
  branch_excluded a [3,7,8,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,8,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,0,1] (by decide +kernel))
      node_748
      (invalid_excluded a [3,7,8,6,1,0,3] (by decide +kernel))
      node_749
      node_750
      (invalid_excluded a [3,7,8,6,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,0,8] (by decide +kernel)))

theorem node_755 : Excluded a [3,7,8,6,1,2,0] :=
  source_excluded a [3,7,8,6,1,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_756 : Excluded a [3,7,8,6,1,2,4] :=
  source_excluded a [3,7,8,6,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_758 : Excluded a [3,7,8,6,1,2,5,0] :=
  source_excluded a [3,7,8,6,1,2,5,0] 1 2 7 (by decide) (by decide +kernel)

def b_760 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 7
  | 2 => 8
  | 3 => 6
  | 4 => 1
  | 5 => 2
  | 6 => 5
  | 7 => 4
  | 8 => 0
  | _ => 0

def cert_760 : LosingRegion (edgeOf a b_760) 0 :=
  losingMask a b_760 0 1210109914544533327053824
    (by decide +kernel) (by decide +kernel)

theorem node_760 : Excluded a [3,7,8,6,1,2,5,4,0] :=
  losing_excluded a [3,7,8,6,1,2,5,4,0] (by decide) b_760 (by decide +kernel) 2 0 7 cert_760 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_760 2 0 ∧ 7 ≠ 2 ∧ maskRegion 1210109914544533327053824 2 7; decide +kernel)

theorem node_759 : Excluded a [3,7,8,6,1,2,5,4] :=
  branch_excluded a [3,7,8,6,1,2,5,4] (by decide)
    (fin9_cases _
      node_760
      (invalid_excluded a [3,7,8,6,1,2,5,4,1] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,5,4,2] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,5,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,5,4,4] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,5,4,5] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,5,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,5,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,5,4,8] (by decide +kernel)))

theorem node_757 : Excluded a [3,7,8,6,1,2,5] :=
  branch_excluded a [3,7,8,6,1,2,5] (by decide)
    (fin9_cases _
      node_758
      (invalid_excluded a [3,7,8,6,1,2,5,1] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,5,2] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,5,3] (by decide +kernel))
      node_759
      (invalid_excluded a [3,7,8,6,1,2,5,5] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,5,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,5,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,5,8] (by decide +kernel)))

theorem node_754 : Excluded a [3,7,8,6,1,2] :=
  branch_excluded a [3,7,8,6,1,2] (by decide)
    (fin9_cases _
      node_755
      (invalid_excluded a [3,7,8,6,1,2,1] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,3] (by decide +kernel))
      node_756
      node_757
      (invalid_excluded a [3,7,8,6,1,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,8] (by decide +kernel)))

theorem node_761 : Excluded a [3,7,8,6,1,4] :=
  source_excluded a [3,7,8,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_746 : Excluded a [3,7,8,6,1] :=
  branch_excluded a [3,7,8,6,1] (by decide)
    (fin9_cases _
      node_747
      (invalid_excluded a [3,7,8,6,1,1] (by decide +kernel))
      node_754
      (invalid_excluded a [3,7,8,6,1,3] (by decide +kernel))
      node_761
      (invalid_excluded a [3,7,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,8] (by decide +kernel)))

theorem node_764 : Excluded a [3,7,8,6,5,0,1] :=
  source_excluded a [3,7,8,6,5,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_765 : Excluded a [3,7,8,6,5,0,2] :=
  predecessor_excluded a [3,7,8,6,5,0,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_766 : Excluded a [3,7,8,6,5,0,4] :=
  source_excluded a [3,7,8,6,5,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_763 : Excluded a [3,7,8,6,5,0] :=
  branch_excluded a [3,7,8,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,8,6,5,0,0] (by decide +kernel))
      node_764
      node_765
      (invalid_excluded a [3,7,8,6,5,0,3] (by decide +kernel))
      node_766
      (invalid_excluded a [3,7,8,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,5,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,5,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,5,0,8] (by decide +kernel)))

theorem node_767 : Excluded a [3,7,8,6,5,1] :=
  predecessor_excluded a [3,7,8,6,5,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_768 : Excluded a [3,7,8,6,5,2] :=
  source_excluded a [3,7,8,6,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_769 : Excluded a [3,7,8,6,5,4] :=
  source_excluded a [3,7,8,6,5,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_762 : Excluded a [3,7,8,6,5] :=
  branch_excluded a [3,7,8,6,5] (by decide)
    (fin9_cases _
      node_763
      node_767
      node_768
      (invalid_excluded a [3,7,8,6,5,3] (by decide +kernel))
      node_769
      (invalid_excluded a [3,7,8,6,5,5] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,5,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,5,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,5,8] (by decide +kernel)))

theorem node_744 : Excluded a [3,7,8,6] :=
  branch_excluded a [3,7,8,6] (by decide)
    (fin9_cases _
      node_745
      node_746
      (invalid_excluded a [3,7,8,6,2] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,4] (by decide +kernel))
      node_762
      (invalid_excluded a [3,7,8,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,8] (by decide +kernel)))

theorem node_739 : Excluded a [3,7,8] :=
  branch_excluded a [3,7,8] (by decide)
    (fin9_cases _
      node_740
      node_741
      node_742
      (invalid_excluded a [3,7,8,3] (by decide +kernel))
      (invalid_excluded a [3,7,8,4] (by decide +kernel))
      node_743
      node_744
      (invalid_excluded a [3,7,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,8] (by decide +kernel)))

theorem node_649 : Excluded a [3,7] :=
  branch_excluded a [3,7] (by decide)
    (fin9_cases _
      node_650
      node_651
      (invalid_excluded a [3,7,2] (by decide +kernel))
      (invalid_excluded a [3,7,3] (by decide +kernel))
      node_652
      node_653
      node_687
      (invalid_excluded a [3,7,7] (by decide +kernel))
      node_739)

theorem node_771 : Excluded a [3,8,0] :=
  source_excluded a [3,8,0] 2 1 0 (by decide) (by decide +kernel)

theorem node_772 : Excluded a [3,8,1] :=
  source_excluded a [3,8,1] 0 2 2 (by decide) (by decide +kernel)

theorem node_773 : Excluded a [3,8,4] :=
  source_excluded a [3,8,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_775 : Excluded a [3,8,5,0] :=
  predecessor_excluded a [3,8,5,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_776 : Excluded a [3,8,5,1] :=
  source_excluded a [3,8,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_777 : Excluded a [3,8,5,2] :=
  source_excluded a [3,8,5,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_778 : Excluded a [3,8,5,6] :=
  predecessor_excluded a [3,8,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_780 : Excluded a [3,8,5,7,0] :=
  predecessor_excluded a [3,8,5,7,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_784 : Excluded a [3,8,5,7,1,0,2,4] :=
  source_excluded a [3,8,5,7,1,0,2,4] 3 0 7 (by decide) (by decide +kernel)

def b_786 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 8
  | 2 => 5
  | 3 => 7
  | 4 => 1
  | 5 => 0
  | 6 => 2
  | 7 => 6
  | 8 => 4
  | _ => 0

def cert_786 : LosingRegion (edgeOf a b_786) 0 :=
  losingMask a b_786 0 1212494437057735454360576
    (by decide +kernel) (by decide +kernel)

theorem node_786 : Excluded a [3,8,5,7,1,0,2,6,4] :=
  losing_excluded a [3,8,5,7,1,0,2,6,4] (by decide) b_786 (by decide +kernel) 2 0 5 cert_786 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_786 2 0 ∧ 5 ≠ 2 ∧ maskRegion 1212494437057735454360576 2 5; decide +kernel)

theorem node_785 : Excluded a [3,8,5,7,1,0,2,6] :=
  branch_excluded a [3,8,5,7,1,0,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,1,0,2,6,0] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,6,1] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,6,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,6,3] (by decide +kernel))
      node_786
      (invalid_excluded a [3,8,5,7,1,0,2,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,6,8] (by decide +kernel)))

theorem node_783 : Excluded a [3,8,5,7,1,0,2] :=
  branch_excluded a [3,8,5,7,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,3] (by decide +kernel))
      node_784
      (invalid_excluded a [3,8,5,7,1,0,2,5] (by decide +kernel))
      node_785
      (invalid_excluded a [3,8,5,7,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,2,8] (by decide +kernel)))

theorem node_787 : Excluded a [3,8,5,7,1,0,4] :=
  source_excluded a [3,8,5,7,1,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_782 : Excluded a [3,8,5,7,1,0] :=
  branch_excluded a [3,8,5,7,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,1] (by decide +kernel))
      node_783
      (invalid_excluded a [3,8,5,7,1,0,3] (by decide +kernel))
      node_787
      (invalid_excluded a [3,8,5,7,1,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,0,8] (by decide +kernel)))

theorem node_790 : Excluded a [3,8,5,7,1,2,0,4] :=
  source_excluded a [3,8,5,7,1,2,0,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_792 : Excluded a [3,8,5,7,1,2,0,6,4] :=
  predecessor_excluded a [3,8,5,7,1,2,0,6,4] 0 2 8 5 (by decide) (by decide +kernel)

theorem node_791 : Excluded a [3,8,5,7,1,2,0,6] :=
  branch_excluded a [3,8,5,7,1,2,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,1,2,0,6,0] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,6,1] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,6,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,6,3] (by decide +kernel))
      node_792
      (invalid_excluded a [3,8,5,7,1,2,0,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,6,8] (by decide +kernel)))

theorem node_789 : Excluded a [3,8,5,7,1,2,0] :=
  branch_excluded a [3,8,5,7,1,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,1,2,0,0] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,1] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,3] (by decide +kernel))
      node_790
      (invalid_excluded a [3,8,5,7,1,2,0,5] (by decide +kernel))
      node_791
      (invalid_excluded a [3,8,5,7,1,2,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,8] (by decide +kernel)))

theorem node_793 : Excluded a [3,8,5,7,1,2,4] :=
  source_excluded a [3,8,5,7,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_788 : Excluded a [3,8,5,7,1,2] :=
  branch_excluded a [3,8,5,7,1,2] (by decide)
    (fin9_cases _
      node_789
      (invalid_excluded a [3,8,5,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,3] (by decide +kernel))
      node_793
      (invalid_excluded a [3,8,5,7,1,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,8] (by decide +kernel)))

theorem node_794 : Excluded a [3,8,5,7,1,4] :=
  predecessor_excluded a [3,8,5,7,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_781 : Excluded a [3,8,5,7,1] :=
  branch_excluded a [3,8,5,7,1] (by decide)
    (fin9_cases _
      node_782
      (invalid_excluded a [3,8,5,7,1,1] (by decide +kernel))
      node_788
      (invalid_excluded a [3,8,5,7,1,3] (by decide +kernel))
      node_794
      (invalid_excluded a [3,8,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,8] (by decide +kernel)))

theorem node_797 : Excluded a [3,8,5,7,6,0,1] :=
  predecessor_excluded a [3,8,5,7,6,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_798 : Excluded a [3,8,5,7,6,0,2] :=
  source_excluded a [3,8,5,7,6,0,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_799 : Excluded a [3,8,5,7,6,0,4] :=
  source_excluded a [3,8,5,7,6,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_796 : Excluded a [3,8,5,7,6,0] :=
  branch_excluded a [3,8,5,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,6,0,0] (by decide +kernel))
      node_797
      node_798
      (invalid_excluded a [3,8,5,7,6,0,3] (by decide +kernel))
      node_799
      (invalid_excluded a [3,8,5,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,6,0,8] (by decide +kernel)))

theorem node_801 : Excluded a [3,8,5,7,6,1,0] :=
  predecessor_excluded a [3,8,5,7,6,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_802 : Excluded a [3,8,5,7,6,1,2] :=
  source_excluded a [3,8,5,7,6,1,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_803 : Excluded a [3,8,5,7,6,1,4] :=
  source_excluded a [3,8,5,7,6,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_800 : Excluded a [3,8,5,7,6,1] :=
  branch_excluded a [3,8,5,7,6,1] (by decide)
    (fin9_cases _
      node_801
      (invalid_excluded a [3,8,5,7,6,1,1] (by decide +kernel))
      node_802
      (invalid_excluded a [3,8,5,7,6,1,3] (by decide +kernel))
      node_803
      (invalid_excluded a [3,8,5,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,6,1,8] (by decide +kernel)))

theorem node_804 : Excluded a [3,8,5,7,6,2] :=
  source_excluded a [3,8,5,7,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_805 : Excluded a [3,8,5,7,6,4] :=
  source_excluded a [3,8,5,7,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_795 : Excluded a [3,8,5,7,6] :=
  branch_excluded a [3,8,5,7,6] (by decide)
    (fin9_cases _
      node_796
      node_800
      node_804
      (invalid_excluded a [3,8,5,7,6,3] (by decide +kernel))
      node_805
      (invalid_excluded a [3,8,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,6,8] (by decide +kernel)))

theorem node_779 : Excluded a [3,8,5,7] :=
  branch_excluded a [3,8,5,7] (by decide)
    (fin9_cases _
      node_780
      node_781
      (invalid_excluded a [3,8,5,7,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,3] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,4] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,5] (by decide +kernel))
      node_795
      (invalid_excluded a [3,8,5,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,8] (by decide +kernel)))

theorem node_774 : Excluded a [3,8,5] :=
  branch_excluded a [3,8,5] (by decide)
    (fin9_cases _
      node_775
      node_776
      node_777
      (invalid_excluded a [3,8,5,3] (by decide +kernel))
      (invalid_excluded a [3,8,5,4] (by decide +kernel))
      (invalid_excluded a [3,8,5,5] (by decide +kernel))
      node_778
      node_779
      (invalid_excluded a [3,8,5,8] (by decide +kernel)))

theorem node_807 : Excluded a [3,8,6,0] :=
  predecessor_excluded a [3,8,6,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_808 : Excluded a [3,8,6,1] :=
  source_excluded a [3,8,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_809 : Excluded a [3,8,6,2] :=
  source_excluded a [3,8,6,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_811 : Excluded a [3,8,6,5,0] :=
  predecessor_excluded a [3,8,6,5,0] 1 3 4 0 (by decide) (by decide +kernel)

def b_816 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 8
  | 2 => 6
  | 3 => 5
  | 4 => 1
  | 5 => 0
  | 6 => 2
  | 7 => 4
  | 8 => 7
  | _ => 0

def cert_816 : LosingRegion (edgeOf a b_816) 0 :=
  losingMask a b_816 0 1399406882032566519727104
    (by decide +kernel) (by decide +kernel)

theorem node_816 : Excluded a [3,8,6,5,1,0,2,4,7] :=
  losing_excluded a [3,8,6,5,1,0,2,4,7] (by decide) b_816 (by decide +kernel) 2 0 0 cert_816 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_816 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1399406882032566519727104 2 0; decide +kernel)

theorem node_815 : Excluded a [3,8,6,5,1,0,2,4] :=
  branch_excluded a [3,8,6,5,1,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,5,1,0,2,4,0] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,0,2,4,1] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,0,2,4,2] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,0,2,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,0,2,4,4] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,0,2,4,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,0,2,4,6] (by decide +kernel))
      node_816
      (invalid_excluded a [3,8,6,5,1,0,2,4,8] (by decide +kernel)))

theorem node_814 : Excluded a [3,8,6,5,1,0,2] :=
  branch_excluded a [3,8,6,5,1,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,5,1,0,2,0] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,0,2,1] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,0,2,3] (by decide +kernel))
      node_815
      (invalid_excluded a [3,8,6,5,1,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,0,2,8] (by decide +kernel)))

theorem node_817 : Excluded a [3,8,6,5,1,0,4] :=
  predecessor_excluded a [3,8,6,5,1,0,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_813 : Excluded a [3,8,6,5,1,0] :=
  branch_excluded a [3,8,6,5,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,5,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,0,1] (by decide +kernel))
      node_814
      (invalid_excluded a [3,8,6,5,1,0,3] (by decide +kernel))
      node_817
      (invalid_excluded a [3,8,6,5,1,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,0,8] (by decide +kernel)))

theorem node_818 : Excluded a [3,8,6,5,1,2] :=
  source_excluded a [3,8,6,5,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_819 : Excluded a [3,8,6,5,1,4] :=
  source_excluded a [3,8,6,5,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_820 : Excluded a [3,8,6,5,1,7] :=
  source_excluded a [3,8,6,5,1,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_812 : Excluded a [3,8,6,5,1] :=
  branch_excluded a [3,8,6,5,1] (by decide)
    (fin9_cases _
      node_813
      (invalid_excluded a [3,8,6,5,1,1] (by decide +kernel))
      node_818
      (invalid_excluded a [3,8,6,5,1,3] (by decide +kernel))
      node_819
      (invalid_excluded a [3,8,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,1,6] (by decide +kernel))
      node_820
      (invalid_excluded a [3,8,6,5,1,8] (by decide +kernel)))

theorem node_823 : Excluded a [3,8,6,5,7,0,1] :=
  predecessor_excluded a [3,8,6,5,7,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_824 : Excluded a [3,8,6,5,7,0,2] :=
  source_excluded a [3,8,6,5,7,0,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_825 : Excluded a [3,8,6,5,7,0,4] :=
  source_excluded a [3,8,6,5,7,0,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_822 : Excluded a [3,8,6,5,7,0] :=
  branch_excluded a [3,8,6,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,5,7,0,0] (by decide +kernel))
      node_823
      node_824
      (invalid_excluded a [3,8,6,5,7,0,3] (by decide +kernel))
      node_825
      (invalid_excluded a [3,8,6,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,7,0,8] (by decide +kernel)))

theorem node_827 : Excluded a [3,8,6,5,7,1,0] :=
  predecessor_excluded a [3,8,6,5,7,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_828 : Excluded a [3,8,6,5,7,1,2] :=
  source_excluded a [3,8,6,5,7,1,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_829 : Excluded a [3,8,6,5,7,1,4] :=
  source_excluded a [3,8,6,5,7,1,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_826 : Excluded a [3,8,6,5,7,1] :=
  branch_excluded a [3,8,6,5,7,1] (by decide)
    (fin9_cases _
      node_827
      (invalid_excluded a [3,8,6,5,7,1,1] (by decide +kernel))
      node_828
      (invalid_excluded a [3,8,6,5,7,1,3] (by decide +kernel))
      node_829
      (invalid_excluded a [3,8,6,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,7,1,8] (by decide +kernel)))

theorem node_830 : Excluded a [3,8,6,5,7,2] :=
  source_excluded a [3,8,6,5,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_831 : Excluded a [3,8,6,5,7,4] :=
  source_excluded a [3,8,6,5,7,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_821 : Excluded a [3,8,6,5,7] :=
  branch_excluded a [3,8,6,5,7] (by decide)
    (fin9_cases _
      node_822
      node_826
      node_830
      (invalid_excluded a [3,8,6,5,7,3] (by decide +kernel))
      node_831
      (invalid_excluded a [3,8,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,7,8] (by decide +kernel)))

theorem node_810 : Excluded a [3,8,6,5] :=
  branch_excluded a [3,8,6,5] (by decide)
    (fin9_cases _
      node_811
      node_812
      (invalid_excluded a [3,8,6,5,2] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,4] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,5,6] (by decide +kernel))
      node_821
      (invalid_excluded a [3,8,6,5,8] (by decide +kernel)))

theorem node_832 : Excluded a [3,8,6,7] :=
  predecessor_excluded a [3,8,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_806 : Excluded a [3,8,6] :=
  branch_excluded a [3,8,6] (by decide)
    (fin9_cases _
      node_807
      node_808
      node_809
      (invalid_excluded a [3,8,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,4] (by decide +kernel))
      node_810
      (invalid_excluded a [3,8,6,6] (by decide +kernel))
      node_832
      (invalid_excluded a [3,8,6,8] (by decide +kernel)))

theorem node_834 : Excluded a [3,8,7,0] :=
  predecessor_excluded a [3,8,7,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_835 : Excluded a [3,8,7,1] :=
  source_excluded a [3,8,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_836 : Excluded a [3,8,7,2] :=
  source_excluded a [3,8,7,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_838 : Excluded a [3,8,7,5,0] :=
  predecessor_excluded a [3,8,7,5,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_841 : Excluded a [3,8,7,5,1,0,2] :=
  source_excluded a [3,8,7,5,1,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_843 : Excluded a [3,8,7,5,1,0,4,2] :=
  predecessor_excluded a [3,8,7,5,1,0,4,2] 0 2 6 7 (by decide) (by decide +kernel)

def b_845 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 8
  | 2 => 7
  | 3 => 5
  | 4 => 1
  | 5 => 0
  | 6 => 4
  | 7 => 6
  | 8 => 2
  | _ => 0

def cert_845 : LosingRegion (edgeOf a b_845) 0 :=
  losingMask a b_845 0 1401797969175527082427392
    (by decide +kernel) (by decide +kernel)

theorem node_845 : Excluded a [3,8,7,5,1,0,4,6,2] :=
  losing_excluded a [3,8,7,5,1,0,4,6,2] (by decide) b_845 (by decide +kernel) 2 0 0 cert_845 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_845 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1401797969175527082427392 2 0; decide +kernel)

theorem node_844 : Excluded a [3,8,7,5,1,0,4,6] :=
  branch_excluded a [3,8,7,5,1,0,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,5,1,0,4,6,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,0,4,6,1] (by decide +kernel))
      node_845
      (invalid_excluded a [3,8,7,5,1,0,4,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,0,4,6,4] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,0,4,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,0,4,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,0,4,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,0,4,6,8] (by decide +kernel)))

theorem node_842 : Excluded a [3,8,7,5,1,0,4] :=
  branch_excluded a [3,8,7,5,1,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,5,1,0,4,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,0,4,1] (by decide +kernel))
      node_843
      (invalid_excluded a [3,8,7,5,1,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,0,4,4] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,0,4,5] (by decide +kernel))
      node_844
      (invalid_excluded a [3,8,7,5,1,0,4,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,0,4,8] (by decide +kernel)))

theorem node_840 : Excluded a [3,8,7,5,1,0] :=
  branch_excluded a [3,8,7,5,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,5,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,0,1] (by decide +kernel))
      node_841
      (invalid_excluded a [3,8,7,5,1,0,3] (by decide +kernel))
      node_842
      (invalid_excluded a [3,8,7,5,1,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,0,8] (by decide +kernel)))

theorem node_846 : Excluded a [3,8,7,5,1,2] :=
  predecessor_excluded a [3,8,7,5,1,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_847 : Excluded a [3,8,7,5,1,4] :=
  source_excluded a [3,8,7,5,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_839 : Excluded a [3,8,7,5,1] :=
  branch_excluded a [3,8,7,5,1] (by decide)
    (fin9_cases _
      node_840
      (invalid_excluded a [3,8,7,5,1,1] (by decide +kernel))
      node_846
      (invalid_excluded a [3,8,7,5,1,3] (by decide +kernel))
      node_847
      (invalid_excluded a [3,8,7,5,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,1,8] (by decide +kernel)))

theorem node_848 : Excluded a [3,8,7,5,6] :=
  predecessor_excluded a [3,8,7,5,6] 0 7 4 2 (by decide) (by decide +kernel)

theorem node_837 : Excluded a [3,8,7,5] :=
  branch_excluded a [3,8,7,5] (by decide)
    (fin9_cases _
      node_838
      node_839
      (invalid_excluded a [3,8,7,5,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,4] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,5] (by decide +kernel))
      node_848
      (invalid_excluded a [3,8,7,5,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,5,8] (by decide +kernel)))

theorem node_850 : Excluded a [3,8,7,6,0] :=
  predecessor_excluded a [3,8,7,6,0] 1 3 4 0 (by decide) (by decide +kernel)

theorem node_853 : Excluded a [3,8,7,6,1,0,2] :=
  source_excluded a [3,8,7,6,1,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_854 : Excluded a [3,8,7,6,1,0,4] :=
  source_excluded a [3,8,7,6,1,0,4] 3 0 6 (by decide) (by decide +kernel)

def b_857 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 8
  | 2 => 7
  | 3 => 6
  | 4 => 1
  | 5 => 0
  | 6 => 5
  | 7 => 2
  | 8 => 4
  | _ => 0

def cert_857 : LosingRegion (edgeOf a b_857) 0 :=
  losingMask a b_857 0 1364493554583742868882432
    (by decide +kernel) (by decide +kernel)

theorem node_857 : Excluded a [3,8,7,6,1,0,5,2,4] :=
  losing_excluded a [3,8,7,6,1,0,5,2,4] (by decide) b_857 (by decide +kernel) 2 0 0 cert_857 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_857 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1364493554583742868882432 2 0; decide +kernel)

theorem node_856 : Excluded a [3,8,7,6,1,0,5,2] :=
  branch_excluded a [3,8,7,6,1,0,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,6,1,0,5,2,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,5,2,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,5,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,5,2,3] (by decide +kernel))
      node_857
      (invalid_excluded a [3,8,7,6,1,0,5,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,5,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,5,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,5,2,8] (by decide +kernel)))

theorem node_858 : Excluded a [3,8,7,6,1,0,5,4] :=
  predecessor_excluded a [3,8,7,6,1,0,5,4] 0 4 2 7 (by decide) (by decide +kernel)

theorem node_855 : Excluded a [3,8,7,6,1,0,5] :=
  branch_excluded a [3,8,7,6,1,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,6,1,0,5,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,5,1] (by decide +kernel))
      node_856
      (invalid_excluded a [3,8,7,6,1,0,5,3] (by decide +kernel))
      node_858
      (invalid_excluded a [3,8,7,6,1,0,5,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,5,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,5,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,5,8] (by decide +kernel)))

theorem node_852 : Excluded a [3,8,7,6,1,0] :=
  branch_excluded a [3,8,7,6,1,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,6,1,0,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,1] (by decide +kernel))
      node_853
      (invalid_excluded a [3,8,7,6,1,0,3] (by decide +kernel))
      node_854
      node_855
      (invalid_excluded a [3,8,7,6,1,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,0,8] (by decide +kernel)))

theorem node_859 : Excluded a [3,8,7,6,1,2] :=
  predecessor_excluded a [3,8,7,6,1,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_860 : Excluded a [3,8,7,6,1,4] :=
  source_excluded a [3,8,7,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_851 : Excluded a [3,8,7,6,1] :=
  branch_excluded a [3,8,7,6,1] (by decide)
    (fin9_cases _
      node_852
      (invalid_excluded a [3,8,7,6,1,1] (by decide +kernel))
      node_859
      (invalid_excluded a [3,8,7,6,1,3] (by decide +kernel))
      node_860
      (invalid_excluded a [3,8,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,8] (by decide +kernel)))

theorem node_863 : Excluded a [3,8,7,6,5,0,1] :=
  predecessor_excluded a [3,8,7,6,5,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_864 : Excluded a [3,8,7,6,5,0,2] :=
  source_excluded a [3,8,7,6,5,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_865 : Excluded a [3,8,7,6,5,0,4] :=
  source_excluded a [3,8,7,6,5,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_862 : Excluded a [3,8,7,6,5,0] :=
  branch_excluded a [3,8,7,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,6,5,0,0] (by decide +kernel))
      node_863
      node_864
      (invalid_excluded a [3,8,7,6,5,0,3] (by decide +kernel))
      node_865
      (invalid_excluded a [3,8,7,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,5,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,5,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,5,0,8] (by decide +kernel)))

theorem node_867 : Excluded a [3,8,7,6,5,1,0] :=
  predecessor_excluded a [3,8,7,6,5,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_868 : Excluded a [3,8,7,6,5,1,2] :=
  source_excluded a [3,8,7,6,5,1,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_869 : Excluded a [3,8,7,6,5,1,4] :=
  source_excluded a [3,8,7,6,5,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_866 : Excluded a [3,8,7,6,5,1] :=
  branch_excluded a [3,8,7,6,5,1] (by decide)
    (fin9_cases _
      node_867
      (invalid_excluded a [3,8,7,6,5,1,1] (by decide +kernel))
      node_868
      (invalid_excluded a [3,8,7,6,5,1,3] (by decide +kernel))
      node_869
      (invalid_excluded a [3,8,7,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,5,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,5,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,5,1,8] (by decide +kernel)))

theorem node_870 : Excluded a [3,8,7,6,5,2] :=
  source_excluded a [3,8,7,6,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_871 : Excluded a [3,8,7,6,5,4] :=
  source_excluded a [3,8,7,6,5,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_861 : Excluded a [3,8,7,6,5] :=
  branch_excluded a [3,8,7,6,5] (by decide)
    (fin9_cases _
      node_862
      node_866
      node_870
      (invalid_excluded a [3,8,7,6,5,3] (by decide +kernel))
      node_871
      (invalid_excluded a [3,8,7,6,5,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,5,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,5,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,5,8] (by decide +kernel)))

theorem node_849 : Excluded a [3,8,7,6] :=
  branch_excluded a [3,8,7,6] (by decide)
    (fin9_cases _
      node_850
      node_851
      (invalid_excluded a [3,8,7,6,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,4] (by decide +kernel))
      node_861
      (invalid_excluded a [3,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,8] (by decide +kernel)))

theorem node_833 : Excluded a [3,8,7] :=
  branch_excluded a [3,8,7] (by decide)
    (fin9_cases _
      node_834
      node_835
      node_836
      (invalid_excluded a [3,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,4] (by decide +kernel))
      node_837
      node_849
      (invalid_excluded a [3,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,8] (by decide +kernel)))

theorem node_770 : Excluded a [3,8] :=
  branch_excluded a [3,8] (by decide)
    (fin9_cases _
      node_771
      node_772
      (invalid_excluded a [3,8,2] (by decide +kernel))
      (invalid_excluded a [3,8,3] (by decide +kernel))
      node_773
      node_774
      node_806
      node_833
      (invalid_excluded a [3,8,8] (by decide +kernel)))

theorem node_463 : Excluded a [3] :=
  branch_excluded a [3] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,0] (by decide +kernel))
      (invalid_excluded a [3,1] (by decide +kernel))
      node_464
      (invalid_excluded a [3,3] (by decide +kernel))
      node_465
      node_466
      node_551
      node_649
      node_770)

theorem node_873 : Excluded a [4,2] :=
  predecessor_excluded a [4,2] 3 2 0 1 (by decide) (by decide +kernel)

theorem node_874 : Excluded a [4,3] :=
  predecessor_excluded a [4,3] 2 4 1 0 (by decide) (by decide +kernel)

theorem node_876 : Excluded a [4,5,0] :=
  predecessor_excluded a [4,5,0] 1 4 2 0 (by decide) (by decide +kernel)

theorem node_878 : Excluded a [4,5,1,0] :=
  source_excluded a [4,5,1,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_879 : Excluded a [4,5,1,2] :=
  source_excluded a [4,5,1,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_881 : Excluded a [4,5,1,6,0] :=
  predecessor_excluded a [4,5,1,6,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_882 : Excluded a [4,5,1,6,3] :=
  source_excluded a [4,5,1,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_883 : Excluded a [4,5,1,6,7] :=
  predecessor_excluded a [4,5,1,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_885 : Excluded a [4,5,1,6,8,0] :=
  source_excluded a [4,5,1,6,8,0] 1 2 5 (by decide) (by decide +kernel)

def b_889 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 1
  | 3 => 6
  | 4 => 8
  | 5 => 2
  | 6 => 0
  | 7 => 3
  | 8 => 7
  | _ => 0

def cert_889 : LosingRegion (edgeOf a b_889) 0 :=
  losingMask a b_889 0 1373379697082947872490496
    (by decide +kernel) (by decide +kernel)

theorem node_889 : Excluded a [4,5,1,6,8,2,0,3,7] :=
  losing_excluded a [4,5,1,6,8,2,0,3,7] (by decide) b_889 (by decide +kernel) 2 0 1 cert_889 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_889 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1373379697082947872490496 2 1; decide +kernel)

theorem node_888 : Excluded a [4,5,1,6,8,2,0,3] :=
  branch_excluded a [4,5,1,6,8,2,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,5,1,6,8,2,0,3,0] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,0,3,1] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,0,3,2] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,0,3,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,0,3,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,0,3,6] (by decide +kernel))
      node_889
      (invalid_excluded a [4,5,1,6,8,2,0,3,8] (by decide +kernel)))

theorem node_887 : Excluded a [4,5,1,6,8,2,0] :=
  branch_excluded a [4,5,1,6,8,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,5,1,6,8,2,0,0] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,0,1] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,0,2] (by decide +kernel))
      node_888
      (invalid_excluded a [4,5,1,6,8,2,0,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,0,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,0,6] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,0,7] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,0,8] (by decide +kernel)))

theorem node_890 : Excluded a [4,5,1,6,8,2,3] :=
  predecessor_excluded a [4,5,1,6,8,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_886 : Excluded a [4,5,1,6,8,2] :=
  branch_excluded a [4,5,1,6,8,2] (by decide)
    (fin9_cases _
      node_887
      (invalid_excluded a [4,5,1,6,8,2,1] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,2] (by decide +kernel))
      node_890
      (invalid_excluded a [4,5,1,6,8,2,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,2,8] (by decide +kernel)))

theorem node_891 : Excluded a [4,5,1,6,8,3] :=
  source_excluded a [4,5,1,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_892 : Excluded a [4,5,1,6,8,7] :=
  source_excluded a [4,5,1,6,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_884 : Excluded a [4,5,1,6,8] :=
  branch_excluded a [4,5,1,6,8] (by decide)
    (fin9_cases _
      node_885
      (invalid_excluded a [4,5,1,6,8,1] (by decide +kernel))
      node_886
      node_891
      (invalid_excluded a [4,5,1,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,8,6] (by decide +kernel))
      node_892
      (invalid_excluded a [4,5,1,6,8,8] (by decide +kernel)))

theorem node_880 : Excluded a [4,5,1,6] :=
  branch_excluded a [4,5,1,6] (by decide)
    (fin9_cases _
      node_881
      (invalid_excluded a [4,5,1,6,1] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,2] (by decide +kernel))
      node_882
      (invalid_excluded a [4,5,1,6,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,6,6] (by decide +kernel))
      node_883
      node_884)

theorem node_894 : Excluded a [4,5,1,7,0] :=
  predecessor_excluded a [4,5,1,7,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_895 : Excluded a [4,5,1,7,3] :=
  source_excluded a [4,5,1,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_897 : Excluded a [4,5,1,7,6,0] :=
  source_excluded a [4,5,1,7,6,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_898 : Excluded a [4,5,1,7,6,2] :=
  source_excluded a [4,5,1,7,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_899 : Excluded a [4,5,1,7,6,3] :=
  predecessor_excluded a [4,5,1,7,6,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_902 : Excluded a [4,5,1,7,6,8,0,2] :=
  predecessor_excluded a [4,5,1,7,6,8,0,2] 0 2 3 7 (by decide) (by decide +kernel)

def b_904 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 1
  | 3 => 7
  | 4 => 6
  | 5 => 8
  | 6 => 0
  | 7 => 3
  | 8 => 2
  | _ => 0

def cert_904 : LosingRegion (edgeOf a b_904) 0 :=
  losingMask a b_904 0 1605596537671310598996992
    (by decide +kernel) (by decide +kernel)

theorem node_904 : Excluded a [4,5,1,7,6,8,0,3,2] :=
  losing_excluded a [4,5,1,7,6,8,0,3,2] (by decide) b_904 (by decide +kernel) 2 0 0 cert_904 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_904 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1605596537671310598996992 2 0; decide +kernel)

theorem node_903 : Excluded a [4,5,1,7,6,8,0,3] :=
  branch_excluded a [4,5,1,7,6,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,5,1,7,6,8,0,3,0] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,8,0,3,1] (by decide +kernel))
      node_904
      (invalid_excluded a [4,5,1,7,6,8,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,8,0,3,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,8,0,3,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,8,0,3,6] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,8,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,8,0,3,8] (by decide +kernel)))

theorem node_901 : Excluded a [4,5,1,7,6,8,0] :=
  branch_excluded a [4,5,1,7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,5,1,7,6,8,0,0] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,8,0,1] (by decide +kernel))
      node_902
      node_903
      (invalid_excluded a [4,5,1,7,6,8,0,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,8,0,8] (by decide +kernel)))

theorem node_905 : Excluded a [4,5,1,7,6,8,2] :=
  source_excluded a [4,5,1,7,6,8,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_906 : Excluded a [4,5,1,7,6,8,3] :=
  source_excluded a [4,5,1,7,6,8,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_900 : Excluded a [4,5,1,7,6,8] :=
  branch_excluded a [4,5,1,7,6,8] (by decide)
    (fin9_cases _
      node_901
      (invalid_excluded a [4,5,1,7,6,8,1] (by decide +kernel))
      node_905
      node_906
      (invalid_excluded a [4,5,1,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,8,8] (by decide +kernel)))

theorem node_896 : Excluded a [4,5,1,7,6] :=
  branch_excluded a [4,5,1,7,6] (by decide)
    (fin9_cases _
      node_897
      (invalid_excluded a [4,5,1,7,6,1] (by decide +kernel))
      node_898
      node_899
      (invalid_excluded a [4,5,1,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,6,7] (by decide +kernel))
      node_900)

theorem node_907 : Excluded a [4,5,1,7,8] :=
  predecessor_excluded a [4,5,1,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_893 : Excluded a [4,5,1,7] :=
  branch_excluded a [4,5,1,7] (by decide)
    (fin9_cases _
      node_894
      (invalid_excluded a [4,5,1,7,1] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,2] (by decide +kernel))
      node_895
      (invalid_excluded a [4,5,1,7,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,7,5] (by decide +kernel))
      node_896
      (invalid_excluded a [4,5,1,7,7] (by decide +kernel))
      node_907)

theorem node_909 : Excluded a [4,5,1,8,0] :=
  predecessor_excluded a [4,5,1,8,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_910 : Excluded a [4,5,1,8,3] :=
  source_excluded a [4,5,1,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_912 : Excluded a [4,5,1,8,6,0] :=
  source_excluded a [4,5,1,8,6,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_913 : Excluded a [4,5,1,8,6,2] :=
  source_excluded a [4,5,1,8,6,2] 4 0 5 (by decide) (by decide +kernel)

def b_917 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 1
  | 3 => 8
  | 4 => 6
  | 5 => 3
  | 6 => 0
  | 7 => 2
  | 8 => 7
  | _ => 0

def cert_917 : LosingRegion (edgeOf a b_917) 0 :=
  losingMask a b_917 0 1791761078863187393905664
    (by decide +kernel) (by decide +kernel)

theorem node_917 : Excluded a [4,5,1,8,6,3,0,2,7] :=
  losing_excluded a [4,5,1,8,6,3,0,2,7] (by decide) b_917 (by decide +kernel) 2 0 0 cert_917 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_917 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1791761078863187393905664 2 0; decide +kernel)

theorem node_916 : Excluded a [4,5,1,8,6,3,0,2] :=
  branch_excluded a [4,5,1,8,6,3,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,5,1,8,6,3,0,2,0] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,0,2,1] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,0,2,2] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,0,2,3] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,0,2,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,0,2,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,0,2,6] (by decide +kernel))
      node_917
      (invalid_excluded a [4,5,1,8,6,3,0,2,8] (by decide +kernel)))

theorem node_915 : Excluded a [4,5,1,8,6,3,0] :=
  branch_excluded a [4,5,1,8,6,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,5,1,8,6,3,0,0] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,0,1] (by decide +kernel))
      node_916
      (invalid_excluded a [4,5,1,8,6,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,0,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,0,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,0,8] (by decide +kernel)))

theorem node_918 : Excluded a [4,5,1,8,6,3,2] :=
  source_excluded a [4,5,1,8,6,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_914 : Excluded a [4,5,1,8,6,3] :=
  branch_excluded a [4,5,1,8,6,3] (by decide)
    (fin9_cases _
      node_915
      (invalid_excluded a [4,5,1,8,6,3,1] (by decide +kernel))
      node_918
      (invalid_excluded a [4,5,1,8,6,3,3] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,6] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,7] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,3,8] (by decide +kernel)))

theorem node_919 : Excluded a [4,5,1,8,6,7] :=
  source_excluded a [4,5,1,8,6,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_911 : Excluded a [4,5,1,8,6] :=
  branch_excluded a [4,5,1,8,6] (by decide)
    (fin9_cases _
      node_912
      (invalid_excluded a [4,5,1,8,6,1] (by decide +kernel))
      node_913
      node_914
      (invalid_excluded a [4,5,1,8,6,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,6,6] (by decide +kernel))
      node_919
      (invalid_excluded a [4,5,1,8,6,8] (by decide +kernel)))

theorem node_921 : Excluded a [4,5,1,8,7,0] :=
  source_excluded a [4,5,1,8,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_924 : Excluded a [4,5,1,8,7,2,0,3] :=
  source_excluded a [4,5,1,8,7,2,0,3] 7 0 3 (by decide) (by decide +kernel)

def b_926 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 1
  | 3 => 8
  | 4 => 7
  | 5 => 2
  | 6 => 0
  | 7 => 6
  | 8 => 3
  | _ => 0

def cert_926 : LosingRegion (edgeOf a b_926) 0 :=
  losingMask a b_926 0 2278247836386531397600256
    (by decide +kernel) (by decide +kernel)

theorem node_926 : Excluded a [4,5,1,8,7,2,0,6,3] :=
  losing_excluded a [4,5,1,8,7,2,0,6,3] (by decide) b_926 (by decide +kernel) 2 0 0 cert_926 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_926 2 0 ∧ 0 ≠ 2 ∧ maskRegion 2278247836386531397600256 2 0; decide +kernel)

theorem node_925 : Excluded a [4,5,1,8,7,2,0,6] :=
  branch_excluded a [4,5,1,8,7,2,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,5,1,8,7,2,0,6,0] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,2,0,6,1] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,2,0,6,2] (by decide +kernel))
      node_926
      (invalid_excluded a [4,5,1,8,7,2,0,6,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,2,0,6,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,2,0,6,6] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,2,0,6,7] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,2,0,6,8] (by decide +kernel)))

theorem node_923 : Excluded a [4,5,1,8,7,2,0] :=
  branch_excluded a [4,5,1,8,7,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,5,1,8,7,2,0,0] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,2,0,1] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,2,0,2] (by decide +kernel))
      node_924
      (invalid_excluded a [4,5,1,8,7,2,0,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,2,0,5] (by decide +kernel))
      node_925
      (invalid_excluded a [4,5,1,8,7,2,0,7] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,2,0,8] (by decide +kernel)))

theorem node_927 : Excluded a [4,5,1,8,7,2,3] :=
  predecessor_excluded a [4,5,1,8,7,2,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_922 : Excluded a [4,5,1,8,7,2] :=
  branch_excluded a [4,5,1,8,7,2] (by decide)
    (fin9_cases _
      node_923
      (invalid_excluded a [4,5,1,8,7,2,1] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,2,2] (by decide +kernel))
      node_927
      (invalid_excluded a [4,5,1,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,2,8] (by decide +kernel)))

theorem node_930 : Excluded a [4,5,1,8,7,3,0,2] :=
  source_excluded a [4,5,1,8,7,3,0,2] 4 0 7 (by decide) (by decide +kernel)

theorem node_932 : Excluded a [4,5,1,8,7,3,0,6,2] :=
  predecessor_excluded a [4,5,1,8,7,3,0,6,2] 0 3 8 5 (by decide) (by decide +kernel)

theorem node_931 : Excluded a [4,5,1,8,7,3,0,6] :=
  branch_excluded a [4,5,1,8,7,3,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,5,1,8,7,3,0,6,0] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,3,0,6,1] (by decide +kernel))
      node_932
      (invalid_excluded a [4,5,1,8,7,3,0,6,3] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,3,0,6,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,3,0,6,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,3,0,6,6] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,3,0,6,7] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,3,0,6,8] (by decide +kernel)))

theorem node_929 : Excluded a [4,5,1,8,7,3,0] :=
  branch_excluded a [4,5,1,8,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,5,1,8,7,3,0,0] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,3,0,1] (by decide +kernel))
      node_930
      (invalid_excluded a [4,5,1,8,7,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,3,0,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,3,0,5] (by decide +kernel))
      node_931
      (invalid_excluded a [4,5,1,8,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,3,0,8] (by decide +kernel)))

theorem node_933 : Excluded a [4,5,1,8,7,3,2] :=
  source_excluded a [4,5,1,8,7,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_928 : Excluded a [4,5,1,8,7,3] :=
  branch_excluded a [4,5,1,8,7,3] (by decide)
    (fin9_cases _
      node_929
      (invalid_excluded a [4,5,1,8,7,3,1] (by decide +kernel))
      node_933
      (invalid_excluded a [4,5,1,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,3,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,3,8] (by decide +kernel)))

theorem node_920 : Excluded a [4,5,1,8,7] :=
  branch_excluded a [4,5,1,8,7] (by decide)
    (fin9_cases _
      node_921
      (invalid_excluded a [4,5,1,8,7,1] (by decide +kernel))
      node_922
      node_928
      (invalid_excluded a [4,5,1,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,7,8] (by decide +kernel)))

theorem node_908 : Excluded a [4,5,1,8] :=
  branch_excluded a [4,5,1,8] (by decide)
    (fin9_cases _
      node_909
      (invalid_excluded a [4,5,1,8,1] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,2] (by decide +kernel))
      node_910
      (invalid_excluded a [4,5,1,8,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,8,5] (by decide +kernel))
      node_911
      node_920
      (invalid_excluded a [4,5,1,8,8] (by decide +kernel)))

theorem node_877 : Excluded a [4,5,1] :=
  branch_excluded a [4,5,1] (by decide)
    (fin9_cases _
      node_878
      (invalid_excluded a [4,5,1,1] (by decide +kernel))
      node_879
      (invalid_excluded a [4,5,1,3] (by decide +kernel))
      (invalid_excluded a [4,5,1,4] (by decide +kernel))
      (invalid_excluded a [4,5,1,5] (by decide +kernel))
      node_880
      node_893
      node_908)

theorem node_935 : Excluded a [4,5,6,0] :=
  source_excluded a [4,5,6,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_936 : Excluded a [4,5,6,1] :=
  source_excluded a [4,5,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_937 : Excluded a [4,5,6,2] :=
  source_excluded a [4,5,6,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_938 : Excluded a [4,5,6,7] :=
  predecessor_excluded a [4,5,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_940 : Excluded a [4,5,6,8,0] :=
  predecessor_excluded a [4,5,6,8,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_941 : Excluded a [4,5,6,8,1] :=
  source_excluded a [4,5,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_942 : Excluded a [4,5,6,8,3] :=
  source_excluded a [4,5,6,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_944 : Excluded a [4,5,6,8,7,0] :=
  source_excluded a [4,5,6,8,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_945 : Excluded a [4,5,6,8,7,1] :=
  predecessor_excluded a [4,5,6,8,7,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_946 : Excluded a [4,5,6,8,7,2] :=
  source_excluded a [4,5,6,8,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_947 : Excluded a [4,5,6,8,7,3] :=
  source_excluded a [4,5,6,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_943 : Excluded a [4,5,6,8,7] :=
  branch_excluded a [4,5,6,8,7] (by decide)
    (fin9_cases _
      node_944
      node_945
      node_946
      node_947
      (invalid_excluded a [4,5,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,5,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,5,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,5,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,5,6,8,7,8] (by decide +kernel)))

theorem node_939 : Excluded a [4,5,6,8] :=
  branch_excluded a [4,5,6,8] (by decide)
    (fin9_cases _
      node_940
      node_941
      (invalid_excluded a [4,5,6,8,2] (by decide +kernel))
      node_942
      (invalid_excluded a [4,5,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,5,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,5,6,8,6] (by decide +kernel))
      node_943
      (invalid_excluded a [4,5,6,8,8] (by decide +kernel)))

theorem node_934 : Excluded a [4,5,6] :=
  branch_excluded a [4,5,6] (by decide)
    (fin9_cases _
      node_935
      node_936
      node_937
      (invalid_excluded a [4,5,6,3] (by decide +kernel))
      (invalid_excluded a [4,5,6,4] (by decide +kernel))
      (invalid_excluded a [4,5,6,5] (by decide +kernel))
      (invalid_excluded a [4,5,6,6] (by decide +kernel))
      node_938
      node_939)

theorem node_949 : Excluded a [4,5,7,0] :=
  source_excluded a [4,5,7,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_950 : Excluded a [4,5,7,1] :=
  source_excluded a [4,5,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_951 : Excluded a [4,5,7,2] :=
  source_excluded a [4,5,7,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_953 : Excluded a [4,5,7,6,0] :=
  predecessor_excluded a [4,5,7,6,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_954 : Excluded a [4,5,7,6,1] :=
  source_excluded a [4,5,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_955 : Excluded a [4,5,7,6,3] :=
  source_excluded a [4,5,7,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_957 : Excluded a [4,5,7,6,8,0] :=
  source_excluded a [4,5,7,6,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_958 : Excluded a [4,5,7,6,8,1] :=
  predecessor_excluded a [4,5,7,6,8,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_959 : Excluded a [4,5,7,6,8,2] :=
  predecessor_excluded a [4,5,7,6,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_960 : Excluded a [4,5,7,6,8,3] :=
  source_excluded a [4,5,7,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_956 : Excluded a [4,5,7,6,8] :=
  branch_excluded a [4,5,7,6,8] (by decide)
    (fin9_cases _
      node_957
      node_958
      node_959
      node_960
      (invalid_excluded a [4,5,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,5,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,5,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,5,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,5,7,6,8,8] (by decide +kernel)))

theorem node_952 : Excluded a [4,5,7,6] :=
  branch_excluded a [4,5,7,6] (by decide)
    (fin9_cases _
      node_953
      node_954
      (invalid_excluded a [4,5,7,6,2] (by decide +kernel))
      node_955
      (invalid_excluded a [4,5,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,5,7,6,7] (by decide +kernel))
      node_956)

theorem node_961 : Excluded a [4,5,7,8] :=
  predecessor_excluded a [4,5,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_948 : Excluded a [4,5,7] :=
  branch_excluded a [4,5,7] (by decide)
    (fin9_cases _
      node_949
      node_950
      node_951
      (invalid_excluded a [4,5,7,3] (by decide +kernel))
      (invalid_excluded a [4,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,5,7,5] (by decide +kernel))
      node_952
      (invalid_excluded a [4,5,7,7] (by decide +kernel))
      node_961)

theorem node_963 : Excluded a [4,5,8,0] :=
  source_excluded a [4,5,8,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_964 : Excluded a [4,5,8,1] :=
  source_excluded a [4,5,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_965 : Excluded a [4,5,8,2] :=
  source_excluded a [4,5,8,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_967 : Excluded a [4,5,8,6,0] :=
  predecessor_excluded a [4,5,8,6,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_968 : Excluded a [4,5,8,6,1] :=
  source_excluded a [4,5,8,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_969 : Excluded a [4,5,8,6,3] :=
  source_excluded a [4,5,8,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_970 : Excluded a [4,5,8,6,7] :=
  predecessor_excluded a [4,5,8,6,7] 0 8 4 2 (by decide) (by decide +kernel)

theorem node_966 : Excluded a [4,5,8,6] :=
  branch_excluded a [4,5,8,6] (by decide)
    (fin9_cases _
      node_967
      node_968
      (invalid_excluded a [4,5,8,6,2] (by decide +kernel))
      node_969
      (invalid_excluded a [4,5,8,6,4] (by decide +kernel))
      (invalid_excluded a [4,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [4,5,8,6,6] (by decide +kernel))
      node_970
      (invalid_excluded a [4,5,8,6,8] (by decide +kernel)))

theorem node_972 : Excluded a [4,5,8,7,0] :=
  predecessor_excluded a [4,5,8,7,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_973 : Excluded a [4,5,8,7,1] :=
  source_excluded a [4,5,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_974 : Excluded a [4,5,8,7,3] :=
  source_excluded a [4,5,8,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_976 : Excluded a [4,5,8,7,6,0] :=
  source_excluded a [4,5,8,7,6,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_977 : Excluded a [4,5,8,7,6,1] :=
  predecessor_excluded a [4,5,8,7,6,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_978 : Excluded a [4,5,8,7,6,2] :=
  source_excluded a [4,5,8,7,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_979 : Excluded a [4,5,8,7,6,3] :=
  predecessor_excluded a [4,5,8,7,6,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_975 : Excluded a [4,5,8,7,6] :=
  branch_excluded a [4,5,8,7,6] (by decide)
    (fin9_cases _
      node_976
      node_977
      node_978
      node_979
      (invalid_excluded a [4,5,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,5,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,5,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,5,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [4,5,8,7,6,8] (by decide +kernel)))

theorem node_971 : Excluded a [4,5,8,7] :=
  branch_excluded a [4,5,8,7] (by decide)
    (fin9_cases _
      node_972
      node_973
      (invalid_excluded a [4,5,8,7,2] (by decide +kernel))
      node_974
      (invalid_excluded a [4,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,5,8,7,5] (by decide +kernel))
      node_975
      (invalid_excluded a [4,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,5,8,7,8] (by decide +kernel)))

theorem node_962 : Excluded a [4,5,8] :=
  branch_excluded a [4,5,8] (by decide)
    (fin9_cases _
      node_963
      node_964
      node_965
      (invalid_excluded a [4,5,8,3] (by decide +kernel))
      (invalid_excluded a [4,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,5,8,5] (by decide +kernel))
      node_966
      node_971
      (invalid_excluded a [4,5,8,8] (by decide +kernel)))

theorem node_875 : Excluded a [4,5] :=
  branch_excluded a [4,5] (by decide)
    (fin9_cases _
      node_876
      node_877
      (invalid_excluded a [4,5,2] (by decide +kernel))
      (invalid_excluded a [4,5,3] (by decide +kernel))
      (invalid_excluded a [4,5,4] (by decide +kernel))
      (invalid_excluded a [4,5,5] (by decide +kernel))
      node_934
      node_948
      node_962)

theorem node_981 : Excluded a [4,6,0] :=
  predecessor_excluded a [4,6,0] 1 4 2 0 (by decide) (by decide +kernel)

theorem node_983 : Excluded a [4,6,1,0] :=
  source_excluded a [4,6,1,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_984 : Excluded a [4,6,1,2] :=
  source_excluded a [4,6,1,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_986 : Excluded a [4,6,1,5,0] :=
  predecessor_excluded a [4,6,1,5,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_987 : Excluded a [4,6,1,5,3] :=
  source_excluded a [4,6,1,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_989 : Excluded a [4,6,1,5,7,0] :=
  source_excluded a [4,6,1,5,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_990 : Excluded a [4,6,1,5,7,2] :=
  predecessor_excluded a [4,6,1,5,7,2] 0 2 3 5 (by decide) (by decide +kernel)

theorem node_992 : Excluded a [4,6,1,5,7,3,0] :=
  source_excluded a [4,6,1,5,7,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_993 : Excluded a [4,6,1,5,7,3,2] :=
  source_excluded a [4,6,1,5,7,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_994 : Excluded a [4,6,1,5,7,3,8] :=
  source_excluded a [4,6,1,5,7,3,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_991 : Excluded a [4,6,1,5,7,3] :=
  branch_excluded a [4,6,1,5,7,3] (by decide)
    (fin9_cases _
      node_992
      (invalid_excluded a [4,6,1,5,7,3,1] (by decide +kernel))
      node_993
      (invalid_excluded a [4,6,1,5,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,3,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,3,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,3,7] (by decide +kernel))
      node_994)

theorem node_996 : Excluded a [4,6,1,5,7,8,0] :=
  source_excluded a [4,6,1,5,7,8,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_997 : Excluded a [4,6,1,5,7,8,2] :=
  source_excluded a [4,6,1,5,7,8,2] 4 0 6 (by decide) (by decide +kernel)

def b_1000 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 6
  | 2 => 1
  | 3 => 5
  | 4 => 7
  | 5 => 8
  | 6 => 3
  | 7 => 0
  | 8 => 2
  | _ => 0

def cert_1000 : LosingRegion (edgeOf a b_1000) 0 :=
  losingMask a b_1000 0 1923187505984755111560192
    (by decide +kernel) (by decide +kernel)

theorem node_1000 : Excluded a [4,6,1,5,7,8,3,0,2] :=
  losing_excluded a [4,6,1,5,7,8,3,0,2] (by decide) b_1000 (by decide +kernel) 2 0 0 cert_1000 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1000 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1923187505984755111560192 2 0; decide +kernel)

theorem node_999 : Excluded a [4,6,1,5,7,8,3,0] :=
  branch_excluded a [4,6,1,5,7,8,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,5,7,8,3,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,8,3,0,1] (by decide +kernel))
      node_1000
      (invalid_excluded a [4,6,1,5,7,8,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,8,3,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,8,3,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,8,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,8,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,8,3,0,8] (by decide +kernel)))

theorem node_1001 : Excluded a [4,6,1,5,7,8,3,2] :=
  source_excluded a [4,6,1,5,7,8,3,2] 4 0 7 (by decide) (by decide +kernel)

theorem node_998 : Excluded a [4,6,1,5,7,8,3] :=
  branch_excluded a [4,6,1,5,7,8,3] (by decide)
    (fin9_cases _
      node_999
      (invalid_excluded a [4,6,1,5,7,8,3,1] (by decide +kernel))
      node_1001
      (invalid_excluded a [4,6,1,5,7,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,8,3,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,8,3,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,8,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,8,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,8,3,8] (by decide +kernel)))

theorem node_995 : Excluded a [4,6,1,5,7,8] :=
  branch_excluded a [4,6,1,5,7,8] (by decide)
    (fin9_cases _
      node_996
      (invalid_excluded a [4,6,1,5,7,8,1] (by decide +kernel))
      node_997
      node_998
      (invalid_excluded a [4,6,1,5,7,8,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,8,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,8,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,8,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,8,8] (by decide +kernel)))

theorem node_988 : Excluded a [4,6,1,5,7] :=
  branch_excluded a [4,6,1,5,7] (by decide)
    (fin9_cases _
      node_989
      (invalid_excluded a [4,6,1,5,7,1] (by decide +kernel))
      node_990
      node_991
      (invalid_excluded a [4,6,1,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,7,7] (by decide +kernel))
      node_995)

theorem node_1003 : Excluded a [4,6,1,5,8,0] :=
  source_excluded a [4,6,1,5,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_1004 : Excluded a [4,6,1,5,8,2] :=
  predecessor_excluded a [4,6,1,5,8,2] 0 2 3 5 (by decide) (by decide +kernel)

theorem node_1006 : Excluded a [4,6,1,5,8,3,0] :=
  source_excluded a [4,6,1,5,8,3,0] 1 2 6 (by decide) (by decide +kernel)

def b_1009 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 6
  | 2 => 1
  | 3 => 5
  | 4 => 8
  | 5 => 3
  | 6 => 2
  | 7 => 0
  | 8 => 7
  | _ => 0

def cert_1009 : LosingRegion (edgeOf a b_1009) 0 :=
  losingMask a b_1009 0 2116804251684199311606784
    (by decide +kernel) (by decide +kernel)

theorem node_1009 : Excluded a [4,6,1,5,8,3,2,0,7] :=
  losing_excluded a [4,6,1,5,8,3,2,0,7] (by decide) b_1009 (by decide +kernel) 2 0 0 cert_1009 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1009 2 0 ∧ 0 ≠ 2 ∧ maskRegion 2116804251684199311606784 2 0; decide +kernel)

theorem node_1008 : Excluded a [4,6,1,5,8,3,2,0] :=
  branch_excluded a [4,6,1,5,8,3,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,5,8,3,2,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,2,0,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,2,0,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,2,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,2,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,2,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,2,0,6] (by decide +kernel))
      node_1009
      (invalid_excluded a [4,6,1,5,8,3,2,0,8] (by decide +kernel)))

theorem node_1007 : Excluded a [4,6,1,5,8,3,2] :=
  branch_excluded a [4,6,1,5,8,3,2] (by decide)
    (fin9_cases _
      node_1008
      (invalid_excluded a [4,6,1,5,8,3,2,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,2,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,2,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,2,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,2,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,2,8] (by decide +kernel)))

theorem node_1005 : Excluded a [4,6,1,5,8,3] :=
  branch_excluded a [4,6,1,5,8,3] (by decide)
    (fin9_cases _
      node_1006
      (invalid_excluded a [4,6,1,5,8,3,1] (by decide +kernel))
      node_1007
      (invalid_excluded a [4,6,1,5,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,3,8] (by decide +kernel)))

theorem node_1010 : Excluded a [4,6,1,5,8,7] :=
  source_excluded a [4,6,1,5,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1002 : Excluded a [4,6,1,5,8] :=
  branch_excluded a [4,6,1,5,8] (by decide)
    (fin9_cases _
      node_1003
      (invalid_excluded a [4,6,1,5,8,1] (by decide +kernel))
      node_1004
      node_1005
      (invalid_excluded a [4,6,1,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,8,6] (by decide +kernel))
      node_1010
      (invalid_excluded a [4,6,1,5,8,8] (by decide +kernel)))

theorem node_985 : Excluded a [4,6,1,5] :=
  branch_excluded a [4,6,1,5] (by decide)
    (fin9_cases _
      node_986
      (invalid_excluded a [4,6,1,5,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,2] (by decide +kernel))
      node_987
      (invalid_excluded a [4,6,1,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,5,6] (by decide +kernel))
      node_988
      node_1002)

theorem node_1012 : Excluded a [4,6,1,7,0] :=
  predecessor_excluded a [4,6,1,7,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_1013 : Excluded a [4,6,1,7,3] :=
  source_excluded a [4,6,1,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1015 : Excluded a [4,6,1,7,5,0] :=
  source_excluded a [4,6,1,7,5,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_1016 : Excluded a [4,6,1,7,5,2] :=
  source_excluded a [4,6,1,7,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1017 : Excluded a [4,6,1,7,5,3] :=
  predecessor_excluded a [4,6,1,7,5,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1019 : Excluded a [4,6,1,7,5,8,0] :=
  source_excluded a [4,6,1,7,5,8,0] 1 2 6 (by decide) (by decide +kernel)

def b_1022 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 6
  | 2 => 1
  | 3 => 7
  | 4 => 5
  | 5 => 8
  | 6 => 2
  | 7 => 0
  | 8 => 3
  | _ => 0

def cert_1022 : LosingRegion (edgeOf a b_1022) 0 :=
  losingMask a b_1022 0 1691788948863628908954624
    (by decide +kernel) (by decide +kernel)

theorem node_1022 : Excluded a [4,6,1,7,5,8,2,0,3] :=
  losing_excluded a [4,6,1,7,5,8,2,0,3] (by decide) b_1022 (by decide +kernel) 2 0 1 cert_1022 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1022 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1691788948863628908954624 2 1; decide +kernel)

theorem node_1021 : Excluded a [4,6,1,7,5,8,2,0] :=
  branch_excluded a [4,6,1,7,5,8,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,7,5,8,2,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,8,2,0,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,8,2,0,2] (by decide +kernel))
      node_1022
      (invalid_excluded a [4,6,1,7,5,8,2,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,8,2,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,8,2,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,8,2,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,8,2,0,8] (by decide +kernel)))

theorem node_1023 : Excluded a [4,6,1,7,5,8,2,3] :=
  predecessor_excluded a [4,6,1,7,5,8,2,3] 0 3 6 7 (by decide) (by decide +kernel)

theorem node_1020 : Excluded a [4,6,1,7,5,8,2] :=
  branch_excluded a [4,6,1,7,5,8,2] (by decide)
    (fin9_cases _
      node_1021
      (invalid_excluded a [4,6,1,7,5,8,2,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,8,2,2] (by decide +kernel))
      node_1023
      (invalid_excluded a [4,6,1,7,5,8,2,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,8,2,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,8,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,8,2,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,8,2,8] (by decide +kernel)))

theorem node_1024 : Excluded a [4,6,1,7,5,8,3] :=
  source_excluded a [4,6,1,7,5,8,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1018 : Excluded a [4,6,1,7,5,8] :=
  branch_excluded a [4,6,1,7,5,8] (by decide)
    (fin9_cases _
      node_1019
      (invalid_excluded a [4,6,1,7,5,8,1] (by decide +kernel))
      node_1020
      node_1024
      (invalid_excluded a [4,6,1,7,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,8,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,8,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,8,8] (by decide +kernel)))

theorem node_1014 : Excluded a [4,6,1,7,5] :=
  branch_excluded a [4,6,1,7,5] (by decide)
    (fin9_cases _
      node_1015
      (invalid_excluded a [4,6,1,7,5,1] (by decide +kernel))
      node_1016
      node_1017
      (invalid_excluded a [4,6,1,7,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5,7] (by decide +kernel))
      node_1018)

theorem node_1025 : Excluded a [4,6,1,7,8] :=
  predecessor_excluded a [4,6,1,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_1011 : Excluded a [4,6,1,7] :=
  branch_excluded a [4,6,1,7] (by decide)
    (fin9_cases _
      node_1012
      (invalid_excluded a [4,6,1,7,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,2] (by decide +kernel))
      node_1013
      (invalid_excluded a [4,6,1,7,4] (by decide +kernel))
      node_1014
      (invalid_excluded a [4,6,1,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,7] (by decide +kernel))
      node_1025)

theorem node_1027 : Excluded a [4,6,1,8,0] :=
  predecessor_excluded a [4,6,1,8,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_1028 : Excluded a [4,6,1,8,3] :=
  source_excluded a [4,6,1,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1029 : Excluded a [4,6,1,8,5] :=
  predecessor_excluded a [4,6,1,8,5] 0 5 3 4 (by decide) (by decide +kernel)

theorem node_1031 : Excluded a [4,6,1,8,7,0] :=
  source_excluded a [4,6,1,8,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_1033 : Excluded a [4,6,1,8,7,2,0] :=
  source_excluded a [4,6,1,8,7,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1034 : Excluded a [4,6,1,8,7,2,3] :=
  predecessor_excluded a [4,6,1,8,7,2,3] 0 8 6 3 (by decide) (by decide +kernel)

def b_1037 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 6
  | 2 => 1
  | 3 => 8
  | 4 => 7
  | 5 => 2
  | 6 => 5
  | 7 => 0
  | 8 => 3
  | _ => 0

def cert_1037 : LosingRegion (edgeOf a b_1037) 0 :=
  losingMask a b_1037 0 2414313617669923423388672
    (by decide +kernel) (by decide +kernel)

theorem node_1037 : Excluded a [4,6,1,8,7,2,5,0,3] :=
  losing_excluded a [4,6,1,8,7,2,5,0,3] (by decide) b_1037 (by decide +kernel) 2 0 0 cert_1037 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1037 2 0 ∧ 0 ≠ 2 ∧ maskRegion 2414313617669923423388672 2 0; decide +kernel)

theorem node_1036 : Excluded a [4,6,1,8,7,2,5,0] :=
  branch_excluded a [4,6,1,8,7,2,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,8,7,2,5,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,5,0,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,5,0,2] (by decide +kernel))
      node_1037
      (invalid_excluded a [4,6,1,8,7,2,5,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,5,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,5,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,5,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,5,0,8] (by decide +kernel)))

theorem node_1038 : Excluded a [4,6,1,8,7,2,5,3] :=
  source_excluded a [4,6,1,8,7,2,5,3] 7 0 3 (by decide) (by decide +kernel)

theorem node_1035 : Excluded a [4,6,1,8,7,2,5] :=
  branch_excluded a [4,6,1,8,7,2,5] (by decide)
    (fin9_cases _
      node_1036
      (invalid_excluded a [4,6,1,8,7,2,5,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,5,2] (by decide +kernel))
      node_1038
      (invalid_excluded a [4,6,1,8,7,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,5,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,5,8] (by decide +kernel)))

theorem node_1032 : Excluded a [4,6,1,8,7,2] :=
  branch_excluded a [4,6,1,8,7,2] (by decide)
    (fin9_cases _
      node_1033
      (invalid_excluded a [4,6,1,8,7,2,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,2] (by decide +kernel))
      node_1034
      (invalid_excluded a [4,6,1,8,7,2,4] (by decide +kernel))
      node_1035
      (invalid_excluded a [4,6,1,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,8] (by decide +kernel)))

theorem node_1040 : Excluded a [4,6,1,8,7,3,0] :=
  source_excluded a [4,6,1,8,7,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1041 : Excluded a [4,6,1,8,7,3,2] :=
  source_excluded a [4,6,1,8,7,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1044 : Excluded a [4,6,1,8,7,3,5,0,2] :=
  predecessor_excluded a [4,6,1,8,7,3,5,0,2] 0 3 8 5 (by decide) (by decide +kernel)

theorem node_1043 : Excluded a [4,6,1,8,7,3,5,0] :=
  branch_excluded a [4,6,1,8,7,3,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,8,7,3,5,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,5,0,1] (by decide +kernel))
      node_1044
      (invalid_excluded a [4,6,1,8,7,3,5,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,5,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,5,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,5,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,5,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,5,0,8] (by decide +kernel)))

theorem node_1045 : Excluded a [4,6,1,8,7,3,5,2] :=
  source_excluded a [4,6,1,8,7,3,5,2] 4 0 7 (by decide) (by decide +kernel)

theorem node_1042 : Excluded a [4,6,1,8,7,3,5] :=
  branch_excluded a [4,6,1,8,7,3,5] (by decide)
    (fin9_cases _
      node_1043
      (invalid_excluded a [4,6,1,8,7,3,5,1] (by decide +kernel))
      node_1045
      (invalid_excluded a [4,6,1,8,7,3,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,5,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,5,8] (by decide +kernel)))

theorem node_1039 : Excluded a [4,6,1,8,7,3] :=
  branch_excluded a [4,6,1,8,7,3] (by decide)
    (fin9_cases _
      node_1040
      (invalid_excluded a [4,6,1,8,7,3,1] (by decide +kernel))
      node_1041
      (invalid_excluded a [4,6,1,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,4] (by decide +kernel))
      node_1042
      (invalid_excluded a [4,6,1,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,8] (by decide +kernel)))

theorem node_1030 : Excluded a [4,6,1,8,7] :=
  branch_excluded a [4,6,1,8,7] (by decide)
    (fin9_cases _
      node_1031
      (invalid_excluded a [4,6,1,8,7,1] (by decide +kernel))
      node_1032
      node_1039
      (invalid_excluded a [4,6,1,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,8] (by decide +kernel)))

theorem node_1026 : Excluded a [4,6,1,8] :=
  branch_excluded a [4,6,1,8] (by decide)
    (fin9_cases _
      node_1027
      (invalid_excluded a [4,6,1,8,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,2] (by decide +kernel))
      node_1028
      (invalid_excluded a [4,6,1,8,4] (by decide +kernel))
      node_1029
      (invalid_excluded a [4,6,1,8,6] (by decide +kernel))
      node_1030
      (invalid_excluded a [4,6,1,8,8] (by decide +kernel)))

theorem node_982 : Excluded a [4,6,1] :=
  branch_excluded a [4,6,1] (by decide)
    (fin9_cases _
      node_983
      (invalid_excluded a [4,6,1,1] (by decide +kernel))
      node_984
      (invalid_excluded a [4,6,1,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,4] (by decide +kernel))
      node_985
      (invalid_excluded a [4,6,1,6] (by decide +kernel))
      node_1011
      node_1026)

theorem node_1047 : Excluded a [4,6,5,0] :=
  source_excluded a [4,6,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1048 : Excluded a [4,6,5,1] :=
  source_excluded a [4,6,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1049 : Excluded a [4,6,5,2] :=
  source_excluded a [4,6,5,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1051 : Excluded a [4,6,5,7,0] :=
  predecessor_excluded a [4,6,5,7,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1052 : Excluded a [4,6,5,7,1] :=
  source_excluded a [4,6,5,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1053 : Excluded a [4,6,5,7,3] :=
  source_excluded a [4,6,5,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1054 : Excluded a [4,6,5,7,8] :=
  predecessor_excluded a [4,6,5,7,8] 0 5 4 2 (by decide) (by decide +kernel)

theorem node_1050 : Excluded a [4,6,5,7] :=
  branch_excluded a [4,6,5,7] (by decide)
    (fin9_cases _
      node_1051
      node_1052
      (invalid_excluded a [4,6,5,7,2] (by decide +kernel))
      node_1053
      (invalid_excluded a [4,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,7] (by decide +kernel))
      node_1054)

theorem node_1056 : Excluded a [4,6,5,8,0] :=
  predecessor_excluded a [4,6,5,8,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1057 : Excluded a [4,6,5,8,1] :=
  source_excluded a [4,6,5,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1058 : Excluded a [4,6,5,8,3] :=
  source_excluded a [4,6,5,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1060 : Excluded a [4,6,5,8,7,0] :=
  source_excluded a [4,6,5,8,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_1061 : Excluded a [4,6,5,8,7,1] :=
  source_excluded a [4,6,5,8,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_1063 : Excluded a [4,6,5,8,7,2,0] :=
  source_excluded a [4,6,5,8,7,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1064 : Excluded a [4,6,5,8,7,2,1] :=
  predecessor_excluded a [4,6,5,8,7,2,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_1065 : Excluded a [4,6,5,8,7,2,3] :=
  predecessor_excluded a [4,6,5,8,7,2,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_1062 : Excluded a [4,6,5,8,7,2] :=
  branch_excluded a [4,6,5,8,7,2] (by decide)
    (fin9_cases _
      node_1063
      node_1064
      (invalid_excluded a [4,6,5,8,7,2,2] (by decide +kernel))
      node_1065
      (invalid_excluded a [4,6,5,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,8] (by decide +kernel)))

theorem node_1066 : Excluded a [4,6,5,8,7,3] :=
  source_excluded a [4,6,5,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1059 : Excluded a [4,6,5,8,7] :=
  branch_excluded a [4,6,5,8,7] (by decide)
    (fin9_cases _
      node_1060
      node_1061
      node_1062
      node_1066
      (invalid_excluded a [4,6,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,8] (by decide +kernel)))

theorem node_1055 : Excluded a [4,6,5,8] :=
  branch_excluded a [4,6,5,8] (by decide)
    (fin9_cases _
      node_1056
      node_1057
      (invalid_excluded a [4,6,5,8,2] (by decide +kernel))
      node_1058
      (invalid_excluded a [4,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,6] (by decide +kernel))
      node_1059
      (invalid_excluded a [4,6,5,8,8] (by decide +kernel)))

theorem node_1046 : Excluded a [4,6,5] :=
  branch_excluded a [4,6,5] (by decide)
    (fin9_cases _
      node_1047
      node_1048
      node_1049
      (invalid_excluded a [4,6,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,6] (by decide +kernel))
      node_1050
      node_1055)

theorem node_1068 : Excluded a [4,6,7,0] :=
  source_excluded a [4,6,7,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1069 : Excluded a [4,6,7,1] :=
  source_excluded a [4,6,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1070 : Excluded a [4,6,7,2] :=
  source_excluded a [4,6,7,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1072 : Excluded a [4,6,7,5,0] :=
  predecessor_excluded a [4,6,7,5,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1073 : Excluded a [4,6,7,5,1] :=
  source_excluded a [4,6,7,5,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1074 : Excluded a [4,6,7,5,3] :=
  source_excluded a [4,6,7,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1076 : Excluded a [4,6,7,5,8,0] :=
  source_excluded a [4,6,7,5,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_1077 : Excluded a [4,6,7,5,8,1] :=
  source_excluded a [4,6,7,5,8,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_1078 : Excluded a [4,6,7,5,8,2] :=
  predecessor_excluded a [4,6,7,5,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1080 : Excluded a [4,6,7,5,8,3,0] :=
  source_excluded a [4,6,7,5,8,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1081 : Excluded a [4,6,7,5,8,3,1] :=
  predecessor_excluded a [4,6,7,5,8,3,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_1082 : Excluded a [4,6,7,5,8,3,2] :=
  source_excluded a [4,6,7,5,8,3,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1079 : Excluded a [4,6,7,5,8,3] :=
  branch_excluded a [4,6,7,5,8,3] (by decide)
    (fin9_cases _
      node_1080
      node_1081
      node_1082
      (invalid_excluded a [4,6,7,5,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,7,5,8,3,4] (by decide +kernel))
      (invalid_excluded a [4,6,7,5,8,3,5] (by decide +kernel))
      (invalid_excluded a [4,6,7,5,8,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,7,5,8,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,7,5,8,3,8] (by decide +kernel)))

theorem node_1075 : Excluded a [4,6,7,5,8] :=
  branch_excluded a [4,6,7,5,8] (by decide)
    (fin9_cases _
      node_1076
      node_1077
      node_1078
      node_1079
      (invalid_excluded a [4,6,7,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,6,7,5,8,5] (by decide +kernel))
      (invalid_excluded a [4,6,7,5,8,6] (by decide +kernel))
      (invalid_excluded a [4,6,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [4,6,7,5,8,8] (by decide +kernel)))

theorem node_1071 : Excluded a [4,6,7,5] :=
  branch_excluded a [4,6,7,5] (by decide)
    (fin9_cases _
      node_1072
      node_1073
      (invalid_excluded a [4,6,7,5,2] (by decide +kernel))
      node_1074
      (invalid_excluded a [4,6,7,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,7,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,7,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,7,5,7] (by decide +kernel))
      node_1075)

theorem node_1083 : Excluded a [4,6,7,8] :=
  predecessor_excluded a [4,6,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_1067 : Excluded a [4,6,7] :=
  branch_excluded a [4,6,7] (by decide)
    (fin9_cases _
      node_1068
      node_1069
      node_1070
      (invalid_excluded a [4,6,7,3] (by decide +kernel))
      (invalid_excluded a [4,6,7,4] (by decide +kernel))
      node_1071
      (invalid_excluded a [4,6,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,7,7] (by decide +kernel))
      node_1083)

theorem node_1085 : Excluded a [4,6,8,0] :=
  source_excluded a [4,6,8,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1086 : Excluded a [4,6,8,1] :=
  source_excluded a [4,6,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1087 : Excluded a [4,6,8,2] :=
  source_excluded a [4,6,8,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1088 : Excluded a [4,6,8,5] :=
  predecessor_excluded a [4,6,8,5] 0 5 2 3 (by decide) (by decide +kernel)

theorem node_1090 : Excluded a [4,6,8,7,0] :=
  predecessor_excluded a [4,6,8,7,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1091 : Excluded a [4,6,8,7,1] :=
  source_excluded a [4,6,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1092 : Excluded a [4,6,8,7,3] :=
  source_excluded a [4,6,8,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1094 : Excluded a [4,6,8,7,5,0] :=
  source_excluded a [4,6,8,7,5,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_1095 : Excluded a [4,6,8,7,5,1] :=
  source_excluded a [4,6,8,7,5,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_1096 : Excluded a [4,6,8,7,5,2] :=
  source_excluded a [4,6,8,7,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1097 : Excluded a [4,6,8,7,5,3] :=
  predecessor_excluded a [4,6,8,7,5,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1093 : Excluded a [4,6,8,7,5] :=
  branch_excluded a [4,6,8,7,5] (by decide)
    (fin9_cases _
      node_1094
      node_1095
      node_1096
      node_1097
      (invalid_excluded a [4,6,8,7,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,5,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,5,8] (by decide +kernel)))

theorem node_1089 : Excluded a [4,6,8,7] :=
  branch_excluded a [4,6,8,7] (by decide)
    (fin9_cases _
      node_1090
      node_1091
      (invalid_excluded a [4,6,8,7,2] (by decide +kernel))
      node_1092
      (invalid_excluded a [4,6,8,7,4] (by decide +kernel))
      node_1093
      (invalid_excluded a [4,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,8] (by decide +kernel)))

theorem node_1084 : Excluded a [4,6,8] :=
  branch_excluded a [4,6,8] (by decide)
    (fin9_cases _
      node_1085
      node_1086
      node_1087
      (invalid_excluded a [4,6,8,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,4] (by decide +kernel))
      node_1088
      (invalid_excluded a [4,6,8,6] (by decide +kernel))
      node_1089
      (invalid_excluded a [4,6,8,8] (by decide +kernel)))

theorem node_980 : Excluded a [4,6] :=
  branch_excluded a [4,6] (by decide)
    (fin9_cases _
      node_981
      node_982
      (invalid_excluded a [4,6,2] (by decide +kernel))
      (invalid_excluded a [4,6,3] (by decide +kernel))
      (invalid_excluded a [4,6,4] (by decide +kernel))
      node_1046
      (invalid_excluded a [4,6,6] (by decide +kernel))
      node_1067
      node_1084)

theorem node_1099 : Excluded a [4,7,0] :=
  predecessor_excluded a [4,7,0] 1 4 2 0 (by decide) (by decide +kernel)

theorem node_1101 : Excluded a [4,7,1,0] :=
  source_excluded a [4,7,1,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1102 : Excluded a [4,7,1,2] :=
  source_excluded a [4,7,1,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1104 : Excluded a [4,7,1,5,0] :=
  predecessor_excluded a [4,7,1,5,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_1105 : Excluded a [4,7,1,5,3] :=
  source_excluded a [4,7,1,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1106 : Excluded a [4,7,1,5,6] :=
  predecessor_excluded a [4,7,1,5,6] 0 6 3 4 (by decide) (by decide +kernel)

theorem node_1110 : Excluded a [4,7,1,5,8,0,2,3] :=
  predecessor_excluded a [4,7,1,5,8,0,2,3] 0 5 7 3 (by decide) (by decide +kernel)

theorem node_1112 : Excluded a [4,7,1,5,8,0,2,6,3] :=
  source_excluded a [4,7,1,5,8,0,2,6,3] 8 0 3 (by decide) (by decide +kernel)

theorem node_1111 : Excluded a [4,7,1,5,8,0,2,6] :=
  branch_excluded a [4,7,1,5,8,0,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,5,8,0,2,6,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,2,6,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,2,6,2] (by decide +kernel))
      node_1112
      (invalid_excluded a [4,7,1,5,8,0,2,6,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,2,6,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,2,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,2,6,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,2,6,8] (by decide +kernel)))

theorem node_1109 : Excluded a [4,7,1,5,8,0,2] :=
  branch_excluded a [4,7,1,5,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,5,8,0,2,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,2,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,2,2] (by decide +kernel))
      node_1110
      (invalid_excluded a [4,7,1,5,8,0,2,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,2,5] (by decide +kernel))
      node_1111
      (invalid_excluded a [4,7,1,5,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,2,8] (by decide +kernel)))

theorem node_1114 : Excluded a [4,7,1,5,8,0,3,2] :=
  source_excluded a [4,7,1,5,8,0,3,2] 4 0 7 (by decide) (by decide +kernel)

theorem node_1116 : Excluded a [4,7,1,5,8,0,3,6,2] :=
  source_excluded a [4,7,1,5,8,0,3,6,2] 4 0 8 (by decide) (by decide +kernel)

theorem node_1115 : Excluded a [4,7,1,5,8,0,3,6] :=
  branch_excluded a [4,7,1,5,8,0,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,5,8,0,3,6,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,3,6,1] (by decide +kernel))
      node_1116
      (invalid_excluded a [4,7,1,5,8,0,3,6,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,3,6,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,3,6,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,3,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,3,6,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,3,6,8] (by decide +kernel)))

theorem node_1113 : Excluded a [4,7,1,5,8,0,3] :=
  branch_excluded a [4,7,1,5,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,5,8,0,3,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,3,1] (by decide +kernel))
      node_1114
      (invalid_excluded a [4,7,1,5,8,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,3,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,3,5] (by decide +kernel))
      node_1115
      (invalid_excluded a [4,7,1,5,8,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,3,8] (by decide +kernel)))

theorem node_1108 : Excluded a [4,7,1,5,8,0] :=
  branch_excluded a [4,7,1,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,5,8,0,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,1] (by decide +kernel))
      node_1109
      node_1113
      (invalid_excluded a [4,7,1,5,8,0,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,0,8] (by decide +kernel)))

theorem node_1117 : Excluded a [4,7,1,5,8,2] :=
  predecessor_excluded a [4,7,1,5,8,2] 0 2 3 5 (by decide) (by decide +kernel)

theorem node_1119 : Excluded a [4,7,1,5,8,3,0] :=
  source_excluded a [4,7,1,5,8,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1121 : Excluded a [4,7,1,5,8,3,2,0] :=
  source_excluded a [4,7,1,5,8,3,2,0] 1 2 7 (by decide) (by decide +kernel)

def b_1123 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 7
  | 2 => 1
  | 3 => 5
  | 4 => 8
  | 5 => 3
  | 6 => 2
  | 7 => 6
  | 8 => 0
  | _ => 0

def cert_1123 : LosingRegion (edgeOf a b_1123) 0 :=
  losingMask a b_1123 0 1212621293308426531374080
    (by decide +kernel) (by decide +kernel)

theorem node_1123 : Excluded a [4,7,1,5,8,3,2,6,0] :=
  losing_excluded a [4,7,1,5,8,3,2,6,0] (by decide) b_1123 (by decide +kernel) 2 0 0 cert_1123 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1123 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1212621293308426531374080 2 0; decide +kernel)

theorem node_1122 : Excluded a [4,7,1,5,8,3,2,6] :=
  branch_excluded a [4,7,1,5,8,3,2,6] (by decide)
    (fin9_cases _
      node_1123
      (invalid_excluded a [4,7,1,5,8,3,2,6,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,2,6,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,2,6,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,2,6,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,2,6,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,2,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,2,6,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,2,6,8] (by decide +kernel)))

theorem node_1120 : Excluded a [4,7,1,5,8,3,2] :=
  branch_excluded a [4,7,1,5,8,3,2] (by decide)
    (fin9_cases _
      node_1121
      (invalid_excluded a [4,7,1,5,8,3,2,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,2,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,2,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,2,5] (by decide +kernel))
      node_1122
      (invalid_excluded a [4,7,1,5,8,3,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,2,8] (by decide +kernel)))

theorem node_1118 : Excluded a [4,7,1,5,8,3] :=
  branch_excluded a [4,7,1,5,8,3] (by decide)
    (fin9_cases _
      node_1119
      (invalid_excluded a [4,7,1,5,8,3,1] (by decide +kernel))
      node_1120
      (invalid_excluded a [4,7,1,5,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,3,8] (by decide +kernel)))

theorem node_1107 : Excluded a [4,7,1,5,8] :=
  branch_excluded a [4,7,1,5,8] (by decide)
    (fin9_cases _
      node_1108
      (invalid_excluded a [4,7,1,5,8,1] (by decide +kernel))
      node_1117
      node_1118
      (invalid_excluded a [4,7,1,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,8,8] (by decide +kernel)))

theorem node_1103 : Excluded a [4,7,1,5] :=
  branch_excluded a [4,7,1,5] (by decide)
    (fin9_cases _
      node_1104
      (invalid_excluded a [4,7,1,5,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,2] (by decide +kernel))
      node_1105
      (invalid_excluded a [4,7,1,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,5,5] (by decide +kernel))
      node_1106
      (invalid_excluded a [4,7,1,5,7] (by decide +kernel))
      node_1107)

theorem node_1125 : Excluded a [4,7,1,6,0] :=
  predecessor_excluded a [4,7,1,6,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_1126 : Excluded a [4,7,1,6,3] :=
  source_excluded a [4,7,1,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1129 : Excluded a [4,7,1,6,5,0,2] :=
  predecessor_excluded a [4,7,1,6,5,0,2] 0 2 3 6 (by decide) (by decide +kernel)

theorem node_1131 : Excluded a [4,7,1,6,5,0,3,2] :=
  branch_excluded a [4,7,1,6,5,0,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,5,0,3,2,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,3,2,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,3,2,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,3,2,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,3,2,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,3,2,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,3,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,3,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,3,2,8] (by decide +kernel)))

theorem node_1130 : Excluded a [4,7,1,6,5,0,3] :=
  branch_excluded a [4,7,1,6,5,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,5,0,3,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,3,1] (by decide +kernel))
      node_1131
      (invalid_excluded a [4,7,1,6,5,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,3,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,3,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,3,8] (by decide +kernel)))

theorem node_1132 : Excluded a [4,7,1,6,5,0,8] :=
  source_excluded a [4,7,1,6,5,0,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_1128 : Excluded a [4,7,1,6,5,0] :=
  branch_excluded a [4,7,1,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,5,0,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,1] (by decide +kernel))
      node_1129
      node_1130
      (invalid_excluded a [4,7,1,6,5,0,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,0,7] (by decide +kernel))
      node_1132)

theorem node_1133 : Excluded a [4,7,1,6,5,2] :=
  source_excluded a [4,7,1,6,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1134 : Excluded a [4,7,1,6,5,3] :=
  source_excluded a [4,7,1,6,5,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1136 : Excluded a [4,7,1,6,5,8,0] :=
  source_excluded a [4,7,1,6,5,8,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1137 : Excluded a [4,7,1,6,5,8,2] :=
  predecessor_excluded a [4,7,1,6,5,8,2] 0 2 3 6 (by decide) (by decide +kernel)

theorem node_1139 : Excluded a [4,7,1,6,5,8,3,0] :=
  source_excluded a [4,7,1,6,5,8,3,0] 1 2 7 (by decide) (by decide +kernel)

def b_1141 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 7
  | 2 => 1
  | 3 => 6
  | 4 => 5
  | 5 => 8
  | 6 => 3
  | 7 => 2
  | 8 => 0
  | _ => 0

def cert_1141 : LosingRegion (edgeOf a b_1141) 0 :=
  losingMask a b_1141 0 1212476292081255584629760
    (by decide +kernel) (by decide +kernel)

theorem node_1141 : Excluded a [4,7,1,6,5,8,3,2,0] :=
  losing_excluded a [4,7,1,6,5,8,3,2,0] (by decide) b_1141 (by decide +kernel) 2 0 0 cert_1141 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1141 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1212476292081255584629760 2 0; decide +kernel)

theorem node_1140 : Excluded a [4,7,1,6,5,8,3,2] :=
  branch_excluded a [4,7,1,6,5,8,3,2] (by decide)
    (fin9_cases _
      node_1141
      (invalid_excluded a [4,7,1,6,5,8,3,2,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,8,3,2,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,8,3,2,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,8,3,2,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,8,3,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,8,3,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,8,3,2,8] (by decide +kernel)))

theorem node_1138 : Excluded a [4,7,1,6,5,8,3] :=
  branch_excluded a [4,7,1,6,5,8,3] (by decide)
    (fin9_cases _
      node_1139
      (invalid_excluded a [4,7,1,6,5,8,3,1] (by decide +kernel))
      node_1140
      (invalid_excluded a [4,7,1,6,5,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,8,3,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,8,3,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,8,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,8,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,8,3,8] (by decide +kernel)))

theorem node_1135 : Excluded a [4,7,1,6,5,8] :=
  branch_excluded a [4,7,1,6,5,8] (by decide)
    (fin9_cases _
      node_1136
      (invalid_excluded a [4,7,1,6,5,8,1] (by decide +kernel))
      node_1137
      node_1138
      (invalid_excluded a [4,7,1,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,8,8] (by decide +kernel)))

theorem node_1127 : Excluded a [4,7,1,6,5] :=
  branch_excluded a [4,7,1,6,5] (by decide)
    (fin9_cases _
      node_1128
      (invalid_excluded a [4,7,1,6,5,1] (by decide +kernel))
      node_1133
      node_1134
      (invalid_excluded a [4,7,1,6,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5,7] (by decide +kernel))
      node_1135)

theorem node_1144 : Excluded a [4,7,1,6,8,0,2] :=
  predecessor_excluded a [4,7,1,6,8,0,2] 0 2 3 6 (by decide) (by decide +kernel)

theorem node_1146 : Excluded a [4,7,1,6,8,0,3,2] :=
  source_excluded a [4,7,1,6,8,0,3,2] 4 0 7 (by decide) (by decide +kernel)

theorem node_1147 : Excluded a [4,7,1,6,8,0,3,5] :=
  source_excluded a [4,7,1,6,8,0,3,5] 7 0 8 (by decide) (by decide +kernel)

theorem node_1145 : Excluded a [4,7,1,6,8,0,3] :=
  branch_excluded a [4,7,1,6,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,8,0,3,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,3,1] (by decide +kernel))
      node_1146
      (invalid_excluded a [4,7,1,6,8,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,3,4] (by decide +kernel))
      node_1147
      (invalid_excluded a [4,7,1,6,8,0,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,3,8] (by decide +kernel)))

theorem node_1149 : Excluded a [4,7,1,6,8,0,5,2] :=
  source_excluded a [4,7,1,6,8,0,5,2] 4 0 7 (by decide) (by decide +kernel)

theorem node_1151 : Excluded a [4,7,1,6,8,0,5,3,2] :=
  source_excluded a [4,7,1,6,8,0,5,3,2] 4 0 8 (by decide) (by decide +kernel)

theorem node_1150 : Excluded a [4,7,1,6,8,0,5,3] :=
  branch_excluded a [4,7,1,6,8,0,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,8,0,5,3,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,5,3,1] (by decide +kernel))
      node_1151
      (invalid_excluded a [4,7,1,6,8,0,5,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,5,3,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,5,3,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,5,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,5,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,5,3,8] (by decide +kernel)))

theorem node_1148 : Excluded a [4,7,1,6,8,0,5] :=
  branch_excluded a [4,7,1,6,8,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,8,0,5,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,5,1] (by decide +kernel))
      node_1149
      node_1150
      (invalid_excluded a [4,7,1,6,8,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,5,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,5,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,5,8] (by decide +kernel)))

theorem node_1143 : Excluded a [4,7,1,6,8,0] :=
  branch_excluded a [4,7,1,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,8,0,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,1] (by decide +kernel))
      node_1144
      node_1145
      (invalid_excluded a [4,7,1,6,8,0,4] (by decide +kernel))
      node_1148
      (invalid_excluded a [4,7,1,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,8] (by decide +kernel)))

theorem node_1153 : Excluded a [4,7,1,6,8,2,0] :=
  source_excluded a [4,7,1,6,8,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1154 : Excluded a [4,7,1,6,8,2,3] :=
  predecessor_excluded a [4,7,1,6,8,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_1156 : Excluded a [4,7,1,6,8,2,5,0] :=
  source_excluded a [4,7,1,6,8,2,5,0] 1 2 7 (by decide) (by decide +kernel)

def b_1158 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 7
  | 2 => 1
  | 3 => 6
  | 4 => 8
  | 5 => 2
  | 6 => 5
  | 7 => 3
  | 8 => 0
  | _ => 0

def cert_1158 : LosingRegion (edgeOf a b_1158) 0 :=
  losingMask a b_1158 0 1212623736229749403157504
    (by decide +kernel) (by decide +kernel)

theorem node_1158 : Excluded a [4,7,1,6,8,2,5,3,0] :=
  losing_excluded a [4,7,1,6,8,2,5,3,0] (by decide) b_1158 (by decide +kernel) 2 0 0 cert_1158 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1158 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1212623736229749403157504 2 0; decide +kernel)

theorem node_1157 : Excluded a [4,7,1,6,8,2,5,3] :=
  branch_excluded a [4,7,1,6,8,2,5,3] (by decide)
    (fin9_cases _
      node_1158
      (invalid_excluded a [4,7,1,6,8,2,5,3,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,5,3,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,5,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,5,3,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,5,3,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,5,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,5,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,5,3,8] (by decide +kernel)))

theorem node_1155 : Excluded a [4,7,1,6,8,2,5] :=
  branch_excluded a [4,7,1,6,8,2,5] (by decide)
    (fin9_cases _
      node_1156
      (invalid_excluded a [4,7,1,6,8,2,5,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,5,2] (by decide +kernel))
      node_1157
      (invalid_excluded a [4,7,1,6,8,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,5,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,5,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,5,8] (by decide +kernel)))

theorem node_1152 : Excluded a [4,7,1,6,8,2] :=
  branch_excluded a [4,7,1,6,8,2] (by decide)
    (fin9_cases _
      node_1153
      (invalid_excluded a [4,7,1,6,8,2,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,2] (by decide +kernel))
      node_1154
      (invalid_excluded a [4,7,1,6,8,2,4] (by decide +kernel))
      node_1155
      (invalid_excluded a [4,7,1,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,2,8] (by decide +kernel)))

theorem node_1159 : Excluded a [4,7,1,6,8,3] :=
  source_excluded a [4,7,1,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1142 : Excluded a [4,7,1,6,8] :=
  branch_excluded a [4,7,1,6,8] (by decide)
    (fin9_cases _
      node_1143
      (invalid_excluded a [4,7,1,6,8,1] (by decide +kernel))
      node_1152
      node_1159
      (invalid_excluded a [4,7,1,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,8] (by decide +kernel)))

theorem node_1124 : Excluded a [4,7,1,6] :=
  branch_excluded a [4,7,1,6] (by decide)
    (fin9_cases _
      node_1125
      (invalid_excluded a [4,7,1,6,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2] (by decide +kernel))
      node_1126
      (invalid_excluded a [4,7,1,6,4] (by decide +kernel))
      node_1127
      (invalid_excluded a [4,7,1,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,7] (by decide +kernel))
      node_1142)

theorem node_1161 : Excluded a [4,7,1,8,0] :=
  predecessor_excluded a [4,7,1,8,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_1162 : Excluded a [4,7,1,8,3] :=
  source_excluded a [4,7,1,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1163 : Excluded a [4,7,1,8,5] :=
  predecessor_excluded a [4,7,1,8,5] 0 5 3 4 (by decide) (by decide +kernel)

theorem node_1166 : Excluded a [4,7,1,8,6,0,2] :=
  source_excluded a [4,7,1,8,6,0,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1167 : Excluded a [4,7,1,8,6,0,3] :=
  predecessor_excluded a [4,7,1,8,6,0,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_1170 : Excluded a [4,7,1,8,6,0,5,2,3] :=
  predecessor_excluded a [4,7,1,8,6,0,5,2,3] 0 3 7 8 (by decide) (by decide +kernel)

theorem node_1169 : Excluded a [4,7,1,8,6,0,5,2] :=
  branch_excluded a [4,7,1,8,6,0,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,8,6,0,5,2,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,0,5,2,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,0,5,2,2] (by decide +kernel))
      node_1170
      (invalid_excluded a [4,7,1,8,6,0,5,2,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,0,5,2,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,0,5,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,0,5,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,0,5,2,8] (by decide +kernel)))

theorem node_1171 : Excluded a [4,7,1,8,6,0,5,3] :=
  source_excluded a [4,7,1,8,6,0,5,3] 7 0 3 (by decide) (by decide +kernel)

theorem node_1168 : Excluded a [4,7,1,8,6,0,5] :=
  branch_excluded a [4,7,1,8,6,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,8,6,0,5,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,0,5,1] (by decide +kernel))
      node_1169
      node_1171
      (invalid_excluded a [4,7,1,8,6,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,0,5,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,0,5,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,0,5,8] (by decide +kernel)))

theorem node_1165 : Excluded a [4,7,1,8,6,0] :=
  branch_excluded a [4,7,1,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,8,6,0,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,0,1] (by decide +kernel))
      node_1166
      node_1167
      (invalid_excluded a [4,7,1,8,6,0,4] (by decide +kernel))
      node_1168
      (invalid_excluded a [4,7,1,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,0,8] (by decide +kernel)))

theorem node_1172 : Excluded a [4,7,1,8,6,2] :=
  source_excluded a [4,7,1,8,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1174 : Excluded a [4,7,1,8,6,3,0] :=
  source_excluded a [4,7,1,8,6,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1175 : Excluded a [4,7,1,8,6,3,2] :=
  source_excluded a [4,7,1,8,6,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1177 : Excluded a [4,7,1,8,6,3,5,0] :=
  source_excluded a [4,7,1,8,6,3,5,0] 1 2 7 (by decide) (by decide +kernel)

def b_1179 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 7
  | 2 => 1
  | 3 => 8
  | 4 => 6
  | 5 => 3
  | 6 => 5
  | 7 => 2
  | 8 => 0
  | _ => 0

def cert_1179 : LosingRegion (edgeOf a b_1179) 0 :=
  losingMask a b_1179 0 1210109914131492261856256
    (by decide +kernel) (by decide +kernel)

theorem node_1179 : Excluded a [4,7,1,8,6,3,5,2,0] :=
  losing_excluded a [4,7,1,8,6,3,5,2,0] (by decide) b_1179 (by decide +kernel) 2 0 1 cert_1179 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1179 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1210109914131492261856256 2 1; decide +kernel)

theorem node_1178 : Excluded a [4,7,1,8,6,3,5,2] :=
  branch_excluded a [4,7,1,8,6,3,5,2] (by decide)
    (fin9_cases _
      node_1179
      (invalid_excluded a [4,7,1,8,6,3,5,2,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,3,5,2,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,3,5,2,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,3,5,2,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,3,5,2,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,3,5,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,3,5,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,3,5,2,8] (by decide +kernel)))

theorem node_1176 : Excluded a [4,7,1,8,6,3,5] :=
  branch_excluded a [4,7,1,8,6,3,5] (by decide)
    (fin9_cases _
      node_1177
      (invalid_excluded a [4,7,1,8,6,3,5,1] (by decide +kernel))
      node_1178
      (invalid_excluded a [4,7,1,8,6,3,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,3,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,3,5,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,3,5,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,3,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,3,5,8] (by decide +kernel)))

theorem node_1173 : Excluded a [4,7,1,8,6,3] :=
  branch_excluded a [4,7,1,8,6,3] (by decide)
    (fin9_cases _
      node_1174
      (invalid_excluded a [4,7,1,8,6,3,1] (by decide +kernel))
      node_1175
      (invalid_excluded a [4,7,1,8,6,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,3,4] (by decide +kernel))
      node_1176
      (invalid_excluded a [4,7,1,8,6,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,3,8] (by decide +kernel)))

theorem node_1164 : Excluded a [4,7,1,8,6] :=
  branch_excluded a [4,7,1,8,6] (by decide)
    (fin9_cases _
      node_1165
      (invalid_excluded a [4,7,1,8,6,1] (by decide +kernel))
      node_1172
      node_1173
      (invalid_excluded a [4,7,1,8,6,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,6,8] (by decide +kernel)))

theorem node_1160 : Excluded a [4,7,1,8] :=
  branch_excluded a [4,7,1,8] (by decide)
    (fin9_cases _
      node_1161
      (invalid_excluded a [4,7,1,8,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,2] (by decide +kernel))
      node_1162
      (invalid_excluded a [4,7,1,8,4] (by decide +kernel))
      node_1163
      node_1164
      (invalid_excluded a [4,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,8] (by decide +kernel)))

theorem node_1100 : Excluded a [4,7,1] :=
  branch_excluded a [4,7,1] (by decide)
    (fin9_cases _
      node_1101
      (invalid_excluded a [4,7,1,1] (by decide +kernel))
      node_1102
      (invalid_excluded a [4,7,1,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,4] (by decide +kernel))
      node_1103
      node_1124
      (invalid_excluded a [4,7,1,7] (by decide +kernel))
      node_1160)

theorem node_1181 : Excluded a [4,7,5,0] :=
  source_excluded a [4,7,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1182 : Excluded a [4,7,5,1] :=
  source_excluded a [4,7,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1183 : Excluded a [4,7,5,2] :=
  source_excluded a [4,7,5,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1184 : Excluded a [4,7,5,6] :=
  predecessor_excluded a [4,7,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_1186 : Excluded a [4,7,5,8,0] :=
  predecessor_excluded a [4,7,5,8,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1187 : Excluded a [4,7,5,8,1] :=
  source_excluded a [4,7,5,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1188 : Excluded a [4,7,5,8,3] :=
  source_excluded a [4,7,5,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1191 : Excluded a [4,7,5,8,6,0,1] :=
  source_excluded a [4,7,5,8,6,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1192 : Excluded a [4,7,5,8,6,0,2] :=
  source_excluded a [4,7,5,8,6,0,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1193 : Excluded a [4,7,5,8,6,0,3] :=
  predecessor_excluded a [4,7,5,8,6,0,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_1190 : Excluded a [4,7,5,8,6,0] :=
  branch_excluded a [4,7,5,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,5,8,6,0,0] (by decide +kernel))
      node_1191
      node_1192
      node_1193
      (invalid_excluded a [4,7,5,8,6,0,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,6,0,8] (by decide +kernel)))

theorem node_1194 : Excluded a [4,7,5,8,6,1] :=
  predecessor_excluded a [4,7,5,8,6,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_1195 : Excluded a [4,7,5,8,6,2] :=
  source_excluded a [4,7,5,8,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1196 : Excluded a [4,7,5,8,6,3] :=
  source_excluded a [4,7,5,8,6,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1189 : Excluded a [4,7,5,8,6] :=
  branch_excluded a [4,7,5,8,6] (by decide)
    (fin9_cases _
      node_1190
      node_1194
      node_1195
      node_1196
      (invalid_excluded a [4,7,5,8,6,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,6,7] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,6,8] (by decide +kernel)))

theorem node_1185 : Excluded a [4,7,5,8] :=
  branch_excluded a [4,7,5,8] (by decide)
    (fin9_cases _
      node_1186
      node_1187
      (invalid_excluded a [4,7,5,8,2] (by decide +kernel))
      node_1188
      (invalid_excluded a [4,7,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,5] (by decide +kernel))
      node_1189
      (invalid_excluded a [4,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,8] (by decide +kernel)))

theorem node_1180 : Excluded a [4,7,5] :=
  branch_excluded a [4,7,5] (by decide)
    (fin9_cases _
      node_1181
      node_1182
      node_1183
      (invalid_excluded a [4,7,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,5] (by decide +kernel))
      node_1184
      (invalid_excluded a [4,7,5,7] (by decide +kernel))
      node_1185)

theorem node_1198 : Excluded a [4,7,6,0] :=
  source_excluded a [4,7,6,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1199 : Excluded a [4,7,6,1] :=
  source_excluded a [4,7,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1200 : Excluded a [4,7,6,2] :=
  source_excluded a [4,7,6,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1202 : Excluded a [4,7,6,5,0] :=
  predecessor_excluded a [4,7,6,5,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1203 : Excluded a [4,7,6,5,1] :=
  source_excluded a [4,7,6,5,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1204 : Excluded a [4,7,6,5,3] :=
  source_excluded a [4,7,6,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1207 : Excluded a [4,7,6,5,8,0,1] :=
  source_excluded a [4,7,6,5,8,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1209 : Excluded a [4,7,6,5,8,0,2,1] :=
  predecessor_excluded a [4,7,6,5,8,0,2,1] 2 1 1 7 (by decide) (by decide +kernel)

theorem node_1210 : Excluded a [4,7,6,5,8,0,2,3] :=
  predecessor_excluded a [4,7,6,5,8,0,2,3] 0 5 7 3 (by decide) (by decide +kernel)

theorem node_1208 : Excluded a [4,7,6,5,8,0,2] :=
  branch_excluded a [4,7,6,5,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,5,8,0,2,0] (by decide +kernel))
      node_1209
      (invalid_excluded a [4,7,6,5,8,0,2,2] (by decide +kernel))
      node_1210
      (invalid_excluded a [4,7,6,5,8,0,2,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,5,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,5,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,5,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,5,8,0,2,8] (by decide +kernel)))

theorem node_1211 : Excluded a [4,7,6,5,8,0,3] :=
  source_excluded a [4,7,6,5,8,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1206 : Excluded a [4,7,6,5,8,0] :=
  branch_excluded a [4,7,6,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,5,8,0,0] (by decide +kernel))
      node_1207
      node_1208
      node_1211
      (invalid_excluded a [4,7,6,5,8,0,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,5,8,0,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,5,8,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,5,8,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,5,8,0,8] (by decide +kernel)))

theorem node_1212 : Excluded a [4,7,6,5,8,1] :=
  predecessor_excluded a [4,7,6,5,8,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_1213 : Excluded a [4,7,6,5,8,2] :=
  source_excluded a [4,7,6,5,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1214 : Excluded a [4,7,6,5,8,3] :=
  source_excluded a [4,7,6,5,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1205 : Excluded a [4,7,6,5,8] :=
  branch_excluded a [4,7,6,5,8] (by decide)
    (fin9_cases _
      node_1206
      node_1212
      node_1213
      node_1214
      (invalid_excluded a [4,7,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,5,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,5,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,5,8,8] (by decide +kernel)))

theorem node_1201 : Excluded a [4,7,6,5] :=
  branch_excluded a [4,7,6,5] (by decide)
    (fin9_cases _
      node_1202
      node_1203
      (invalid_excluded a [4,7,6,5,2] (by decide +kernel))
      node_1204
      (invalid_excluded a [4,7,6,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,5,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,5,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,5,7] (by decide +kernel))
      node_1205)

theorem node_1216 : Excluded a [4,7,6,8,0] :=
  predecessor_excluded a [4,7,6,8,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1217 : Excluded a [4,7,6,8,1] :=
  source_excluded a [4,7,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1218 : Excluded a [4,7,6,8,3] :=
  source_excluded a [4,7,6,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1219 : Excluded a [4,7,6,8,5] :=
  predecessor_excluded a [4,7,6,8,5] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_1215 : Excluded a [4,7,6,8] :=
  branch_excluded a [4,7,6,8] (by decide)
    (fin9_cases _
      node_1216
      node_1217
      (invalid_excluded a [4,7,6,8,2] (by decide +kernel))
      node_1218
      (invalid_excluded a [4,7,6,8,4] (by decide +kernel))
      node_1219
      (invalid_excluded a [4,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,8] (by decide +kernel)))

theorem node_1197 : Excluded a [4,7,6] :=
  branch_excluded a [4,7,6] (by decide)
    (fin9_cases _
      node_1198
      node_1199
      node_1200
      (invalid_excluded a [4,7,6,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,4] (by decide +kernel))
      node_1201
      (invalid_excluded a [4,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,7] (by decide +kernel))
      node_1215)

theorem node_1221 : Excluded a [4,7,8,0] :=
  source_excluded a [4,7,8,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1222 : Excluded a [4,7,8,1] :=
  source_excluded a [4,7,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1223 : Excluded a [4,7,8,2] :=
  source_excluded a [4,7,8,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1224 : Excluded a [4,7,8,5] :=
  predecessor_excluded a [4,7,8,5] 0 5 2 3 (by decide) (by decide +kernel)

theorem node_1226 : Excluded a [4,7,8,6,0] :=
  predecessor_excluded a [4,7,8,6,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1227 : Excluded a [4,7,8,6,1] :=
  source_excluded a [4,7,8,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1228 : Excluded a [4,7,8,6,3] :=
  source_excluded a [4,7,8,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1231 : Excluded a [4,7,8,6,5,0,1] :=
  source_excluded a [4,7,8,6,5,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1232 : Excluded a [4,7,8,6,5,0,2] :=
  predecessor_excluded a [4,7,8,6,5,0,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_1234 : Excluded a [4,7,8,6,5,0,3,1] :=
  predecessor_excluded a [4,7,8,6,5,0,3,1] 2 1 1 7 (by decide) (by decide +kernel)

theorem node_1235 : Excluded a [4,7,8,6,5,0,3,2] :=
  source_excluded a [4,7,8,6,5,0,3,2] 7 0 2 (by decide) (by decide +kernel)

theorem node_1233 : Excluded a [4,7,8,6,5,0,3] :=
  branch_excluded a [4,7,8,6,5,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,8,6,5,0,3,0] (by decide +kernel))
      node_1234
      node_1235
      (invalid_excluded a [4,7,8,6,5,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,5,0,3,4] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,5,0,3,5] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,5,0,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,5,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,5,0,3,8] (by decide +kernel)))

theorem node_1230 : Excluded a [4,7,8,6,5,0] :=
  branch_excluded a [4,7,8,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,8,6,5,0,0] (by decide +kernel))
      node_1231
      node_1232
      node_1233
      (invalid_excluded a [4,7,8,6,5,0,4] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,5,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,5,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,5,0,8] (by decide +kernel)))

theorem node_1236 : Excluded a [4,7,8,6,5,1] :=
  predecessor_excluded a [4,7,8,6,5,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_1237 : Excluded a [4,7,8,6,5,2] :=
  source_excluded a [4,7,8,6,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1238 : Excluded a [4,7,8,6,5,3] :=
  source_excluded a [4,7,8,6,5,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1229 : Excluded a [4,7,8,6,5] :=
  branch_excluded a [4,7,8,6,5] (by decide)
    (fin9_cases _
      node_1230
      node_1236
      node_1237
      node_1238
      (invalid_excluded a [4,7,8,6,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,5,5] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,5,6] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,5,8] (by decide +kernel)))

theorem node_1225 : Excluded a [4,7,8,6] :=
  branch_excluded a [4,7,8,6] (by decide)
    (fin9_cases _
      node_1226
      node_1227
      (invalid_excluded a [4,7,8,6,2] (by decide +kernel))
      node_1228
      (invalid_excluded a [4,7,8,6,4] (by decide +kernel))
      node_1229
      (invalid_excluded a [4,7,8,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,7] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,8] (by decide +kernel)))

theorem node_1220 : Excluded a [4,7,8] :=
  branch_excluded a [4,7,8] (by decide)
    (fin9_cases _
      node_1221
      node_1222
      node_1223
      (invalid_excluded a [4,7,8,3] (by decide +kernel))
      (invalid_excluded a [4,7,8,4] (by decide +kernel))
      node_1224
      node_1225
      (invalid_excluded a [4,7,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,8,8] (by decide +kernel)))

theorem node_1098 : Excluded a [4,7] :=
  branch_excluded a [4,7] (by decide)
    (fin9_cases _
      node_1099
      node_1100
      (invalid_excluded a [4,7,2] (by decide +kernel))
      (invalid_excluded a [4,7,3] (by decide +kernel))
      (invalid_excluded a [4,7,4] (by decide +kernel))
      node_1180
      node_1197
      (invalid_excluded a [4,7,7] (by decide +kernel))
      node_1220)

theorem node_1240 : Excluded a [4,8,0] :=
  predecessor_excluded a [4,8,0] 1 4 2 0 (by decide) (by decide +kernel)

theorem node_1242 : Excluded a [4,8,1,0] :=
  source_excluded a [4,8,1,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1243 : Excluded a [4,8,1,2] :=
  source_excluded a [4,8,1,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1245 : Excluded a [4,8,1,5,0] :=
  predecessor_excluded a [4,8,1,5,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_1246 : Excluded a [4,8,1,5,3] :=
  source_excluded a [4,8,1,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1247 : Excluded a [4,8,1,5,6] :=
  predecessor_excluded a [4,8,1,5,6] 0 6 3 4 (by decide) (by decide +kernel)

theorem node_1250 : Excluded a [4,8,1,5,7,0,2] :=
  source_excluded a [4,8,1,5,7,0,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1252 : Excluded a [4,8,1,5,7,0,3,2] :=
  source_excluded a [4,8,1,5,7,0,3,2] 4 0 7 (by decide) (by decide +kernel)

def b_1254 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 8
  | 2 => 1
  | 3 => 5
  | 4 => 7
  | 5 => 0
  | 6 => 3
  | 7 => 6
  | 8 => 2
  | _ => 0

def cert_1254 : LosingRegion (edgeOf a b_1254) 0 :=
  losingMask a b_1254 0 1212494220902890793862144
    (by decide +kernel) (by decide +kernel)

theorem node_1254 : Excluded a [4,8,1,5,7,0,3,6,2] :=
  losing_excluded a [4,8,1,5,7,0,3,6,2] (by decide) b_1254 (by decide +kernel) 2 0 1 cert_1254 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1254 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1212494220902890793862144 2 1; decide +kernel)

theorem node_1253 : Excluded a [4,8,1,5,7,0,3,6] :=
  branch_excluded a [4,8,1,5,7,0,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,5,7,0,3,6,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,0,3,6,1] (by decide +kernel))
      node_1254
      (invalid_excluded a [4,8,1,5,7,0,3,6,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,0,3,6,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,0,3,6,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,0,3,6,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,0,3,6,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,0,3,6,8] (by decide +kernel)))

theorem node_1251 : Excluded a [4,8,1,5,7,0,3] :=
  branch_excluded a [4,8,1,5,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,5,7,0,3,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,0,3,1] (by decide +kernel))
      node_1252
      (invalid_excluded a [4,8,1,5,7,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,0,3,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,0,3,5] (by decide +kernel))
      node_1253
      (invalid_excluded a [4,8,1,5,7,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,0,3,8] (by decide +kernel)))

theorem node_1249 : Excluded a [4,8,1,5,7,0] :=
  branch_excluded a [4,8,1,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,5,7,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,0,1] (by decide +kernel))
      node_1250
      node_1251
      (invalid_excluded a [4,8,1,5,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,0,8] (by decide +kernel)))

theorem node_1255 : Excluded a [4,8,1,5,7,2] :=
  predecessor_excluded a [4,8,1,5,7,2] 0 2 3 5 (by decide) (by decide +kernel)

theorem node_1258 : Excluded a [4,8,1,5,7,3,0,2] :=
  source_excluded a [4,8,1,5,7,3,0,2] 4 0 7 (by decide) (by decide +kernel)

theorem node_1260 : Excluded a [4,8,1,5,7,3,0,6,2] :=
  predecessor_excluded a [4,8,1,5,7,3,0,6,2] 0 3 8 5 (by decide) (by decide +kernel)

theorem node_1259 : Excluded a [4,8,1,5,7,3,0,6] :=
  branch_excluded a [4,8,1,5,7,3,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,5,7,3,0,6,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,3,0,6,1] (by decide +kernel))
      node_1260
      (invalid_excluded a [4,8,1,5,7,3,0,6,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,3,0,6,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,3,0,6,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,3,0,6,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,3,0,6,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,3,0,6,8] (by decide +kernel)))

theorem node_1257 : Excluded a [4,8,1,5,7,3,0] :=
  branch_excluded a [4,8,1,5,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,5,7,3,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,3,0,1] (by decide +kernel))
      node_1258
      (invalid_excluded a [4,8,1,5,7,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,3,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,3,0,5] (by decide +kernel))
      node_1259
      (invalid_excluded a [4,8,1,5,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,3,0,8] (by decide +kernel)))

theorem node_1261 : Excluded a [4,8,1,5,7,3,2] :=
  source_excluded a [4,8,1,5,7,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1256 : Excluded a [4,8,1,5,7,3] :=
  branch_excluded a [4,8,1,5,7,3] (by decide)
    (fin9_cases _
      node_1257
      (invalid_excluded a [4,8,1,5,7,3,1] (by decide +kernel))
      node_1261
      (invalid_excluded a [4,8,1,5,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,3,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,3,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,3,8] (by decide +kernel)))

theorem node_1248 : Excluded a [4,8,1,5,7] :=
  branch_excluded a [4,8,1,5,7] (by decide)
    (fin9_cases _
      node_1249
      (invalid_excluded a [4,8,1,5,7,1] (by decide +kernel))
      node_1255
      node_1256
      (invalid_excluded a [4,8,1,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,7,8] (by decide +kernel)))

theorem node_1244 : Excluded a [4,8,1,5] :=
  branch_excluded a [4,8,1,5] (by decide)
    (fin9_cases _
      node_1245
      (invalid_excluded a [4,8,1,5,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,2] (by decide +kernel))
      node_1246
      (invalid_excluded a [4,8,1,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,5,5] (by decide +kernel))
      node_1247
      node_1248
      (invalid_excluded a [4,8,1,5,8] (by decide +kernel)))

theorem node_1263 : Excluded a [4,8,1,6,0] :=
  predecessor_excluded a [4,8,1,6,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_1264 : Excluded a [4,8,1,6,3] :=
  source_excluded a [4,8,1,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1267 : Excluded a [4,8,1,6,5,0,2] :=
  predecessor_excluded a [4,8,1,6,5,0,2] 0 2 3 6 (by decide) (by decide +kernel)

def b_1270 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 8
  | 2 => 1
  | 3 => 6
  | 4 => 5
  | 5 => 0
  | 6 => 3
  | 7 => 2
  | 8 => 7
  | _ => 0

def cert_1270 : LosingRegion (edgeOf a b_1270) 0 :=
  losingMask a b_1270 0 1437259600873847948837888
    (by decide +kernel) (by decide +kernel)

theorem node_1270 : Excluded a [4,8,1,6,5,0,3,2,7] :=
  losing_excluded a [4,8,1,6,5,0,3,2,7] (by decide) b_1270 (by decide +kernel) 2 0 0 cert_1270 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1270 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1437259600873847948837888 2 0; decide +kernel)

theorem node_1269 : Excluded a [4,8,1,6,5,0,3,2] :=
  branch_excluded a [4,8,1,6,5,0,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,6,5,0,3,2,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,3,2,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,3,2,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,3,2,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,3,2,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,3,2,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,3,2,6] (by decide +kernel))
      node_1270
      (invalid_excluded a [4,8,1,6,5,0,3,2,8] (by decide +kernel)))

theorem node_1268 : Excluded a [4,8,1,6,5,0,3] :=
  branch_excluded a [4,8,1,6,5,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,6,5,0,3,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,3,1] (by decide +kernel))
      node_1269
      (invalid_excluded a [4,8,1,6,5,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,3,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,3,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,3,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,3,8] (by decide +kernel)))

theorem node_1266 : Excluded a [4,8,1,6,5,0] :=
  branch_excluded a [4,8,1,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,6,5,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,1] (by decide +kernel))
      node_1267
      node_1268
      (invalid_excluded a [4,8,1,6,5,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,0,8] (by decide +kernel)))

theorem node_1271 : Excluded a [4,8,1,6,5,2] :=
  source_excluded a [4,8,1,6,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1272 : Excluded a [4,8,1,6,5,3] :=
  source_excluded a [4,8,1,6,5,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1273 : Excluded a [4,8,1,6,5,7] :=
  source_excluded a [4,8,1,6,5,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1265 : Excluded a [4,8,1,6,5] :=
  branch_excluded a [4,8,1,6,5] (by decide)
    (fin9_cases _
      node_1266
      (invalid_excluded a [4,8,1,6,5,1] (by decide +kernel))
      node_1271
      node_1272
      (invalid_excluded a [4,8,1,6,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5,6] (by decide +kernel))
      node_1273
      (invalid_excluded a [4,8,1,6,5,8] (by decide +kernel)))

theorem node_1274 : Excluded a [4,8,1,6,7] :=
  predecessor_excluded a [4,8,1,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_1262 : Excluded a [4,8,1,6] :=
  branch_excluded a [4,8,1,6] (by decide)
    (fin9_cases _
      node_1263
      (invalid_excluded a [4,8,1,6,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2] (by decide +kernel))
      node_1264
      (invalid_excluded a [4,8,1,6,4] (by decide +kernel))
      node_1265
      (invalid_excluded a [4,8,1,6,6] (by decide +kernel))
      node_1274
      (invalid_excluded a [4,8,1,6,8] (by decide +kernel)))

theorem node_1276 : Excluded a [4,8,1,7,0] :=
  predecessor_excluded a [4,8,1,7,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_1277 : Excluded a [4,8,1,7,3] :=
  source_excluded a [4,8,1,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1281 : Excluded a [4,8,1,7,5,0,2,3] :=
  predecessor_excluded a [4,8,1,7,5,0,2,3] 0 3 6 7 (by decide) (by decide +kernel)

def b_1283 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 8
  | 2 => 1
  | 3 => 7
  | 4 => 5
  | 5 => 0
  | 6 => 2
  | 7 => 6
  | 8 => 3
  | _ => 0

def cert_1283 : LosingRegion (edgeOf a b_1283) 0 :=
  losingMask a b_1283 0 1439687509447361892713472
    (by decide +kernel) (by decide +kernel)

theorem node_1283 : Excluded a [4,8,1,7,5,0,2,6,3] :=
  losing_excluded a [4,8,1,7,5,0,2,6,3] (by decide) b_1283 (by decide +kernel) 2 0 0 cert_1283 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1283 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1439687509447361892713472 2 0; decide +kernel)

theorem node_1282 : Excluded a [4,8,1,7,5,0,2,6] :=
  branch_excluded a [4,8,1,7,5,0,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,5,0,2,6,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,0,2,6,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,0,2,6,2] (by decide +kernel))
      node_1283
      (invalid_excluded a [4,8,1,7,5,0,2,6,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,0,2,6,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,0,2,6,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,0,2,6,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,0,2,6,8] (by decide +kernel)))

theorem node_1280 : Excluded a [4,8,1,7,5,0,2] :=
  branch_excluded a [4,8,1,7,5,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,5,0,2,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,0,2,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,0,2,2] (by decide +kernel))
      node_1281
      (invalid_excluded a [4,8,1,7,5,0,2,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,0,2,5] (by decide +kernel))
      node_1282
      (invalid_excluded a [4,8,1,7,5,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,0,2,8] (by decide +kernel)))

theorem node_1284 : Excluded a [4,8,1,7,5,0,3] :=
  source_excluded a [4,8,1,7,5,0,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1279 : Excluded a [4,8,1,7,5,0] :=
  branch_excluded a [4,8,1,7,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,5,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,0,1] (by decide +kernel))
      node_1280
      node_1284
      (invalid_excluded a [4,8,1,7,5,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,0,8] (by decide +kernel)))

theorem node_1285 : Excluded a [4,8,1,7,5,2] :=
  source_excluded a [4,8,1,7,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1286 : Excluded a [4,8,1,7,5,3] :=
  predecessor_excluded a [4,8,1,7,5,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1278 : Excluded a [4,8,1,7,5] :=
  branch_excluded a [4,8,1,7,5] (by decide)
    (fin9_cases _
      node_1279
      (invalid_excluded a [4,8,1,7,5,1] (by decide +kernel))
      node_1285
      node_1286
      (invalid_excluded a [4,8,1,7,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5,8] (by decide +kernel)))

theorem node_1289 : Excluded a [4,8,1,7,6,0,2] :=
  source_excluded a [4,8,1,7,6,0,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1290 : Excluded a [4,8,1,7,6,0,3] :=
  source_excluded a [4,8,1,7,6,0,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1292 : Excluded a [4,8,1,7,6,0,5,2] :=
  predecessor_excluded a [4,8,1,7,6,0,5,2] 0 2 3 7 (by decide) (by decide +kernel)

def b_1294 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 8
  | 2 => 1
  | 3 => 7
  | 4 => 6
  | 5 => 0
  | 6 => 5
  | 7 => 3
  | 8 => 2
  | _ => 0

def cert_1294 : LosingRegion (edgeOf a b_1294) 0 :=
  losingMask a b_1294 0 1364493554603493814961152
    (by decide +kernel) (by decide +kernel)

theorem node_1294 : Excluded a [4,8,1,7,6,0,5,3,2] :=
  losing_excluded a [4,8,1,7,6,0,5,3,2] (by decide) b_1294 (by decide +kernel) 2 0 0 cert_1294 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1294 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1364493554603493814961152 2 0; decide +kernel)

theorem node_1293 : Excluded a [4,8,1,7,6,0,5,3] :=
  branch_excluded a [4,8,1,7,6,0,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,6,0,5,3,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,0,5,3,1] (by decide +kernel))
      node_1294
      (invalid_excluded a [4,8,1,7,6,0,5,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,0,5,3,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,0,5,3,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,0,5,3,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,0,5,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,0,5,3,8] (by decide +kernel)))

theorem node_1291 : Excluded a [4,8,1,7,6,0,5] :=
  branch_excluded a [4,8,1,7,6,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,6,0,5,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,0,5,1] (by decide +kernel))
      node_1292
      node_1293
      (invalid_excluded a [4,8,1,7,6,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,0,5,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,0,5,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,0,5,8] (by decide +kernel)))

theorem node_1288 : Excluded a [4,8,1,7,6,0] :=
  branch_excluded a [4,8,1,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,6,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,0,1] (by decide +kernel))
      node_1289
      node_1290
      (invalid_excluded a [4,8,1,7,6,0,4] (by decide +kernel))
      node_1291
      (invalid_excluded a [4,8,1,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,0,8] (by decide +kernel)))

theorem node_1295 : Excluded a [4,8,1,7,6,2] :=
  source_excluded a [4,8,1,7,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1296 : Excluded a [4,8,1,7,6,3] :=
  predecessor_excluded a [4,8,1,7,6,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1287 : Excluded a [4,8,1,7,6] :=
  branch_excluded a [4,8,1,7,6] (by decide)
    (fin9_cases _
      node_1288
      (invalid_excluded a [4,8,1,7,6,1] (by decide +kernel))
      node_1295
      node_1296
      (invalid_excluded a [4,8,1,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,6,8] (by decide +kernel)))

theorem node_1275 : Excluded a [4,8,1,7] :=
  branch_excluded a [4,8,1,7] (by decide)
    (fin9_cases _
      node_1276
      (invalid_excluded a [4,8,1,7,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2] (by decide +kernel))
      node_1277
      (invalid_excluded a [4,8,1,7,4] (by decide +kernel))
      node_1278
      node_1287
      (invalid_excluded a [4,8,1,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,8] (by decide +kernel)))

theorem node_1241 : Excluded a [4,8,1] :=
  branch_excluded a [4,8,1] (by decide)
    (fin9_cases _
      node_1242
      (invalid_excluded a [4,8,1,1] (by decide +kernel))
      node_1243
      (invalid_excluded a [4,8,1,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,4] (by decide +kernel))
      node_1244
      node_1262
      node_1275
      (invalid_excluded a [4,8,1,8] (by decide +kernel)))

theorem node_1298 : Excluded a [4,8,5,0] :=
  source_excluded a [4,8,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1299 : Excluded a [4,8,5,1] :=
  source_excluded a [4,8,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1300 : Excluded a [4,8,5,2] :=
  source_excluded a [4,8,5,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1301 : Excluded a [4,8,5,6] :=
  predecessor_excluded a [4,8,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_1303 : Excluded a [4,8,5,7,0] :=
  predecessor_excluded a [4,8,5,7,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1304 : Excluded a [4,8,5,7,1] :=
  source_excluded a [4,8,5,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1305 : Excluded a [4,8,5,7,3] :=
  source_excluded a [4,8,5,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1308 : Excluded a [4,8,5,7,6,0,1] :=
  predecessor_excluded a [4,8,5,7,6,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_1309 : Excluded a [4,8,5,7,6,0,2] :=
  source_excluded a [4,8,5,7,6,0,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1310 : Excluded a [4,8,5,7,6,0,3] :=
  source_excluded a [4,8,5,7,6,0,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1307 : Excluded a [4,8,5,7,6,0] :=
  branch_excluded a [4,8,5,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,5,7,6,0,0] (by decide +kernel))
      node_1308
      node_1309
      node_1310
      (invalid_excluded a [4,8,5,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,0,8] (by decide +kernel)))

theorem node_1312 : Excluded a [4,8,5,7,6,1,0] :=
  predecessor_excluded a [4,8,5,7,6,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_1313 : Excluded a [4,8,5,7,6,1,2] :=
  source_excluded a [4,8,5,7,6,1,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1314 : Excluded a [4,8,5,7,6,1,3] :=
  source_excluded a [4,8,5,7,6,1,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1311 : Excluded a [4,8,5,7,6,1] :=
  branch_excluded a [4,8,5,7,6,1] (by decide)
    (fin9_cases _
      node_1312
      (invalid_excluded a [4,8,5,7,6,1,1] (by decide +kernel))
      node_1313
      node_1314
      (invalid_excluded a [4,8,5,7,6,1,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,1,8] (by decide +kernel)))

theorem node_1315 : Excluded a [4,8,5,7,6,2] :=
  source_excluded a [4,8,5,7,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1316 : Excluded a [4,8,5,7,6,3] :=
  source_excluded a [4,8,5,7,6,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1306 : Excluded a [4,8,5,7,6] :=
  branch_excluded a [4,8,5,7,6] (by decide)
    (fin9_cases _
      node_1307
      node_1311
      node_1315
      node_1316
      (invalid_excluded a [4,8,5,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,7] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,6,8] (by decide +kernel)))

theorem node_1302 : Excluded a [4,8,5,7] :=
  branch_excluded a [4,8,5,7] (by decide)
    (fin9_cases _
      node_1303
      node_1304
      (invalid_excluded a [4,8,5,7,2] (by decide +kernel))
      node_1305
      (invalid_excluded a [4,8,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,5] (by decide +kernel))
      node_1306
      (invalid_excluded a [4,8,5,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,8] (by decide +kernel)))

theorem node_1297 : Excluded a [4,8,5] :=
  branch_excluded a [4,8,5] (by decide)
    (fin9_cases _
      node_1298
      node_1299
      node_1300
      (invalid_excluded a [4,8,5,3] (by decide +kernel))
      (invalid_excluded a [4,8,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,5] (by decide +kernel))
      node_1301
      node_1302
      (invalid_excluded a [4,8,5,8] (by decide +kernel)))

theorem node_1318 : Excluded a [4,8,6,0] :=
  source_excluded a [4,8,6,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1319 : Excluded a [4,8,6,1] :=
  source_excluded a [4,8,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1320 : Excluded a [4,8,6,2] :=
  source_excluded a [4,8,6,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1322 : Excluded a [4,8,6,5,0] :=
  predecessor_excluded a [4,8,6,5,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1323 : Excluded a [4,8,6,5,1] :=
  source_excluded a [4,8,6,5,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1324 : Excluded a [4,8,6,5,3] :=
  source_excluded a [4,8,6,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1327 : Excluded a [4,8,6,5,7,0,1] :=
  predecessor_excluded a [4,8,6,5,7,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_1328 : Excluded a [4,8,6,5,7,0,2] :=
  source_excluded a [4,8,6,5,7,0,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1329 : Excluded a [4,8,6,5,7,0,3] :=
  source_excluded a [4,8,6,5,7,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1326 : Excluded a [4,8,6,5,7,0] :=
  branch_excluded a [4,8,6,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,6,5,7,0,0] (by decide +kernel))
      node_1327
      node_1328
      node_1329
      (invalid_excluded a [4,8,6,5,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,5,7,0,8] (by decide +kernel)))

theorem node_1331 : Excluded a [4,8,6,5,7,1,0] :=
  predecessor_excluded a [4,8,6,5,7,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_1332 : Excluded a [4,8,6,5,7,1,2] :=
  source_excluded a [4,8,6,5,7,1,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1333 : Excluded a [4,8,6,5,7,1,3] :=
  source_excluded a [4,8,6,5,7,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1330 : Excluded a [4,8,6,5,7,1] :=
  branch_excluded a [4,8,6,5,7,1] (by decide)
    (fin9_cases _
      node_1331
      (invalid_excluded a [4,8,6,5,7,1,1] (by decide +kernel))
      node_1332
      node_1333
      (invalid_excluded a [4,8,6,5,7,1,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,5,7,1,8] (by decide +kernel)))

theorem node_1334 : Excluded a [4,8,6,5,7,2] :=
  source_excluded a [4,8,6,5,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1335 : Excluded a [4,8,6,5,7,3] :=
  source_excluded a [4,8,6,5,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1325 : Excluded a [4,8,6,5,7] :=
  branch_excluded a [4,8,6,5,7] (by decide)
    (fin9_cases _
      node_1326
      node_1330
      node_1334
      node_1335
      (invalid_excluded a [4,8,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,5,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,5,7,8] (by decide +kernel)))

theorem node_1321 : Excluded a [4,8,6,5] :=
  branch_excluded a [4,8,6,5] (by decide)
    (fin9_cases _
      node_1322
      node_1323
      (invalid_excluded a [4,8,6,5,2] (by decide +kernel))
      node_1324
      (invalid_excluded a [4,8,6,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,5,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,5,6] (by decide +kernel))
      node_1325
      (invalid_excluded a [4,8,6,5,8] (by decide +kernel)))

theorem node_1336 : Excluded a [4,8,6,7] :=
  predecessor_excluded a [4,8,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_1317 : Excluded a [4,8,6] :=
  branch_excluded a [4,8,6] (by decide)
    (fin9_cases _
      node_1318
      node_1319
      node_1320
      (invalid_excluded a [4,8,6,3] (by decide +kernel))
      (invalid_excluded a [4,8,6,4] (by decide +kernel))
      node_1321
      (invalid_excluded a [4,8,6,6] (by decide +kernel))
      node_1336
      (invalid_excluded a [4,8,6,8] (by decide +kernel)))

theorem node_1338 : Excluded a [4,8,7,0] :=
  source_excluded a [4,8,7,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1339 : Excluded a [4,8,7,1] :=
  source_excluded a [4,8,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1340 : Excluded a [4,8,7,2] :=
  source_excluded a [4,8,7,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1342 : Excluded a [4,8,7,5,0] :=
  predecessor_excluded a [4,8,7,5,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1343 : Excluded a [4,8,7,5,1] :=
  source_excluded a [4,8,7,5,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1344 : Excluded a [4,8,7,5,3] :=
  source_excluded a [4,8,7,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1345 : Excluded a [4,8,7,5,6] :=
  predecessor_excluded a [4,8,7,5,6] 0 7 4 2 (by decide) (by decide +kernel)

theorem node_1341 : Excluded a [4,8,7,5] :=
  branch_excluded a [4,8,7,5] (by decide)
    (fin9_cases _
      node_1342
      node_1343
      (invalid_excluded a [4,8,7,5,2] (by decide +kernel))
      node_1344
      (invalid_excluded a [4,8,7,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,5,5] (by decide +kernel))
      node_1345
      (invalid_excluded a [4,8,7,5,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,5,8] (by decide +kernel)))

theorem node_1347 : Excluded a [4,8,7,6,0] :=
  predecessor_excluded a [4,8,7,6,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1348 : Excluded a [4,8,7,6,1] :=
  source_excluded a [4,8,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1349 : Excluded a [4,8,7,6,3] :=
  source_excluded a [4,8,7,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1352 : Excluded a [4,8,7,6,5,0,1] :=
  predecessor_excluded a [4,8,7,6,5,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_1353 : Excluded a [4,8,7,6,5,0,2] :=
  source_excluded a [4,8,7,6,5,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1354 : Excluded a [4,8,7,6,5,0,3] :=
  source_excluded a [4,8,7,6,5,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1351 : Excluded a [4,8,7,6,5,0] :=
  branch_excluded a [4,8,7,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,7,6,5,0,0] (by decide +kernel))
      node_1352
      node_1353
      node_1354
      (invalid_excluded a [4,8,7,6,5,0,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,5,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,5,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,5,0,8] (by decide +kernel)))

theorem node_1356 : Excluded a [4,8,7,6,5,1,0] :=
  predecessor_excluded a [4,8,7,6,5,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_1357 : Excluded a [4,8,7,6,5,1,2] :=
  source_excluded a [4,8,7,6,5,1,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1358 : Excluded a [4,8,7,6,5,1,3] :=
  source_excluded a [4,8,7,6,5,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1355 : Excluded a [4,8,7,6,5,1] :=
  branch_excluded a [4,8,7,6,5,1] (by decide)
    (fin9_cases _
      node_1356
      (invalid_excluded a [4,8,7,6,5,1,1] (by decide +kernel))
      node_1357
      node_1358
      (invalid_excluded a [4,8,7,6,5,1,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,5,1,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,5,1,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,5,1,8] (by decide +kernel)))

theorem node_1359 : Excluded a [4,8,7,6,5,2] :=
  source_excluded a [4,8,7,6,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1360 : Excluded a [4,8,7,6,5,3] :=
  source_excluded a [4,8,7,6,5,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1350 : Excluded a [4,8,7,6,5] :=
  branch_excluded a [4,8,7,6,5] (by decide)
    (fin9_cases _
      node_1351
      node_1355
      node_1359
      node_1360
      (invalid_excluded a [4,8,7,6,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,5,5] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,5,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,5,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,5,8] (by decide +kernel)))

theorem node_1346 : Excluded a [4,8,7,6] :=
  branch_excluded a [4,8,7,6] (by decide)
    (fin9_cases _
      node_1347
      node_1348
      (invalid_excluded a [4,8,7,6,2] (by decide +kernel))
      node_1349
      (invalid_excluded a [4,8,7,6,4] (by decide +kernel))
      node_1350
      (invalid_excluded a [4,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,8] (by decide +kernel)))

theorem node_1337 : Excluded a [4,8,7] :=
  branch_excluded a [4,8,7] (by decide)
    (fin9_cases _
      node_1338
      node_1339
      node_1340
      (invalid_excluded a [4,8,7,3] (by decide +kernel))
      (invalid_excluded a [4,8,7,4] (by decide +kernel))
      node_1341
      node_1346
      (invalid_excluded a [4,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,8] (by decide +kernel)))

theorem node_1239 : Excluded a [4,8] :=
  branch_excluded a [4,8] (by decide)
    (fin9_cases _
      node_1240
      node_1241
      (invalid_excluded a [4,8,2] (by decide +kernel))
      (invalid_excluded a [4,8,3] (by decide +kernel))
      (invalid_excluded a [4,8,4] (by decide +kernel))
      node_1297
      node_1317
      node_1337
      (invalid_excluded a [4,8,8] (by decide +kernel)))

theorem node_872 : Excluded a [4] :=
  branch_excluded a [4] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0] (by decide +kernel))
      (invalid_excluded a [4,1] (by decide +kernel))
      node_873
      node_874
      (invalid_excluded a [4,4] (by decide +kernel))
      node_875
      node_980
      node_1098
      node_1239)

theorem node_1363 : Excluded a [5,2,0] :=
  source_excluded a [5,2,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_1364 : Excluded a [5,2,1] :=
  predecessor_excluded a [5,2,1] 3 1 1 2 (by decide) (by decide +kernel)

theorem node_1365 : Excluded a [5,2,4] :=
  source_excluded a [5,2,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_1368 : Excluded a [5,2,6,0,1] :=
  source_excluded a [5,2,6,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1369 : Excluded a [5,2,6,0,3] :=
  source_excluded a [5,2,6,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1371 : Excluded a [5,2,6,0,7,1] :=
  source_excluded a [5,2,6,0,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1372 : Excluded a [5,2,6,0,7,3] :=
  source_excluded a [5,2,6,0,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1373 : Excluded a [5,2,6,0,7,4] :=
  predecessor_excluded a [5,2,6,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1376 : Excluded a [5,2,6,0,7,8,1,3] :=
  predecessor_excluded a [5,2,6,0,7,8,1,3] 0 3 4 7 (by decide) (by decide +kernel)

def b_1378 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 2
  | 2 => 6
  | 3 => 0
  | 4 => 7
  | 5 => 8
  | 6 => 1
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_1378 : LosingRegion (edgeOf a b_1378) 0 :=
  losingMask a b_1378 0 1269709049940338245895168
    (by decide +kernel) (by decide +kernel)

theorem node_1378 : Excluded a [5,2,6,0,7,8,1,4,3] :=
  losing_excluded a [5,2,6,0,7,8,1,4,3] (by decide) b_1378 (by decide +kernel) 2 0 3 cert_1378 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1378 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1269709049940338245895168 2 3; decide +kernel)

theorem node_1377 : Excluded a [5,2,6,0,7,8,1,4] :=
  branch_excluded a [5,2,6,0,7,8,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,6,0,7,8,1,4,0] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,7,8,1,4,1] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,7,8,1,4,2] (by decide +kernel))
      node_1378
      (invalid_excluded a [5,2,6,0,7,8,1,4,4] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,7,8,1,4,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,7,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,7,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,7,8,1,4,8] (by decide +kernel)))

theorem node_1375 : Excluded a [5,2,6,0,7,8,1] :=
  branch_excluded a [5,2,6,0,7,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,6,0,7,8,1,0] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,7,8,1,1] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,7,8,1,2] (by decide +kernel))
      node_1376
      node_1377
      (invalid_excluded a [5,2,6,0,7,8,1,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,7,8,1,6] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,7,8,1,7] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,7,8,1,8] (by decide +kernel)))

theorem node_1379 : Excluded a [5,2,6,0,7,8,3] :=
  source_excluded a [5,2,6,0,7,8,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1380 : Excluded a [5,2,6,0,7,8,4] :=
  source_excluded a [5,2,6,0,7,8,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1374 : Excluded a [5,2,6,0,7,8] :=
  branch_excluded a [5,2,6,0,7,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,6,0,7,8,0] (by decide +kernel))
      node_1375
      (invalid_excluded a [5,2,6,0,7,8,2] (by decide +kernel))
      node_1379
      node_1380
      (invalid_excluded a [5,2,6,0,7,8,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,7,8,6] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,7,8,7] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,7,8,8] (by decide +kernel)))

theorem node_1370 : Excluded a [5,2,6,0,7] :=
  branch_excluded a [5,2,6,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,6,0,7,0] (by decide +kernel))
      node_1371
      (invalid_excluded a [5,2,6,0,7,2] (by decide +kernel))
      node_1372
      node_1373
      (invalid_excluded a [5,2,6,0,7,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,7,6] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,7,7] (by decide +kernel))
      node_1374)

theorem node_1382 : Excluded a [5,2,6,0,8,1] :=
  source_excluded a [5,2,6,0,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1383 : Excluded a [5,2,6,0,8,3] :=
  source_excluded a [5,2,6,0,8,3] 2 0 5 (by decide) (by decide +kernel)

def b_1387 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 2
  | 2 => 6
  | 3 => 0
  | 4 => 8
  | 5 => 4
  | 6 => 1
  | 7 => 3
  | 8 => 7
  | _ => 0

def cert_1387 : LosingRegion (edgeOf a b_1387) 0 :=
  losingMask a b_1387 0 1654120733665340347646976
    (by decide +kernel) (by decide +kernel)

theorem node_1387 : Excluded a [5,2,6,0,8,4,1,3,7] :=
  losing_excluded a [5,2,6,0,8,4,1,3,7] (by decide) b_1387 (by decide +kernel) 4 0 1 cert_1387 (by change 4 ≠ 0 ∧ ¬ edgeOf a b_1387 4 0 ∧ 1 ≠ 4 ∧ maskRegion 1654120733665340347646976 4 1; decide +kernel)

theorem node_1386 : Excluded a [5,2,6,0,8,4,1,3] :=
  branch_excluded a [5,2,6,0,8,4,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,6,0,8,4,1,3,0] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,4,1,3,1] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,4,1,3,2] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,4,1,3,3] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,4,1,3,4] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,4,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,4,1,3,6] (by decide +kernel))
      node_1387
      (invalid_excluded a [5,2,6,0,8,4,1,3,8] (by decide +kernel)))

theorem node_1385 : Excluded a [5,2,6,0,8,4,1] :=
  branch_excluded a [5,2,6,0,8,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,6,0,8,4,1,0] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,4,1,2] (by decide +kernel))
      node_1386
      (invalid_excluded a [5,2,6,0,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,4,1,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,4,1,6] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,4,1,8] (by decide +kernel)))

theorem node_1388 : Excluded a [5,2,6,0,8,4,3] :=
  source_excluded a [5,2,6,0,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1384 : Excluded a [5,2,6,0,8,4] :=
  branch_excluded a [5,2,6,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,6,0,8,4,0] (by decide +kernel))
      node_1385
      (invalid_excluded a [5,2,6,0,8,4,2] (by decide +kernel))
      node_1388
      (invalid_excluded a [5,2,6,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,4,8] (by decide +kernel)))

theorem node_1389 : Excluded a [5,2,6,0,8,7] :=
  source_excluded a [5,2,6,0,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1381 : Excluded a [5,2,6,0,8] :=
  branch_excluded a [5,2,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,6,0,8,0] (by decide +kernel))
      node_1382
      (invalid_excluded a [5,2,6,0,8,2] (by decide +kernel))
      node_1383
      node_1384
      (invalid_excluded a [5,2,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,8,6] (by decide +kernel))
      node_1389
      (invalid_excluded a [5,2,6,0,8,8] (by decide +kernel)))

theorem node_1367 : Excluded a [5,2,6,0] :=
  branch_excluded a [5,2,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,6,0,0] (by decide +kernel))
      node_1368
      (invalid_excluded a [5,2,6,0,2] (by decide +kernel))
      node_1369
      (invalid_excluded a [5,2,6,0,4] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,0,6] (by decide +kernel))
      node_1370
      node_1381)

theorem node_1390 : Excluded a [5,2,6,1] :=
  predecessor_excluded a [5,2,6,1] 0 2 3 1 (by decide) (by decide +kernel)

theorem node_1391 : Excluded a [5,2,6,7] :=
  predecessor_excluded a [5,2,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_1393 : Excluded a [5,2,6,8,0] :=
  source_excluded a [5,2,6,8,0] 1 3 4 (by decide) (by decide +kernel)

theorem node_1394 : Excluded a [5,2,6,8,1] :=
  source_excluded a [5,2,6,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1395 : Excluded a [5,2,6,8,3] :=
  source_excluded a [5,2,6,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1397 : Excluded a [5,2,6,8,7,0] :=
  predecessor_excluded a [5,2,6,8,7,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1398 : Excluded a [5,2,6,8,7,1] :=
  source_excluded a [5,2,6,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1399 : Excluded a [5,2,6,8,7,3] :=
  source_excluded a [5,2,6,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1400 : Excluded a [5,2,6,8,7,4] :=
  predecessor_excluded a [5,2,6,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1396 : Excluded a [5,2,6,8,7] :=
  branch_excluded a [5,2,6,8,7] (by decide)
    (fin9_cases _
      node_1397
      node_1398
      (invalid_excluded a [5,2,6,8,7,2] (by decide +kernel))
      node_1399
      node_1400
      (invalid_excluded a [5,2,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,2,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,2,6,8,7,8] (by decide +kernel)))

theorem node_1392 : Excluded a [5,2,6,8] :=
  branch_excluded a [5,2,6,8] (by decide)
    (fin9_cases _
      node_1393
      node_1394
      (invalid_excluded a [5,2,6,8,2] (by decide +kernel))
      node_1395
      (invalid_excluded a [5,2,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,2,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,8,6] (by decide +kernel))
      node_1396
      (invalid_excluded a [5,2,6,8,8] (by decide +kernel)))

theorem node_1366 : Excluded a [5,2,6] :=
  branch_excluded a [5,2,6] (by decide)
    (fin9_cases _
      node_1367
      node_1390
      (invalid_excluded a [5,2,6,2] (by decide +kernel))
      (invalid_excluded a [5,2,6,3] (by decide +kernel))
      (invalid_excluded a [5,2,6,4] (by decide +kernel))
      (invalid_excluded a [5,2,6,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,6] (by decide +kernel))
      node_1391
      node_1392)

theorem node_1403 : Excluded a [5,2,7,0,1] :=
  source_excluded a [5,2,7,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1404 : Excluded a [5,2,7,0,3] :=
  source_excluded a [5,2,7,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1405 : Excluded a [5,2,7,0,6] :=
  predecessor_excluded a [5,2,7,0,6] 0 7 4 2 (by decide) (by decide +kernel)

theorem node_1407 : Excluded a [5,2,7,0,8,1] :=
  source_excluded a [5,2,7,0,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1410 : Excluded a [5,2,7,0,8,3,1,4] :=
  source_excluded a [5,2,7,0,8,3,1,4] 7 0 4 (by decide) (by decide +kernel)

def b_1412 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 2
  | 2 => 7
  | 3 => 0
  | 4 => 8
  | 5 => 3
  | 6 => 1
  | 7 => 6
  | 8 => 4
  | _ => 0

def cert_1412 : LosingRegion (edgeOf a b_1412) 0 :=
  losingMask a b_1412 0 1423010716356062993187840
    (by decide +kernel) (by decide +kernel)

theorem node_1412 : Excluded a [5,2,7,0,8,3,1,6,4] :=
  losing_excluded a [5,2,7,0,8,3,1,6,4] (by decide) b_1412 (by decide +kernel) 2 0 3 cert_1412 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1412 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1423010716356062993187840 2 3; decide +kernel)

theorem node_1411 : Excluded a [5,2,7,0,8,3,1,6] :=
  branch_excluded a [5,2,7,0,8,3,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,7,0,8,3,1,6,0] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,3,1,6,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,3,1,6,2] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,3,1,6,3] (by decide +kernel))
      node_1412
      (invalid_excluded a [5,2,7,0,8,3,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,3,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,3,1,6,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,3,1,6,8] (by decide +kernel)))

theorem node_1409 : Excluded a [5,2,7,0,8,3,1] :=
  branch_excluded a [5,2,7,0,8,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,7,0,8,3,1,0] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,3,1,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,3,1,2] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,3,1,3] (by decide +kernel))
      node_1410
      (invalid_excluded a [5,2,7,0,8,3,1,5] (by decide +kernel))
      node_1411
      (invalid_excluded a [5,2,7,0,8,3,1,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,3,1,8] (by decide +kernel)))

theorem node_1413 : Excluded a [5,2,7,0,8,3,4] :=
  predecessor_excluded a [5,2,7,0,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_1408 : Excluded a [5,2,7,0,8,3] :=
  branch_excluded a [5,2,7,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,7,0,8,3,0] (by decide +kernel))
      node_1409
      (invalid_excluded a [5,2,7,0,8,3,2] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,3,3] (by decide +kernel))
      node_1413
      (invalid_excluded a [5,2,7,0,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,3,8] (by decide +kernel)))

theorem node_1416 : Excluded a [5,2,7,0,8,4,1,3] :=
  source_excluded a [5,2,7,0,8,4,1,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_1418 : Excluded a [5,2,7,0,8,4,1,6,3] :=
  predecessor_excluded a [5,2,7,0,8,4,1,6,3] 0 4 8 5 (by decide) (by decide +kernel)

theorem node_1417 : Excluded a [5,2,7,0,8,4,1,6] :=
  branch_excluded a [5,2,7,0,8,4,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,7,0,8,4,1,6,0] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,4,1,6,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,4,1,6,2] (by decide +kernel))
      node_1418
      (invalid_excluded a [5,2,7,0,8,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,4,1,6,8] (by decide +kernel)))

theorem node_1415 : Excluded a [5,2,7,0,8,4,1] :=
  branch_excluded a [5,2,7,0,8,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,7,0,8,4,1,0] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,4,1,2] (by decide +kernel))
      node_1416
      (invalid_excluded a [5,2,7,0,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,4,1,5] (by decide +kernel))
      node_1417
      (invalid_excluded a [5,2,7,0,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,4,1,8] (by decide +kernel)))

theorem node_1419 : Excluded a [5,2,7,0,8,4,3] :=
  source_excluded a [5,2,7,0,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1414 : Excluded a [5,2,7,0,8,4] :=
  branch_excluded a [5,2,7,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,7,0,8,4,0] (by decide +kernel))
      node_1415
      (invalid_excluded a [5,2,7,0,8,4,2] (by decide +kernel))
      node_1419
      (invalid_excluded a [5,2,7,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,4,8] (by decide +kernel)))

theorem node_1406 : Excluded a [5,2,7,0,8] :=
  branch_excluded a [5,2,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,7,0,8,0] (by decide +kernel))
      node_1407
      (invalid_excluded a [5,2,7,0,8,2] (by decide +kernel))
      node_1408
      node_1414
      (invalid_excluded a [5,2,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,8,8] (by decide +kernel)))

theorem node_1402 : Excluded a [5,2,7,0] :=
  branch_excluded a [5,2,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,7,0,0] (by decide +kernel))
      node_1403
      (invalid_excluded a [5,2,7,0,2] (by decide +kernel))
      node_1404
      (invalid_excluded a [5,2,7,0,4] (by decide +kernel))
      (invalid_excluded a [5,2,7,0,5] (by decide +kernel))
      node_1405
      (invalid_excluded a [5,2,7,0,7] (by decide +kernel))
      node_1406)

theorem node_1420 : Excluded a [5,2,7,1] :=
  predecessor_excluded a [5,2,7,1] 0 2 3 1 (by decide) (by decide +kernel)

theorem node_1422 : Excluded a [5,2,7,6,0] :=
  source_excluded a [5,2,7,6,0] 1 3 4 (by decide) (by decide +kernel)

theorem node_1423 : Excluded a [5,2,7,6,1] :=
  source_excluded a [5,2,7,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1424 : Excluded a [5,2,7,6,3] :=
  source_excluded a [5,2,7,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1426 : Excluded a [5,2,7,6,8,0] :=
  predecessor_excluded a [5,2,7,6,8,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1427 : Excluded a [5,2,7,6,8,1] :=
  source_excluded a [5,2,7,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1428 : Excluded a [5,2,7,6,8,3] :=
  source_excluded a [5,2,7,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1429 : Excluded a [5,2,7,6,8,4] :=
  source_excluded a [5,2,7,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1425 : Excluded a [5,2,7,6,8] :=
  branch_excluded a [5,2,7,6,8] (by decide)
    (fin9_cases _
      node_1426
      node_1427
      (invalid_excluded a [5,2,7,6,8,2] (by decide +kernel))
      node_1428
      node_1429
      (invalid_excluded a [5,2,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,2,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,2,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,6,8,8] (by decide +kernel)))

theorem node_1421 : Excluded a [5,2,7,6] :=
  branch_excluded a [5,2,7,6] (by decide)
    (fin9_cases _
      node_1422
      node_1423
      (invalid_excluded a [5,2,7,6,2] (by decide +kernel))
      node_1424
      (invalid_excluded a [5,2,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,2,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,2,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,2,7,6,7] (by decide +kernel))
      node_1425)

theorem node_1430 : Excluded a [5,2,7,8] :=
  predecessor_excluded a [5,2,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_1401 : Excluded a [5,2,7] :=
  branch_excluded a [5,2,7] (by decide)
    (fin9_cases _
      node_1402
      node_1420
      (invalid_excluded a [5,2,7,2] (by decide +kernel))
      (invalid_excluded a [5,2,7,3] (by decide +kernel))
      (invalid_excluded a [5,2,7,4] (by decide +kernel))
      (invalid_excluded a [5,2,7,5] (by decide +kernel))
      node_1421
      (invalid_excluded a [5,2,7,7] (by decide +kernel))
      node_1430)

theorem node_1433 : Excluded a [5,2,8,0,1] :=
  source_excluded a [5,2,8,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1434 : Excluded a [5,2,8,0,3] :=
  source_excluded a [5,2,8,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1436 : Excluded a [5,2,8,0,6,1] :=
  source_excluded a [5,2,8,0,6,1] 0 2 5 (by decide) (by decide +kernel)

def b_1440 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 2
  | 2 => 8
  | 3 => 0
  | 4 => 6
  | 5 => 3
  | 6 => 1
  | 7 => 4
  | 8 => 7
  | _ => 0

def cert_1440 : LosingRegion (edgeOf a b_1440) 0 :=
  losingMask a b_1440 0 1425556367020367847359488
    (by decide +kernel) (by decide +kernel)

theorem node_1440 : Excluded a [5,2,8,0,6,3,1,4,7] :=
  losing_excluded a [5,2,8,0,6,3,1,4,7] (by decide) b_1440 (by decide +kernel) 2 0 3 cert_1440 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1440 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1425556367020367847359488 2 3; decide +kernel)

theorem node_1439 : Excluded a [5,2,8,0,6,3,1,4] :=
  branch_excluded a [5,2,8,0,6,3,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,8,0,6,3,1,4,0] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,3,1,4,1] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,3,1,4,2] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,3,1,4,3] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,3,1,4,4] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,3,1,4,5] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,3,1,4,6] (by decide +kernel))
      node_1440
      (invalid_excluded a [5,2,8,0,6,3,1,4,8] (by decide +kernel)))

theorem node_1438 : Excluded a [5,2,8,0,6,3,1] :=
  branch_excluded a [5,2,8,0,6,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,8,0,6,3,1,0] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,3,1,1] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,3,1,2] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,3,1,3] (by decide +kernel))
      node_1439
      (invalid_excluded a [5,2,8,0,6,3,1,5] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,3,1,6] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,3,1,7] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,3,1,8] (by decide +kernel)))

theorem node_1441 : Excluded a [5,2,8,0,6,3,4] :=
  predecessor_excluded a [5,2,8,0,6,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_1437 : Excluded a [5,2,8,0,6,3] :=
  branch_excluded a [5,2,8,0,6,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,8,0,6,3,0] (by decide +kernel))
      node_1438
      (invalid_excluded a [5,2,8,0,6,3,2] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,3,3] (by decide +kernel))
      node_1441
      (invalid_excluded a [5,2,8,0,6,3,5] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,3,6] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,3,7] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,3,8] (by decide +kernel)))

theorem node_1442 : Excluded a [5,2,8,0,6,4] :=
  source_excluded a [5,2,8,0,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_1443 : Excluded a [5,2,8,0,6,7] :=
  source_excluded a [5,2,8,0,6,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1435 : Excluded a [5,2,8,0,6] :=
  branch_excluded a [5,2,8,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,8,0,6,0] (by decide +kernel))
      node_1436
      (invalid_excluded a [5,2,8,0,6,2] (by decide +kernel))
      node_1437
      node_1442
      (invalid_excluded a [5,2,8,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,6,6] (by decide +kernel))
      node_1443
      (invalid_excluded a [5,2,8,0,6,8] (by decide +kernel)))

theorem node_1444 : Excluded a [5,2,8,0,7] :=
  predecessor_excluded a [5,2,8,0,7] 0 8 4 2 (by decide) (by decide +kernel)

theorem node_1432 : Excluded a [5,2,8,0] :=
  branch_excluded a [5,2,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,8,0,0] (by decide +kernel))
      node_1433
      (invalid_excluded a [5,2,8,0,2] (by decide +kernel))
      node_1434
      (invalid_excluded a [5,2,8,0,4] (by decide +kernel))
      (invalid_excluded a [5,2,8,0,5] (by decide +kernel))
      node_1435
      node_1444
      (invalid_excluded a [5,2,8,0,8] (by decide +kernel)))

theorem node_1445 : Excluded a [5,2,8,1] :=
  predecessor_excluded a [5,2,8,1] 0 2 3 1 (by decide) (by decide +kernel)

theorem node_1447 : Excluded a [5,2,8,6,0] :=
  source_excluded a [5,2,8,6,0] 1 3 4 (by decide) (by decide +kernel)

theorem node_1448 : Excluded a [5,2,8,6,1] :=
  source_excluded a [5,2,8,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1449 : Excluded a [5,2,8,6,3] :=
  source_excluded a [5,2,8,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1450 : Excluded a [5,2,8,6,7] :=
  predecessor_excluded a [5,2,8,6,7] 0 8 4 2 (by decide) (by decide +kernel)

theorem node_1446 : Excluded a [5,2,8,6] :=
  branch_excluded a [5,2,8,6] (by decide)
    (fin9_cases _
      node_1447
      node_1448
      (invalid_excluded a [5,2,8,6,2] (by decide +kernel))
      node_1449
      (invalid_excluded a [5,2,8,6,4] (by decide +kernel))
      (invalid_excluded a [5,2,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,2,8,6,6] (by decide +kernel))
      node_1450
      (invalid_excluded a [5,2,8,6,8] (by decide +kernel)))

theorem node_1452 : Excluded a [5,2,8,7,0] :=
  source_excluded a [5,2,8,7,0] 1 3 4 (by decide) (by decide +kernel)

theorem node_1453 : Excluded a [5,2,8,7,1] :=
  source_excluded a [5,2,8,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1454 : Excluded a [5,2,8,7,3] :=
  source_excluded a [5,2,8,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1456 : Excluded a [5,2,8,7,6,0] :=
  predecessor_excluded a [5,2,8,7,6,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1457 : Excluded a [5,2,8,7,6,1] :=
  source_excluded a [5,2,8,7,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1458 : Excluded a [5,2,8,7,6,3] :=
  predecessor_excluded a [5,2,8,7,6,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1459 : Excluded a [5,2,8,7,6,4] :=
  source_excluded a [5,2,8,7,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_1455 : Excluded a [5,2,8,7,6] :=
  branch_excluded a [5,2,8,7,6] (by decide)
    (fin9_cases _
      node_1456
      node_1457
      (invalid_excluded a [5,2,8,7,6,2] (by decide +kernel))
      node_1458
      node_1459
      (invalid_excluded a [5,2,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,2,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,2,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [5,2,8,7,6,8] (by decide +kernel)))

theorem node_1451 : Excluded a [5,2,8,7] :=
  branch_excluded a [5,2,8,7] (by decide)
    (fin9_cases _
      node_1452
      node_1453
      (invalid_excluded a [5,2,8,7,2] (by decide +kernel))
      node_1454
      (invalid_excluded a [5,2,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,2,8,7,5] (by decide +kernel))
      node_1455
      (invalid_excluded a [5,2,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,2,8,7,8] (by decide +kernel)))

theorem node_1431 : Excluded a [5,2,8] :=
  branch_excluded a [5,2,8] (by decide)
    (fin9_cases _
      node_1432
      node_1445
      (invalid_excluded a [5,2,8,2] (by decide +kernel))
      (invalid_excluded a [5,2,8,3] (by decide +kernel))
      (invalid_excluded a [5,2,8,4] (by decide +kernel))
      (invalid_excluded a [5,2,8,5] (by decide +kernel))
      node_1446
      node_1451
      (invalid_excluded a [5,2,8,8] (by decide +kernel)))

theorem node_1362 : Excluded a [5,2] :=
  branch_excluded a [5,2] (by decide)
    (fin9_cases _
      node_1363
      node_1364
      (invalid_excluded a [5,2,2] (by decide +kernel))
      (invalid_excluded a [5,2,3] (by decide +kernel))
      node_1365
      (invalid_excluded a [5,2,5] (by decide +kernel))
      node_1366
      node_1401
      node_1431)

theorem node_1461 : Excluded a [5,3,0] :=
  source_excluded a [5,3,0] 1 2 2 (by decide) (by decide +kernel)

theorem node_1462 : Excluded a [5,3,1] :=
  source_excluded a [5,3,1] 2 0 1 (by decide) (by decide +kernel)

theorem node_1463 : Excluded a [5,3,4] :=
  source_excluded a [5,3,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_1465 : Excluded a [5,3,6,0] :=
  source_excluded a [5,3,6,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_1466 : Excluded a [5,3,6,1] :=
  predecessor_excluded a [5,3,6,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_1467 : Excluded a [5,3,6,2] :=
  source_excluded a [5,3,6,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1468 : Excluded a [5,3,6,7] :=
  predecessor_excluded a [5,3,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_1471 : Excluded a [5,3,6,8,0,1] :=
  source_excluded a [5,3,6,8,0,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1472 : Excluded a [5,3,6,8,0,2] :=
  source_excluded a [5,3,6,8,0,2] 5 0 2 (by decide) (by decide +kernel)

def b_1476 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 6
  | 3 => 8
  | 4 => 0
  | 5 => 4
  | 6 => 1
  | 7 => 2
  | 8 => 7
  | _ => 0

def cert_1476 : LosingRegion (edgeOf a b_1476) 0 :=
  losingMask a b_1476 0 1482224765093330074469376
    (by decide +kernel) (by decide +kernel)

theorem node_1476 : Excluded a [5,3,6,8,0,4,1,2,7] :=
  losing_excluded a [5,3,6,8,0,4,1,2,7] (by decide) b_1476 (by decide +kernel) 2 0 0 cert_1476 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1476 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1482224765093330074469376 2 0; decide +kernel)

theorem node_1475 : Excluded a [5,3,6,8,0,4,1,2] :=
  branch_excluded a [5,3,6,8,0,4,1,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,6,8,0,4,1,2,0] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,1,2,1] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,1,2,2] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,1,2,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,1,2,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,1,2,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,1,2,6] (by decide +kernel))
      node_1476
      (invalid_excluded a [5,3,6,8,0,4,1,2,8] (by decide +kernel)))

theorem node_1474 : Excluded a [5,3,6,8,0,4,1] :=
  branch_excluded a [5,3,6,8,0,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,6,8,0,4,1,0] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,1,1] (by decide +kernel))
      node_1475
      (invalid_excluded a [5,3,6,8,0,4,1,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,1,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,1,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,1,6] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,1,7] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,1,8] (by decide +kernel)))

theorem node_1477 : Excluded a [5,3,6,8,0,4,2] :=
  predecessor_excluded a [5,3,6,8,0,4,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_1473 : Excluded a [5,3,6,8,0,4] :=
  branch_excluded a [5,3,6,8,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,6,8,0,4,0] (by decide +kernel))
      node_1474
      node_1477
      (invalid_excluded a [5,3,6,8,0,4,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,6] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,7] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,4,8] (by decide +kernel)))

theorem node_1478 : Excluded a [5,3,6,8,0,7] :=
  source_excluded a [5,3,6,8,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1470 : Excluded a [5,3,6,8,0] :=
  branch_excluded a [5,3,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,6,8,0,0] (by decide +kernel))
      node_1471
      node_1472
      (invalid_excluded a [5,3,6,8,0,3] (by decide +kernel))
      node_1473
      (invalid_excluded a [5,3,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,0,6] (by decide +kernel))
      node_1478
      (invalid_excluded a [5,3,6,8,0,8] (by decide +kernel)))

theorem node_1479 : Excluded a [5,3,6,8,1] :=
  predecessor_excluded a [5,3,6,8,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1481 : Excluded a [5,3,6,8,7,0] :=
  predecessor_excluded a [5,3,6,8,7,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1482 : Excluded a [5,3,6,8,7,1] :=
  source_excluded a [5,3,6,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1483 : Excluded a [5,3,6,8,7,2] :=
  source_excluded a [5,3,6,8,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1484 : Excluded a [5,3,6,8,7,4] :=
  predecessor_excluded a [5,3,6,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1480 : Excluded a [5,3,6,8,7] :=
  branch_excluded a [5,3,6,8,7] (by decide)
    (fin9_cases _
      node_1481
      node_1482
      node_1483
      (invalid_excluded a [5,3,6,8,7,3] (by decide +kernel))
      node_1484
      (invalid_excluded a [5,3,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,7,8] (by decide +kernel)))

theorem node_1469 : Excluded a [5,3,6,8] :=
  branch_excluded a [5,3,6,8] (by decide)
    (fin9_cases _
      node_1470
      node_1479
      (invalid_excluded a [5,3,6,8,2] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,6] (by decide +kernel))
      node_1480
      (invalid_excluded a [5,3,6,8,8] (by decide +kernel)))

theorem node_1464 : Excluded a [5,3,6] :=
  branch_excluded a [5,3,6] (by decide)
    (fin9_cases _
      node_1465
      node_1466
      node_1467
      (invalid_excluded a [5,3,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,6] (by decide +kernel))
      node_1468
      node_1469)

theorem node_1486 : Excluded a [5,3,7,0] :=
  source_excluded a [5,3,7,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_1487 : Excluded a [5,3,7,1] :=
  predecessor_excluded a [5,3,7,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_1488 : Excluded a [5,3,7,2] :=
  source_excluded a [5,3,7,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1491 : Excluded a [5,3,7,6,0,1] :=
  source_excluded a [5,3,7,6,0,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1492 : Excluded a [5,3,7,6,0,2] :=
  predecessor_excluded a [5,3,7,6,0,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1493 : Excluded a [5,3,7,6,0,4] :=
  source_excluded a [5,3,7,6,0,4] 3 0 5 (by decide) (by decide +kernel)

def b_1497 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 7
  | 3 => 6
  | 4 => 0
  | 5 => 8
  | 6 => 1
  | 7 => 2
  | 8 => 4
  | _ => 0

def cert_1497 : LosingRegion (edgeOf a b_1497) 0 :=
  losingMask a b_1497 0 1326377448138434414117888
    (by decide +kernel) (by decide +kernel)

theorem node_1497 : Excluded a [5,3,7,6,0,8,1,2,4] :=
  losing_excluded a [5,3,7,6,0,8,1,2,4] (by decide) b_1497 (by decide +kernel) 2 0 1 cert_1497 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1497 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1326377448138434414117888 2 1; decide +kernel)

theorem node_1496 : Excluded a [5,3,7,6,0,8,1,2] :=
  branch_excluded a [5,3,7,6,0,8,1,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,7,6,0,8,1,2,0] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,0,8,1,2,1] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,0,8,1,2,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,0,8,1,2,3] (by decide +kernel))
      node_1497
      (invalid_excluded a [5,3,7,6,0,8,1,2,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,0,8,1,2,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,0,8,1,2,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,0,8,1,2,8] (by decide +kernel)))

theorem node_1498 : Excluded a [5,3,7,6,0,8,1,4] :=
  predecessor_excluded a [5,3,7,6,0,8,1,4] 0 4 2 7 (by decide) (by decide +kernel)

theorem node_1495 : Excluded a [5,3,7,6,0,8,1] :=
  branch_excluded a [5,3,7,6,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,7,6,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,0,8,1,1] (by decide +kernel))
      node_1496
      (invalid_excluded a [5,3,7,6,0,8,1,3] (by decide +kernel))
      node_1498
      (invalid_excluded a [5,3,7,6,0,8,1,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,0,8,1,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,0,8,1,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,0,8,1,8] (by decide +kernel)))

theorem node_1499 : Excluded a [5,3,7,6,0,8,2] :=
  source_excluded a [5,3,7,6,0,8,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_1500 : Excluded a [5,3,7,6,0,8,4] :=
  source_excluded a [5,3,7,6,0,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1494 : Excluded a [5,3,7,6,0,8] :=
  branch_excluded a [5,3,7,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,7,6,0,8,0] (by decide +kernel))
      node_1495
      node_1499
      (invalid_excluded a [5,3,7,6,0,8,3] (by decide +kernel))
      node_1500
      (invalid_excluded a [5,3,7,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,0,8,8] (by decide +kernel)))

theorem node_1490 : Excluded a [5,3,7,6,0] :=
  branch_excluded a [5,3,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,7,6,0,0] (by decide +kernel))
      node_1491
      node_1492
      (invalid_excluded a [5,3,7,6,0,3] (by decide +kernel))
      node_1493
      (invalid_excluded a [5,3,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,0,7] (by decide +kernel))
      node_1494)

theorem node_1501 : Excluded a [5,3,7,6,1] :=
  predecessor_excluded a [5,3,7,6,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1503 : Excluded a [5,3,7,6,8,0] :=
  predecessor_excluded a [5,3,7,6,8,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1504 : Excluded a [5,3,7,6,8,1] :=
  source_excluded a [5,3,7,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1505 : Excluded a [5,3,7,6,8,2] :=
  predecessor_excluded a [5,3,7,6,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1506 : Excluded a [5,3,7,6,8,4] :=
  source_excluded a [5,3,7,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1502 : Excluded a [5,3,7,6,8] :=
  branch_excluded a [5,3,7,6,8] (by decide)
    (fin9_cases _
      node_1503
      node_1504
      node_1505
      (invalid_excluded a [5,3,7,6,8,3] (by decide +kernel))
      node_1506
      (invalid_excluded a [5,3,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,8,8] (by decide +kernel)))

theorem node_1489 : Excluded a [5,3,7,6] :=
  branch_excluded a [5,3,7,6] (by decide)
    (fin9_cases _
      node_1490
      node_1501
      (invalid_excluded a [5,3,7,6,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,7] (by decide +kernel))
      node_1502)

theorem node_1507 : Excluded a [5,3,7,8] :=
  predecessor_excluded a [5,3,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_1485 : Excluded a [5,3,7] :=
  branch_excluded a [5,3,7] (by decide)
    (fin9_cases _
      node_1486
      node_1487
      node_1488
      (invalid_excluded a [5,3,7,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,5] (by decide +kernel))
      node_1489
      (invalid_excluded a [5,3,7,7] (by decide +kernel))
      node_1507)

theorem node_1509 : Excluded a [5,3,8,0] :=
  source_excluded a [5,3,8,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_1510 : Excluded a [5,3,8,1] :=
  predecessor_excluded a [5,3,8,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_1511 : Excluded a [5,3,8,2] :=
  source_excluded a [5,3,8,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1514 : Excluded a [5,3,8,6,0,1] :=
  source_excluded a [5,3,8,6,0,1] 0 2 5 (by decide) (by decide +kernel)

def b_1518 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 8
  | 3 => 6
  | 4 => 0
  | 5 => 2
  | 6 => 1
  | 7 => 4
  | 8 => 7
  | _ => 0

def cert_1518 : LosingRegion (edgeOf a b_1518) 0 :=
  losingMask a b_1518 0 1654231414270107779073024
    (by decide +kernel) (by decide +kernel)

theorem node_1518 : Excluded a [5,3,8,6,0,2,1,4,7] :=
  losing_excluded a [5,3,8,6,0,2,1,4,7] (by decide) b_1518 (by decide +kernel) 2 0 1 cert_1518 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1518 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1654231414270107779073024 2 1; decide +kernel)

theorem node_1517 : Excluded a [5,3,8,6,0,2,1,4] :=
  branch_excluded a [5,3,8,6,0,2,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,8,6,0,2,1,4,0] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,2,1,4,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,2,1,4,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,2,1,4,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,2,1,4,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,2,1,4,6] (by decide +kernel))
      node_1518
      (invalid_excluded a [5,3,8,6,0,2,1,4,8] (by decide +kernel)))

theorem node_1516 : Excluded a [5,3,8,6,0,2,1] :=
  branch_excluded a [5,3,8,6,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,8,6,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,2,1,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,2,1,3] (by decide +kernel))
      node_1517
      (invalid_excluded a [5,3,8,6,0,2,1,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,2,1,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,2,1,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,2,1,8] (by decide +kernel)))

theorem node_1519 : Excluded a [5,3,8,6,0,2,4] :=
  source_excluded a [5,3,8,6,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1515 : Excluded a [5,3,8,6,0,2] :=
  branch_excluded a [5,3,8,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,8,6,0,2,0] (by decide +kernel))
      node_1516
      (invalid_excluded a [5,3,8,6,0,2,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,2,3] (by decide +kernel))
      node_1519
      (invalid_excluded a [5,3,8,6,0,2,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,2,8] (by decide +kernel)))

theorem node_1520 : Excluded a [5,3,8,6,0,4] :=
  source_excluded a [5,3,8,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1521 : Excluded a [5,3,8,6,0,7] :=
  source_excluded a [5,3,8,6,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1513 : Excluded a [5,3,8,6,0] :=
  branch_excluded a [5,3,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,8,6,0,0] (by decide +kernel))
      node_1514
      node_1515
      (invalid_excluded a [5,3,8,6,0,3] (by decide +kernel))
      node_1520
      (invalid_excluded a [5,3,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,0,6] (by decide +kernel))
      node_1521
      (invalid_excluded a [5,3,8,6,0,8] (by decide +kernel)))

theorem node_1522 : Excluded a [5,3,8,6,1] :=
  predecessor_excluded a [5,3,8,6,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1523 : Excluded a [5,3,8,6,7] :=
  predecessor_excluded a [5,3,8,6,7] 0 8 4 2 (by decide) (by decide +kernel)

theorem node_1512 : Excluded a [5,3,8,6] :=
  branch_excluded a [5,3,8,6] (by decide)
    (fin9_cases _
      node_1513
      node_1522
      (invalid_excluded a [5,3,8,6,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,6] (by decide +kernel))
      node_1523
      (invalid_excluded a [5,3,8,6,8] (by decide +kernel)))

theorem node_1526 : Excluded a [5,3,8,7,0,1] :=
  source_excluded a [5,3,8,7,0,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1529 : Excluded a [5,3,8,7,0,2,1,4] :=
  source_excluded a [5,3,8,7,0,2,1,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_1531 : Excluded a [5,3,8,7,0,2,1,6,4] :=
  predecessor_excluded a [5,3,8,7,0,2,1,6,4] 0 2 8 5 (by decide) (by decide +kernel)

theorem node_1530 : Excluded a [5,3,8,7,0,2,1,6] :=
  branch_excluded a [5,3,8,7,0,2,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,8,7,0,2,1,6,0] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,2,1,6,1] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,2,1,6,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,2,1,6,3] (by decide +kernel))
      node_1531
      (invalid_excluded a [5,3,8,7,0,2,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,2,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,2,1,6,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,2,1,6,8] (by decide +kernel)))

theorem node_1528 : Excluded a [5,3,8,7,0,2,1] :=
  branch_excluded a [5,3,8,7,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,8,7,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,2,1,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,2,1,3] (by decide +kernel))
      node_1529
      (invalid_excluded a [5,3,8,7,0,2,1,5] (by decide +kernel))
      node_1530
      (invalid_excluded a [5,3,8,7,0,2,1,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,2,1,8] (by decide +kernel)))

theorem node_1532 : Excluded a [5,3,8,7,0,2,4] :=
  source_excluded a [5,3,8,7,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1527 : Excluded a [5,3,8,7,0,2] :=
  branch_excluded a [5,3,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,8,7,0,2,0] (by decide +kernel))
      node_1528
      (invalid_excluded a [5,3,8,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,2,3] (by decide +kernel))
      node_1532
      (invalid_excluded a [5,3,8,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,2,8] (by decide +kernel)))

theorem node_1535 : Excluded a [5,3,8,7,0,4,1,2] :=
  source_excluded a [5,3,8,7,0,4,1,2] 7 0 2 (by decide) (by decide +kernel)

def b_1537 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 8
  | 3 => 7
  | 4 => 0
  | 5 => 4
  | 6 => 1
  | 7 => 6
  | 8 => 2
  | _ => 0

def cert_1537 : LosingRegion (edgeOf a b_1537) 0 :=
  losingMask a b_1537 0 1479752901387453063758848
    (by decide +kernel) (by decide +kernel)

theorem node_1537 : Excluded a [5,3,8,7,0,4,1,6,2] :=
  losing_excluded a [5,3,8,7,0,4,1,6,2] (by decide) b_1537 (by decide +kernel) 2 0 0 cert_1537 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1537 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1479752901387453063758848 2 0; decide +kernel)

theorem node_1536 : Excluded a [5,3,8,7,0,4,1,6] :=
  branch_excluded a [5,3,8,7,0,4,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,8,7,0,4,1,6,0] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,4,1,6,1] (by decide +kernel))
      node_1537
      (invalid_excluded a [5,3,8,7,0,4,1,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,4,1,6,8] (by decide +kernel)))

theorem node_1534 : Excluded a [5,3,8,7,0,4,1] :=
  branch_excluded a [5,3,8,7,0,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,8,7,0,4,1,0] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,4,1,1] (by decide +kernel))
      node_1535
      (invalid_excluded a [5,3,8,7,0,4,1,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,4,1,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,4,1,5] (by decide +kernel))
      node_1536
      (invalid_excluded a [5,3,8,7,0,4,1,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,4,1,8] (by decide +kernel)))

theorem node_1538 : Excluded a [5,3,8,7,0,4,2] :=
  predecessor_excluded a [5,3,8,7,0,4,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_1533 : Excluded a [5,3,8,7,0,4] :=
  branch_excluded a [5,3,8,7,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,8,7,0,4,0] (by decide +kernel))
      node_1534
      node_1538
      (invalid_excluded a [5,3,8,7,0,4,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,4,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,4,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,4,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,4,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,4,8] (by decide +kernel)))

theorem node_1525 : Excluded a [5,3,8,7,0] :=
  branch_excluded a [5,3,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,8,7,0,0] (by decide +kernel))
      node_1526
      node_1527
      (invalid_excluded a [5,3,8,7,0,3] (by decide +kernel))
      node_1533
      (invalid_excluded a [5,3,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,0,8] (by decide +kernel)))

theorem node_1539 : Excluded a [5,3,8,7,1] :=
  predecessor_excluded a [5,3,8,7,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1541 : Excluded a [5,3,8,7,6,0] :=
  predecessor_excluded a [5,3,8,7,6,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1542 : Excluded a [5,3,8,7,6,1] :=
  source_excluded a [5,3,8,7,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1543 : Excluded a [5,3,8,7,6,2] :=
  source_excluded a [5,3,8,7,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1544 : Excluded a [5,3,8,7,6,4] :=
  source_excluded a [5,3,8,7,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_1540 : Excluded a [5,3,8,7,6] :=
  branch_excluded a [5,3,8,7,6] (by decide)
    (fin9_cases _
      node_1541
      node_1542
      node_1543
      (invalid_excluded a [5,3,8,7,6,3] (by decide +kernel))
      node_1544
      (invalid_excluded a [5,3,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,6,8] (by decide +kernel)))

theorem node_1524 : Excluded a [5,3,8,7] :=
  branch_excluded a [5,3,8,7] (by decide)
    (fin9_cases _
      node_1525
      node_1539
      (invalid_excluded a [5,3,8,7,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,5] (by decide +kernel))
      node_1540
      (invalid_excluded a [5,3,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,8] (by decide +kernel)))

theorem node_1508 : Excluded a [5,3,8] :=
  branch_excluded a [5,3,8] (by decide)
    (fin9_cases _
      node_1509
      node_1510
      node_1511
      (invalid_excluded a [5,3,8,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,5] (by decide +kernel))
      node_1512
      node_1524
      (invalid_excluded a [5,3,8,8] (by decide +kernel)))

theorem node_1460 : Excluded a [5,3] :=
  branch_excluded a [5,3] (by decide)
    (fin9_cases _
      node_1461
      node_1462
      (invalid_excluded a [5,3,2] (by decide +kernel))
      (invalid_excluded a [5,3,3] (by decide +kernel))
      node_1463
      (invalid_excluded a [5,3,5] (by decide +kernel))
      node_1464
      node_1485
      node_1508)

theorem node_1547 : Excluded a [5,4,0,1] :=
  source_excluded a [5,4,0,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1548 : Excluded a [5,4,0,2] :=
  source_excluded a [5,4,0,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1550 : Excluded a [5,4,0,6,1] :=
  predecessor_excluded a [5,4,0,6,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_1551 : Excluded a [5,4,0,6,3] :=
  source_excluded a [5,4,0,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1552 : Excluded a [5,4,0,6,7] :=
  predecessor_excluded a [5,4,0,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_1554 : Excluded a [5,4,0,6,8,1] :=
  source_excluded a [5,4,0,6,8,1] 0 2 5 (by decide) (by decide +kernel)

def b_1558 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 0
  | 3 => 6
  | 4 => 8
  | 5 => 2
  | 6 => 1
  | 7 => 3
  | 8 => 7
  | _ => 0

def cert_1558 : LosingRegion (edgeOf a b_1558) 0 :=
  losingMask a b_1558 0 1463335298742111708382208
    (by decide +kernel) (by decide +kernel)

theorem node_1558 : Excluded a [5,4,0,6,8,2,1,3,7] :=
  losing_excluded a [5,4,0,6,8,2,1,3,7] (by decide) b_1558 (by decide +kernel) 3 0 0 cert_1558 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_1558 3 0 ∧ 0 ≠ 3 ∧ maskRegion 1463335298742111708382208 3 0; decide +kernel)

theorem node_1557 : Excluded a [5,4,0,6,8,2,1,3] :=
  branch_excluded a [5,4,0,6,8,2,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,6,8,2,1,3,0] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,2,1,3,3] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,2,1,3,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,2,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,2,1,3,6] (by decide +kernel))
      node_1558
      (invalid_excluded a [5,4,0,6,8,2,1,3,8] (by decide +kernel)))

theorem node_1556 : Excluded a [5,4,0,6,8,2,1] :=
  branch_excluded a [5,4,0,6,8,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,6,8,2,1,0] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,2,1,1] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,2,1,2] (by decide +kernel))
      node_1557
      (invalid_excluded a [5,4,0,6,8,2,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,2,1,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,2,1,6] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,2,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,2,1,8] (by decide +kernel)))

theorem node_1559 : Excluded a [5,4,0,6,8,2,3] :=
  predecessor_excluded a [5,4,0,6,8,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_1555 : Excluded a [5,4,0,6,8,2] :=
  branch_excluded a [5,4,0,6,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,6,8,2,0] (by decide +kernel))
      node_1556
      (invalid_excluded a [5,4,0,6,8,2,2] (by decide +kernel))
      node_1559
      (invalid_excluded a [5,4,0,6,8,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,2,8] (by decide +kernel)))

theorem node_1560 : Excluded a [5,4,0,6,8,3] :=
  source_excluded a [5,4,0,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1561 : Excluded a [5,4,0,6,8,7] :=
  source_excluded a [5,4,0,6,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1553 : Excluded a [5,4,0,6,8] :=
  branch_excluded a [5,4,0,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,6,8,0] (by decide +kernel))
      node_1554
      node_1555
      node_1560
      (invalid_excluded a [5,4,0,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,8,6] (by decide +kernel))
      node_1561
      (invalid_excluded a [5,4,0,6,8,8] (by decide +kernel)))

theorem node_1549 : Excluded a [5,4,0,6] :=
  branch_excluded a [5,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,6,0] (by decide +kernel))
      node_1550
      (invalid_excluded a [5,4,0,6,2] (by decide +kernel))
      node_1551
      (invalid_excluded a [5,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,6,6] (by decide +kernel))
      node_1552
      node_1553)

theorem node_1563 : Excluded a [5,4,0,7,1] :=
  predecessor_excluded a [5,4,0,7,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_1564 : Excluded a [5,4,0,7,3] :=
  source_excluded a [5,4,0,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1566 : Excluded a [5,4,0,7,6,1] :=
  source_excluded a [5,4,0,7,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1567 : Excluded a [5,4,0,7,6,2] :=
  source_excluded a [5,4,0,7,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1568 : Excluded a [5,4,0,7,6,3] :=
  predecessor_excluded a [5,4,0,7,6,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1571 : Excluded a [5,4,0,7,6,8,1,2] :=
  predecessor_excluded a [5,4,0,7,6,8,1,2] 0 2 3 7 (by decide) (by decide +kernel)

def b_1573 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 0
  | 3 => 7
  | 4 => 6
  | 5 => 8
  | 6 => 1
  | 7 => 3
  | 8 => 2
  | _ => 0

def cert_1573 : LosingRegion (edgeOf a b_1573) 0 :=
  losingMask a b_1573 0 1307487982066528313934848
    (by decide +kernel) (by decide +kernel)

theorem node_1573 : Excluded a [5,4,0,7,6,8,1,3,2] :=
  losing_excluded a [5,4,0,7,6,8,1,3,2] (by decide) b_1573 (by decide +kernel) 3 0 1 cert_1573 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_1573 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1307487982066528313934848 3 1; decide +kernel)

theorem node_1572 : Excluded a [5,4,0,7,6,8,1,3] :=
  branch_excluded a [5,4,0,7,6,8,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,7,6,8,1,3,0] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,8,1,3,1] (by decide +kernel))
      node_1573
      (invalid_excluded a [5,4,0,7,6,8,1,3,3] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,8,1,3,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,8,1,3,8] (by decide +kernel)))

theorem node_1570 : Excluded a [5,4,0,7,6,8,1] :=
  branch_excluded a [5,4,0,7,6,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,7,6,8,1,0] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,8,1,1] (by decide +kernel))
      node_1571
      node_1572
      (invalid_excluded a [5,4,0,7,6,8,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,8,1,8] (by decide +kernel)))

theorem node_1574 : Excluded a [5,4,0,7,6,8,2] :=
  source_excluded a [5,4,0,7,6,8,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1575 : Excluded a [5,4,0,7,6,8,3] :=
  source_excluded a [5,4,0,7,6,8,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1569 : Excluded a [5,4,0,7,6,8] :=
  branch_excluded a [5,4,0,7,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,7,6,8,0] (by decide +kernel))
      node_1570
      node_1574
      node_1575
      (invalid_excluded a [5,4,0,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,8,8] (by decide +kernel)))

theorem node_1565 : Excluded a [5,4,0,7,6] :=
  branch_excluded a [5,4,0,7,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,7,6,0] (by decide +kernel))
      node_1566
      node_1567
      node_1568
      (invalid_excluded a [5,4,0,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,6,7] (by decide +kernel))
      node_1569)

theorem node_1576 : Excluded a [5,4,0,7,8] :=
  predecessor_excluded a [5,4,0,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_1562 : Excluded a [5,4,0,7] :=
  branch_excluded a [5,4,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,7,0] (by decide +kernel))
      node_1563
      (invalid_excluded a [5,4,0,7,2] (by decide +kernel))
      node_1564
      (invalid_excluded a [5,4,0,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,7,5] (by decide +kernel))
      node_1565
      (invalid_excluded a [5,4,0,7,7] (by decide +kernel))
      node_1576)

theorem node_1578 : Excluded a [5,4,0,8,1] :=
  predecessor_excluded a [5,4,0,8,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_1579 : Excluded a [5,4,0,8,3] :=
  source_excluded a [5,4,0,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1581 : Excluded a [5,4,0,8,6,1] :=
  source_excluded a [5,4,0,8,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1582 : Excluded a [5,4,0,8,6,2] :=
  source_excluded a [5,4,0,8,6,2] 4 0 5 (by decide) (by decide +kernel)

def b_1586 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 0
  | 3 => 8
  | 4 => 6
  | 5 => 3
  | 6 => 1
  | 7 => 2
  | 8 => 7
  | _ => 0

def cert_1586 : LosingRegion (edgeOf a b_1586) 0 :=
  losingMask a b_1586 0 1654194521063437749978112
    (by decide +kernel) (by decide +kernel)

theorem node_1586 : Excluded a [5,4,0,8,6,3,1,2,7] :=
  losing_excluded a [5,4,0,8,6,3,1,2,7] (by decide) b_1586 (by decide +kernel) 3 0 1 cert_1586 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_1586 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1654194521063437749978112 3 1; decide +kernel)

theorem node_1585 : Excluded a [5,4,0,8,6,3,1,2] :=
  branch_excluded a [5,4,0,8,6,3,1,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,6,3,1,2,0] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,1,2,1] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,1,2,2] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,1,2,3] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,1,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,1,2,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,1,2,6] (by decide +kernel))
      node_1586
      (invalid_excluded a [5,4,0,8,6,3,1,2,8] (by decide +kernel)))

theorem node_1584 : Excluded a [5,4,0,8,6,3,1] :=
  branch_excluded a [5,4,0,8,6,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,6,3,1,0] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,1,1] (by decide +kernel))
      node_1585
      (invalid_excluded a [5,4,0,8,6,3,1,3] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,1,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,1,6] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,1,8] (by decide +kernel)))

theorem node_1587 : Excluded a [5,4,0,8,6,3,2] :=
  source_excluded a [5,4,0,8,6,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1583 : Excluded a [5,4,0,8,6,3] :=
  branch_excluded a [5,4,0,8,6,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,6,3,0] (by decide +kernel))
      node_1584
      node_1587
      (invalid_excluded a [5,4,0,8,6,3,3] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,6] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,3,8] (by decide +kernel)))

theorem node_1588 : Excluded a [5,4,0,8,6,7] :=
  source_excluded a [5,4,0,8,6,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1580 : Excluded a [5,4,0,8,6] :=
  branch_excluded a [5,4,0,8,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,6,0] (by decide +kernel))
      node_1581
      node_1582
      node_1583
      (invalid_excluded a [5,4,0,8,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,6,6] (by decide +kernel))
      node_1588
      (invalid_excluded a [5,4,0,8,6,8] (by decide +kernel)))

theorem node_1590 : Excluded a [5,4,0,8,7,1] :=
  source_excluded a [5,4,0,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1593 : Excluded a [5,4,0,8,7,2,1,3] :=
  source_excluded a [5,4,0,8,7,2,1,3] 7 0 3 (by decide) (by decide +kernel)

def b_1595 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 0
  | 3 => 8
  | 4 => 7
  | 5 => 2
  | 6 => 1
  | 7 => 6
  | 8 => 3
  | _ => 0

def cert_1595 : LosingRegion (edgeOf a b_1595) 0 :=
  losingMask a b_1595 0 1460752754571828878377984
    (by decide +kernel) (by decide +kernel)

theorem node_1595 : Excluded a [5,4,0,8,7,2,1,6,3] :=
  losing_excluded a [5,4,0,8,7,2,1,6,3] (by decide) b_1595 (by decide +kernel) 3 0 0 cert_1595 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_1595 3 0 ∧ 0 ≠ 3 ∧ maskRegion 1460752754571828878377984 3 0; decide +kernel)

theorem node_1594 : Excluded a [5,4,0,8,7,2,1,6] :=
  branch_excluded a [5,4,0,8,7,2,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,7,2,1,6,0] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,2,1,6,1] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,2,1,6,2] (by decide +kernel))
      node_1595
      (invalid_excluded a [5,4,0,8,7,2,1,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,2,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,2,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,2,1,6,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,2,1,6,8] (by decide +kernel)))

theorem node_1592 : Excluded a [5,4,0,8,7,2,1] :=
  branch_excluded a [5,4,0,8,7,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,7,2,1,0] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,2,1,2] (by decide +kernel))
      node_1593
      (invalid_excluded a [5,4,0,8,7,2,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,2,1,5] (by decide +kernel))
      node_1594
      (invalid_excluded a [5,4,0,8,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,2,1,8] (by decide +kernel)))

theorem node_1596 : Excluded a [5,4,0,8,7,2,3] :=
  predecessor_excluded a [5,4,0,8,7,2,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_1591 : Excluded a [5,4,0,8,7,2] :=
  branch_excluded a [5,4,0,8,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,7,2,0] (by decide +kernel))
      node_1592
      (invalid_excluded a [5,4,0,8,7,2,2] (by decide +kernel))
      node_1596
      (invalid_excluded a [5,4,0,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,2,8] (by decide +kernel)))

theorem node_1599 : Excluded a [5,4,0,8,7,3,1,2] :=
  source_excluded a [5,4,0,8,7,3,1,2] 4 0 7 (by decide) (by decide +kernel)

theorem node_1601 : Excluded a [5,4,0,8,7,3,1,6,2] :=
  predecessor_excluded a [5,4,0,8,7,3,1,6,2] 0 3 8 5 (by decide) (by decide +kernel)

theorem node_1600 : Excluded a [5,4,0,8,7,3,1,6] :=
  branch_excluded a [5,4,0,8,7,3,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,7,3,1,6,0] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,1,6,1] (by decide +kernel))
      node_1601
      (invalid_excluded a [5,4,0,8,7,3,1,6,3] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,1,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,1,6,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,1,6,8] (by decide +kernel)))

theorem node_1598 : Excluded a [5,4,0,8,7,3,1] :=
  branch_excluded a [5,4,0,8,7,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,7,3,1,0] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,1,1] (by decide +kernel))
      node_1599
      (invalid_excluded a [5,4,0,8,7,3,1,3] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,1,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,1,5] (by decide +kernel))
      node_1600
      (invalid_excluded a [5,4,0,8,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,1,8] (by decide +kernel)))

theorem node_1602 : Excluded a [5,4,0,8,7,3,2] :=
  source_excluded a [5,4,0,8,7,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1597 : Excluded a [5,4,0,8,7,3] :=
  branch_excluded a [5,4,0,8,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,7,3,0] (by decide +kernel))
      node_1598
      node_1602
      (invalid_excluded a [5,4,0,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,3,8] (by decide +kernel)))

theorem node_1589 : Excluded a [5,4,0,8,7] :=
  branch_excluded a [5,4,0,8,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,7,0] (by decide +kernel))
      node_1590
      node_1591
      node_1597
      (invalid_excluded a [5,4,0,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,7,8] (by decide +kernel)))

theorem node_1577 : Excluded a [5,4,0,8] :=
  branch_excluded a [5,4,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,8,0] (by decide +kernel))
      node_1578
      (invalid_excluded a [5,4,0,8,2] (by decide +kernel))
      node_1579
      (invalid_excluded a [5,4,0,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,8,5] (by decide +kernel))
      node_1580
      node_1589
      (invalid_excluded a [5,4,0,8,8] (by decide +kernel)))

theorem node_1546 : Excluded a [5,4,0] :=
  branch_excluded a [5,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,4,0,0] (by decide +kernel))
      node_1547
      node_1548
      (invalid_excluded a [5,4,0,3] (by decide +kernel))
      (invalid_excluded a [5,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,4,0,5] (by decide +kernel))
      node_1549
      node_1562
      node_1577)

theorem node_1603 : Excluded a [5,4,1] :=
  predecessor_excluded a [5,4,1] 0 4 2 1 (by decide) (by decide +kernel)

theorem node_1605 : Excluded a [5,4,6,0] :=
  source_excluded a [5,4,6,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_1606 : Excluded a [5,4,6,1] :=
  source_excluded a [5,4,6,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1607 : Excluded a [5,4,6,2] :=
  source_excluded a [5,4,6,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1608 : Excluded a [5,4,6,7] :=
  predecessor_excluded a [5,4,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_1610 : Excluded a [5,4,6,8,0] :=
  source_excluded a [5,4,6,8,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_1611 : Excluded a [5,4,6,8,1] :=
  predecessor_excluded a [5,4,6,8,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_1612 : Excluded a [5,4,6,8,3] :=
  source_excluded a [5,4,6,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1614 : Excluded a [5,4,6,8,7,0] :=
  predecessor_excluded a [5,4,6,8,7,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1615 : Excluded a [5,4,6,8,7,1] :=
  source_excluded a [5,4,6,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1616 : Excluded a [5,4,6,8,7,2] :=
  source_excluded a [5,4,6,8,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1617 : Excluded a [5,4,6,8,7,3] :=
  source_excluded a [5,4,6,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1613 : Excluded a [5,4,6,8,7] :=
  branch_excluded a [5,4,6,8,7] (by decide)
    (fin9_cases _
      node_1614
      node_1615
      node_1616
      node_1617
      (invalid_excluded a [5,4,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,7,8] (by decide +kernel)))

theorem node_1609 : Excluded a [5,4,6,8] :=
  branch_excluded a [5,4,6,8] (by decide)
    (fin9_cases _
      node_1610
      node_1611
      (invalid_excluded a [5,4,6,8,2] (by decide +kernel))
      node_1612
      (invalid_excluded a [5,4,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,8,6] (by decide +kernel))
      node_1613
      (invalid_excluded a [5,4,6,8,8] (by decide +kernel)))

theorem node_1604 : Excluded a [5,4,6] :=
  branch_excluded a [5,4,6] (by decide)
    (fin9_cases _
      node_1605
      node_1606
      node_1607
      (invalid_excluded a [5,4,6,3] (by decide +kernel))
      (invalid_excluded a [5,4,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,6,6] (by decide +kernel))
      node_1608
      node_1609)

theorem node_1619 : Excluded a [5,4,7,0] :=
  source_excluded a [5,4,7,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_1620 : Excluded a [5,4,7,1] :=
  source_excluded a [5,4,7,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1621 : Excluded a [5,4,7,2] :=
  source_excluded a [5,4,7,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1623 : Excluded a [5,4,7,6,0] :=
  source_excluded a [5,4,7,6,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_1624 : Excluded a [5,4,7,6,1] :=
  predecessor_excluded a [5,4,7,6,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_1625 : Excluded a [5,4,7,6,3] :=
  source_excluded a [5,4,7,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1627 : Excluded a [5,4,7,6,8,0] :=
  predecessor_excluded a [5,4,7,6,8,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1628 : Excluded a [5,4,7,6,8,1] :=
  source_excluded a [5,4,7,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1629 : Excluded a [5,4,7,6,8,2] :=
  predecessor_excluded a [5,4,7,6,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1630 : Excluded a [5,4,7,6,8,3] :=
  source_excluded a [5,4,7,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1626 : Excluded a [5,4,7,6,8] :=
  branch_excluded a [5,4,7,6,8] (by decide)
    (fin9_cases _
      node_1627
      node_1628
      node_1629
      node_1630
      (invalid_excluded a [5,4,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,8,8] (by decide +kernel)))

theorem node_1622 : Excluded a [5,4,7,6] :=
  branch_excluded a [5,4,7,6] (by decide)
    (fin9_cases _
      node_1623
      node_1624
      (invalid_excluded a [5,4,7,6,2] (by decide +kernel))
      node_1625
      (invalid_excluded a [5,4,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,4,7,6,7] (by decide +kernel))
      node_1626)

theorem node_1631 : Excluded a [5,4,7,8] :=
  predecessor_excluded a [5,4,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_1618 : Excluded a [5,4,7] :=
  branch_excluded a [5,4,7] (by decide)
    (fin9_cases _
      node_1619
      node_1620
      node_1621
      (invalid_excluded a [5,4,7,3] (by decide +kernel))
      (invalid_excluded a [5,4,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,7,5] (by decide +kernel))
      node_1622
      (invalid_excluded a [5,4,7,7] (by decide +kernel))
      node_1631)

theorem node_1633 : Excluded a [5,4,8,0] :=
  source_excluded a [5,4,8,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_1634 : Excluded a [5,4,8,1] :=
  source_excluded a [5,4,8,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_1635 : Excluded a [5,4,8,2] :=
  source_excluded a [5,4,8,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1637 : Excluded a [5,4,8,6,0] :=
  source_excluded a [5,4,8,6,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_1638 : Excluded a [5,4,8,6,1] :=
  predecessor_excluded a [5,4,8,6,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_1639 : Excluded a [5,4,8,6,3] :=
  source_excluded a [5,4,8,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1640 : Excluded a [5,4,8,6,7] :=
  predecessor_excluded a [5,4,8,6,7] 0 8 4 2 (by decide) (by decide +kernel)

theorem node_1636 : Excluded a [5,4,8,6] :=
  branch_excluded a [5,4,8,6] (by decide)
    (fin9_cases _
      node_1637
      node_1638
      (invalid_excluded a [5,4,8,6,2] (by decide +kernel))
      node_1639
      (invalid_excluded a [5,4,8,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,8,6,6] (by decide +kernel))
      node_1640
      (invalid_excluded a [5,4,8,6,8] (by decide +kernel)))

theorem node_1642 : Excluded a [5,4,8,7,0] :=
  source_excluded a [5,4,8,7,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_1643 : Excluded a [5,4,8,7,1] :=
  predecessor_excluded a [5,4,8,7,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_1644 : Excluded a [5,4,8,7,3] :=
  source_excluded a [5,4,8,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1646 : Excluded a [5,4,8,7,6,0] :=
  predecessor_excluded a [5,4,8,7,6,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1647 : Excluded a [5,4,8,7,6,1] :=
  source_excluded a [5,4,8,7,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1648 : Excluded a [5,4,8,7,6,2] :=
  source_excluded a [5,4,8,7,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1649 : Excluded a [5,4,8,7,6,3] :=
  predecessor_excluded a [5,4,8,7,6,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1645 : Excluded a [5,4,8,7,6] :=
  branch_excluded a [5,4,8,7,6] (by decide)
    (fin9_cases _
      node_1646
      node_1647
      node_1648
      node_1649
      (invalid_excluded a [5,4,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,6,8] (by decide +kernel)))

theorem node_1641 : Excluded a [5,4,8,7] :=
  branch_excluded a [5,4,8,7] (by decide)
    (fin9_cases _
      node_1642
      node_1643
      (invalid_excluded a [5,4,8,7,2] (by decide +kernel))
      node_1644
      (invalid_excluded a [5,4,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,5] (by decide +kernel))
      node_1645
      (invalid_excluded a [5,4,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,4,8,7,8] (by decide +kernel)))

theorem node_1632 : Excluded a [5,4,8] :=
  branch_excluded a [5,4,8] (by decide)
    (fin9_cases _
      node_1633
      node_1634
      node_1635
      (invalid_excluded a [5,4,8,3] (by decide +kernel))
      (invalid_excluded a [5,4,8,4] (by decide +kernel))
      (invalid_excluded a [5,4,8,5] (by decide +kernel))
      node_1636
      node_1641
      (invalid_excluded a [5,4,8,8] (by decide +kernel)))

theorem node_1545 : Excluded a [5,4] :=
  branch_excluded a [5,4] (by decide)
    (fin9_cases _
      node_1546
      node_1603
      (invalid_excluded a [5,4,2] (by decide +kernel))
      (invalid_excluded a [5,4,3] (by decide +kernel))
      (invalid_excluded a [5,4,4] (by decide +kernel))
      (invalid_excluded a [5,4,5] (by decide +kernel))
      node_1604
      node_1618
      node_1632)

theorem node_1650 : Excluded a [5,6] :=
  predecessor_excluded a [5,6] 2 6 0 1 (by decide) (by decide +kernel)

theorem node_1653 : Excluded a [5,7,0,1] :=
  predecessor_excluded a [5,7,0,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_1654 : Excluded a [5,7,0,2] :=
  source_excluded a [5,7,0,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1656 : Excluded a [5,7,0,6,1] :=
  predecessor_excluded a [5,7,0,6,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_1657 : Excluded a [5,7,0,6,3] :=
  source_excluded a [5,7,0,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1659 : Excluded a [5,7,0,6,8,1] :=
  source_excluded a [5,7,0,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1661 : Excluded a [5,7,0,6,8,2,1] :=
  source_excluded a [5,7,0,6,8,2,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1662 : Excluded a [5,7,0,6,8,2,3] :=
  predecessor_excluded a [5,7,0,6,8,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_1663 : Excluded a [5,7,0,6,8,2,4] :=
  source_excluded a [5,7,0,6,8,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1660 : Excluded a [5,7,0,6,8,2] :=
  branch_excluded a [5,7,0,6,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,6,8,2,0] (by decide +kernel))
      node_1661
      (invalid_excluded a [5,7,0,6,8,2,2] (by decide +kernel))
      node_1662
      node_1663
      (invalid_excluded a [5,7,0,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,8,2,8] (by decide +kernel)))

theorem node_1664 : Excluded a [5,7,0,6,8,3] :=
  source_excluded a [5,7,0,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1665 : Excluded a [5,7,0,6,8,4] :=
  source_excluded a [5,7,0,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1658 : Excluded a [5,7,0,6,8] :=
  branch_excluded a [5,7,0,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,6,8,0] (by decide +kernel))
      node_1659
      node_1660
      node_1664
      node_1665
      (invalid_excluded a [5,7,0,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,8,8] (by decide +kernel)))

theorem node_1655 : Excluded a [5,7,0,6] :=
  branch_excluded a [5,7,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,6,0] (by decide +kernel))
      node_1656
      (invalid_excluded a [5,7,0,6,2] (by decide +kernel))
      node_1657
      (invalid_excluded a [5,7,0,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,7] (by decide +kernel))
      node_1658)

theorem node_1667 : Excluded a [5,7,0,8,1] :=
  predecessor_excluded a [5,7,0,8,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_1668 : Excluded a [5,7,0,8,3] :=
  source_excluded a [5,7,0,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1670 : Excluded a [5,7,0,8,6,1] :=
  source_excluded a [5,7,0,8,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1671 : Excluded a [5,7,0,8,6,2] :=
  source_excluded a [5,7,0,8,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1673 : Excluded a [5,7,0,8,6,3,1] :=
  source_excluded a [5,7,0,8,6,3,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1674 : Excluded a [5,7,0,8,6,3,2] :=
  source_excluded a [5,7,0,8,6,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1675 : Excluded a [5,7,0,8,6,3,4] :=
  predecessor_excluded a [5,7,0,8,6,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_1672 : Excluded a [5,7,0,8,6,3] :=
  branch_excluded a [5,7,0,8,6,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,8,6,3,0] (by decide +kernel))
      node_1673
      node_1674
      (invalid_excluded a [5,7,0,8,6,3,3] (by decide +kernel))
      node_1675
      (invalid_excluded a [5,7,0,8,6,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,6,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,6,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,6,3,8] (by decide +kernel)))

theorem node_1676 : Excluded a [5,7,0,8,6,4] :=
  source_excluded a [5,7,0,8,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_1669 : Excluded a [5,7,0,8,6] :=
  branch_excluded a [5,7,0,8,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,8,6,0] (by decide +kernel))
      node_1670
      node_1671
      node_1672
      node_1676
      (invalid_excluded a [5,7,0,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,6,8] (by decide +kernel)))

theorem node_1666 : Excluded a [5,7,0,8] :=
  branch_excluded a [5,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,8,0] (by decide +kernel))
      node_1667
      (invalid_excluded a [5,7,0,8,2] (by decide +kernel))
      node_1668
      (invalid_excluded a [5,7,0,8,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,5] (by decide +kernel))
      node_1669
      (invalid_excluded a [5,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,8] (by decide +kernel)))

theorem node_1652 : Excluded a [5,7,0] :=
  branch_excluded a [5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,0] (by decide +kernel))
      node_1653
      node_1654
      (invalid_excluded a [5,7,0,3] (by decide +kernel))
      (invalid_excluded a [5,7,0,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,5] (by decide +kernel))
      node_1655
      (invalid_excluded a [5,7,0,7] (by decide +kernel))
      node_1666)

theorem node_1678 : Excluded a [5,7,1,0] :=
  predecessor_excluded a [5,7,1,0] 4 0 2 3 (by decide) (by decide +kernel)

theorem node_1679 : Excluded a [5,7,1,2] :=
  source_excluded a [5,7,1,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1681 : Excluded a [5,7,1,6,0] :=
  predecessor_excluded a [5,7,1,6,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_1682 : Excluded a [5,7,1,6,3] :=
  source_excluded a [5,7,1,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1684 : Excluded a [5,7,1,6,8,0] :=
  predecessor_excluded a [5,7,1,6,8,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1686 : Excluded a [5,7,1,6,8,2,0] :=
  source_excluded a [5,7,1,6,8,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1687 : Excluded a [5,7,1,6,8,2,3] :=
  predecessor_excluded a [5,7,1,6,8,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_1688 : Excluded a [5,7,1,6,8,2,4] :=
  source_excluded a [5,7,1,6,8,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1685 : Excluded a [5,7,1,6,8,2] :=
  branch_excluded a [5,7,1,6,8,2] (by decide)
    (fin9_cases _
      node_1686
      (invalid_excluded a [5,7,1,6,8,2,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,8,2,2] (by decide +kernel))
      node_1687
      node_1688
      (invalid_excluded a [5,7,1,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,8,2,8] (by decide +kernel)))

theorem node_1689 : Excluded a [5,7,1,6,8,3] :=
  source_excluded a [5,7,1,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1690 : Excluded a [5,7,1,6,8,4] :=
  source_excluded a [5,7,1,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1683 : Excluded a [5,7,1,6,8] :=
  branch_excluded a [5,7,1,6,8] (by decide)
    (fin9_cases _
      node_1684
      (invalid_excluded a [5,7,1,6,8,1] (by decide +kernel))
      node_1685
      node_1689
      node_1690
      (invalid_excluded a [5,7,1,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,8,8] (by decide +kernel)))

theorem node_1680 : Excluded a [5,7,1,6] :=
  branch_excluded a [5,7,1,6] (by decide)
    (fin9_cases _
      node_1681
      (invalid_excluded a [5,7,1,6,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2] (by decide +kernel))
      node_1682
      (invalid_excluded a [5,7,1,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,7] (by decide +kernel))
      node_1683)

theorem node_1692 : Excluded a [5,7,1,8,0] :=
  predecessor_excluded a [5,7,1,8,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_1693 : Excluded a [5,7,1,8,3] :=
  source_excluded a [5,7,1,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1695 : Excluded a [5,7,1,8,6,0] :=
  predecessor_excluded a [5,7,1,8,6,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1696 : Excluded a [5,7,1,8,6,2] :=
  source_excluded a [5,7,1,8,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1698 : Excluded a [5,7,1,8,6,3,0] :=
  source_excluded a [5,7,1,8,6,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1699 : Excluded a [5,7,1,8,6,3,2] :=
  source_excluded a [5,7,1,8,6,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1700 : Excluded a [5,7,1,8,6,3,4] :=
  predecessor_excluded a [5,7,1,8,6,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_1697 : Excluded a [5,7,1,8,6,3] :=
  branch_excluded a [5,7,1,8,6,3] (by decide)
    (fin9_cases _
      node_1698
      (invalid_excluded a [5,7,1,8,6,3,1] (by decide +kernel))
      node_1699
      (invalid_excluded a [5,7,1,8,6,3,3] (by decide +kernel))
      node_1700
      (invalid_excluded a [5,7,1,8,6,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,6,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,6,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,6,3,8] (by decide +kernel)))

theorem node_1701 : Excluded a [5,7,1,8,6,4] :=
  source_excluded a [5,7,1,8,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_1694 : Excluded a [5,7,1,8,6] :=
  branch_excluded a [5,7,1,8,6] (by decide)
    (fin9_cases _
      node_1695
      (invalid_excluded a [5,7,1,8,6,1] (by decide +kernel))
      node_1696
      node_1697
      node_1701
      (invalid_excluded a [5,7,1,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,6,8] (by decide +kernel)))

theorem node_1691 : Excluded a [5,7,1,8] :=
  branch_excluded a [5,7,1,8] (by decide)
    (fin9_cases _
      node_1692
      (invalid_excluded a [5,7,1,8,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,2] (by decide +kernel))
      node_1693
      (invalid_excluded a [5,7,1,8,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,5] (by decide +kernel))
      node_1694
      (invalid_excluded a [5,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,8] (by decide +kernel)))

theorem node_1677 : Excluded a [5,7,1] :=
  branch_excluded a [5,7,1] (by decide)
    (fin9_cases _
      node_1678
      (invalid_excluded a [5,7,1,1] (by decide +kernel))
      node_1679
      (invalid_excluded a [5,7,1,3] (by decide +kernel))
      (invalid_excluded a [5,7,1,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,5] (by decide +kernel))
      node_1680
      (invalid_excluded a [5,7,1,7] (by decide +kernel))
      node_1691)

theorem node_1702 : Excluded a [5,7,4] :=
  source_excluded a [5,7,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_1705 : Excluded a [5,7,6,0,1] :=
  predecessor_excluded a [5,7,6,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1706 : Excluded a [5,7,6,0,3] :=
  source_excluded a [5,7,6,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1708 : Excluded a [5,7,6,0,8,1] :=
  source_excluded a [5,7,6,0,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1709 : Excluded a [5,7,6,0,8,2] :=
  source_excluded a [5,7,6,0,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1710 : Excluded a [5,7,6,0,8,3] :=
  source_excluded a [5,7,6,0,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1712 : Excluded a [5,7,6,0,8,4,1] :=
  source_excluded a [5,7,6,0,8,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1713 : Excluded a [5,7,6,0,8,4,2] :=
  predecessor_excluded a [5,7,6,0,8,4,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_1714 : Excluded a [5,7,6,0,8,4,3] :=
  source_excluded a [5,7,6,0,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1711 : Excluded a [5,7,6,0,8,4] :=
  branch_excluded a [5,7,6,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,6,0,8,4,0] (by decide +kernel))
      node_1712
      node_1713
      node_1714
      (invalid_excluded a [5,7,6,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,0,8,4,8] (by decide +kernel)))

theorem node_1707 : Excluded a [5,7,6,0,8] :=
  branch_excluded a [5,7,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,6,0,8,0] (by decide +kernel))
      node_1708
      node_1709
      node_1710
      node_1711
      (invalid_excluded a [5,7,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,0,8,8] (by decide +kernel)))

theorem node_1704 : Excluded a [5,7,6,0] :=
  branch_excluded a [5,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,6,0,0] (by decide +kernel))
      node_1705
      (invalid_excluded a [5,7,6,0,2] (by decide +kernel))
      node_1706
      (invalid_excluded a [5,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,0,7] (by decide +kernel))
      node_1707)

theorem node_1716 : Excluded a [5,7,6,1,0] :=
  predecessor_excluded a [5,7,6,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_1717 : Excluded a [5,7,6,1,3] :=
  source_excluded a [5,7,6,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1719 : Excluded a [5,7,6,1,8,0] :=
  predecessor_excluded a [5,7,6,1,8,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1720 : Excluded a [5,7,6,1,8,2] :=
  source_excluded a [5,7,6,1,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1721 : Excluded a [5,7,6,1,8,3] :=
  source_excluded a [5,7,6,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1723 : Excluded a [5,7,6,1,8,4,0] :=
  source_excluded a [5,7,6,1,8,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1724 : Excluded a [5,7,6,1,8,4,2] :=
  predecessor_excluded a [5,7,6,1,8,4,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_1725 : Excluded a [5,7,6,1,8,4,3] :=
  source_excluded a [5,7,6,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1722 : Excluded a [5,7,6,1,8,4] :=
  branch_excluded a [5,7,6,1,8,4] (by decide)
    (fin9_cases _
      node_1723
      (invalid_excluded a [5,7,6,1,8,4,1] (by decide +kernel))
      node_1724
      node_1725
      (invalid_excluded a [5,7,6,1,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,8] (by decide +kernel)))

theorem node_1718 : Excluded a [5,7,6,1,8] :=
  branch_excluded a [5,7,6,1,8] (by decide)
    (fin9_cases _
      node_1719
      (invalid_excluded a [5,7,6,1,8,1] (by decide +kernel))
      node_1720
      node_1721
      node_1722
      (invalid_excluded a [5,7,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,8] (by decide +kernel)))

theorem node_1715 : Excluded a [5,7,6,1] :=
  branch_excluded a [5,7,6,1] (by decide)
    (fin9_cases _
      node_1716
      (invalid_excluded a [5,7,6,1,1] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,2] (by decide +kernel))
      node_1717
      (invalid_excluded a [5,7,6,1,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,7] (by decide +kernel))
      node_1718)

theorem node_1726 : Excluded a [5,7,6,2] :=
  source_excluded a [5,7,6,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1729 : Excluded a [5,7,6,8,0,1] :=
  source_excluded a [5,7,6,8,0,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1730 : Excluded a [5,7,6,8,0,2] :=
  source_excluded a [5,7,6,8,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1731 : Excluded a [5,7,6,8,0,3] :=
  source_excluded a [5,7,6,8,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1733 : Excluded a [5,7,6,8,0,4,1] :=
  source_excluded a [5,7,6,8,0,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1734 : Excluded a [5,7,6,8,0,4,2] :=
  predecessor_excluded a [5,7,6,8,0,4,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_1735 : Excluded a [5,7,6,8,0,4,3] :=
  source_excluded a [5,7,6,8,0,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1732 : Excluded a [5,7,6,8,0,4] :=
  branch_excluded a [5,7,6,8,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,6,8,0,4,0] (by decide +kernel))
      node_1733
      node_1734
      node_1735
      (invalid_excluded a [5,7,6,8,0,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,0,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,0,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,0,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,0,4,8] (by decide +kernel)))

theorem node_1728 : Excluded a [5,7,6,8,0] :=
  branch_excluded a [5,7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,6,8,0,0] (by decide +kernel))
      node_1729
      node_1730
      node_1731
      node_1732
      (invalid_excluded a [5,7,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,0,8] (by decide +kernel)))

theorem node_1737 : Excluded a [5,7,6,8,1,0] :=
  predecessor_excluded a [5,7,6,8,1,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1738 : Excluded a [5,7,6,8,1,2] :=
  source_excluded a [5,7,6,8,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1739 : Excluded a [5,7,6,8,1,3] :=
  source_excluded a [5,7,6,8,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1741 : Excluded a [5,7,6,8,1,4,0] :=
  source_excluded a [5,7,6,8,1,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1742 : Excluded a [5,7,6,8,1,4,2] :=
  predecessor_excluded a [5,7,6,8,1,4,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_1743 : Excluded a [5,7,6,8,1,4,3] :=
  source_excluded a [5,7,6,8,1,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1740 : Excluded a [5,7,6,8,1,4] :=
  branch_excluded a [5,7,6,8,1,4] (by decide)
    (fin9_cases _
      node_1741
      (invalid_excluded a [5,7,6,8,1,4,1] (by decide +kernel))
      node_1742
      node_1743
      (invalid_excluded a [5,7,6,8,1,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,1,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,1,4,8] (by decide +kernel)))

theorem node_1736 : Excluded a [5,7,6,8,1] :=
  branch_excluded a [5,7,6,8,1] (by decide)
    (fin9_cases _
      node_1737
      (invalid_excluded a [5,7,6,8,1,1] (by decide +kernel))
      node_1738
      node_1739
      node_1740
      (invalid_excluded a [5,7,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,1,8] (by decide +kernel)))

theorem node_1744 : Excluded a [5,7,6,8,3] :=
  source_excluded a [5,7,6,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1727 : Excluded a [5,7,6,8] :=
  branch_excluded a [5,7,6,8] (by decide)
    (fin9_cases _
      node_1728
      node_1736
      (invalid_excluded a [5,7,6,8,2] (by decide +kernel))
      node_1744
      (invalid_excluded a [5,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,8] (by decide +kernel)))

theorem node_1703 : Excluded a [5,7,6] :=
  branch_excluded a [5,7,6] (by decide)
    (fin9_cases _
      node_1704
      node_1715
      node_1726
      (invalid_excluded a [5,7,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,7] (by decide +kernel))
      node_1727)

theorem node_1747 : Excluded a [5,7,8,0,1] :=
  predecessor_excluded a [5,7,8,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1748 : Excluded a [5,7,8,0,3] :=
  source_excluded a [5,7,8,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1750 : Excluded a [5,7,8,0,6,1] :=
  source_excluded a [5,7,8,0,6,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1751 : Excluded a [5,7,8,0,6,2] :=
  source_excluded a [5,7,8,0,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1753 : Excluded a [5,7,8,0,6,3,1] :=
  source_excluded a [5,7,8,0,6,3,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1754 : Excluded a [5,7,8,0,6,3,2] :=
  source_excluded a [5,7,8,0,6,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1755 : Excluded a [5,7,8,0,6,3,4] :=
  predecessor_excluded a [5,7,8,0,6,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_1752 : Excluded a [5,7,8,0,6,3] :=
  branch_excluded a [5,7,8,0,6,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,8,0,6,3,0] (by decide +kernel))
      node_1753
      node_1754
      (invalid_excluded a [5,7,8,0,6,3,3] (by decide +kernel))
      node_1755
      (invalid_excluded a [5,7,8,0,6,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,0,6,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,0,6,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,0,6,3,8] (by decide +kernel)))

theorem node_1756 : Excluded a [5,7,8,0,6,4] :=
  source_excluded a [5,7,8,0,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_1749 : Excluded a [5,7,8,0,6] :=
  branch_excluded a [5,7,8,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,8,0,6,0] (by decide +kernel))
      node_1750
      node_1751
      node_1752
      node_1756
      (invalid_excluded a [5,7,8,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,0,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,0,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,0,6,8] (by decide +kernel)))

theorem node_1746 : Excluded a [5,7,8,0] :=
  branch_excluded a [5,7,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,8,0,0] (by decide +kernel))
      node_1747
      (invalid_excluded a [5,7,8,0,2] (by decide +kernel))
      node_1748
      (invalid_excluded a [5,7,8,0,4] (by decide +kernel))
      (invalid_excluded a [5,7,8,0,5] (by decide +kernel))
      node_1749
      (invalid_excluded a [5,7,8,0,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,0,8] (by decide +kernel)))

theorem node_1758 : Excluded a [5,7,8,1,0] :=
  predecessor_excluded a [5,7,8,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_1759 : Excluded a [5,7,8,1,3] :=
  source_excluded a [5,7,8,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1761 : Excluded a [5,7,8,1,6,0] :=
  predecessor_excluded a [5,7,8,1,6,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1762 : Excluded a [5,7,8,1,6,2] :=
  source_excluded a [5,7,8,1,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1764 : Excluded a [5,7,8,1,6,3,0] :=
  source_excluded a [5,7,8,1,6,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1765 : Excluded a [5,7,8,1,6,3,2] :=
  source_excluded a [5,7,8,1,6,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_1766 : Excluded a [5,7,8,1,6,3,4] :=
  predecessor_excluded a [5,7,8,1,6,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_1763 : Excluded a [5,7,8,1,6,3] :=
  branch_excluded a [5,7,8,1,6,3] (by decide)
    (fin9_cases _
      node_1764
      (invalid_excluded a [5,7,8,1,6,3,1] (by decide +kernel))
      node_1765
      (invalid_excluded a [5,7,8,1,6,3,3] (by decide +kernel))
      node_1766
      (invalid_excluded a [5,7,8,1,6,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,6,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,6,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,6,3,8] (by decide +kernel)))

theorem node_1767 : Excluded a [5,7,8,1,6,4] :=
  source_excluded a [5,7,8,1,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_1760 : Excluded a [5,7,8,1,6] :=
  branch_excluded a [5,7,8,1,6] (by decide)
    (fin9_cases _
      node_1761
      (invalid_excluded a [5,7,8,1,6,1] (by decide +kernel))
      node_1762
      node_1763
      node_1767
      (invalid_excluded a [5,7,8,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,6,8] (by decide +kernel)))

theorem node_1757 : Excluded a [5,7,8,1] :=
  branch_excluded a [5,7,8,1] (by decide)
    (fin9_cases _
      node_1758
      (invalid_excluded a [5,7,8,1,1] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2] (by decide +kernel))
      node_1759
      (invalid_excluded a [5,7,8,1,4] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,5] (by decide +kernel))
      node_1760
      (invalid_excluded a [5,7,8,1,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,8] (by decide +kernel)))

theorem node_1768 : Excluded a [5,7,8,2] :=
  source_excluded a [5,7,8,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1771 : Excluded a [5,7,8,6,0,1] :=
  source_excluded a [5,7,8,6,0,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1773 : Excluded a [5,7,8,6,0,2,1] :=
  source_excluded a [5,7,8,6,0,2,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1774 : Excluded a [5,7,8,6,0,2,3] :=
  predecessor_excluded a [5,7,8,6,0,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_1775 : Excluded a [5,7,8,6,0,2,4] :=
  source_excluded a [5,7,8,6,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1772 : Excluded a [5,7,8,6,0,2] :=
  branch_excluded a [5,7,8,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,8,6,0,2,0] (by decide +kernel))
      node_1773
      (invalid_excluded a [5,7,8,6,0,2,2] (by decide +kernel))
      node_1774
      node_1775
      (invalid_excluded a [5,7,8,6,0,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,0,2,8] (by decide +kernel)))

theorem node_1776 : Excluded a [5,7,8,6,0,3] :=
  source_excluded a [5,7,8,6,0,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1777 : Excluded a [5,7,8,6,0,4] :=
  source_excluded a [5,7,8,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1770 : Excluded a [5,7,8,6,0] :=
  branch_excluded a [5,7,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,8,6,0,0] (by decide +kernel))
      node_1771
      node_1772
      node_1776
      node_1777
      (invalid_excluded a [5,7,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,0,8] (by decide +kernel)))

theorem node_1779 : Excluded a [5,7,8,6,1,0] :=
  predecessor_excluded a [5,7,8,6,1,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1781 : Excluded a [5,7,8,6,1,2,0] :=
  source_excluded a [5,7,8,6,1,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1782 : Excluded a [5,7,8,6,1,2,3] :=
  predecessor_excluded a [5,7,8,6,1,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_1783 : Excluded a [5,7,8,6,1,2,4] :=
  source_excluded a [5,7,8,6,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1780 : Excluded a [5,7,8,6,1,2] :=
  branch_excluded a [5,7,8,6,1,2] (by decide)
    (fin9_cases _
      node_1781
      (invalid_excluded a [5,7,8,6,1,2,1] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,1,2,2] (by decide +kernel))
      node_1782
      node_1783
      (invalid_excluded a [5,7,8,6,1,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,1,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,1,2,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,1,2,8] (by decide +kernel)))

theorem node_1784 : Excluded a [5,7,8,6,1,3] :=
  source_excluded a [5,7,8,6,1,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1785 : Excluded a [5,7,8,6,1,4] :=
  source_excluded a [5,7,8,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1778 : Excluded a [5,7,8,6,1] :=
  branch_excluded a [5,7,8,6,1] (by decide)
    (fin9_cases _
      node_1779
      (invalid_excluded a [5,7,8,6,1,1] (by decide +kernel))
      node_1780
      node_1784
      node_1785
      (invalid_excluded a [5,7,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,1,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,1,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,1,8] (by decide +kernel)))

theorem node_1786 : Excluded a [5,7,8,6,3] :=
  source_excluded a [5,7,8,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1769 : Excluded a [5,7,8,6] :=
  branch_excluded a [5,7,8,6] (by decide)
    (fin9_cases _
      node_1770
      node_1778
      (invalid_excluded a [5,7,8,6,2] (by decide +kernel))
      node_1786
      (invalid_excluded a [5,7,8,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,8] (by decide +kernel)))

theorem node_1745 : Excluded a [5,7,8] :=
  branch_excluded a [5,7,8] (by decide)
    (fin9_cases _
      node_1746
      node_1757
      node_1768
      (invalid_excluded a [5,7,8,3] (by decide +kernel))
      (invalid_excluded a [5,7,8,4] (by decide +kernel))
      (invalid_excluded a [5,7,8,5] (by decide +kernel))
      node_1769
      (invalid_excluded a [5,7,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,8] (by decide +kernel)))

theorem node_1651 : Excluded a [5,7] :=
  branch_excluded a [5,7] (by decide)
    (fin9_cases _
      node_1652
      node_1677
      (invalid_excluded a [5,7,2] (by decide +kernel))
      (invalid_excluded a [5,7,3] (by decide +kernel))
      node_1702
      (invalid_excluded a [5,7,5] (by decide +kernel))
      node_1703
      (invalid_excluded a [5,7,7] (by decide +kernel))
      node_1745)

theorem node_1787 : Excluded a [5,8] :=
  predecessor_excluded a [5,8] 2 5 1 0 (by decide) (by decide +kernel)

theorem node_1361 : Excluded a [5] :=
  branch_excluded a [5] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0] (by decide +kernel))
      (invalid_excluded a [5,1] (by decide +kernel))
      node_1362
      node_1460
      node_1545
      (invalid_excluded a [5,5] (by decide +kernel))
      node_1650
      node_1651
      node_1787)

theorem node_1790 : Excluded a [6,2,0] :=
  source_excluded a [6,2,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_1791 : Excluded a [6,2,1] :=
  predecessor_excluded a [6,2,1] 3 1 1 2 (by decide) (by decide +kernel)

theorem node_1792 : Excluded a [6,2,4] :=
  source_excluded a [6,2,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_1795 : Excluded a [6,2,5,0,1] :=
  source_excluded a [6,2,5,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1796 : Excluded a [6,2,5,0,3] :=
  source_excluded a [6,2,5,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1798 : Excluded a [6,2,5,0,7,1] :=
  source_excluded a [6,2,5,0,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1799 : Excluded a [6,2,5,0,7,3] :=
  source_excluded a [6,2,5,0,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1800 : Excluded a [6,2,5,0,7,4] :=
  predecessor_excluded a [6,2,5,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1802 : Excluded a [6,2,5,0,7,8,1] :=
  source_excluded a [6,2,5,0,7,8,1] 0 2 6 (by decide) (by decide +kernel)

def b_1805 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 2
  | 2 => 5
  | 3 => 0
  | 4 => 7
  | 5 => 8
  | 6 => 3
  | 7 => 1
  | 8 => 4
  | _ => 0

def cert_1805 : LosingRegion (edgeOf a b_1805) 0 :=
  losingMask a b_1805 0 1809875925553945898910720
    (by decide +kernel) (by decide +kernel)

theorem node_1805 : Excluded a [6,2,5,0,7,8,3,1,4] :=
  losing_excluded a [6,2,5,0,7,8,3,1,4] (by decide) b_1805 (by decide +kernel) 2 0 3 cert_1805 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1805 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1809875925553945898910720 2 3; decide +kernel)

theorem node_1804 : Excluded a [6,2,5,0,7,8,3,1] :=
  branch_excluded a [6,2,5,0,7,8,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,5,0,7,8,3,1,0] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,8,3,1,1] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,8,3,1,2] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,8,3,1,3] (by decide +kernel))
      node_1805
      (invalid_excluded a [6,2,5,0,7,8,3,1,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,8,3,1,6] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,8,3,1,7] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,8,3,1,8] (by decide +kernel)))

theorem node_1806 : Excluded a [6,2,5,0,7,8,3,4] :=
  predecessor_excluded a [6,2,5,0,7,8,3,4] 0 4 6 7 (by decide) (by decide +kernel)

theorem node_1803 : Excluded a [6,2,5,0,7,8,3] :=
  branch_excluded a [6,2,5,0,7,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,5,0,7,8,3,0] (by decide +kernel))
      node_1804
      (invalid_excluded a [6,2,5,0,7,8,3,2] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,8,3,3] (by decide +kernel))
      node_1806
      (invalid_excluded a [6,2,5,0,7,8,3,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,8,3,6] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,8,3,7] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,8,3,8] (by decide +kernel)))

theorem node_1807 : Excluded a [6,2,5,0,7,8,4] :=
  source_excluded a [6,2,5,0,7,8,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1801 : Excluded a [6,2,5,0,7,8] :=
  branch_excluded a [6,2,5,0,7,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,5,0,7,8,0] (by decide +kernel))
      node_1802
      (invalid_excluded a [6,2,5,0,7,8,2] (by decide +kernel))
      node_1803
      node_1807
      (invalid_excluded a [6,2,5,0,7,8,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,8,6] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,8,7] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,8,8] (by decide +kernel)))

theorem node_1797 : Excluded a [6,2,5,0,7] :=
  branch_excluded a [6,2,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,5,0,7,0] (by decide +kernel))
      node_1798
      (invalid_excluded a [6,2,5,0,7,2] (by decide +kernel))
      node_1799
      node_1800
      (invalid_excluded a [6,2,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,7] (by decide +kernel))
      node_1801)

theorem node_1808 : Excluded a [6,2,5,0,8] :=
  predecessor_excluded a [6,2,5,0,8] 0 5 4 2 (by decide) (by decide +kernel)

theorem node_1794 : Excluded a [6,2,5,0] :=
  branch_excluded a [6,2,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,5,0,0] (by decide +kernel))
      node_1795
      (invalid_excluded a [6,2,5,0,2] (by decide +kernel))
      node_1796
      (invalid_excluded a [6,2,5,0,4] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,6] (by decide +kernel))
      node_1797
      node_1808)

theorem node_1809 : Excluded a [6,2,5,1] :=
  predecessor_excluded a [6,2,5,1] 0 2 3 1 (by decide) (by decide +kernel)

theorem node_1811 : Excluded a [6,2,5,7,0] :=
  source_excluded a [6,2,5,7,0] 1 3 4 (by decide) (by decide +kernel)

theorem node_1812 : Excluded a [6,2,5,7,1] :=
  source_excluded a [6,2,5,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1813 : Excluded a [6,2,5,7,3] :=
  source_excluded a [6,2,5,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1814 : Excluded a [6,2,5,7,8] :=
  predecessor_excluded a [6,2,5,7,8] 0 5 4 2 (by decide) (by decide +kernel)

theorem node_1810 : Excluded a [6,2,5,7] :=
  branch_excluded a [6,2,5,7] (by decide)
    (fin9_cases _
      node_1811
      node_1812
      (invalid_excluded a [6,2,5,7,2] (by decide +kernel))
      node_1813
      (invalid_excluded a [6,2,5,7,4] (by decide +kernel))
      (invalid_excluded a [6,2,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,2,5,7,7] (by decide +kernel))
      node_1814)

theorem node_1816 : Excluded a [6,2,5,8,0] :=
  source_excluded a [6,2,5,8,0] 1 3 4 (by decide) (by decide +kernel)

theorem node_1817 : Excluded a [6,2,5,8,1] :=
  source_excluded a [6,2,5,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1818 : Excluded a [6,2,5,8,3] :=
  source_excluded a [6,2,5,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1820 : Excluded a [6,2,5,8,7,0] :=
  source_excluded a [6,2,5,8,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1821 : Excluded a [6,2,5,8,7,1] :=
  source_excluded a [6,2,5,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1822 : Excluded a [6,2,5,8,7,3] :=
  source_excluded a [6,2,5,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1823 : Excluded a [6,2,5,8,7,4] :=
  predecessor_excluded a [6,2,5,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1819 : Excluded a [6,2,5,8,7] :=
  branch_excluded a [6,2,5,8,7] (by decide)
    (fin9_cases _
      node_1820
      node_1821
      (invalid_excluded a [6,2,5,8,7,2] (by decide +kernel))
      node_1822
      node_1823
      (invalid_excluded a [6,2,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,2,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,2,5,8,7,8] (by decide +kernel)))

theorem node_1815 : Excluded a [6,2,5,8] :=
  branch_excluded a [6,2,5,8] (by decide)
    (fin9_cases _
      node_1816
      node_1817
      (invalid_excluded a [6,2,5,8,2] (by decide +kernel))
      node_1818
      (invalid_excluded a [6,2,5,8,4] (by decide +kernel))
      (invalid_excluded a [6,2,5,8,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,8,6] (by decide +kernel))
      node_1819
      (invalid_excluded a [6,2,5,8,8] (by decide +kernel)))

theorem node_1793 : Excluded a [6,2,5] :=
  branch_excluded a [6,2,5] (by decide)
    (fin9_cases _
      node_1794
      node_1809
      (invalid_excluded a [6,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,2,5,3] (by decide +kernel))
      (invalid_excluded a [6,2,5,4] (by decide +kernel))
      (invalid_excluded a [6,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,6] (by decide +kernel))
      node_1810
      node_1815)

theorem node_1826 : Excluded a [6,2,7,0,1] :=
  source_excluded a [6,2,7,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1827 : Excluded a [6,2,7,0,3] :=
  source_excluded a [6,2,7,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1829 : Excluded a [6,2,7,0,5,1] :=
  source_excluded a [6,2,7,0,5,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1830 : Excluded a [6,2,7,0,5,3] :=
  predecessor_excluded a [6,2,7,0,5,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_1832 : Excluded a [6,2,7,0,5,4,1] :=
  source_excluded a [6,2,7,0,5,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1833 : Excluded a [6,2,7,0,5,4,3] :=
  source_excluded a [6,2,7,0,5,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1834 : Excluded a [6,2,7,0,5,4,8] :=
  source_excluded a [6,2,7,0,5,4,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_1831 : Excluded a [6,2,7,0,5,4] :=
  branch_excluded a [6,2,7,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,5,4,0] (by decide +kernel))
      node_1832
      (invalid_excluded a [6,2,7,0,5,4,2] (by decide +kernel))
      node_1833
      (invalid_excluded a [6,2,7,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,4,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,4,7] (by decide +kernel))
      node_1834)

theorem node_1836 : Excluded a [6,2,7,0,5,8,1] :=
  source_excluded a [6,2,7,0,5,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1837 : Excluded a [6,2,7,0,5,8,3] :=
  source_excluded a [6,2,7,0,5,8,3] 2 0 6 (by decide) (by decide +kernel)

def b_1840 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 2
  | 2 => 7
  | 3 => 0
  | 4 => 5
  | 5 => 8
  | 6 => 4
  | 7 => 1
  | 8 => 3
  | _ => 0

def cert_1840 : LosingRegion (edgeOf a b_1840) 0 :=
  losingMask a b_1840 0 1266796847325703025198080
    (by decide +kernel) (by decide +kernel)

theorem node_1840 : Excluded a [6,2,7,0,5,8,4,1,3] :=
  losing_excluded a [6,2,7,0,5,8,4,1,3] (by decide) b_1840 (by decide +kernel) 4 0 1 cert_1840 (by change 4 ≠ 0 ∧ ¬ edgeOf a b_1840 4 0 ∧ 1 ≠ 4 ∧ maskRegion 1266796847325703025198080 4 1; decide +kernel)

theorem node_1839 : Excluded a [6,2,7,0,5,8,4,1] :=
  branch_excluded a [6,2,7,0,5,8,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,5,8,4,1,0] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,8,4,1,2] (by decide +kernel))
      node_1840
      (invalid_excluded a [6,2,7,0,5,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,8,4,1,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,8,4,1,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,8,4,1,8] (by decide +kernel)))

theorem node_1841 : Excluded a [6,2,7,0,5,8,4,3] :=
  source_excluded a [6,2,7,0,5,8,4,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_1838 : Excluded a [6,2,7,0,5,8,4] :=
  branch_excluded a [6,2,7,0,5,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,5,8,4,0] (by decide +kernel))
      node_1839
      (invalid_excluded a [6,2,7,0,5,8,4,2] (by decide +kernel))
      node_1841
      (invalid_excluded a [6,2,7,0,5,8,4,4] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,8,4,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,8,4,8] (by decide +kernel)))

theorem node_1835 : Excluded a [6,2,7,0,5,8] :=
  branch_excluded a [6,2,7,0,5,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,5,8,0] (by decide +kernel))
      node_1836
      (invalid_excluded a [6,2,7,0,5,8,2] (by decide +kernel))
      node_1837
      node_1838
      (invalid_excluded a [6,2,7,0,5,8,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,8,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,8,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,8,8] (by decide +kernel)))

theorem node_1828 : Excluded a [6,2,7,0,5] :=
  branch_excluded a [6,2,7,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,5,0] (by decide +kernel))
      node_1829
      (invalid_excluded a [6,2,7,0,5,2] (by decide +kernel))
      node_1830
      node_1831
      (invalid_excluded a [6,2,7,0,5,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5,7] (by decide +kernel))
      node_1835)

theorem node_1843 : Excluded a [6,2,7,0,8,1] :=
  source_excluded a [6,2,7,0,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1845 : Excluded a [6,2,7,0,8,3,1] :=
  source_excluded a [6,2,7,0,8,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1846 : Excluded a [6,2,7,0,8,3,4] :=
  predecessor_excluded a [6,2,7,0,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

def b_1849 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 2
  | 2 => 7
  | 3 => 0
  | 4 => 8
  | 5 => 3
  | 6 => 5
  | 7 => 1
  | 8 => 4
  | _ => 0

def cert_1849 : LosingRegion (edgeOf a b_1849) 0 :=
  losingMask a b_1849 0 1805153664868490243212288
    (by decide +kernel) (by decide +kernel)

theorem node_1849 : Excluded a [6,2,7,0,8,3,5,1,4] :=
  losing_excluded a [6,2,7,0,8,3,5,1,4] (by decide) b_1849 (by decide +kernel) 2 0 3 cert_1849 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1849 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1805153664868490243212288 2 3; decide +kernel)

theorem node_1848 : Excluded a [6,2,7,0,8,3,5,1] :=
  branch_excluded a [6,2,7,0,8,3,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,8,3,5,1,0] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,5,1,1] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,5,1,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,5,1,3] (by decide +kernel))
      node_1849
      (invalid_excluded a [6,2,7,0,8,3,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,5,1,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,5,1,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,5,1,8] (by decide +kernel)))

theorem node_1850 : Excluded a [6,2,7,0,8,3,5,4] :=
  source_excluded a [6,2,7,0,8,3,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_1847 : Excluded a [6,2,7,0,8,3,5] :=
  branch_excluded a [6,2,7,0,8,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,8,3,5,0] (by decide +kernel))
      node_1848
      (invalid_excluded a [6,2,7,0,8,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,5,3] (by decide +kernel))
      node_1850
      (invalid_excluded a [6,2,7,0,8,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,5,8] (by decide +kernel)))

theorem node_1844 : Excluded a [6,2,7,0,8,3] :=
  branch_excluded a [6,2,7,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,8,3,0] (by decide +kernel))
      node_1845
      (invalid_excluded a [6,2,7,0,8,3,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,3] (by decide +kernel))
      node_1846
      node_1847
      (invalid_excluded a [6,2,7,0,8,3,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,8] (by decide +kernel)))

theorem node_1852 : Excluded a [6,2,7,0,8,4,1] :=
  source_excluded a [6,2,7,0,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1853 : Excluded a [6,2,7,0,8,4,3] :=
  source_excluded a [6,2,7,0,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1856 : Excluded a [6,2,7,0,8,4,5,1,3] :=
  predecessor_excluded a [6,2,7,0,8,4,5,1,3] 0 4 8 5 (by decide) (by decide +kernel)

theorem node_1855 : Excluded a [6,2,7,0,8,4,5,1] :=
  branch_excluded a [6,2,7,0,8,4,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,8,4,5,1,0] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,4,5,1,1] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,4,5,1,2] (by decide +kernel))
      node_1856
      (invalid_excluded a [6,2,7,0,8,4,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,4,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,4,5,1,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,4,5,1,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,4,5,1,8] (by decide +kernel)))

theorem node_1857 : Excluded a [6,2,7,0,8,4,5,3] :=
  source_excluded a [6,2,7,0,8,4,5,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_1854 : Excluded a [6,2,7,0,8,4,5] :=
  branch_excluded a [6,2,7,0,8,4,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,8,4,5,0] (by decide +kernel))
      node_1855
      (invalid_excluded a [6,2,7,0,8,4,5,2] (by decide +kernel))
      node_1857
      (invalid_excluded a [6,2,7,0,8,4,5,4] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,4,5,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,4,5,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,4,5,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,4,5,8] (by decide +kernel)))

theorem node_1851 : Excluded a [6,2,7,0,8,4] :=
  branch_excluded a [6,2,7,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,8,4,0] (by decide +kernel))
      node_1852
      (invalid_excluded a [6,2,7,0,8,4,2] (by decide +kernel))
      node_1853
      (invalid_excluded a [6,2,7,0,8,4,4] (by decide +kernel))
      node_1854
      (invalid_excluded a [6,2,7,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,4,8] (by decide +kernel)))

theorem node_1842 : Excluded a [6,2,7,0,8] :=
  branch_excluded a [6,2,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,8,0] (by decide +kernel))
      node_1843
      (invalid_excluded a [6,2,7,0,8,2] (by decide +kernel))
      node_1844
      node_1851
      (invalid_excluded a [6,2,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,8] (by decide +kernel)))

theorem node_1825 : Excluded a [6,2,7,0] :=
  branch_excluded a [6,2,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,0] (by decide +kernel))
      node_1826
      (invalid_excluded a [6,2,7,0,2] (by decide +kernel))
      node_1827
      (invalid_excluded a [6,2,7,0,4] (by decide +kernel))
      node_1828
      (invalid_excluded a [6,2,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,7] (by decide +kernel))
      node_1842)

theorem node_1858 : Excluded a [6,2,7,1] :=
  predecessor_excluded a [6,2,7,1] 0 2 3 1 (by decide) (by decide +kernel)

theorem node_1860 : Excluded a [6,2,7,5,0] :=
  source_excluded a [6,2,7,5,0] 1 3 4 (by decide) (by decide +kernel)

theorem node_1861 : Excluded a [6,2,7,5,1] :=
  source_excluded a [6,2,7,5,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1862 : Excluded a [6,2,7,5,3] :=
  source_excluded a [6,2,7,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1864 : Excluded a [6,2,7,5,8,0] :=
  source_excluded a [6,2,7,5,8,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1865 : Excluded a [6,2,7,5,8,1] :=
  source_excluded a [6,2,7,5,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1867 : Excluded a [6,2,7,5,8,3,0] :=
  predecessor_excluded a [6,2,7,5,8,3,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_1868 : Excluded a [6,2,7,5,8,3,1] :=
  source_excluded a [6,2,7,5,8,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1869 : Excluded a [6,2,7,5,8,3,4] :=
  predecessor_excluded a [6,2,7,5,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_1866 : Excluded a [6,2,7,5,8,3] :=
  branch_excluded a [6,2,7,5,8,3] (by decide)
    (fin9_cases _
      node_1867
      node_1868
      (invalid_excluded a [6,2,7,5,8,3,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,5,8,3,3] (by decide +kernel))
      node_1869
      (invalid_excluded a [6,2,7,5,8,3,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,5,8,3,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,5,8,3,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,5,8,3,8] (by decide +kernel)))

theorem node_1870 : Excluded a [6,2,7,5,8,4] :=
  source_excluded a [6,2,7,5,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1863 : Excluded a [6,2,7,5,8] :=
  branch_excluded a [6,2,7,5,8] (by decide)
    (fin9_cases _
      node_1864
      node_1865
      (invalid_excluded a [6,2,7,5,8,2] (by decide +kernel))
      node_1866
      node_1870
      (invalid_excluded a [6,2,7,5,8,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,5,8,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,5,8,8] (by decide +kernel)))

theorem node_1859 : Excluded a [6,2,7,5] :=
  branch_excluded a [6,2,7,5] (by decide)
    (fin9_cases _
      node_1860
      node_1861
      (invalid_excluded a [6,2,7,5,2] (by decide +kernel))
      node_1862
      (invalid_excluded a [6,2,7,5,4] (by decide +kernel))
      (invalid_excluded a [6,2,7,5,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,5,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,5,7] (by decide +kernel))
      node_1863)

theorem node_1871 : Excluded a [6,2,7,8] :=
  predecessor_excluded a [6,2,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_1824 : Excluded a [6,2,7] :=
  branch_excluded a [6,2,7] (by decide)
    (fin9_cases _
      node_1825
      node_1858
      (invalid_excluded a [6,2,7,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,3] (by decide +kernel))
      (invalid_excluded a [6,2,7,4] (by decide +kernel))
      node_1859
      (invalid_excluded a [6,2,7,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,7] (by decide +kernel))
      node_1871)

theorem node_1874 : Excluded a [6,2,8,0,1] :=
  source_excluded a [6,2,8,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1875 : Excluded a [6,2,8,0,3] :=
  source_excluded a [6,2,8,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1877 : Excluded a [6,2,8,0,5,1] :=
  source_excluded a [6,2,8,0,5,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1878 : Excluded a [6,2,8,0,5,3] :=
  predecessor_excluded a [6,2,8,0,5,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_1880 : Excluded a [6,2,8,0,5,4,1] :=
  source_excluded a [6,2,8,0,5,4,1] 0 2 6 (by decide) (by decide +kernel)

def b_1883 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 2
  | 2 => 8
  | 3 => 0
  | 4 => 5
  | 5 => 4
  | 6 => 3
  | 7 => 1
  | 8 => 7
  | _ => 0

def cert_1883 : LosingRegion (edgeOf a b_1883) 0 :=
  losingMask a b_1883 0 1564312868447198248961024
    (by decide +kernel) (by decide +kernel)

theorem node_1883 : Excluded a [6,2,8,0,5,4,3,1,7] :=
  losing_excluded a [6,2,8,0,5,4,3,1,7] (by decide) b_1883 (by decide +kernel) 2 0 3 cert_1883 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1883 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1564312868447198248961024 2 3; decide +kernel)

theorem node_1882 : Excluded a [6,2,8,0,5,4,3,1] :=
  branch_excluded a [6,2,8,0,5,4,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,8,0,5,4,3,1,0] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,4,3,1,1] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,4,3,1,2] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,4,3,1,3] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,4,3,1,4] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,4,3,1,5] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,4,3,1,6] (by decide +kernel))
      node_1883
      (invalid_excluded a [6,2,8,0,5,4,3,1,8] (by decide +kernel)))

theorem node_1881 : Excluded a [6,2,8,0,5,4,3] :=
  branch_excluded a [6,2,8,0,5,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,8,0,5,4,3,0] (by decide +kernel))
      node_1882
      (invalid_excluded a [6,2,8,0,5,4,3,2] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,4,3,3] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,4,3,4] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,4,3,5] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,4,3,6] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,4,3,7] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,4,3,8] (by decide +kernel)))

theorem node_1879 : Excluded a [6,2,8,0,5,4] :=
  branch_excluded a [6,2,8,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,8,0,5,4,0] (by decide +kernel))
      node_1880
      (invalid_excluded a [6,2,8,0,5,4,2] (by decide +kernel))
      node_1881
      (invalid_excluded a [6,2,8,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,4,6] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,4,7] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,4,8] (by decide +kernel)))

theorem node_1884 : Excluded a [6,2,8,0,5,7] :=
  source_excluded a [6,2,8,0,5,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1876 : Excluded a [6,2,8,0,5] :=
  branch_excluded a [6,2,8,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,8,0,5,0] (by decide +kernel))
      node_1877
      (invalid_excluded a [6,2,8,0,5,2] (by decide +kernel))
      node_1878
      node_1879
      (invalid_excluded a [6,2,8,0,5,5] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5,6] (by decide +kernel))
      node_1884
      (invalid_excluded a [6,2,8,0,5,8] (by decide +kernel)))

theorem node_1885 : Excluded a [6,2,8,0,7] :=
  predecessor_excluded a [6,2,8,0,7] 0 8 4 2 (by decide) (by decide +kernel)

theorem node_1873 : Excluded a [6,2,8,0] :=
  branch_excluded a [6,2,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,8,0,0] (by decide +kernel))
      node_1874
      (invalid_excluded a [6,2,8,0,2] (by decide +kernel))
      node_1875
      (invalid_excluded a [6,2,8,0,4] (by decide +kernel))
      node_1876
      (invalid_excluded a [6,2,8,0,6] (by decide +kernel))
      node_1885
      (invalid_excluded a [6,2,8,0,8] (by decide +kernel)))

theorem node_1886 : Excluded a [6,2,8,1] :=
  predecessor_excluded a [6,2,8,1] 0 2 3 1 (by decide) (by decide +kernel)

theorem node_1887 : Excluded a [6,2,8,5] :=
  predecessor_excluded a [6,2,8,5] 0 5 2 3 (by decide) (by decide +kernel)

theorem node_1889 : Excluded a [6,2,8,7,0] :=
  source_excluded a [6,2,8,7,0] 1 3 4 (by decide) (by decide +kernel)

theorem node_1890 : Excluded a [6,2,8,7,1] :=
  source_excluded a [6,2,8,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_1891 : Excluded a [6,2,8,7,3] :=
  source_excluded a [6,2,8,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_1893 : Excluded a [6,2,8,7,5,0] :=
  source_excluded a [6,2,8,7,5,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1894 : Excluded a [6,2,8,7,5,1] :=
  source_excluded a [6,2,8,7,5,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1895 : Excluded a [6,2,8,7,5,3] :=
  predecessor_excluded a [6,2,8,7,5,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1897 : Excluded a [6,2,8,7,5,4,0] :=
  predecessor_excluded a [6,2,8,7,5,4,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_1898 : Excluded a [6,2,8,7,5,4,1] :=
  source_excluded a [6,2,8,7,5,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1899 : Excluded a [6,2,8,7,5,4,3] :=
  source_excluded a [6,2,8,7,5,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1896 : Excluded a [6,2,8,7,5,4] :=
  branch_excluded a [6,2,8,7,5,4] (by decide)
    (fin9_cases _
      node_1897
      node_1898
      (invalid_excluded a [6,2,8,7,5,4,2] (by decide +kernel))
      node_1899
      (invalid_excluded a [6,2,8,7,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,5,4,6] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,5,4,7] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,5,4,8] (by decide +kernel)))

theorem node_1892 : Excluded a [6,2,8,7,5] :=
  branch_excluded a [6,2,8,7,5] (by decide)
    (fin9_cases _
      node_1893
      node_1894
      (invalid_excluded a [6,2,8,7,5,2] (by decide +kernel))
      node_1895
      node_1896
      (invalid_excluded a [6,2,8,7,5,5] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,5,6] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,5,7] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,5,8] (by decide +kernel)))

theorem node_1888 : Excluded a [6,2,8,7] :=
  branch_excluded a [6,2,8,7] (by decide)
    (fin9_cases _
      node_1889
      node_1890
      (invalid_excluded a [6,2,8,7,2] (by decide +kernel))
      node_1891
      (invalid_excluded a [6,2,8,7,4] (by decide +kernel))
      node_1892
      (invalid_excluded a [6,2,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,8] (by decide +kernel)))

theorem node_1872 : Excluded a [6,2,8] :=
  branch_excluded a [6,2,8] (by decide)
    (fin9_cases _
      node_1873
      node_1886
      (invalid_excluded a [6,2,8,2] (by decide +kernel))
      (invalid_excluded a [6,2,8,3] (by decide +kernel))
      (invalid_excluded a [6,2,8,4] (by decide +kernel))
      node_1887
      (invalid_excluded a [6,2,8,6] (by decide +kernel))
      node_1888
      (invalid_excluded a [6,2,8,8] (by decide +kernel)))

theorem node_1789 : Excluded a [6,2] :=
  branch_excluded a [6,2] (by decide)
    (fin9_cases _
      node_1790
      node_1791
      (invalid_excluded a [6,2,2] (by decide +kernel))
      (invalid_excluded a [6,2,3] (by decide +kernel))
      node_1792
      node_1793
      (invalid_excluded a [6,2,6] (by decide +kernel))
      node_1824
      node_1872)

theorem node_1901 : Excluded a [6,3,0] :=
  source_excluded a [6,3,0] 1 2 2 (by decide) (by decide +kernel)

theorem node_1902 : Excluded a [6,3,1] :=
  source_excluded a [6,3,1] 2 0 1 (by decide) (by decide +kernel)

theorem node_1903 : Excluded a [6,3,4] :=
  source_excluded a [6,3,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_1905 : Excluded a [6,3,5,0] :=
  source_excluded a [6,3,5,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_1906 : Excluded a [6,3,5,1] :=
  predecessor_excluded a [6,3,5,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_1907 : Excluded a [6,3,5,2] :=
  source_excluded a [6,3,5,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1910 : Excluded a [6,3,5,7,0,1] :=
  source_excluded a [6,3,5,7,0,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1912 : Excluded a [6,3,5,7,0,2,1] :=
  source_excluded a [6,3,5,7,0,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1913 : Excluded a [6,3,5,7,0,2,4] :=
  source_excluded a [6,3,5,7,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1914 : Excluded a [6,3,5,7,0,2,8] :=
  source_excluded a [6,3,5,7,0,2,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_1911 : Excluded a [6,3,5,7,0,2] :=
  branch_excluded a [6,3,5,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,5,7,0,2,0] (by decide +kernel))
      node_1912
      (invalid_excluded a [6,3,5,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,2,3] (by decide +kernel))
      node_1913
      (invalid_excluded a [6,3,5,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,2,7] (by decide +kernel))
      node_1914)

theorem node_1915 : Excluded a [6,3,5,7,0,4] :=
  predecessor_excluded a [6,3,5,7,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_1917 : Excluded a [6,3,5,7,0,8,1] :=
  source_excluded a [6,3,5,7,0,8,1] 0 2 6 (by decide) (by decide +kernel)

def b_1920 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 0
  | 5 => 8
  | 6 => 2
  | 7 => 1
  | 8 => 4
  | _ => 0

def cert_1920 : LosingRegion (edgeOf a b_1920) 0 :=
  losingMask a b_1920 0 1323465317177320491451392
    (by decide +kernel) (by decide +kernel)

theorem node_1920 : Excluded a [6,3,5,7,0,8,2,1,4] :=
  losing_excluded a [6,3,5,7,0,8,2,1,4] (by decide) b_1920 (by decide +kernel) 2 0 1 cert_1920 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1920 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1323465317177320491451392 2 1; decide +kernel)

theorem node_1919 : Excluded a [6,3,5,7,0,8,2,1] :=
  branch_excluded a [6,3,5,7,0,8,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,5,7,0,8,2,1,0] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,8,2,1,1] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,8,2,1,2] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,8,2,1,3] (by decide +kernel))
      node_1920
      (invalid_excluded a [6,3,5,7,0,8,2,1,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,8,2,1,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,8,2,1,7] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,8,2,1,8] (by decide +kernel)))

theorem node_1921 : Excluded a [6,3,5,7,0,8,2,4] :=
  source_excluded a [6,3,5,7,0,8,2,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_1918 : Excluded a [6,3,5,7,0,8,2] :=
  branch_excluded a [6,3,5,7,0,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,5,7,0,8,2,0] (by decide +kernel))
      node_1919
      (invalid_excluded a [6,3,5,7,0,8,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,8,2,3] (by decide +kernel))
      node_1921
      (invalid_excluded a [6,3,5,7,0,8,2,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,8,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,8,2,7] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,8,2,8] (by decide +kernel)))

theorem node_1922 : Excluded a [6,3,5,7,0,8,4] :=
  source_excluded a [6,3,5,7,0,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1916 : Excluded a [6,3,5,7,0,8] :=
  branch_excluded a [6,3,5,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,5,7,0,8,0] (by decide +kernel))
      node_1917
      node_1918
      (invalid_excluded a [6,3,5,7,0,8,3] (by decide +kernel))
      node_1922
      (invalid_excluded a [6,3,5,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,8,8] (by decide +kernel)))

theorem node_1909 : Excluded a [6,3,5,7,0] :=
  branch_excluded a [6,3,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,5,7,0,0] (by decide +kernel))
      node_1910
      node_1911
      (invalid_excluded a [6,3,5,7,0,3] (by decide +kernel))
      node_1915
      (invalid_excluded a [6,3,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,0,7] (by decide +kernel))
      node_1916)

theorem node_1923 : Excluded a [6,3,5,7,1] :=
  predecessor_excluded a [6,3,5,7,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1924 : Excluded a [6,3,5,7,8] :=
  predecessor_excluded a [6,3,5,7,8] 0 5 4 2 (by decide) (by decide +kernel)

theorem node_1908 : Excluded a [6,3,5,7] :=
  branch_excluded a [6,3,5,7] (by decide)
    (fin9_cases _
      node_1909
      node_1923
      (invalid_excluded a [6,3,5,7,2] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,3] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,4] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,7] (by decide +kernel))
      node_1924)

theorem node_1927 : Excluded a [6,3,5,8,0,1] :=
  source_excluded a [6,3,5,8,0,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1929 : Excluded a [6,3,5,8,0,2,1] :=
  source_excluded a [6,3,5,8,0,2,1] 0 2 6 (by decide) (by decide +kernel)

def b_1932 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 3
  | 2 => 5
  | 3 => 8
  | 4 => 0
  | 5 => 2
  | 6 => 4
  | 7 => 1
  | 8 => 7
  | _ => 0

def cert_1932 : LosingRegion (edgeOf a b_1932) 0 :=
  losingMask a b_1932 0 1602091944839938840462336
    (by decide +kernel) (by decide +kernel)

theorem node_1932 : Excluded a [6,3,5,8,0,2,4,1,7] :=
  losing_excluded a [6,3,5,8,0,2,4,1,7] (by decide) b_1932 (by decide +kernel) 2 0 0 cert_1932 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1932 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1602091944839938840462336 2 0; decide +kernel)

theorem node_1931 : Excluded a [6,3,5,8,0,2,4,1] :=
  branch_excluded a [6,3,5,8,0,2,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,5,8,0,2,4,1,0] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,2,4,1,1] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,2,4,1,2] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,2,4,1,3] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,2,4,1,4] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,2,4,1,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,2,4,1,6] (by decide +kernel))
      node_1932
      (invalid_excluded a [6,3,5,8,0,2,4,1,8] (by decide +kernel)))

theorem node_1930 : Excluded a [6,3,5,8,0,2,4] :=
  branch_excluded a [6,3,5,8,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,5,8,0,2,4,0] (by decide +kernel))
      node_1931
      (invalid_excluded a [6,3,5,8,0,2,4,2] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,2,4,3] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,2,4,4] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,2,4,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,2,4,8] (by decide +kernel)))

theorem node_1928 : Excluded a [6,3,5,8,0,2] :=
  branch_excluded a [6,3,5,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,5,8,0,2,0] (by decide +kernel))
      node_1929
      (invalid_excluded a [6,3,5,8,0,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,2,3] (by decide +kernel))
      node_1930
      (invalid_excluded a [6,3,5,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,2,8] (by decide +kernel)))

theorem node_1933 : Excluded a [6,3,5,8,0,4] :=
  predecessor_excluded a [6,3,5,8,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_1934 : Excluded a [6,3,5,8,0,7] :=
  source_excluded a [6,3,5,8,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1926 : Excluded a [6,3,5,8,0] :=
  branch_excluded a [6,3,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,5,8,0,0] (by decide +kernel))
      node_1927
      node_1928
      (invalid_excluded a [6,3,5,8,0,3] (by decide +kernel))
      node_1933
      (invalid_excluded a [6,3,5,8,0,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,0,6] (by decide +kernel))
      node_1934
      (invalid_excluded a [6,3,5,8,0,8] (by decide +kernel)))

theorem node_1935 : Excluded a [6,3,5,8,1] :=
  predecessor_excluded a [6,3,5,8,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1937 : Excluded a [6,3,5,8,7,0] :=
  source_excluded a [6,3,5,8,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1938 : Excluded a [6,3,5,8,7,1] :=
  source_excluded a [6,3,5,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1940 : Excluded a [6,3,5,8,7,2,0] :=
  predecessor_excluded a [6,3,5,8,7,2,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_1941 : Excluded a [6,3,5,8,7,2,1] :=
  source_excluded a [6,3,5,8,7,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1942 : Excluded a [6,3,5,8,7,2,4] :=
  source_excluded a [6,3,5,8,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1939 : Excluded a [6,3,5,8,7,2] :=
  branch_excluded a [6,3,5,8,7,2] (by decide)
    (fin9_cases _
      node_1940
      node_1941
      (invalid_excluded a [6,3,5,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,2,3] (by decide +kernel))
      node_1942
      (invalid_excluded a [6,3,5,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,2,8] (by decide +kernel)))

theorem node_1943 : Excluded a [6,3,5,8,7,4] :=
  predecessor_excluded a [6,3,5,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1936 : Excluded a [6,3,5,8,7] :=
  branch_excluded a [6,3,5,8,7] (by decide)
    (fin9_cases _
      node_1937
      node_1938
      node_1939
      (invalid_excluded a [6,3,5,8,7,3] (by decide +kernel))
      node_1943
      (invalid_excluded a [6,3,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,8] (by decide +kernel)))

theorem node_1925 : Excluded a [6,3,5,8] :=
  branch_excluded a [6,3,5,8] (by decide)
    (fin9_cases _
      node_1926
      node_1935
      (invalid_excluded a [6,3,5,8,2] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,3] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,4] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,6] (by decide +kernel))
      node_1936
      (invalid_excluded a [6,3,5,8,8] (by decide +kernel)))

theorem node_1904 : Excluded a [6,3,5] :=
  branch_excluded a [6,3,5] (by decide)
    (fin9_cases _
      node_1905
      node_1906
      node_1907
      (invalid_excluded a [6,3,5,3] (by decide +kernel))
      (invalid_excluded a [6,3,5,4] (by decide +kernel))
      (invalid_excluded a [6,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,6] (by decide +kernel))
      node_1908
      node_1925)

theorem node_1945 : Excluded a [6,3,7,0] :=
  source_excluded a [6,3,7,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_1946 : Excluded a [6,3,7,1] :=
  predecessor_excluded a [6,3,7,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_1947 : Excluded a [6,3,7,2] :=
  source_excluded a [6,3,7,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1950 : Excluded a [6,3,7,5,0,1] :=
  source_excluded a [6,3,7,5,0,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1951 : Excluded a [6,3,7,5,0,2] :=
  predecessor_excluded a [6,3,7,5,0,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1952 : Excluded a [6,3,7,5,0,4] :=
  source_excluded a [6,3,7,5,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1954 : Excluded a [6,3,7,5,0,8,1] :=
  source_excluded a [6,3,7,5,0,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1955 : Excluded a [6,3,7,5,0,8,2] :=
  source_excluded a [6,3,7,5,0,8,2] 6 0 2 (by decide) (by decide +kernel)

def b_1958 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 3
  | 2 => 7
  | 3 => 5
  | 4 => 0
  | 5 => 8
  | 6 => 4
  | 7 => 1
  | 8 => 2
  | _ => 0

def cert_1958 : LosingRegion (edgeOf a b_1958) 0 :=
  losingMask a b_1958 0 1809876070086203219379200
    (by decide +kernel) (by decide +kernel)

theorem node_1958 : Excluded a [6,3,7,5,0,8,4,1,2] :=
  losing_excluded a [6,3,7,5,0,8,4,1,2] (by decide) b_1958 (by decide +kernel) 2 0 0 cert_1958 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1958 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1809876070086203219379200 2 0; decide +kernel)

theorem node_1957 : Excluded a [6,3,7,5,0,8,4,1] :=
  branch_excluded a [6,3,7,5,0,8,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,7,5,0,8,4,1,0] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,0,8,4,1,1] (by decide +kernel))
      node_1958
      (invalid_excluded a [6,3,7,5,0,8,4,1,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,0,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,0,8,4,1,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,0,8,4,1,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,0,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,0,8,4,1,8] (by decide +kernel)))

theorem node_1959 : Excluded a [6,3,7,5,0,8,4,2] :=
  predecessor_excluded a [6,3,7,5,0,8,4,2] 0 2 6 7 (by decide) (by decide +kernel)

theorem node_1956 : Excluded a [6,3,7,5,0,8,4] :=
  branch_excluded a [6,3,7,5,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,7,5,0,8,4,0] (by decide +kernel))
      node_1957
      node_1959
      (invalid_excluded a [6,3,7,5,0,8,4,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,0,8,4,8] (by decide +kernel)))

theorem node_1953 : Excluded a [6,3,7,5,0,8] :=
  branch_excluded a [6,3,7,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,7,5,0,8,0] (by decide +kernel))
      node_1954
      node_1955
      (invalid_excluded a [6,3,7,5,0,8,3] (by decide +kernel))
      node_1956
      (invalid_excluded a [6,3,7,5,0,8,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,0,8,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,0,8,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,0,8,8] (by decide +kernel)))

theorem node_1949 : Excluded a [6,3,7,5,0] :=
  branch_excluded a [6,3,7,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,7,5,0,0] (by decide +kernel))
      node_1950
      node_1951
      (invalid_excluded a [6,3,7,5,0,3] (by decide +kernel))
      node_1952
      (invalid_excluded a [6,3,7,5,0,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,0,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,0,7] (by decide +kernel))
      node_1953)

theorem node_1960 : Excluded a [6,3,7,5,1] :=
  predecessor_excluded a [6,3,7,5,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1962 : Excluded a [6,3,7,5,8,0] :=
  source_excluded a [6,3,7,5,8,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1963 : Excluded a [6,3,7,5,8,1] :=
  source_excluded a [6,3,7,5,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1964 : Excluded a [6,3,7,5,8,2] :=
  predecessor_excluded a [6,3,7,5,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1965 : Excluded a [6,3,7,5,8,4] :=
  source_excluded a [6,3,7,5,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1961 : Excluded a [6,3,7,5,8] :=
  branch_excluded a [6,3,7,5,8] (by decide)
    (fin9_cases _
      node_1962
      node_1963
      node_1964
      (invalid_excluded a [6,3,7,5,8,3] (by decide +kernel))
      node_1965
      (invalid_excluded a [6,3,7,5,8,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,8,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,8,8] (by decide +kernel)))

theorem node_1948 : Excluded a [6,3,7,5] :=
  branch_excluded a [6,3,7,5] (by decide)
    (fin9_cases _
      node_1949
      node_1960
      (invalid_excluded a [6,3,7,5,2] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,4] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,5,7] (by decide +kernel))
      node_1961)

theorem node_1966 : Excluded a [6,3,7,8] :=
  predecessor_excluded a [6,3,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_1944 : Excluded a [6,3,7] :=
  branch_excluded a [6,3,7] (by decide)
    (fin9_cases _
      node_1945
      node_1946
      node_1947
      (invalid_excluded a [6,3,7,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,4] (by decide +kernel))
      node_1948
      (invalid_excluded a [6,3,7,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,7] (by decide +kernel))
      node_1966)

theorem node_1968 : Excluded a [6,3,8,0] :=
  source_excluded a [6,3,8,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_1969 : Excluded a [6,3,8,1] :=
  predecessor_excluded a [6,3,8,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_1970 : Excluded a [6,3,8,2] :=
  source_excluded a [6,3,8,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_1971 : Excluded a [6,3,8,5] :=
  predecessor_excluded a [6,3,8,5] 0 5 2 3 (by decide) (by decide +kernel)

theorem node_1974 : Excluded a [6,3,8,7,0,1] :=
  source_excluded a [6,3,8,7,0,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1976 : Excluded a [6,3,8,7,0,2,1] :=
  source_excluded a [6,3,8,7,0,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1977 : Excluded a [6,3,8,7,0,2,4] :=
  source_excluded a [6,3,8,7,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1980 : Excluded a [6,3,8,7,0,2,5,1,4] :=
  predecessor_excluded a [6,3,8,7,0,2,5,1,4] 0 2 8 5 (by decide) (by decide +kernel)

theorem node_1979 : Excluded a [6,3,8,7,0,2,5,1] :=
  branch_excluded a [6,3,8,7,0,2,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,8,7,0,2,5,1,0] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,2,5,1,1] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,2,5,1,2] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,2,5,1,3] (by decide +kernel))
      node_1980
      (invalid_excluded a [6,3,8,7,0,2,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,2,5,1,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,2,5,1,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,2,5,1,8] (by decide +kernel)))

theorem node_1981 : Excluded a [6,3,8,7,0,2,5,4] :=
  source_excluded a [6,3,8,7,0,2,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_1978 : Excluded a [6,3,8,7,0,2,5] :=
  branch_excluded a [6,3,8,7,0,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,8,7,0,2,5,0] (by decide +kernel))
      node_1979
      (invalid_excluded a [6,3,8,7,0,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,2,5,3] (by decide +kernel))
      node_1981
      (invalid_excluded a [6,3,8,7,0,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,2,5,8] (by decide +kernel)))

theorem node_1975 : Excluded a [6,3,8,7,0,2] :=
  branch_excluded a [6,3,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,8,7,0,2,0] (by decide +kernel))
      node_1976
      (invalid_excluded a [6,3,8,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,2,3] (by decide +kernel))
      node_1977
      node_1978
      (invalid_excluded a [6,3,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,2,8] (by decide +kernel)))

theorem node_1983 : Excluded a [6,3,8,7,0,4,1] :=
  source_excluded a [6,3,8,7,0,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1984 : Excluded a [6,3,8,7,0,4,2] :=
  predecessor_excluded a [6,3,8,7,0,4,2] 0 8 6 2 (by decide) (by decide +kernel)

def b_1987 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 3
  | 2 => 8
  | 3 => 7
  | 4 => 0
  | 5 => 4
  | 6 => 5
  | 7 => 1
  | 8 => 2
  | _ => 0

def cert_1987 : LosingRegion (edgeOf a b_1987) 0 :=
  losingMask a b_1987 0 1805153881460325886723072
    (by decide +kernel) (by decide +kernel)

theorem node_1987 : Excluded a [6,3,8,7,0,4,5,1,2] :=
  losing_excluded a [6,3,8,7,0,4,5,1,2] (by decide) b_1987 (by decide +kernel) 2 0 1 cert_1987 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1987 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1805153881460325886723072 2 1; decide +kernel)

theorem node_1986 : Excluded a [6,3,8,7,0,4,5,1] :=
  branch_excluded a [6,3,8,7,0,4,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,8,7,0,4,5,1,0] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,4,5,1,1] (by decide +kernel))
      node_1987
      (invalid_excluded a [6,3,8,7,0,4,5,1,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,4,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,4,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,4,5,1,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,4,5,1,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,4,5,1,8] (by decide +kernel)))

theorem node_1988 : Excluded a [6,3,8,7,0,4,5,2] :=
  source_excluded a [6,3,8,7,0,4,5,2] 7 0 2 (by decide) (by decide +kernel)

theorem node_1985 : Excluded a [6,3,8,7,0,4,5] :=
  branch_excluded a [6,3,8,7,0,4,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,8,7,0,4,5,0] (by decide +kernel))
      node_1986
      node_1988
      (invalid_excluded a [6,3,8,7,0,4,5,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,4,5,4] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,4,5,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,4,5,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,4,5,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,4,5,8] (by decide +kernel)))

theorem node_1982 : Excluded a [6,3,8,7,0,4] :=
  branch_excluded a [6,3,8,7,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,8,7,0,4,0] (by decide +kernel))
      node_1983
      node_1984
      (invalid_excluded a [6,3,8,7,0,4,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,4,4] (by decide +kernel))
      node_1985
      (invalid_excluded a [6,3,8,7,0,4,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,4,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,4,8] (by decide +kernel)))

theorem node_1973 : Excluded a [6,3,8,7,0] :=
  branch_excluded a [6,3,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,8,7,0,0] (by decide +kernel))
      node_1974
      node_1975
      (invalid_excluded a [6,3,8,7,0,3] (by decide +kernel))
      node_1982
      (invalid_excluded a [6,3,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,0,8] (by decide +kernel)))

theorem node_1989 : Excluded a [6,3,8,7,1] :=
  predecessor_excluded a [6,3,8,7,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_1991 : Excluded a [6,3,8,7,5,0] :=
  source_excluded a [6,3,8,7,5,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1992 : Excluded a [6,3,8,7,5,1] :=
  source_excluded a [6,3,8,7,5,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1993 : Excluded a [6,3,8,7,5,2] :=
  source_excluded a [6,3,8,7,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_1995 : Excluded a [6,3,8,7,5,4,0] :=
  predecessor_excluded a [6,3,8,7,5,4,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_1996 : Excluded a [6,3,8,7,5,4,1] :=
  source_excluded a [6,3,8,7,5,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_1997 : Excluded a [6,3,8,7,5,4,2] :=
  predecessor_excluded a [6,3,8,7,5,4,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_1994 : Excluded a [6,3,8,7,5,4] :=
  branch_excluded a [6,3,8,7,5,4] (by decide)
    (fin9_cases _
      node_1995
      node_1996
      node_1997
      (invalid_excluded a [6,3,8,7,5,4,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,5,4,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,5,4,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,5,4,8] (by decide +kernel)))

theorem node_1990 : Excluded a [6,3,8,7,5] :=
  branch_excluded a [6,3,8,7,5] (by decide)
    (fin9_cases _
      node_1991
      node_1992
      node_1993
      (invalid_excluded a [6,3,8,7,5,3] (by decide +kernel))
      node_1994
      (invalid_excluded a [6,3,8,7,5,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,5,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,5,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,5,8] (by decide +kernel)))

theorem node_1972 : Excluded a [6,3,8,7] :=
  branch_excluded a [6,3,8,7] (by decide)
    (fin9_cases _
      node_1973
      node_1989
      (invalid_excluded a [6,3,8,7,2] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,4] (by decide +kernel))
      node_1990
      (invalid_excluded a [6,3,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,8] (by decide +kernel)))

theorem node_1967 : Excluded a [6,3,8] :=
  branch_excluded a [6,3,8] (by decide)
    (fin9_cases _
      node_1968
      node_1969
      node_1970
      (invalid_excluded a [6,3,8,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,4] (by decide +kernel))
      node_1971
      (invalid_excluded a [6,3,8,6] (by decide +kernel))
      node_1972
      (invalid_excluded a [6,3,8,8] (by decide +kernel)))

theorem node_1900 : Excluded a [6,3] :=
  branch_excluded a [6,3] (by decide)
    (fin9_cases _
      node_1901
      node_1902
      (invalid_excluded a [6,3,2] (by decide +kernel))
      (invalid_excluded a [6,3,3] (by decide +kernel))
      node_1903
      node_1904
      (invalid_excluded a [6,3,6] (by decide +kernel))
      node_1944
      node_1967)

theorem node_2000 : Excluded a [6,4,0,1] :=
  source_excluded a [6,4,0,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2001 : Excluded a [6,4,0,2] :=
  source_excluded a [6,4,0,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2003 : Excluded a [6,4,0,5,1] :=
  predecessor_excluded a [6,4,0,5,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_2004 : Excluded a [6,4,0,5,3] :=
  source_excluded a [6,4,0,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2006 : Excluded a [6,4,0,5,7,1] :=
  source_excluded a [6,4,0,5,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2007 : Excluded a [6,4,0,5,7,2] :=
  predecessor_excluded a [6,4,0,5,7,2] 0 2 3 5 (by decide) (by decide +kernel)

theorem node_2009 : Excluded a [6,4,0,5,7,3,1] :=
  source_excluded a [6,4,0,5,7,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2010 : Excluded a [6,4,0,5,7,3,2] :=
  source_excluded a [6,4,0,5,7,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_2011 : Excluded a [6,4,0,5,7,3,8] :=
  source_excluded a [6,4,0,5,7,3,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_2008 : Excluded a [6,4,0,5,7,3] :=
  branch_excluded a [6,4,0,5,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,5,7,3,0] (by decide +kernel))
      node_2009
      node_2010
      (invalid_excluded a [6,4,0,5,7,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,3,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,3,7] (by decide +kernel))
      node_2011)

theorem node_2013 : Excluded a [6,4,0,5,7,8,1] :=
  source_excluded a [6,4,0,5,7,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2014 : Excluded a [6,4,0,5,7,8,2] :=
  source_excluded a [6,4,0,5,7,8,2] 4 0 6 (by decide) (by decide +kernel)

def b_2017 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 4
  | 2 => 0
  | 3 => 5
  | 4 => 7
  | 5 => 8
  | 6 => 3
  | 7 => 1
  | 8 => 2
  | _ => 0

def cert_2017 : LosingRegion (edgeOf a b_2017) 0 :=
  losingMask a b_2017 0 1304575995361032399750144
    (by decide +kernel) (by decide +kernel)

theorem node_2017 : Excluded a [6,4,0,5,7,8,3,1,2] :=
  losing_excluded a [6,4,0,5,7,8,3,1,2] (by decide) b_2017 (by decide +kernel) 3 0 1 cert_2017 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_2017 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1304575995361032399750144 3 1; decide +kernel)

theorem node_2016 : Excluded a [6,4,0,5,7,8,3,1] :=
  branch_excluded a [6,4,0,5,7,8,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,5,7,8,3,1,0] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,8,3,1,1] (by decide +kernel))
      node_2017
      (invalid_excluded a [6,4,0,5,7,8,3,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,8,3,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,8,3,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,8,3,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,8,3,1,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,8,3,1,8] (by decide +kernel)))

theorem node_2018 : Excluded a [6,4,0,5,7,8,3,2] :=
  source_excluded a [6,4,0,5,7,8,3,2] 4 0 7 (by decide) (by decide +kernel)

theorem node_2015 : Excluded a [6,4,0,5,7,8,3] :=
  branch_excluded a [6,4,0,5,7,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,5,7,8,3,0] (by decide +kernel))
      node_2016
      node_2018
      (invalid_excluded a [6,4,0,5,7,8,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,8,3,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,8,3,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,8,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,8,3,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,8,3,8] (by decide +kernel)))

theorem node_2012 : Excluded a [6,4,0,5,7,8] :=
  branch_excluded a [6,4,0,5,7,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,5,7,8,0] (by decide +kernel))
      node_2013
      node_2014
      node_2015
      (invalid_excluded a [6,4,0,5,7,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,8,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,8,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,8,8] (by decide +kernel)))

theorem node_2005 : Excluded a [6,4,0,5,7] :=
  branch_excluded a [6,4,0,5,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,5,7,0] (by decide +kernel))
      node_2006
      node_2007
      node_2008
      (invalid_excluded a [6,4,0,5,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,7,7] (by decide +kernel))
      node_2012)

theorem node_2020 : Excluded a [6,4,0,5,8,1] :=
  source_excluded a [6,4,0,5,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2021 : Excluded a [6,4,0,5,8,2] :=
  predecessor_excluded a [6,4,0,5,8,2] 0 2 3 5 (by decide) (by decide +kernel)

theorem node_2023 : Excluded a [6,4,0,5,8,3,1] :=
  source_excluded a [6,4,0,5,8,3,1] 0 2 6 (by decide) (by decide +kernel)

def b_2026 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 4
  | 2 => 0
  | 3 => 5
  | 4 => 8
  | 5 => 3
  | 6 => 2
  | 7 => 1
  | 8 => 7
  | _ => 0

def cert_2026 : LosingRegion (edgeOf a b_2026) 0 :=
  losingMask a b_2026 0 1545423330736661622424576
    (by decide +kernel) (by decide +kernel)

theorem node_2026 : Excluded a [6,4,0,5,8,3,2,1,7] :=
  losing_excluded a [6,4,0,5,8,3,2,1,7] (by decide) b_2026 (by decide +kernel) 3 0 0 cert_2026 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_2026 3 0 ∧ 0 ≠ 3 ∧ maskRegion 1545423330736661622424576 3 0; decide +kernel)

theorem node_2025 : Excluded a [6,4,0,5,8,3,2,1] :=
  branch_excluded a [6,4,0,5,8,3,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,5,8,3,2,1,0] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,2,1,1] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,2,1,2] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,2,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,2,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,2,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,2,1,6] (by decide +kernel))
      node_2026
      (invalid_excluded a [6,4,0,5,8,3,2,1,8] (by decide +kernel)))

theorem node_2024 : Excluded a [6,4,0,5,8,3,2] :=
  branch_excluded a [6,4,0,5,8,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,5,8,3,2,0] (by decide +kernel))
      node_2025
      (invalid_excluded a [6,4,0,5,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,2,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,2,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,2,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,2,8] (by decide +kernel)))

theorem node_2022 : Excluded a [6,4,0,5,8,3] :=
  branch_excluded a [6,4,0,5,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,5,8,3,0] (by decide +kernel))
      node_2023
      node_2024
      (invalid_excluded a [6,4,0,5,8,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,3,8] (by decide +kernel)))

theorem node_2027 : Excluded a [6,4,0,5,8,7] :=
  source_excluded a [6,4,0,5,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2019 : Excluded a [6,4,0,5,8] :=
  branch_excluded a [6,4,0,5,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,5,8,0] (by decide +kernel))
      node_2020
      node_2021
      node_2022
      (invalid_excluded a [6,4,0,5,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,8,6] (by decide +kernel))
      node_2027
      (invalid_excluded a [6,4,0,5,8,8] (by decide +kernel)))

theorem node_2002 : Excluded a [6,4,0,5] :=
  branch_excluded a [6,4,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,5,0] (by decide +kernel))
      node_2003
      (invalid_excluded a [6,4,0,5,2] (by decide +kernel))
      node_2004
      (invalid_excluded a [6,4,0,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,5,6] (by decide +kernel))
      node_2005
      node_2019)

theorem node_2029 : Excluded a [6,4,0,7,1] :=
  predecessor_excluded a [6,4,0,7,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_2030 : Excluded a [6,4,0,7,3] :=
  source_excluded a [6,4,0,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2032 : Excluded a [6,4,0,7,5,1] :=
  source_excluded a [6,4,0,7,5,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2033 : Excluded a [6,4,0,7,5,2] :=
  source_excluded a [6,4,0,7,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2034 : Excluded a [6,4,0,7,5,3] :=
  predecessor_excluded a [6,4,0,7,5,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_2036 : Excluded a [6,4,0,7,5,8,1] :=
  source_excluded a [6,4,0,7,5,8,1] 0 2 6 (by decide) (by decide +kernel)

def b_2039 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 4
  | 2 => 0
  | 3 => 7
  | 4 => 5
  | 5 => 8
  | 6 => 2
  | 7 => 1
  | 8 => 3
  | _ => 0

def cert_2039 : LosingRegion (edgeOf a b_2039) 0 :=
  losingMask a b_2039 0 1809875853777355311940608
    (by decide +kernel) (by decide +kernel)

theorem node_2039 : Excluded a [6,4,0,7,5,8,2,1,3] :=
  losing_excluded a [6,4,0,7,5,8,2,1,3] (by decide) b_2039 (by decide +kernel) 3 0 0 cert_2039 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_2039 3 0 ∧ 0 ≠ 3 ∧ maskRegion 1809875853777355311940608 3 0; decide +kernel)

theorem node_2038 : Excluded a [6,4,0,7,5,8,2,1] :=
  branch_excluded a [6,4,0,7,5,8,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,7,5,8,2,1,0] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,8,2,1,1] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,8,2,1,2] (by decide +kernel))
      node_2039
      (invalid_excluded a [6,4,0,7,5,8,2,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,8,2,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,8,2,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,8,2,1,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,8,2,1,8] (by decide +kernel)))

theorem node_2040 : Excluded a [6,4,0,7,5,8,2,3] :=
  predecessor_excluded a [6,4,0,7,5,8,2,3] 0 3 6 7 (by decide) (by decide +kernel)

theorem node_2037 : Excluded a [6,4,0,7,5,8,2] :=
  branch_excluded a [6,4,0,7,5,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,7,5,8,2,0] (by decide +kernel))
      node_2038
      (invalid_excluded a [6,4,0,7,5,8,2,2] (by decide +kernel))
      node_2040
      (invalid_excluded a [6,4,0,7,5,8,2,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,8,2,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,8,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,8,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,8,2,8] (by decide +kernel)))

theorem node_2041 : Excluded a [6,4,0,7,5,8,3] :=
  source_excluded a [6,4,0,7,5,8,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2035 : Excluded a [6,4,0,7,5,8] :=
  branch_excluded a [6,4,0,7,5,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,7,5,8,0] (by decide +kernel))
      node_2036
      node_2037
      node_2041
      (invalid_excluded a [6,4,0,7,5,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,8,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,8,8] (by decide +kernel)))

theorem node_2031 : Excluded a [6,4,0,7,5] :=
  branch_excluded a [6,4,0,7,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,7,5,0] (by decide +kernel))
      node_2032
      node_2033
      node_2034
      (invalid_excluded a [6,4,0,7,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5,7] (by decide +kernel))
      node_2035)

theorem node_2042 : Excluded a [6,4,0,7,8] :=
  predecessor_excluded a [6,4,0,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_2028 : Excluded a [6,4,0,7] :=
  branch_excluded a [6,4,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,7,0] (by decide +kernel))
      node_2029
      (invalid_excluded a [6,4,0,7,2] (by decide +kernel))
      node_2030
      (invalid_excluded a [6,4,0,7,4] (by decide +kernel))
      node_2031
      (invalid_excluded a [6,4,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,7] (by decide +kernel))
      node_2042)

theorem node_2044 : Excluded a [6,4,0,8,1] :=
  predecessor_excluded a [6,4,0,8,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_2045 : Excluded a [6,4,0,8,3] :=
  source_excluded a [6,4,0,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2046 : Excluded a [6,4,0,8,5] :=
  predecessor_excluded a [6,4,0,8,5] 0 5 3 4 (by decide) (by decide +kernel)

theorem node_2048 : Excluded a [6,4,0,8,7,1] :=
  source_excluded a [6,4,0,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2050 : Excluded a [6,4,0,8,7,2,1] :=
  source_excluded a [6,4,0,8,7,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2051 : Excluded a [6,4,0,8,7,2,3] :=
  predecessor_excluded a [6,4,0,8,7,2,3] 0 8 6 3 (by decide) (by decide +kernel)

def b_2054 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 4
  | 2 => 0
  | 3 => 8
  | 4 => 7
  | 5 => 2
  | 6 => 5
  | 7 => 1
  | 8 => 3
  | _ => 0

def cert_2054 : LosingRegion (edgeOf a b_2054) 0 :=
  losingMask a b_2054 0 1805153809262274323416064
    (by decide +kernel) (by decide +kernel)

theorem node_2054 : Excluded a [6,4,0,8,7,2,5,1,3] :=
  losing_excluded a [6,4,0,8,7,2,5,1,3] (by decide) b_2054 (by decide +kernel) 3 0 1 cert_2054 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_2054 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1805153809262274323416064 3 1; decide +kernel)

theorem node_2053 : Excluded a [6,4,0,8,7,2,5,1] :=
  branch_excluded a [6,4,0,8,7,2,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,7,2,5,1,0] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,2,5,1,1] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,2,5,1,2] (by decide +kernel))
      node_2054
      (invalid_excluded a [6,4,0,8,7,2,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,2,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,2,5,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,2,5,1,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,2,5,1,8] (by decide +kernel)))

theorem node_2055 : Excluded a [6,4,0,8,7,2,5,3] :=
  source_excluded a [6,4,0,8,7,2,5,3] 7 0 3 (by decide) (by decide +kernel)

theorem node_2052 : Excluded a [6,4,0,8,7,2,5] :=
  branch_excluded a [6,4,0,8,7,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,7,2,5,0] (by decide +kernel))
      node_2053
      (invalid_excluded a [6,4,0,8,7,2,5,2] (by decide +kernel))
      node_2055
      (invalid_excluded a [6,4,0,8,7,2,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,2,5,8] (by decide +kernel)))

theorem node_2049 : Excluded a [6,4,0,8,7,2] :=
  branch_excluded a [6,4,0,8,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,7,2,0] (by decide +kernel))
      node_2050
      (invalid_excluded a [6,4,0,8,7,2,2] (by decide +kernel))
      node_2051
      (invalid_excluded a [6,4,0,8,7,2,4] (by decide +kernel))
      node_2052
      (invalid_excluded a [6,4,0,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,2,8] (by decide +kernel)))

theorem node_2057 : Excluded a [6,4,0,8,7,3,1] :=
  source_excluded a [6,4,0,8,7,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2058 : Excluded a [6,4,0,8,7,3,2] :=
  source_excluded a [6,4,0,8,7,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_2061 : Excluded a [6,4,0,8,7,3,5,1,2] :=
  predecessor_excluded a [6,4,0,8,7,3,5,1,2] 0 3 8 5 (by decide) (by decide +kernel)

theorem node_2060 : Excluded a [6,4,0,8,7,3,5,1] :=
  branch_excluded a [6,4,0,8,7,3,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,7,3,5,1,0] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,5,1,1] (by decide +kernel))
      node_2061
      (invalid_excluded a [6,4,0,8,7,3,5,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,5,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,5,1,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,5,1,8] (by decide +kernel)))

theorem node_2062 : Excluded a [6,4,0,8,7,3,5,2] :=
  source_excluded a [6,4,0,8,7,3,5,2] 4 0 7 (by decide) (by decide +kernel)

theorem node_2059 : Excluded a [6,4,0,8,7,3,5] :=
  branch_excluded a [6,4,0,8,7,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,7,3,5,0] (by decide +kernel))
      node_2060
      node_2062
      (invalid_excluded a [6,4,0,8,7,3,5,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,5,8] (by decide +kernel)))

theorem node_2056 : Excluded a [6,4,0,8,7,3] :=
  branch_excluded a [6,4,0,8,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,7,3,0] (by decide +kernel))
      node_2057
      node_2058
      (invalid_excluded a [6,4,0,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,4] (by decide +kernel))
      node_2059
      (invalid_excluded a [6,4,0,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,8] (by decide +kernel)))

theorem node_2047 : Excluded a [6,4,0,8,7] :=
  branch_excluded a [6,4,0,8,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,7,0] (by decide +kernel))
      node_2048
      node_2049
      node_2056
      (invalid_excluded a [6,4,0,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,8] (by decide +kernel)))

theorem node_2043 : Excluded a [6,4,0,8] :=
  branch_excluded a [6,4,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,0] (by decide +kernel))
      node_2044
      (invalid_excluded a [6,4,0,8,2] (by decide +kernel))
      node_2045
      (invalid_excluded a [6,4,0,8,4] (by decide +kernel))
      node_2046
      (invalid_excluded a [6,4,0,8,6] (by decide +kernel))
      node_2047
      (invalid_excluded a [6,4,0,8,8] (by decide +kernel)))

theorem node_1999 : Excluded a [6,4,0] :=
  branch_excluded a [6,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,0] (by decide +kernel))
      node_2000
      node_2001
      (invalid_excluded a [6,4,0,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,4] (by decide +kernel))
      node_2002
      (invalid_excluded a [6,4,0,6] (by decide +kernel))
      node_2028
      node_2043)

theorem node_2063 : Excluded a [6,4,1] :=
  predecessor_excluded a [6,4,1] 0 4 2 1 (by decide) (by decide +kernel)

theorem node_2065 : Excluded a [6,4,5,0] :=
  source_excluded a [6,4,5,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2066 : Excluded a [6,4,5,1] :=
  source_excluded a [6,4,5,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2067 : Excluded a [6,4,5,2] :=
  source_excluded a [6,4,5,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2069 : Excluded a [6,4,5,7,0] :=
  source_excluded a [6,4,5,7,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2070 : Excluded a [6,4,5,7,1] :=
  predecessor_excluded a [6,4,5,7,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2071 : Excluded a [6,4,5,7,3] :=
  source_excluded a [6,4,5,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2072 : Excluded a [6,4,5,7,8] :=
  predecessor_excluded a [6,4,5,7,8] 0 5 4 2 (by decide) (by decide +kernel)

theorem node_2068 : Excluded a [6,4,5,7] :=
  branch_excluded a [6,4,5,7] (by decide)
    (fin9_cases _
      node_2069
      node_2070
      (invalid_excluded a [6,4,5,7,2] (by decide +kernel))
      node_2071
      (invalid_excluded a [6,4,5,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,5,7,7] (by decide +kernel))
      node_2072)

theorem node_2074 : Excluded a [6,4,5,8,0] :=
  source_excluded a [6,4,5,8,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2075 : Excluded a [6,4,5,8,1] :=
  predecessor_excluded a [6,4,5,8,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2076 : Excluded a [6,4,5,8,3] :=
  source_excluded a [6,4,5,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2078 : Excluded a [6,4,5,8,7,0] :=
  source_excluded a [6,4,5,8,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2079 : Excluded a [6,4,5,8,7,1] :=
  source_excluded a [6,4,5,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2081 : Excluded a [6,4,5,8,7,2,0] :=
  predecessor_excluded a [6,4,5,8,7,2,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2082 : Excluded a [6,4,5,8,7,2,1] :=
  source_excluded a [6,4,5,8,7,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2083 : Excluded a [6,4,5,8,7,2,3] :=
  predecessor_excluded a [6,4,5,8,7,2,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_2080 : Excluded a [6,4,5,8,7,2] :=
  branch_excluded a [6,4,5,8,7,2] (by decide)
    (fin9_cases _
      node_2081
      node_2082
      (invalid_excluded a [6,4,5,8,7,2,2] (by decide +kernel))
      node_2083
      (invalid_excluded a [6,4,5,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,7,2,8] (by decide +kernel)))

theorem node_2084 : Excluded a [6,4,5,8,7,3] :=
  source_excluded a [6,4,5,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2077 : Excluded a [6,4,5,8,7] :=
  branch_excluded a [6,4,5,8,7] (by decide)
    (fin9_cases _
      node_2078
      node_2079
      node_2080
      node_2084
      (invalid_excluded a [6,4,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,7,8] (by decide +kernel)))

theorem node_2073 : Excluded a [6,4,5,8] :=
  branch_excluded a [6,4,5,8] (by decide)
    (fin9_cases _
      node_2074
      node_2075
      (invalid_excluded a [6,4,5,8,2] (by decide +kernel))
      node_2076
      (invalid_excluded a [6,4,5,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,6] (by decide +kernel))
      node_2077
      (invalid_excluded a [6,4,5,8,8] (by decide +kernel)))

theorem node_2064 : Excluded a [6,4,5] :=
  branch_excluded a [6,4,5] (by decide)
    (fin9_cases _
      node_2065
      node_2066
      node_2067
      (invalid_excluded a [6,4,5,3] (by decide +kernel))
      (invalid_excluded a [6,4,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,5,6] (by decide +kernel))
      node_2068
      node_2073)

theorem node_2086 : Excluded a [6,4,7,0] :=
  source_excluded a [6,4,7,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2087 : Excluded a [6,4,7,1] :=
  source_excluded a [6,4,7,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2088 : Excluded a [6,4,7,2] :=
  source_excluded a [6,4,7,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2090 : Excluded a [6,4,7,5,0] :=
  source_excluded a [6,4,7,5,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2091 : Excluded a [6,4,7,5,1] :=
  predecessor_excluded a [6,4,7,5,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2092 : Excluded a [6,4,7,5,3] :=
  source_excluded a [6,4,7,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2094 : Excluded a [6,4,7,5,8,0] :=
  source_excluded a [6,4,7,5,8,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2095 : Excluded a [6,4,7,5,8,1] :=
  source_excluded a [6,4,7,5,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2096 : Excluded a [6,4,7,5,8,2] :=
  predecessor_excluded a [6,4,7,5,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_2098 : Excluded a [6,4,7,5,8,3,0] :=
  predecessor_excluded a [6,4,7,5,8,3,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2099 : Excluded a [6,4,7,5,8,3,1] :=
  source_excluded a [6,4,7,5,8,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2100 : Excluded a [6,4,7,5,8,3,2] :=
  source_excluded a [6,4,7,5,8,3,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_2097 : Excluded a [6,4,7,5,8,3] :=
  branch_excluded a [6,4,7,5,8,3] (by decide)
    (fin9_cases _
      node_2098
      node_2099
      node_2100
      (invalid_excluded a [6,4,7,5,8,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,5,8,3,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,5,8,3,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,5,8,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,5,8,3,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,5,8,3,8] (by decide +kernel)))

theorem node_2093 : Excluded a [6,4,7,5,8] :=
  branch_excluded a [6,4,7,5,8] (by decide)
    (fin9_cases _
      node_2094
      node_2095
      node_2096
      node_2097
      (invalid_excluded a [6,4,7,5,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,5,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,5,8,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,5,8,8] (by decide +kernel)))

theorem node_2089 : Excluded a [6,4,7,5] :=
  branch_excluded a [6,4,7,5] (by decide)
    (fin9_cases _
      node_2090
      node_2091
      (invalid_excluded a [6,4,7,5,2] (by decide +kernel))
      node_2092
      (invalid_excluded a [6,4,7,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,5,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,5,7] (by decide +kernel))
      node_2093)

theorem node_2101 : Excluded a [6,4,7,8] :=
  predecessor_excluded a [6,4,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_2085 : Excluded a [6,4,7] :=
  branch_excluded a [6,4,7] (by decide)
    (fin9_cases _
      node_2086
      node_2087
      node_2088
      (invalid_excluded a [6,4,7,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,4] (by decide +kernel))
      node_2089
      (invalid_excluded a [6,4,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,7] (by decide +kernel))
      node_2101)

theorem node_2103 : Excluded a [6,4,8,0] :=
  source_excluded a [6,4,8,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2104 : Excluded a [6,4,8,1] :=
  source_excluded a [6,4,8,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2105 : Excluded a [6,4,8,2] :=
  source_excluded a [6,4,8,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2106 : Excluded a [6,4,8,5] :=
  predecessor_excluded a [6,4,8,5] 0 5 2 3 (by decide) (by decide +kernel)

theorem node_2108 : Excluded a [6,4,8,7,0] :=
  source_excluded a [6,4,8,7,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2109 : Excluded a [6,4,8,7,1] :=
  predecessor_excluded a [6,4,8,7,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2110 : Excluded a [6,4,8,7,3] :=
  source_excluded a [6,4,8,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2112 : Excluded a [6,4,8,7,5,0] :=
  source_excluded a [6,4,8,7,5,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2113 : Excluded a [6,4,8,7,5,1] :=
  source_excluded a [6,4,8,7,5,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2114 : Excluded a [6,4,8,7,5,2] :=
  source_excluded a [6,4,8,7,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2115 : Excluded a [6,4,8,7,5,3] :=
  predecessor_excluded a [6,4,8,7,5,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_2111 : Excluded a [6,4,8,7,5] :=
  branch_excluded a [6,4,8,7,5] (by decide)
    (fin9_cases _
      node_2112
      node_2113
      node_2114
      node_2115
      (invalid_excluded a [6,4,8,7,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,5,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,5,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,5,8] (by decide +kernel)))

theorem node_2107 : Excluded a [6,4,8,7] :=
  branch_excluded a [6,4,8,7] (by decide)
    (fin9_cases _
      node_2108
      node_2109
      (invalid_excluded a [6,4,8,7,2] (by decide +kernel))
      node_2110
      (invalid_excluded a [6,4,8,7,4] (by decide +kernel))
      node_2111
      (invalid_excluded a [6,4,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,8] (by decide +kernel)))

theorem node_2102 : Excluded a [6,4,8] :=
  branch_excluded a [6,4,8] (by decide)
    (fin9_cases _
      node_2103
      node_2104
      node_2105
      (invalid_excluded a [6,4,8,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,4] (by decide +kernel))
      node_2106
      (invalid_excluded a [6,4,8,6] (by decide +kernel))
      node_2107
      (invalid_excluded a [6,4,8,8] (by decide +kernel)))

theorem node_1998 : Excluded a [6,4] :=
  branch_excluded a [6,4] (by decide)
    (fin9_cases _
      node_1999
      node_2063
      (invalid_excluded a [6,4,2] (by decide +kernel))
      (invalid_excluded a [6,4,3] (by decide +kernel))
      (invalid_excluded a [6,4,4] (by decide +kernel))
      node_2064
      (invalid_excluded a [6,4,6] (by decide +kernel))
      node_2085
      node_2102)

theorem node_2116 : Excluded a [6,5] :=
  predecessor_excluded a [6,5] 2 6 1 0 (by decide) (by decide +kernel)

theorem node_2117 : Excluded a [6,7] :=
  predecessor_excluded a [6,7] 2 7 0 1 (by decide) (by decide +kernel)

theorem node_2120 : Excluded a [6,8,0,1] :=
  predecessor_excluded a [6,8,0,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_2121 : Excluded a [6,8,0,2] :=
  source_excluded a [6,8,0,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2123 : Excluded a [6,8,0,5,1] :=
  predecessor_excluded a [6,8,0,5,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_2124 : Excluded a [6,8,0,5,3] :=
  source_excluded a [6,8,0,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2126 : Excluded a [6,8,0,5,7,1] :=
  source_excluded a [6,8,0,5,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2127 : Excluded a [6,8,0,5,7,2] :=
  predecessor_excluded a [6,8,0,5,7,2] 0 2 3 5 (by decide) (by decide +kernel)

theorem node_2129 : Excluded a [6,8,0,5,7,3,1] :=
  source_excluded a [6,8,0,5,7,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2130 : Excluded a [6,8,0,5,7,3,2] :=
  source_excluded a [6,8,0,5,7,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_2131 : Excluded a [6,8,0,5,7,3,4] :=
  source_excluded a [6,8,0,5,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2128 : Excluded a [6,8,0,5,7,3] :=
  branch_excluded a [6,8,0,5,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,5,7,3,0] (by decide +kernel))
      node_2129
      node_2130
      (invalid_excluded a [6,8,0,5,7,3,3] (by decide +kernel))
      node_2131
      (invalid_excluded a [6,8,0,5,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,5,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,5,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,5,7,3,8] (by decide +kernel)))

theorem node_2132 : Excluded a [6,8,0,5,7,4] :=
  source_excluded a [6,8,0,5,7,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2125 : Excluded a [6,8,0,5,7] :=
  branch_excluded a [6,8,0,5,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,5,7,0] (by decide +kernel))
      node_2126
      node_2127
      node_2128
      node_2132
      (invalid_excluded a [6,8,0,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,5,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,5,7,8] (by decide +kernel)))

theorem node_2122 : Excluded a [6,8,0,5] :=
  branch_excluded a [6,8,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,5,0] (by decide +kernel))
      node_2123
      (invalid_excluded a [6,8,0,5,2] (by decide +kernel))
      node_2124
      (invalid_excluded a [6,8,0,5,4] (by decide +kernel))
      (invalid_excluded a [6,8,0,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,5,6] (by decide +kernel))
      node_2125
      (invalid_excluded a [6,8,0,5,8] (by decide +kernel)))

theorem node_2134 : Excluded a [6,8,0,7,1] :=
  predecessor_excluded a [6,8,0,7,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_2135 : Excluded a [6,8,0,7,3] :=
  source_excluded a [6,8,0,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2137 : Excluded a [6,8,0,7,5,1] :=
  source_excluded a [6,8,0,7,5,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2138 : Excluded a [6,8,0,7,5,2] :=
  source_excluded a [6,8,0,7,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2139 : Excluded a [6,8,0,7,5,3] :=
  predecessor_excluded a [6,8,0,7,5,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_2141 : Excluded a [6,8,0,7,5,4,1] :=
  source_excluded a [6,8,0,7,5,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2142 : Excluded a [6,8,0,7,5,4,2] :=
  predecessor_excluded a [6,8,0,7,5,4,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2143 : Excluded a [6,8,0,7,5,4,3] :=
  source_excluded a [6,8,0,7,5,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2140 : Excluded a [6,8,0,7,5,4] :=
  branch_excluded a [6,8,0,7,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,7,5,4,0] (by decide +kernel))
      node_2141
      node_2142
      node_2143
      (invalid_excluded a [6,8,0,7,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,5,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,5,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,5,4,8] (by decide +kernel)))

theorem node_2136 : Excluded a [6,8,0,7,5] :=
  branch_excluded a [6,8,0,7,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,7,5,0] (by decide +kernel))
      node_2137
      node_2138
      node_2139
      node_2140
      (invalid_excluded a [6,8,0,7,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,5,8] (by decide +kernel)))

theorem node_2133 : Excluded a [6,8,0,7] :=
  branch_excluded a [6,8,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,7,0] (by decide +kernel))
      node_2134
      (invalid_excluded a [6,8,0,7,2] (by decide +kernel))
      node_2135
      (invalid_excluded a [6,8,0,7,4] (by decide +kernel))
      node_2136
      (invalid_excluded a [6,8,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,8] (by decide +kernel)))

theorem node_2119 : Excluded a [6,8,0] :=
  branch_excluded a [6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,0] (by decide +kernel))
      node_2120
      node_2121
      (invalid_excluded a [6,8,0,3] (by decide +kernel))
      (invalid_excluded a [6,8,0,4] (by decide +kernel))
      node_2122
      (invalid_excluded a [6,8,0,6] (by decide +kernel))
      node_2133
      (invalid_excluded a [6,8,0,8] (by decide +kernel)))

theorem node_2145 : Excluded a [6,8,1,0] :=
  predecessor_excluded a [6,8,1,0] 4 0 2 3 (by decide) (by decide +kernel)

theorem node_2146 : Excluded a [6,8,1,2] :=
  source_excluded a [6,8,1,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2148 : Excluded a [6,8,1,5,0] :=
  predecessor_excluded a [6,8,1,5,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_2149 : Excluded a [6,8,1,5,3] :=
  source_excluded a [6,8,1,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2151 : Excluded a [6,8,1,5,7,0] :=
  source_excluded a [6,8,1,5,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2152 : Excluded a [6,8,1,5,7,2] :=
  predecessor_excluded a [6,8,1,5,7,2] 0 2 3 5 (by decide) (by decide +kernel)

theorem node_2154 : Excluded a [6,8,1,5,7,3,0] :=
  predecessor_excluded a [6,8,1,5,7,3,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2155 : Excluded a [6,8,1,5,7,3,2] :=
  source_excluded a [6,8,1,5,7,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_2156 : Excluded a [6,8,1,5,7,3,4] :=
  source_excluded a [6,8,1,5,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2153 : Excluded a [6,8,1,5,7,3] :=
  branch_excluded a [6,8,1,5,7,3] (by decide)
    (fin9_cases _
      node_2154
      (invalid_excluded a [6,8,1,5,7,3,1] (by decide +kernel))
      node_2155
      (invalid_excluded a [6,8,1,5,7,3,3] (by decide +kernel))
      node_2156
      (invalid_excluded a [6,8,1,5,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,5,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,5,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,5,7,3,8] (by decide +kernel)))

theorem node_2157 : Excluded a [6,8,1,5,7,4] :=
  source_excluded a [6,8,1,5,7,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2150 : Excluded a [6,8,1,5,7] :=
  branch_excluded a [6,8,1,5,7] (by decide)
    (fin9_cases _
      node_2151
      (invalid_excluded a [6,8,1,5,7,1] (by decide +kernel))
      node_2152
      node_2153
      node_2157
      (invalid_excluded a [6,8,1,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,5,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,5,7,8] (by decide +kernel)))

theorem node_2147 : Excluded a [6,8,1,5] :=
  branch_excluded a [6,8,1,5] (by decide)
    (fin9_cases _
      node_2148
      (invalid_excluded a [6,8,1,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,5,2] (by decide +kernel))
      node_2149
      (invalid_excluded a [6,8,1,5,4] (by decide +kernel))
      (invalid_excluded a [6,8,1,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,5,6] (by decide +kernel))
      node_2150
      (invalid_excluded a [6,8,1,5,8] (by decide +kernel)))

theorem node_2159 : Excluded a [6,8,1,7,0] :=
  predecessor_excluded a [6,8,1,7,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_2160 : Excluded a [6,8,1,7,3] :=
  source_excluded a [6,8,1,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2162 : Excluded a [6,8,1,7,5,0] :=
  source_excluded a [6,8,1,7,5,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2163 : Excluded a [6,8,1,7,5,2] :=
  source_excluded a [6,8,1,7,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2164 : Excluded a [6,8,1,7,5,3] :=
  predecessor_excluded a [6,8,1,7,5,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_2166 : Excluded a [6,8,1,7,5,4,0] :=
  predecessor_excluded a [6,8,1,7,5,4,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2167 : Excluded a [6,8,1,7,5,4,2] :=
  predecessor_excluded a [6,8,1,7,5,4,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2168 : Excluded a [6,8,1,7,5,4,3] :=
  source_excluded a [6,8,1,7,5,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2165 : Excluded a [6,8,1,7,5,4] :=
  branch_excluded a [6,8,1,7,5,4] (by decide)
    (fin9_cases _
      node_2166
      (invalid_excluded a [6,8,1,7,5,4,1] (by decide +kernel))
      node_2167
      node_2168
      (invalid_excluded a [6,8,1,7,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,5,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,5,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,5,4,8] (by decide +kernel)))

theorem node_2161 : Excluded a [6,8,1,7,5] :=
  branch_excluded a [6,8,1,7,5] (by decide)
    (fin9_cases _
      node_2162
      (invalid_excluded a [6,8,1,7,5,1] (by decide +kernel))
      node_2163
      node_2164
      node_2165
      (invalid_excluded a [6,8,1,7,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,5,8] (by decide +kernel)))

theorem node_2158 : Excluded a [6,8,1,7] :=
  branch_excluded a [6,8,1,7] (by decide)
    (fin9_cases _
      node_2159
      (invalid_excluded a [6,8,1,7,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2] (by decide +kernel))
      node_2160
      (invalid_excluded a [6,8,1,7,4] (by decide +kernel))
      node_2161
      (invalid_excluded a [6,8,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,8] (by decide +kernel)))

theorem node_2144 : Excluded a [6,8,1] :=
  branch_excluded a [6,8,1] (by decide)
    (fin9_cases _
      node_2145
      (invalid_excluded a [6,8,1,1] (by decide +kernel))
      node_2146
      (invalid_excluded a [6,8,1,3] (by decide +kernel))
      (invalid_excluded a [6,8,1,4] (by decide +kernel))
      node_2147
      (invalid_excluded a [6,8,1,6] (by decide +kernel))
      node_2158
      (invalid_excluded a [6,8,1,8] (by decide +kernel)))

theorem node_2169 : Excluded a [6,8,4] :=
  source_excluded a [6,8,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_2172 : Excluded a [6,8,5,0,1] :=
  predecessor_excluded a [6,8,5,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2173 : Excluded a [6,8,5,0,3] :=
  source_excluded a [6,8,5,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2175 : Excluded a [6,8,5,0,7,1] :=
  source_excluded a [6,8,5,0,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2177 : Excluded a [6,8,5,0,7,2,1] :=
  source_excluded a [6,8,5,0,7,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2178 : Excluded a [6,8,5,0,7,2,3] :=
  predecessor_excluded a [6,8,5,0,7,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_2179 : Excluded a [6,8,5,0,7,2,4] :=
  source_excluded a [6,8,5,0,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2176 : Excluded a [6,8,5,0,7,2] :=
  branch_excluded a [6,8,5,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,0,7,2,0] (by decide +kernel))
      node_2177
      (invalid_excluded a [6,8,5,0,7,2,2] (by decide +kernel))
      node_2178
      node_2179
      (invalid_excluded a [6,8,5,0,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,2,8] (by decide +kernel)))

theorem node_2180 : Excluded a [6,8,5,0,7,3] :=
  source_excluded a [6,8,5,0,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2181 : Excluded a [6,8,5,0,7,4] :=
  predecessor_excluded a [6,8,5,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2174 : Excluded a [6,8,5,0,7] :=
  branch_excluded a [6,8,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,0,7,0] (by decide +kernel))
      node_2175
      node_2176
      node_2180
      node_2181
      (invalid_excluded a [6,8,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,8] (by decide +kernel)))

theorem node_2171 : Excluded a [6,8,5,0] :=
  branch_excluded a [6,8,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,0,0] (by decide +kernel))
      node_2172
      (invalid_excluded a [6,8,5,0,2] (by decide +kernel))
      node_2173
      (invalid_excluded a [6,8,5,0,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,6] (by decide +kernel))
      node_2174
      (invalid_excluded a [6,8,5,0,8] (by decide +kernel)))

theorem node_2183 : Excluded a [6,8,5,1,0] :=
  predecessor_excluded a [6,8,5,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_2184 : Excluded a [6,8,5,1,3] :=
  source_excluded a [6,8,5,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2186 : Excluded a [6,8,5,1,7,0] :=
  source_excluded a [6,8,5,1,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2188 : Excluded a [6,8,5,1,7,2,0] :=
  predecessor_excluded a [6,8,5,1,7,2,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2189 : Excluded a [6,8,5,1,7,2,3] :=
  predecessor_excluded a [6,8,5,1,7,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_2190 : Excluded a [6,8,5,1,7,2,4] :=
  source_excluded a [6,8,5,1,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2187 : Excluded a [6,8,5,1,7,2] :=
  branch_excluded a [6,8,5,1,7,2] (by decide)
    (fin9_cases _
      node_2188
      (invalid_excluded a [6,8,5,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,2] (by decide +kernel))
      node_2189
      node_2190
      (invalid_excluded a [6,8,5,1,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,8] (by decide +kernel)))

theorem node_2191 : Excluded a [6,8,5,1,7,3] :=
  source_excluded a [6,8,5,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2192 : Excluded a [6,8,5,1,7,4] :=
  predecessor_excluded a [6,8,5,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2185 : Excluded a [6,8,5,1,7] :=
  branch_excluded a [6,8,5,1,7] (by decide)
    (fin9_cases _
      node_2186
      (invalid_excluded a [6,8,5,1,7,1] (by decide +kernel))
      node_2187
      node_2191
      node_2192
      (invalid_excluded a [6,8,5,1,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,8] (by decide +kernel)))

theorem node_2182 : Excluded a [6,8,5,1] :=
  branch_excluded a [6,8,5,1] (by decide)
    (fin9_cases _
      node_2183
      (invalid_excluded a [6,8,5,1,1] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,2] (by decide +kernel))
      node_2184
      (invalid_excluded a [6,8,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,6] (by decide +kernel))
      node_2185
      (invalid_excluded a [6,8,5,1,8] (by decide +kernel)))

theorem node_2193 : Excluded a [6,8,5,2] :=
  source_excluded a [6,8,5,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2196 : Excluded a [6,8,5,7,0,1] :=
  source_excluded a [6,8,5,7,0,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2198 : Excluded a [6,8,5,7,0,2,1] :=
  source_excluded a [6,8,5,7,0,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2199 : Excluded a [6,8,5,7,0,2,3] :=
  source_excluded a [6,8,5,7,0,2,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2200 : Excluded a [6,8,5,7,0,2,4] :=
  source_excluded a [6,8,5,7,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2197 : Excluded a [6,8,5,7,0,2] :=
  branch_excluded a [6,8,5,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,7,0,2,0] (by decide +kernel))
      node_2198
      (invalid_excluded a [6,8,5,7,0,2,2] (by decide +kernel))
      node_2199
      node_2200
      (invalid_excluded a [6,8,5,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,0,2,8] (by decide +kernel)))

theorem node_2201 : Excluded a [6,8,5,7,0,3] :=
  source_excluded a [6,8,5,7,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2202 : Excluded a [6,8,5,7,0,4] :=
  predecessor_excluded a [6,8,5,7,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2195 : Excluded a [6,8,5,7,0] :=
  branch_excluded a [6,8,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,7,0,0] (by decide +kernel))
      node_2196
      node_2197
      node_2201
      node_2202
      (invalid_excluded a [6,8,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,0,8] (by decide +kernel)))

theorem node_2204 : Excluded a [6,8,5,7,1,0] :=
  source_excluded a [6,8,5,7,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2206 : Excluded a [6,8,5,7,1,2,0] :=
  predecessor_excluded a [6,8,5,7,1,2,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2207 : Excluded a [6,8,5,7,1,2,3] :=
  source_excluded a [6,8,5,7,1,2,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2208 : Excluded a [6,8,5,7,1,2,4] :=
  source_excluded a [6,8,5,7,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2205 : Excluded a [6,8,5,7,1,2] :=
  branch_excluded a [6,8,5,7,1,2] (by decide)
    (fin9_cases _
      node_2206
      (invalid_excluded a [6,8,5,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,2,2] (by decide +kernel))
      node_2207
      node_2208
      (invalid_excluded a [6,8,5,7,1,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,2,8] (by decide +kernel)))

theorem node_2209 : Excluded a [6,8,5,7,1,3] :=
  source_excluded a [6,8,5,7,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2210 : Excluded a [6,8,5,7,1,4] :=
  predecessor_excluded a [6,8,5,7,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2203 : Excluded a [6,8,5,7,1] :=
  branch_excluded a [6,8,5,7,1] (by decide)
    (fin9_cases _
      node_2204
      (invalid_excluded a [6,8,5,7,1,1] (by decide +kernel))
      node_2205
      node_2209
      node_2210
      (invalid_excluded a [6,8,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,8] (by decide +kernel)))

theorem node_2211 : Excluded a [6,8,5,7,3] :=
  source_excluded a [6,8,5,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2194 : Excluded a [6,8,5,7] :=
  branch_excluded a [6,8,5,7] (by decide)
    (fin9_cases _
      node_2195
      node_2203
      (invalid_excluded a [6,8,5,7,2] (by decide +kernel))
      node_2211
      (invalid_excluded a [6,8,5,7,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,8] (by decide +kernel)))

theorem node_2170 : Excluded a [6,8,5] :=
  branch_excluded a [6,8,5] (by decide)
    (fin9_cases _
      node_2171
      node_2182
      node_2193
      (invalid_excluded a [6,8,5,3] (by decide +kernel))
      (invalid_excluded a [6,8,5,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,6] (by decide +kernel))
      node_2194
      (invalid_excluded a [6,8,5,8] (by decide +kernel)))

theorem node_2214 : Excluded a [6,8,7,0,1] :=
  predecessor_excluded a [6,8,7,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2215 : Excluded a [6,8,7,0,3] :=
  source_excluded a [6,8,7,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2217 : Excluded a [6,8,7,0,5,1] :=
  source_excluded a [6,8,7,0,5,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2218 : Excluded a [6,8,7,0,5,2] :=
  source_excluded a [6,8,7,0,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2219 : Excluded a [6,8,7,0,5,3] :=
  predecessor_excluded a [6,8,7,0,5,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_2221 : Excluded a [6,8,7,0,5,4,1] :=
  source_excluded a [6,8,7,0,5,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2222 : Excluded a [6,8,7,0,5,4,2] :=
  source_excluded a [6,8,7,0,5,4,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_2223 : Excluded a [6,8,7,0,5,4,3] :=
  source_excluded a [6,8,7,0,5,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2220 : Excluded a [6,8,7,0,5,4] :=
  branch_excluded a [6,8,7,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,5,4,0] (by decide +kernel))
      node_2221
      node_2222
      node_2223
      (invalid_excluded a [6,8,7,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,5,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,5,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,5,4,8] (by decide +kernel)))

theorem node_2216 : Excluded a [6,8,7,0,5] :=
  branch_excluded a [6,8,7,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,5,0] (by decide +kernel))
      node_2217
      node_2218
      node_2219
      node_2220
      (invalid_excluded a [6,8,7,0,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,5,8] (by decide +kernel)))

theorem node_2213 : Excluded a [6,8,7,0] :=
  branch_excluded a [6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,0] (by decide +kernel))
      node_2214
      (invalid_excluded a [6,8,7,0,2] (by decide +kernel))
      node_2215
      (invalid_excluded a [6,8,7,0,4] (by decide +kernel))
      node_2216
      (invalid_excluded a [6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,8] (by decide +kernel)))

theorem node_2225 : Excluded a [6,8,7,1,0] :=
  predecessor_excluded a [6,8,7,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_2226 : Excluded a [6,8,7,1,3] :=
  source_excluded a [6,8,7,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2228 : Excluded a [6,8,7,1,5,0] :=
  source_excluded a [6,8,7,1,5,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2229 : Excluded a [6,8,7,1,5,2] :=
  source_excluded a [6,8,7,1,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2230 : Excluded a [6,8,7,1,5,3] :=
  predecessor_excluded a [6,8,7,1,5,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_2232 : Excluded a [6,8,7,1,5,4,0] :=
  predecessor_excluded a [6,8,7,1,5,4,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2233 : Excluded a [6,8,7,1,5,4,2] :=
  source_excluded a [6,8,7,1,5,4,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_2234 : Excluded a [6,8,7,1,5,4,3] :=
  source_excluded a [6,8,7,1,5,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2231 : Excluded a [6,8,7,1,5,4] :=
  branch_excluded a [6,8,7,1,5,4] (by decide)
    (fin9_cases _
      node_2232
      (invalid_excluded a [6,8,7,1,5,4,1] (by decide +kernel))
      node_2233
      node_2234
      (invalid_excluded a [6,8,7,1,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,5,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,5,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,5,4,8] (by decide +kernel)))

theorem node_2227 : Excluded a [6,8,7,1,5] :=
  branch_excluded a [6,8,7,1,5] (by decide)
    (fin9_cases _
      node_2228
      (invalid_excluded a [6,8,7,1,5,1] (by decide +kernel))
      node_2229
      node_2230
      node_2231
      (invalid_excluded a [6,8,7,1,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,5,8] (by decide +kernel)))

theorem node_2224 : Excluded a [6,8,7,1] :=
  branch_excluded a [6,8,7,1] (by decide)
    (fin9_cases _
      node_2225
      (invalid_excluded a [6,8,7,1,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,2] (by decide +kernel))
      node_2226
      (invalid_excluded a [6,8,7,1,4] (by decide +kernel))
      node_2227
      (invalid_excluded a [6,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,8] (by decide +kernel)))

theorem node_2235 : Excluded a [6,8,7,2] :=
  source_excluded a [6,8,7,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2238 : Excluded a [6,8,7,5,0,1] :=
  source_excluded a [6,8,7,5,0,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2239 : Excluded a [6,8,7,5,0,2] :=
  predecessor_excluded a [6,8,7,5,0,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_2241 : Excluded a [6,8,7,5,0,3,1] :=
  source_excluded a [6,8,7,5,0,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2242 : Excluded a [6,8,7,5,0,3,2] :=
  source_excluded a [6,8,7,5,0,3,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_2243 : Excluded a [6,8,7,5,0,3,4] :=
  predecessor_excluded a [6,8,7,5,0,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_2240 : Excluded a [6,8,7,5,0,3] :=
  branch_excluded a [6,8,7,5,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,5,0,3,0] (by decide +kernel))
      node_2241
      node_2242
      (invalid_excluded a [6,8,7,5,0,3,3] (by decide +kernel))
      node_2243
      (invalid_excluded a [6,8,7,5,0,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,5,0,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,5,0,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,5,0,3,8] (by decide +kernel)))

theorem node_2244 : Excluded a [6,8,7,5,0,4] :=
  source_excluded a [6,8,7,5,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2237 : Excluded a [6,8,7,5,0] :=
  branch_excluded a [6,8,7,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,5,0,0] (by decide +kernel))
      node_2238
      node_2239
      node_2240
      node_2244
      (invalid_excluded a [6,8,7,5,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,5,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,5,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,5,0,8] (by decide +kernel)))

theorem node_2246 : Excluded a [6,8,7,5,1,0] :=
  source_excluded a [6,8,7,5,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2247 : Excluded a [6,8,7,5,1,2] :=
  predecessor_excluded a [6,8,7,5,1,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_2249 : Excluded a [6,8,7,5,1,3,0] :=
  predecessor_excluded a [6,8,7,5,1,3,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2250 : Excluded a [6,8,7,5,1,3,2] :=
  source_excluded a [6,8,7,5,1,3,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_2251 : Excluded a [6,8,7,5,1,3,4] :=
  predecessor_excluded a [6,8,7,5,1,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_2248 : Excluded a [6,8,7,5,1,3] :=
  branch_excluded a [6,8,7,5,1,3] (by decide)
    (fin9_cases _
      node_2249
      (invalid_excluded a [6,8,7,5,1,3,1] (by decide +kernel))
      node_2250
      (invalid_excluded a [6,8,7,5,1,3,3] (by decide +kernel))
      node_2251
      (invalid_excluded a [6,8,7,5,1,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,5,1,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,5,1,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,5,1,3,8] (by decide +kernel)))

theorem node_2252 : Excluded a [6,8,7,5,1,4] :=
  source_excluded a [6,8,7,5,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2245 : Excluded a [6,8,7,5,1] :=
  branch_excluded a [6,8,7,5,1] (by decide)
    (fin9_cases _
      node_2246
      (invalid_excluded a [6,8,7,5,1,1] (by decide +kernel))
      node_2247
      node_2248
      node_2252
      (invalid_excluded a [6,8,7,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,5,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,5,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,5,1,8] (by decide +kernel)))

theorem node_2253 : Excluded a [6,8,7,5,3] :=
  source_excluded a [6,8,7,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2236 : Excluded a [6,8,7,5] :=
  branch_excluded a [6,8,7,5] (by decide)
    (fin9_cases _
      node_2237
      node_2245
      (invalid_excluded a [6,8,7,5,2] (by decide +kernel))
      node_2253
      (invalid_excluded a [6,8,7,5,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,5,8] (by decide +kernel)))

theorem node_2212 : Excluded a [6,8,7] :=
  branch_excluded a [6,8,7] (by decide)
    (fin9_cases _
      node_2213
      node_2224
      node_2235
      (invalid_excluded a [6,8,7,3] (by decide +kernel))
      (invalid_excluded a [6,8,7,4] (by decide +kernel))
      node_2236
      (invalid_excluded a [6,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,8] (by decide +kernel)))

theorem node_2118 : Excluded a [6,8] :=
  branch_excluded a [6,8] (by decide)
    (fin9_cases _
      node_2119
      node_2144
      (invalid_excluded a [6,8,2] (by decide +kernel))
      (invalid_excluded a [6,8,3] (by decide +kernel))
      node_2169
      node_2170
      (invalid_excluded a [6,8,6] (by decide +kernel))
      node_2212
      (invalid_excluded a [6,8,8] (by decide +kernel)))

theorem node_1788 : Excluded a [6] :=
  branch_excluded a [6] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0] (by decide +kernel))
      (invalid_excluded a [6,1] (by decide +kernel))
      node_1789
      node_1900
      node_1998
      node_2116
      (invalid_excluded a [6,6] (by decide +kernel))
      node_2117
      node_2118)

theorem node_2256 : Excluded a [7,2,0] :=
  source_excluded a [7,2,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_2257 : Excluded a [7,2,1] :=
  predecessor_excluded a [7,2,1] 3 1 1 2 (by decide) (by decide +kernel)

theorem node_2258 : Excluded a [7,2,4] :=
  source_excluded a [7,2,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_2261 : Excluded a [7,2,5,0,1] :=
  source_excluded a [7,2,5,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2262 : Excluded a [7,2,5,0,3] :=
  source_excluded a [7,2,5,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2265 : Excluded a [7,2,5,0,6,1,3] :=
  predecessor_excluded a [7,2,5,0,6,1,3] 0 3 4 6 (by decide) (by decide +kernel)

theorem node_2267 : Excluded a [7,2,5,0,6,1,4,3] :=
  branch_excluded a [7,2,5,0,6,1,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,5,0,6,1,4,3,0] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,4,3,1] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,4,3,2] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,4,3,4] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,4,3,5] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,4,3,6] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,4,3,8] (by decide +kernel)))

theorem node_2266 : Excluded a [7,2,5,0,6,1,4] :=
  branch_excluded a [7,2,5,0,6,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,5,0,6,1,4,0] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,4,1] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,4,2] (by decide +kernel))
      node_2267
      (invalid_excluded a [7,2,5,0,6,1,4,4] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,4,5] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,4,6] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,4,8] (by decide +kernel)))

theorem node_2268 : Excluded a [7,2,5,0,6,1,8] :=
  source_excluded a [7,2,5,0,6,1,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_2264 : Excluded a [7,2,5,0,6,1] :=
  branch_excluded a [7,2,5,0,6,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,5,0,6,1,0] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,2] (by decide +kernel))
      node_2265
      node_2266
      (invalid_excluded a [7,2,5,0,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,1,7] (by decide +kernel))
      node_2268)

theorem node_2269 : Excluded a [7,2,5,0,6,3] :=
  source_excluded a [7,2,5,0,6,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2270 : Excluded a [7,2,5,0,6,4] :=
  source_excluded a [7,2,5,0,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_2272 : Excluded a [7,2,5,0,6,8,1] :=
  source_excluded a [7,2,5,0,6,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2273 : Excluded a [7,2,5,0,6,8,3] :=
  predecessor_excluded a [7,2,5,0,6,8,3] 0 3 4 6 (by decide) (by decide +kernel)

theorem node_2275 : Excluded a [7,2,5,0,6,8,4,1] :=
  source_excluded a [7,2,5,0,6,8,4,1] 0 2 7 (by decide) (by decide +kernel)

def b_2277 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 2
  | 2 => 5
  | 3 => 0
  | 4 => 6
  | 5 => 8
  | 6 => 4
  | 7 => 3
  | 8 => 1
  | _ => 0

def cert_2277 : LosingRegion (edgeOf a b_2277) 0 :=
  losingMask a b_2277 0 1224350996643797984609280
    (by decide +kernel) (by decide +kernel)

theorem node_2277 : Excluded a [7,2,5,0,6,8,4,3,1] :=
  losing_excluded a [7,2,5,0,6,8,4,3,1] (by decide) b_2277 (by decide +kernel) 2 0 3 cert_2277 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2277 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1224350996643797984609280 2 3; decide +kernel)

theorem node_2276 : Excluded a [7,2,5,0,6,8,4,3] :=
  branch_excluded a [7,2,5,0,6,8,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,5,0,6,8,4,3,0] (by decide +kernel))
      node_2277
      (invalid_excluded a [7,2,5,0,6,8,4,3,2] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,8,4,3,5] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,8,4,3,6] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,8,4,3,8] (by decide +kernel)))

theorem node_2274 : Excluded a [7,2,5,0,6,8,4] :=
  branch_excluded a [7,2,5,0,6,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,5,0,6,8,4,0] (by decide +kernel))
      node_2275
      (invalid_excluded a [7,2,5,0,6,8,4,2] (by decide +kernel))
      node_2276
      (invalid_excluded a [7,2,5,0,6,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,8,4,8] (by decide +kernel)))

theorem node_2271 : Excluded a [7,2,5,0,6,8] :=
  branch_excluded a [7,2,5,0,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,5,0,6,8,0] (by decide +kernel))
      node_2272
      (invalid_excluded a [7,2,5,0,6,8,2] (by decide +kernel))
      node_2273
      node_2274
      (invalid_excluded a [7,2,5,0,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,8,8] (by decide +kernel)))

theorem node_2263 : Excluded a [7,2,5,0,6] :=
  branch_excluded a [7,2,5,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,5,0,6,0] (by decide +kernel))
      node_2264
      (invalid_excluded a [7,2,5,0,6,2] (by decide +kernel))
      node_2269
      node_2270
      (invalid_excluded a [7,2,5,0,6,5] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,6] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,6,7] (by decide +kernel))
      node_2271)

theorem node_2278 : Excluded a [7,2,5,0,8] :=
  predecessor_excluded a [7,2,5,0,8] 0 5 4 2 (by decide) (by decide +kernel)

theorem node_2260 : Excluded a [7,2,5,0] :=
  branch_excluded a [7,2,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,5,0,0] (by decide +kernel))
      node_2261
      (invalid_excluded a [7,2,5,0,2] (by decide +kernel))
      node_2262
      (invalid_excluded a [7,2,5,0,4] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,5] (by decide +kernel))
      node_2263
      (invalid_excluded a [7,2,5,0,7] (by decide +kernel))
      node_2278)

theorem node_2279 : Excluded a [7,2,5,1] :=
  predecessor_excluded a [7,2,5,1] 0 2 3 1 (by decide) (by decide +kernel)

theorem node_2280 : Excluded a [7,2,5,6] :=
  predecessor_excluded a [7,2,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_2282 : Excluded a [7,2,5,8,0] :=
  source_excluded a [7,2,5,8,0] 1 3 4 (by decide) (by decide +kernel)

theorem node_2283 : Excluded a [7,2,5,8,1] :=
  source_excluded a [7,2,5,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2284 : Excluded a [7,2,5,8,3] :=
  source_excluded a [7,2,5,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2286 : Excluded a [7,2,5,8,6,0] :=
  predecessor_excluded a [7,2,5,8,6,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2288 : Excluded a [7,2,5,8,6,1,0] :=
  source_excluded a [7,2,5,8,6,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2289 : Excluded a [7,2,5,8,6,1,3] :=
  predecessor_excluded a [7,2,5,8,6,1,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_2291 : Excluded a [7,2,5,8,6,1,4,0] :=
  predecessor_excluded a [7,2,5,8,6,1,4,0] 2 0 0 7 (by decide) (by decide +kernel)

theorem node_2292 : Excluded a [7,2,5,8,6,1,4,3] :=
  source_excluded a [7,2,5,8,6,1,4,3] 7 0 3 (by decide) (by decide +kernel)

theorem node_2290 : Excluded a [7,2,5,8,6,1,4] :=
  branch_excluded a [7,2,5,8,6,1,4] (by decide)
    (fin9_cases _
      node_2291
      (invalid_excluded a [7,2,5,8,6,1,4,1] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,6,1,4,2] (by decide +kernel))
      node_2292
      (invalid_excluded a [7,2,5,8,6,1,4,4] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,6,1,4,5] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,6,1,4,6] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,6,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,6,1,4,8] (by decide +kernel)))

theorem node_2287 : Excluded a [7,2,5,8,6,1] :=
  branch_excluded a [7,2,5,8,6,1] (by decide)
    (fin9_cases _
      node_2288
      (invalid_excluded a [7,2,5,8,6,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,6,1,2] (by decide +kernel))
      node_2289
      node_2290
      (invalid_excluded a [7,2,5,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,6,1,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,6,1,8] (by decide +kernel)))

theorem node_2293 : Excluded a [7,2,5,8,6,3] :=
  source_excluded a [7,2,5,8,6,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2294 : Excluded a [7,2,5,8,6,4] :=
  source_excluded a [7,2,5,8,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_2285 : Excluded a [7,2,5,8,6] :=
  branch_excluded a [7,2,5,8,6] (by decide)
    (fin9_cases _
      node_2286
      node_2287
      (invalid_excluded a [7,2,5,8,6,2] (by decide +kernel))
      node_2293
      node_2294
      (invalid_excluded a [7,2,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,6,8] (by decide +kernel)))

theorem node_2281 : Excluded a [7,2,5,8] :=
  branch_excluded a [7,2,5,8] (by decide)
    (fin9_cases _
      node_2282
      node_2283
      (invalid_excluded a [7,2,5,8,2] (by decide +kernel))
      node_2284
      (invalid_excluded a [7,2,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,5] (by decide +kernel))
      node_2285
      (invalid_excluded a [7,2,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,8] (by decide +kernel)))

theorem node_2259 : Excluded a [7,2,5] :=
  branch_excluded a [7,2,5] (by decide)
    (fin9_cases _
      node_2260
      node_2279
      (invalid_excluded a [7,2,5,2] (by decide +kernel))
      (invalid_excluded a [7,2,5,3] (by decide +kernel))
      (invalid_excluded a [7,2,5,4] (by decide +kernel))
      (invalid_excluded a [7,2,5,5] (by decide +kernel))
      node_2280
      (invalid_excluded a [7,2,5,7] (by decide +kernel))
      node_2281)

theorem node_2297 : Excluded a [7,2,6,0,1] :=
  source_excluded a [7,2,6,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2298 : Excluded a [7,2,6,0,3] :=
  source_excluded a [7,2,6,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2299 : Excluded a [7,2,6,0,5] :=
  predecessor_excluded a [7,2,6,0,5] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_2302 : Excluded a [7,2,6,0,8,1,3] :=
  source_excluded a [7,2,6,0,8,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2303 : Excluded a [7,2,6,0,8,1,4] :=
  predecessor_excluded a [7,2,6,0,8,1,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_2306 : Excluded a [7,2,6,0,8,1,5,3,4] :=
  predecessor_excluded a [7,2,6,0,8,1,5,3,4] 0 4 7 8 (by decide) (by decide +kernel)

theorem node_2305 : Excluded a [7,2,6,0,8,1,5,3] :=
  branch_excluded a [7,2,6,0,8,1,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,8,1,5,3,0] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,3,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,3,2] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,3,3] (by decide +kernel))
      node_2306
      (invalid_excluded a [7,2,6,0,8,1,5,3,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,3,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,3,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,3,8] (by decide +kernel)))

theorem node_2307 : Excluded a [7,2,6,0,8,1,5,4] :=
  source_excluded a [7,2,6,0,8,1,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_2304 : Excluded a [7,2,6,0,8,1,5] :=
  branch_excluded a [7,2,6,0,8,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,8,1,5,0] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,2] (by decide +kernel))
      node_2305
      node_2307
      (invalid_excluded a [7,2,6,0,8,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,8] (by decide +kernel)))

theorem node_2301 : Excluded a [7,2,6,0,8,1] :=
  branch_excluded a [7,2,6,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,2] (by decide +kernel))
      node_2302
      node_2303
      node_2304
      (invalid_excluded a [7,2,6,0,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,8] (by decide +kernel)))

theorem node_2308 : Excluded a [7,2,6,0,8,3] :=
  source_excluded a [7,2,6,0,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2310 : Excluded a [7,2,6,0,8,4,1] :=
  source_excluded a [7,2,6,0,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2311 : Excluded a [7,2,6,0,8,4,3] :=
  source_excluded a [7,2,6,0,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2313 : Excluded a [7,2,6,0,8,4,5,1] :=
  source_excluded a [7,2,6,0,8,4,5,1] 0 2 7 (by decide) (by decide +kernel)

def b_2315 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 2
  | 2 => 6
  | 3 => 0
  | 4 => 8
  | 5 => 4
  | 6 => 5
  | 7 => 3
  | 8 => 1
  | _ => 0

def cert_2315 : LosingRegion (edgeOf a b_2315) 0 :=
  losingMask a b_2315 0 1224350999594612315653120
    (by decide +kernel) (by decide +kernel)

theorem node_2315 : Excluded a [7,2,6,0,8,4,5,3,1] :=
  losing_excluded a [7,2,6,0,8,4,5,3,1] (by decide) b_2315 (by decide +kernel) 2 0 3 cert_2315 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2315 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1224350999594612315653120 2 3; decide +kernel)

theorem node_2314 : Excluded a [7,2,6,0,8,4,5,3] :=
  branch_excluded a [7,2,6,0,8,4,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,8,4,5,3,0] (by decide +kernel))
      node_2315
      (invalid_excluded a [7,2,6,0,8,4,5,3,2] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,4,5,3,3] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,4,5,3,4] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,4,5,3,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,4,5,3,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,4,5,3,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,4,5,3,8] (by decide +kernel)))

theorem node_2312 : Excluded a [7,2,6,0,8,4,5] :=
  branch_excluded a [7,2,6,0,8,4,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,8,4,5,0] (by decide +kernel))
      node_2313
      (invalid_excluded a [7,2,6,0,8,4,5,2] (by decide +kernel))
      node_2314
      (invalid_excluded a [7,2,6,0,8,4,5,4] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,4,5,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,4,5,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,4,5,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,4,5,8] (by decide +kernel)))

theorem node_2309 : Excluded a [7,2,6,0,8,4] :=
  branch_excluded a [7,2,6,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,8,4,0] (by decide +kernel))
      node_2310
      (invalid_excluded a [7,2,6,0,8,4,2] (by decide +kernel))
      node_2311
      (invalid_excluded a [7,2,6,0,8,4,4] (by decide +kernel))
      node_2312
      (invalid_excluded a [7,2,6,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,4,8] (by decide +kernel)))

theorem node_2300 : Excluded a [7,2,6,0,8] :=
  branch_excluded a [7,2,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,8,0] (by decide +kernel))
      node_2301
      (invalid_excluded a [7,2,6,0,8,2] (by decide +kernel))
      node_2308
      node_2309
      (invalid_excluded a [7,2,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,8] (by decide +kernel)))

theorem node_2296 : Excluded a [7,2,6,0] :=
  branch_excluded a [7,2,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,0] (by decide +kernel))
      node_2297
      (invalid_excluded a [7,2,6,0,2] (by decide +kernel))
      node_2298
      (invalid_excluded a [7,2,6,0,4] (by decide +kernel))
      node_2299
      (invalid_excluded a [7,2,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,7] (by decide +kernel))
      node_2300)

theorem node_2316 : Excluded a [7,2,6,1] :=
  predecessor_excluded a [7,2,6,1] 0 2 3 1 (by decide) (by decide +kernel)

theorem node_2318 : Excluded a [7,2,6,5,0] :=
  source_excluded a [7,2,6,5,0] 1 3 4 (by decide) (by decide +kernel)

theorem node_2319 : Excluded a [7,2,6,5,1] :=
  source_excluded a [7,2,6,5,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2320 : Excluded a [7,2,6,5,3] :=
  source_excluded a [7,2,6,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2322 : Excluded a [7,2,6,5,8,0] :=
  predecessor_excluded a [7,2,6,5,8,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2324 : Excluded a [7,2,6,5,8,1,0] :=
  source_excluded a [7,2,6,5,8,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2325 : Excluded a [7,2,6,5,8,1,3] :=
  source_excluded a [7,2,6,5,8,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2326 : Excluded a [7,2,6,5,8,1,4] :=
  predecessor_excluded a [7,2,6,5,8,1,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_2323 : Excluded a [7,2,6,5,8,1] :=
  branch_excluded a [7,2,6,5,8,1] (by decide)
    (fin9_cases _
      node_2324
      (invalid_excluded a [7,2,6,5,8,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,5,8,1,2] (by decide +kernel))
      node_2325
      node_2326
      (invalid_excluded a [7,2,6,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,5,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,5,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,5,8,1,8] (by decide +kernel)))

theorem node_2327 : Excluded a [7,2,6,5,8,3] :=
  source_excluded a [7,2,6,5,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2328 : Excluded a [7,2,6,5,8,4] :=
  source_excluded a [7,2,6,5,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2321 : Excluded a [7,2,6,5,8] :=
  branch_excluded a [7,2,6,5,8] (by decide)
    (fin9_cases _
      node_2322
      node_2323
      (invalid_excluded a [7,2,6,5,8,2] (by decide +kernel))
      node_2327
      node_2328
      (invalid_excluded a [7,2,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,5,8,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,5,8,8] (by decide +kernel)))

theorem node_2317 : Excluded a [7,2,6,5] :=
  branch_excluded a [7,2,6,5] (by decide)
    (fin9_cases _
      node_2318
      node_2319
      (invalid_excluded a [7,2,6,5,2] (by decide +kernel))
      node_2320
      (invalid_excluded a [7,2,6,5,4] (by decide +kernel))
      (invalid_excluded a [7,2,6,5,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,5,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,5,7] (by decide +kernel))
      node_2321)

theorem node_2330 : Excluded a [7,2,6,8,0] :=
  source_excluded a [7,2,6,8,0] 1 3 4 (by decide) (by decide +kernel)

theorem node_2331 : Excluded a [7,2,6,8,1] :=
  source_excluded a [7,2,6,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2332 : Excluded a [7,2,6,8,3] :=
  source_excluded a [7,2,6,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2333 : Excluded a [7,2,6,8,5] :=
  predecessor_excluded a [7,2,6,8,5] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_2329 : Excluded a [7,2,6,8] :=
  branch_excluded a [7,2,6,8] (by decide)
    (fin9_cases _
      node_2330
      node_2331
      (invalid_excluded a [7,2,6,8,2] (by decide +kernel))
      node_2332
      (invalid_excluded a [7,2,6,8,4] (by decide +kernel))
      node_2333
      (invalid_excluded a [7,2,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,8] (by decide +kernel)))

theorem node_2295 : Excluded a [7,2,6] :=
  branch_excluded a [7,2,6] (by decide)
    (fin9_cases _
      node_2296
      node_2316
      (invalid_excluded a [7,2,6,2] (by decide +kernel))
      (invalid_excluded a [7,2,6,3] (by decide +kernel))
      (invalid_excluded a [7,2,6,4] (by decide +kernel))
      node_2317
      (invalid_excluded a [7,2,6,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,7] (by decide +kernel))
      node_2329)

theorem node_2336 : Excluded a [7,2,8,0,1] :=
  source_excluded a [7,2,8,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2337 : Excluded a [7,2,8,0,3] :=
  source_excluded a [7,2,8,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2341 : Excluded a [7,2,8,0,5,1,3,4] :=
  predecessor_excluded a [7,2,8,0,5,1,3,4] 0 5 7 4 (by decide) (by decide +kernel)

theorem node_2343 : Excluded a [7,2,8,0,5,1,3,6,4] :=
  source_excluded a [7,2,8,0,5,1,3,6,4] 8 0 4 (by decide) (by decide +kernel)

theorem node_2342 : Excluded a [7,2,8,0,5,1,3,6] :=
  branch_excluded a [7,2,8,0,5,1,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,5,1,3,6,0] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,3,6,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,3,6,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,3,6,3] (by decide +kernel))
      node_2343
      (invalid_excluded a [7,2,8,0,5,1,3,6,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,3,6,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,3,6,8] (by decide +kernel)))

theorem node_2340 : Excluded a [7,2,8,0,5,1,3] :=
  branch_excluded a [7,2,8,0,5,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,5,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,3,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,3,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,3,3] (by decide +kernel))
      node_2341
      (invalid_excluded a [7,2,8,0,5,1,3,5] (by decide +kernel))
      node_2342
      (invalid_excluded a [7,2,8,0,5,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,3,8] (by decide +kernel)))

theorem node_2345 : Excluded a [7,2,8,0,5,1,4,3] :=
  source_excluded a [7,2,8,0,5,1,4,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_2347 : Excluded a [7,2,8,0,5,1,4,6,3] :=
  source_excluded a [7,2,8,0,5,1,4,6,3] 2 0 8 (by decide) (by decide +kernel)

theorem node_2346 : Excluded a [7,2,8,0,5,1,4,6] :=
  branch_excluded a [7,2,8,0,5,1,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,5,1,4,6,0] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,4,6,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,4,6,2] (by decide +kernel))
      node_2347
      (invalid_excluded a [7,2,8,0,5,1,4,6,4] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,4,6,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,4,6,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,4,6,8] (by decide +kernel)))

theorem node_2344 : Excluded a [7,2,8,0,5,1,4] :=
  branch_excluded a [7,2,8,0,5,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,5,1,4,0] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,4,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,4,2] (by decide +kernel))
      node_2345
      (invalid_excluded a [7,2,8,0,5,1,4,4] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,4,5] (by decide +kernel))
      node_2346
      (invalid_excluded a [7,2,8,0,5,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,4,8] (by decide +kernel)))

theorem node_2339 : Excluded a [7,2,8,0,5,1] :=
  branch_excluded a [7,2,8,0,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,5,1,0] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,2] (by decide +kernel))
      node_2340
      node_2344
      (invalid_excluded a [7,2,8,0,5,1,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,1,8] (by decide +kernel)))

theorem node_2348 : Excluded a [7,2,8,0,5,3] :=
  predecessor_excluded a [7,2,8,0,5,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_2350 : Excluded a [7,2,8,0,5,4,1] :=
  source_excluded a [7,2,8,0,5,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2352 : Excluded a [7,2,8,0,5,4,3,1] :=
  source_excluded a [7,2,8,0,5,4,3,1] 0 2 7 (by decide) (by decide +kernel)

def b_2354 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 2
  | 2 => 8
  | 3 => 0
  | 4 => 5
  | 5 => 4
  | 6 => 3
  | 7 => 6
  | 8 => 1
  | _ => 0

def cert_2354 : LosingRegion (edgeOf a b_2354) 0 :=
  losingMask a b_2354 0 1224404015930049427407872
    (by decide +kernel) (by decide +kernel)

theorem node_2354 : Excluded a [7,2,8,0,5,4,3,6,1] :=
  losing_excluded a [7,2,8,0,5,4,3,6,1] (by decide) b_2354 (by decide +kernel) 2 0 3 cert_2354 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2354 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1224404015930049427407872 2 3; decide +kernel)

theorem node_2353 : Excluded a [7,2,8,0,5,4,3,6] :=
  branch_excluded a [7,2,8,0,5,4,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,5,4,3,6,0] (by decide +kernel))
      node_2354
      (invalid_excluded a [7,2,8,0,5,4,3,6,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,4,3,6,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,4,3,6,8] (by decide +kernel)))

theorem node_2351 : Excluded a [7,2,8,0,5,4,3] :=
  branch_excluded a [7,2,8,0,5,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,5,4,3,0] (by decide +kernel))
      node_2352
      (invalid_excluded a [7,2,8,0,5,4,3,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,4,3,4] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,4,3,5] (by decide +kernel))
      node_2353
      (invalid_excluded a [7,2,8,0,5,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,4,3,8] (by decide +kernel)))

theorem node_2349 : Excluded a [7,2,8,0,5,4] :=
  branch_excluded a [7,2,8,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,5,4,0] (by decide +kernel))
      node_2350
      (invalid_excluded a [7,2,8,0,5,4,2] (by decide +kernel))
      node_2351
      (invalid_excluded a [7,2,8,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,4,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,4,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,4,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,4,8] (by decide +kernel)))

theorem node_2338 : Excluded a [7,2,8,0,5] :=
  branch_excluded a [7,2,8,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,5,0] (by decide +kernel))
      node_2339
      (invalid_excluded a [7,2,8,0,5,2] (by decide +kernel))
      node_2348
      node_2349
      (invalid_excluded a [7,2,8,0,5,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5,8] (by decide +kernel)))

theorem node_2357 : Excluded a [7,2,8,0,6,1,3] :=
  predecessor_excluded a [7,2,8,0,6,1,3] 0 3 4 6 (by decide) (by decide +kernel)

theorem node_2359 : Excluded a [7,2,8,0,6,1,4,3] :=
  source_excluded a [7,2,8,0,6,1,4,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_2360 : Excluded a [7,2,8,0,6,1,4,5] :=
  source_excluded a [7,2,8,0,6,1,4,5] 7 0 8 (by decide) (by decide +kernel)

theorem node_2358 : Excluded a [7,2,8,0,6,1,4] :=
  branch_excluded a [7,2,8,0,6,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,6,1,4,0] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,4,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,4,2] (by decide +kernel))
      node_2359
      (invalid_excluded a [7,2,8,0,6,1,4,4] (by decide +kernel))
      node_2360
      (invalid_excluded a [7,2,8,0,6,1,4,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,4,8] (by decide +kernel)))

theorem node_2362 : Excluded a [7,2,8,0,6,1,5,3] :=
  source_excluded a [7,2,8,0,6,1,5,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_2364 : Excluded a [7,2,8,0,6,1,5,4,3] :=
  source_excluded a [7,2,8,0,6,1,5,4,3] 2 0 8 (by decide) (by decide +kernel)

theorem node_2363 : Excluded a [7,2,8,0,6,1,5,4] :=
  branch_excluded a [7,2,8,0,6,1,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,6,1,5,4,0] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,5,4,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,5,4,2] (by decide +kernel))
      node_2364
      (invalid_excluded a [7,2,8,0,6,1,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,5,4,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,5,4,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,5,4,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,5,4,8] (by decide +kernel)))

theorem node_2361 : Excluded a [7,2,8,0,6,1,5] :=
  branch_excluded a [7,2,8,0,6,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,6,1,5,0] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,5,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,5,2] (by decide +kernel))
      node_2362
      node_2363
      (invalid_excluded a [7,2,8,0,6,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,5,8] (by decide +kernel)))

theorem node_2356 : Excluded a [7,2,8,0,6,1] :=
  branch_excluded a [7,2,8,0,6,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,6,1,0] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,2] (by decide +kernel))
      node_2357
      node_2358
      node_2361
      (invalid_excluded a [7,2,8,0,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,1,8] (by decide +kernel)))

theorem node_2366 : Excluded a [7,2,8,0,6,3,1] :=
  source_excluded a [7,2,8,0,6,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2367 : Excluded a [7,2,8,0,6,3,4] :=
  predecessor_excluded a [7,2,8,0,6,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_2369 : Excluded a [7,2,8,0,6,3,5,1] :=
  source_excluded a [7,2,8,0,6,3,5,1] 0 2 7 (by decide) (by decide +kernel)

def b_2371 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 2
  | 2 => 8
  | 3 => 0
  | 4 => 6
  | 5 => 3
  | 6 => 5
  | 7 => 4
  | 8 => 1
  | _ => 0

def cert_2371 : LosingRegion (edgeOf a b_2371) 0 :=
  losingMask a b_2371 0 1221983197635882276357120
    (by decide +kernel) (by decide +kernel)

theorem node_2371 : Excluded a [7,2,8,0,6,3,5,4,1] :=
  losing_excluded a [7,2,8,0,6,3,5,4,1] (by decide) b_2371 (by decide +kernel) 4 0 1 cert_2371 (by change 4 ≠ 0 ∧ ¬ edgeOf a b_2371 4 0 ∧ 1 ≠ 4 ∧ maskRegion 1221983197635882276357120 4 1; decide +kernel)

theorem node_2370 : Excluded a [7,2,8,0,6,3,5,4] :=
  branch_excluded a [7,2,8,0,6,3,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,6,3,5,4,0] (by decide +kernel))
      node_2371
      (invalid_excluded a [7,2,8,0,6,3,5,4,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,3,5,4,3] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,3,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,3,5,4,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,3,5,4,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,3,5,4,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,3,5,4,8] (by decide +kernel)))

theorem node_2368 : Excluded a [7,2,8,0,6,3,5] :=
  branch_excluded a [7,2,8,0,6,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,6,3,5,0] (by decide +kernel))
      node_2369
      (invalid_excluded a [7,2,8,0,6,3,5,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,3,5,3] (by decide +kernel))
      node_2370
      (invalid_excluded a [7,2,8,0,6,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,3,5,8] (by decide +kernel)))

theorem node_2365 : Excluded a [7,2,8,0,6,3] :=
  branch_excluded a [7,2,8,0,6,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,6,3,0] (by decide +kernel))
      node_2366
      (invalid_excluded a [7,2,8,0,6,3,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,3,3] (by decide +kernel))
      node_2367
      node_2368
      (invalid_excluded a [7,2,8,0,6,3,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,3,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,3,8] (by decide +kernel)))

theorem node_2372 : Excluded a [7,2,8,0,6,4] :=
  source_excluded a [7,2,8,0,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_2355 : Excluded a [7,2,8,0,6] :=
  branch_excluded a [7,2,8,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,6,0] (by decide +kernel))
      node_2356
      (invalid_excluded a [7,2,8,0,6,2] (by decide +kernel))
      node_2365
      node_2372
      (invalid_excluded a [7,2,8,0,6,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,6,8] (by decide +kernel)))

theorem node_2335 : Excluded a [7,2,8,0] :=
  branch_excluded a [7,2,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,0] (by decide +kernel))
      node_2336
      (invalid_excluded a [7,2,8,0,2] (by decide +kernel))
      node_2337
      (invalid_excluded a [7,2,8,0,4] (by decide +kernel))
      node_2338
      node_2355
      (invalid_excluded a [7,2,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,8] (by decide +kernel)))

theorem node_2373 : Excluded a [7,2,8,1] :=
  predecessor_excluded a [7,2,8,1] 0 2 3 1 (by decide) (by decide +kernel)

theorem node_2374 : Excluded a [7,2,8,5] :=
  predecessor_excluded a [7,2,8,5] 0 5 2 3 (by decide) (by decide +kernel)

theorem node_2376 : Excluded a [7,2,8,6,0] :=
  source_excluded a [7,2,8,6,0] 1 3 4 (by decide) (by decide +kernel)

theorem node_2377 : Excluded a [7,2,8,6,1] :=
  source_excluded a [7,2,8,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2378 : Excluded a [7,2,8,6,3] :=
  source_excluded a [7,2,8,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2380 : Excluded a [7,2,8,6,5,0] :=
  predecessor_excluded a [7,2,8,6,5,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2382 : Excluded a [7,2,8,6,5,1,0] :=
  source_excluded a [7,2,8,6,5,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2384 : Excluded a [7,2,8,6,5,1,3,0] :=
  predecessor_excluded a [7,2,8,6,5,1,3,0] 2 0 0 7 (by decide) (by decide +kernel)

theorem node_2385 : Excluded a [7,2,8,6,5,1,3,4] :=
  predecessor_excluded a [7,2,8,6,5,1,3,4] 0 5 7 4 (by decide) (by decide +kernel)

theorem node_2383 : Excluded a [7,2,8,6,5,1,3] :=
  branch_excluded a [7,2,8,6,5,1,3] (by decide)
    (fin9_cases _
      node_2384
      (invalid_excluded a [7,2,8,6,5,1,3,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,5,1,3,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,5,1,3,3] (by decide +kernel))
      node_2385
      (invalid_excluded a [7,2,8,6,5,1,3,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,5,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,5,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,5,1,3,8] (by decide +kernel)))

theorem node_2386 : Excluded a [7,2,8,6,5,1,4] :=
  source_excluded a [7,2,8,6,5,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2381 : Excluded a [7,2,8,6,5,1] :=
  branch_excluded a [7,2,8,6,5,1] (by decide)
    (fin9_cases _
      node_2382
      (invalid_excluded a [7,2,8,6,5,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,5,1,2] (by decide +kernel))
      node_2383
      node_2386
      (invalid_excluded a [7,2,8,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,5,1,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,5,1,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,5,1,8] (by decide +kernel)))

theorem node_2387 : Excluded a [7,2,8,6,5,3] :=
  source_excluded a [7,2,8,6,5,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2388 : Excluded a [7,2,8,6,5,4] :=
  source_excluded a [7,2,8,6,5,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2379 : Excluded a [7,2,8,6,5] :=
  branch_excluded a [7,2,8,6,5] (by decide)
    (fin9_cases _
      node_2380
      node_2381
      (invalid_excluded a [7,2,8,6,5,2] (by decide +kernel))
      node_2387
      node_2388
      (invalid_excluded a [7,2,8,6,5,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,5,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,5,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,5,8] (by decide +kernel)))

theorem node_2375 : Excluded a [7,2,8,6] :=
  branch_excluded a [7,2,8,6] (by decide)
    (fin9_cases _
      node_2376
      node_2377
      (invalid_excluded a [7,2,8,6,2] (by decide +kernel))
      node_2378
      (invalid_excluded a [7,2,8,6,4] (by decide +kernel))
      node_2379
      (invalid_excluded a [7,2,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,8] (by decide +kernel)))

theorem node_2334 : Excluded a [7,2,8] :=
  branch_excluded a [7,2,8] (by decide)
    (fin9_cases _
      node_2335
      node_2373
      (invalid_excluded a [7,2,8,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,3] (by decide +kernel))
      (invalid_excluded a [7,2,8,4] (by decide +kernel))
      node_2374
      node_2375
      (invalid_excluded a [7,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,8] (by decide +kernel)))

theorem node_2255 : Excluded a [7,2] :=
  branch_excluded a [7,2] (by decide)
    (fin9_cases _
      node_2256
      node_2257
      (invalid_excluded a [7,2,2] (by decide +kernel))
      (invalid_excluded a [7,2,3] (by decide +kernel))
      node_2258
      node_2259
      node_2295
      (invalid_excluded a [7,2,7] (by decide +kernel))
      node_2334)

theorem node_2390 : Excluded a [7,3,0] :=
  source_excluded a [7,3,0] 1 2 2 (by decide) (by decide +kernel)

theorem node_2391 : Excluded a [7,3,1] :=
  source_excluded a [7,3,1] 2 0 1 (by decide) (by decide +kernel)

theorem node_2392 : Excluded a [7,3,4] :=
  source_excluded a [7,3,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_2394 : Excluded a [7,3,5,0] :=
  source_excluded a [7,3,5,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2395 : Excluded a [7,3,5,1] :=
  predecessor_excluded a [7,3,5,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_2396 : Excluded a [7,3,5,2] :=
  source_excluded a [7,3,5,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2397 : Excluded a [7,3,5,6] :=
  predecessor_excluded a [7,3,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_2402 : Excluded a [7,3,5,8,0,1,2,4] :=
  source_excluded a [7,3,5,8,0,1,2,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_2404 : Excluded a [7,3,5,8,0,1,2,6,4] :=
  source_excluded a [7,3,5,8,0,1,2,6,4] 3 0 8 (by decide) (by decide +kernel)

theorem node_2403 : Excluded a [7,3,5,8,0,1,2,6] :=
  branch_excluded a [7,3,5,8,0,1,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,5,8,0,1,2,6,0] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,2,6,1] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,2,6,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,2,6,3] (by decide +kernel))
      node_2404
      (invalid_excluded a [7,3,5,8,0,1,2,6,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,2,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,2,6,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,2,6,8] (by decide +kernel)))

theorem node_2401 : Excluded a [7,3,5,8,0,1,2] :=
  branch_excluded a [7,3,5,8,0,1,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,5,8,0,1,2,0] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,2,1] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,2,3] (by decide +kernel))
      node_2402
      (invalid_excluded a [7,3,5,8,0,1,2,5] (by decide +kernel))
      node_2403
      (invalid_excluded a [7,3,5,8,0,1,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,2,8] (by decide +kernel)))

theorem node_2406 : Excluded a [7,3,5,8,0,1,4,2] :=
  predecessor_excluded a [7,3,5,8,0,1,4,2] 0 5 7 2 (by decide) (by decide +kernel)

theorem node_2408 : Excluded a [7,3,5,8,0,1,4,6,2] :=
  source_excluded a [7,3,5,8,0,1,4,6,2] 8 0 2 (by decide) (by decide +kernel)

theorem node_2407 : Excluded a [7,3,5,8,0,1,4,6] :=
  branch_excluded a [7,3,5,8,0,1,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,5,8,0,1,4,6,0] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,4,6,1] (by decide +kernel))
      node_2408
      (invalid_excluded a [7,3,5,8,0,1,4,6,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,4,6,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,4,6,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,4,6,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,4,6,8] (by decide +kernel)))

theorem node_2405 : Excluded a [7,3,5,8,0,1,4] :=
  branch_excluded a [7,3,5,8,0,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,5,8,0,1,4,0] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,4,1] (by decide +kernel))
      node_2406
      (invalid_excluded a [7,3,5,8,0,1,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,4,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,4,5] (by decide +kernel))
      node_2407
      (invalid_excluded a [7,3,5,8,0,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,4,8] (by decide +kernel)))

theorem node_2400 : Excluded a [7,3,5,8,0,1] :=
  branch_excluded a [7,3,5,8,0,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,5,8,0,1,0] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,1] (by decide +kernel))
      node_2401
      (invalid_excluded a [7,3,5,8,0,1,3] (by decide +kernel))
      node_2405
      (invalid_excluded a [7,3,5,8,0,1,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,1,8] (by decide +kernel)))

theorem node_2410 : Excluded a [7,3,5,8,0,2,1] :=
  source_excluded a [7,3,5,8,0,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2412 : Excluded a [7,3,5,8,0,2,4,1] :=
  source_excluded a [7,3,5,8,0,2,4,1] 0 2 7 (by decide) (by decide +kernel)

def b_2414 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 3
  | 2 => 5
  | 3 => 8
  | 4 => 0
  | 5 => 2
  | 6 => 4
  | 7 => 6
  | 8 => 1
  | _ => 0

def cert_2414 : LosingRegion (edgeOf a b_2414) 0 :=
  losingMask a b_2414 0 1224514912561915848295424
    (by decide +kernel) (by decide +kernel)

theorem node_2414 : Excluded a [7,3,5,8,0,2,4,6,1] :=
  losing_excluded a [7,3,5,8,0,2,4,6,1] (by decide) b_2414 (by decide +kernel) 2 0 1 cert_2414 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2414 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1224514912561915848295424 2 1; decide +kernel)

theorem node_2413 : Excluded a [7,3,5,8,0,2,4,6] :=
  branch_excluded a [7,3,5,8,0,2,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,5,8,0,2,4,6,0] (by decide +kernel))
      node_2414
      (invalid_excluded a [7,3,5,8,0,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,6,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,6,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,6,8] (by decide +kernel)))

theorem node_2411 : Excluded a [7,3,5,8,0,2,4] :=
  branch_excluded a [7,3,5,8,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,5,8,0,2,4,0] (by decide +kernel))
      node_2412
      (invalid_excluded a [7,3,5,8,0,2,4,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,5] (by decide +kernel))
      node_2413
      (invalid_excluded a [7,3,5,8,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,8] (by decide +kernel)))

theorem node_2409 : Excluded a [7,3,5,8,0,2] :=
  branch_excluded a [7,3,5,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,5,8,0,2,0] (by decide +kernel))
      node_2410
      (invalid_excluded a [7,3,5,8,0,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,3] (by decide +kernel))
      node_2411
      (invalid_excluded a [7,3,5,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,8] (by decide +kernel)))

theorem node_2415 : Excluded a [7,3,5,8,0,4] :=
  predecessor_excluded a [7,3,5,8,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2399 : Excluded a [7,3,5,8,0] :=
  branch_excluded a [7,3,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,5,8,0,0] (by decide +kernel))
      node_2400
      node_2409
      (invalid_excluded a [7,3,5,8,0,3] (by decide +kernel))
      node_2415
      (invalid_excluded a [7,3,5,8,0,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,8] (by decide +kernel)))

theorem node_2416 : Excluded a [7,3,5,8,1] :=
  predecessor_excluded a [7,3,5,8,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_2418 : Excluded a [7,3,5,8,6,0] :=
  predecessor_excluded a [7,3,5,8,6,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2420 : Excluded a [7,3,5,8,6,1,0] :=
  source_excluded a [7,3,5,8,6,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2421 : Excluded a [7,3,5,8,6,1,2] :=
  source_excluded a [7,3,5,8,6,1,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_2423 : Excluded a [7,3,5,8,6,1,4,0] :=
  predecessor_excluded a [7,3,5,8,6,1,4,0] 2 0 0 7 (by decide) (by decide +kernel)

theorem node_2424 : Excluded a [7,3,5,8,6,1,4,2] :=
  predecessor_excluded a [7,3,5,8,6,1,4,2] 0 5 7 2 (by decide) (by decide +kernel)

theorem node_2422 : Excluded a [7,3,5,8,6,1,4] :=
  branch_excluded a [7,3,5,8,6,1,4] (by decide)
    (fin9_cases _
      node_2423
      (invalid_excluded a [7,3,5,8,6,1,4,1] (by decide +kernel))
      node_2424
      (invalid_excluded a [7,3,5,8,6,1,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,6,1,4,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,6,1,4,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,6,1,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,6,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,6,1,4,8] (by decide +kernel)))

theorem node_2419 : Excluded a [7,3,5,8,6,1] :=
  branch_excluded a [7,3,5,8,6,1] (by decide)
    (fin9_cases _
      node_2420
      (invalid_excluded a [7,3,5,8,6,1,1] (by decide +kernel))
      node_2421
      (invalid_excluded a [7,3,5,8,6,1,3] (by decide +kernel))
      node_2422
      (invalid_excluded a [7,3,5,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,6,1,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,6,1,8] (by decide +kernel)))

theorem node_2425 : Excluded a [7,3,5,8,6,2] :=
  source_excluded a [7,3,5,8,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2426 : Excluded a [7,3,5,8,6,4] :=
  source_excluded a [7,3,5,8,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_2417 : Excluded a [7,3,5,8,6] :=
  branch_excluded a [7,3,5,8,6] (by decide)
    (fin9_cases _
      node_2418
      node_2419
      node_2425
      (invalid_excluded a [7,3,5,8,6,3] (by decide +kernel))
      node_2426
      (invalid_excluded a [7,3,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,6,8] (by decide +kernel)))

theorem node_2398 : Excluded a [7,3,5,8] :=
  branch_excluded a [7,3,5,8] (by decide)
    (fin9_cases _
      node_2399
      node_2416
      (invalid_excluded a [7,3,5,8,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,5] (by decide +kernel))
      node_2417
      (invalid_excluded a [7,3,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,8] (by decide +kernel)))

theorem node_2393 : Excluded a [7,3,5] :=
  branch_excluded a [7,3,5] (by decide)
    (fin9_cases _
      node_2394
      node_2395
      node_2396
      (invalid_excluded a [7,3,5,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,5] (by decide +kernel))
      node_2397
      (invalid_excluded a [7,3,5,7] (by decide +kernel))
      node_2398)

theorem node_2428 : Excluded a [7,3,6,0] :=
  source_excluded a [7,3,6,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2429 : Excluded a [7,3,6,1] :=
  predecessor_excluded a [7,3,6,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_2430 : Excluded a [7,3,6,2] :=
  source_excluded a [7,3,6,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2435 : Excluded a [7,3,6,5,0,1,2,4] :=
  branch_excluded a [7,3,6,5,0,1,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,5,0,1,2,4,0] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,2,4,1] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,2,4,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,2,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,2,4,4] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,2,4,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,2,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,2,4,8] (by decide +kernel)))

theorem node_2434 : Excluded a [7,3,6,5,0,1,2] :=
  branch_excluded a [7,3,6,5,0,1,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,5,0,1,2,0] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,2,1] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,2,3] (by decide +kernel))
      node_2435
      (invalid_excluded a [7,3,6,5,0,1,2,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,2,8] (by decide +kernel)))

theorem node_2436 : Excluded a [7,3,6,5,0,1,4] :=
  predecessor_excluded a [7,3,6,5,0,1,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_2437 : Excluded a [7,3,6,5,0,1,8] :=
  source_excluded a [7,3,6,5,0,1,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_2433 : Excluded a [7,3,6,5,0,1] :=
  branch_excluded a [7,3,6,5,0,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,5,0,1,0] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,1] (by decide +kernel))
      node_2434
      (invalid_excluded a [7,3,6,5,0,1,3] (by decide +kernel))
      node_2436
      (invalid_excluded a [7,3,6,5,0,1,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,1,7] (by decide +kernel))
      node_2437)

theorem node_2438 : Excluded a [7,3,6,5,0,2] :=
  source_excluded a [7,3,6,5,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2439 : Excluded a [7,3,6,5,0,4] :=
  source_excluded a [7,3,6,5,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2441 : Excluded a [7,3,6,5,0,8,1] :=
  source_excluded a [7,3,6,5,0,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2443 : Excluded a [7,3,6,5,0,8,2,1] :=
  source_excluded a [7,3,6,5,0,8,2,1] 0 2 7 (by decide) (by decide +kernel)

def b_2445 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 3
  | 2 => 6
  | 3 => 5
  | 4 => 0
  | 5 => 8
  | 6 => 2
  | 7 => 4
  | 8 => 1
  | _ => 0

def cert_2445 : LosingRegion (edgeOf a b_2445) 0 :=
  losingMask a b_2445 0 1224425000060144330736640
    (by decide +kernel) (by decide +kernel)

theorem node_2445 : Excluded a [7,3,6,5,0,8,2,4,1] :=
  losing_excluded a [7,3,6,5,0,8,2,4,1] (by decide) b_2445 (by decide +kernel) 2 0 0 cert_2445 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2445 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1224425000060144330736640 2 0; decide +kernel)

theorem node_2444 : Excluded a [7,3,6,5,0,8,2,4] :=
  branch_excluded a [7,3,6,5,0,8,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,5,0,8,2,4,0] (by decide +kernel))
      node_2445
      (invalid_excluded a [7,3,6,5,0,8,2,4,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,8,2,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,8,2,4,4] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,8,2,4,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,8,2,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,8,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,8,2,4,8] (by decide +kernel)))

theorem node_2442 : Excluded a [7,3,6,5,0,8,2] :=
  branch_excluded a [7,3,6,5,0,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,5,0,8,2,0] (by decide +kernel))
      node_2443
      (invalid_excluded a [7,3,6,5,0,8,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,8,2,3] (by decide +kernel))
      node_2444
      (invalid_excluded a [7,3,6,5,0,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,8,2,8] (by decide +kernel)))

theorem node_2446 : Excluded a [7,3,6,5,0,8,4] :=
  predecessor_excluded a [7,3,6,5,0,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_2440 : Excluded a [7,3,6,5,0,8] :=
  branch_excluded a [7,3,6,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,5,0,8,0] (by decide +kernel))
      node_2441
      node_2442
      (invalid_excluded a [7,3,6,5,0,8,3] (by decide +kernel))
      node_2446
      (invalid_excluded a [7,3,6,5,0,8,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,8,8] (by decide +kernel)))

theorem node_2432 : Excluded a [7,3,6,5,0] :=
  branch_excluded a [7,3,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,5,0,0] (by decide +kernel))
      node_2433
      node_2438
      (invalid_excluded a [7,3,6,5,0,3] (by decide +kernel))
      node_2439
      (invalid_excluded a [7,3,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,0,7] (by decide +kernel))
      node_2440)

theorem node_2447 : Excluded a [7,3,6,5,1] :=
  predecessor_excluded a [7,3,6,5,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_2449 : Excluded a [7,3,6,5,8,0] :=
  predecessor_excluded a [7,3,6,5,8,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2451 : Excluded a [7,3,6,5,8,1,0] :=
  source_excluded a [7,3,6,5,8,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2453 : Excluded a [7,3,6,5,8,1,2,0] :=
  predecessor_excluded a [7,3,6,5,8,1,2,0] 2 0 0 7 (by decide) (by decide +kernel)

theorem node_2454 : Excluded a [7,3,6,5,8,1,2,4] :=
  source_excluded a [7,3,6,5,8,1,2,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_2452 : Excluded a [7,3,6,5,8,1,2] :=
  branch_excluded a [7,3,6,5,8,1,2] (by decide)
    (fin9_cases _
      node_2453
      (invalid_excluded a [7,3,6,5,8,1,2,1] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,8,1,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,8,1,2,3] (by decide +kernel))
      node_2454
      (invalid_excluded a [7,3,6,5,8,1,2,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,8,1,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,8,1,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,8,1,2,8] (by decide +kernel)))

theorem node_2455 : Excluded a [7,3,6,5,8,1,4] :=
  predecessor_excluded a [7,3,6,5,8,1,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_2450 : Excluded a [7,3,6,5,8,1] :=
  branch_excluded a [7,3,6,5,8,1] (by decide)
    (fin9_cases _
      node_2451
      (invalid_excluded a [7,3,6,5,8,1,1] (by decide +kernel))
      node_2452
      (invalid_excluded a [7,3,6,5,8,1,3] (by decide +kernel))
      node_2455
      (invalid_excluded a [7,3,6,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,8,1,8] (by decide +kernel)))

theorem node_2456 : Excluded a [7,3,6,5,8,2] :=
  source_excluded a [7,3,6,5,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2457 : Excluded a [7,3,6,5,8,4] :=
  source_excluded a [7,3,6,5,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2448 : Excluded a [7,3,6,5,8] :=
  branch_excluded a [7,3,6,5,8] (by decide)
    (fin9_cases _
      node_2449
      node_2450
      node_2456
      (invalid_excluded a [7,3,6,5,8,3] (by decide +kernel))
      node_2457
      (invalid_excluded a [7,3,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,8,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,8,8] (by decide +kernel)))

theorem node_2431 : Excluded a [7,3,6,5] :=
  branch_excluded a [7,3,6,5] (by decide)
    (fin9_cases _
      node_2432
      node_2447
      (invalid_excluded a [7,3,6,5,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,4] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,5,7] (by decide +kernel))
      node_2448)

theorem node_2462 : Excluded a [7,3,6,8,0,1,2,4] :=
  source_excluded a [7,3,6,8,0,1,2,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_2463 : Excluded a [7,3,6,8,0,1,2,5] :=
  source_excluded a [7,3,6,8,0,1,2,5] 7 0 8 (by decide) (by decide +kernel)

theorem node_2461 : Excluded a [7,3,6,8,0,1,2] :=
  branch_excluded a [7,3,6,8,0,1,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,8,0,1,2,0] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,2,1] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,2,3] (by decide +kernel))
      node_2462
      node_2463
      (invalid_excluded a [7,3,6,8,0,1,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,2,8] (by decide +kernel)))

theorem node_2464 : Excluded a [7,3,6,8,0,1,4] :=
  predecessor_excluded a [7,3,6,8,0,1,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_2467 : Excluded a [7,3,6,8,0,1,5,2,4] :=
  source_excluded a [7,3,6,8,0,1,5,2,4] 3 0 8 (by decide) (by decide +kernel)

theorem node_2466 : Excluded a [7,3,6,8,0,1,5,2] :=
  branch_excluded a [7,3,6,8,0,1,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,8,0,1,5,2,0] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,5,2,1] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,5,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,5,2,3] (by decide +kernel))
      node_2467
      (invalid_excluded a [7,3,6,8,0,1,5,2,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,5,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,5,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,5,2,8] (by decide +kernel)))

theorem node_2468 : Excluded a [7,3,6,8,0,1,5,4] :=
  source_excluded a [7,3,6,8,0,1,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_2465 : Excluded a [7,3,6,8,0,1,5] :=
  branch_excluded a [7,3,6,8,0,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,8,0,1,5,0] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,5,1] (by decide +kernel))
      node_2466
      (invalid_excluded a [7,3,6,8,0,1,5,3] (by decide +kernel))
      node_2468
      (invalid_excluded a [7,3,6,8,0,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,5,8] (by decide +kernel)))

theorem node_2460 : Excluded a [7,3,6,8,0,1] :=
  branch_excluded a [7,3,6,8,0,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,8,0,1,0] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,1] (by decide +kernel))
      node_2461
      (invalid_excluded a [7,3,6,8,0,1,3] (by decide +kernel))
      node_2464
      node_2465
      (invalid_excluded a [7,3,6,8,0,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,1,8] (by decide +kernel)))

theorem node_2469 : Excluded a [7,3,6,8,0,2] :=
  source_excluded a [7,3,6,8,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2471 : Excluded a [7,3,6,8,0,4,1] :=
  source_excluded a [7,3,6,8,0,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2472 : Excluded a [7,3,6,8,0,4,2] :=
  predecessor_excluded a [7,3,6,8,0,4,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2474 : Excluded a [7,3,6,8,0,4,5,1] :=
  source_excluded a [7,3,6,8,0,4,5,1] 0 2 7 (by decide) (by decide +kernel)

def b_2476 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 3
  | 2 => 6
  | 3 => 8
  | 4 => 0
  | 5 => 4
  | 6 => 5
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_2476 : LosingRegion (edgeOf a b_2476) 0 :=
  losingMask a b_2476 0 1222020091545829846287360
    (by decide +kernel) (by decide +kernel)

theorem node_2476 : Excluded a [7,3,6,8,0,4,5,2,1] :=
  losing_excluded a [7,3,6,8,0,4,5,2,1] (by decide) b_2476 (by decide +kernel) 2 0 1 cert_2476 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2476 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1222020091545829846287360 2 1; decide +kernel)

theorem node_2475 : Excluded a [7,3,6,8,0,4,5,2] :=
  branch_excluded a [7,3,6,8,0,4,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,8,0,4,5,2,0] (by decide +kernel))
      node_2476
      (invalid_excluded a [7,3,6,8,0,4,5,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,5,2,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,5,2,4] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,5,2,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,5,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,5,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,5,2,8] (by decide +kernel)))

theorem node_2473 : Excluded a [7,3,6,8,0,4,5] :=
  branch_excluded a [7,3,6,8,0,4,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,8,0,4,5,0] (by decide +kernel))
      node_2474
      node_2475
      (invalid_excluded a [7,3,6,8,0,4,5,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,5,4] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,5,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,5,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,5,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,5,8] (by decide +kernel)))

theorem node_2470 : Excluded a [7,3,6,8,0,4] :=
  branch_excluded a [7,3,6,8,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,8,0,4,0] (by decide +kernel))
      node_2471
      node_2472
      (invalid_excluded a [7,3,6,8,0,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,4] (by decide +kernel))
      node_2473
      (invalid_excluded a [7,3,6,8,0,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,8] (by decide +kernel)))

theorem node_2459 : Excluded a [7,3,6,8,0] :=
  branch_excluded a [7,3,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,8,0,0] (by decide +kernel))
      node_2460
      node_2469
      (invalid_excluded a [7,3,6,8,0,3] (by decide +kernel))
      node_2470
      (invalid_excluded a [7,3,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,8] (by decide +kernel)))

theorem node_2477 : Excluded a [7,3,6,8,1] :=
  predecessor_excluded a [7,3,6,8,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_2478 : Excluded a [7,3,6,8,5] :=
  predecessor_excluded a [7,3,6,8,5] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_2458 : Excluded a [7,3,6,8] :=
  branch_excluded a [7,3,6,8] (by decide)
    (fin9_cases _
      node_2459
      node_2477
      (invalid_excluded a [7,3,6,8,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,4] (by decide +kernel))
      node_2478
      (invalid_excluded a [7,3,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,8] (by decide +kernel)))

theorem node_2427 : Excluded a [7,3,6] :=
  branch_excluded a [7,3,6] (by decide)
    (fin9_cases _
      node_2428
      node_2429
      node_2430
      (invalid_excluded a [7,3,6,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,4] (by decide +kernel))
      node_2431
      (invalid_excluded a [7,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,7] (by decide +kernel))
      node_2458)

theorem node_2480 : Excluded a [7,3,8,0] :=
  source_excluded a [7,3,8,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2481 : Excluded a [7,3,8,1] :=
  predecessor_excluded a [7,3,8,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_2482 : Excluded a [7,3,8,2] :=
  source_excluded a [7,3,8,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2483 : Excluded a [7,3,8,5] :=
  predecessor_excluded a [7,3,8,5] 0 5 2 3 (by decide) (by decide +kernel)

theorem node_2487 : Excluded a [7,3,8,6,0,1,2] :=
  predecessor_excluded a [7,3,8,6,0,1,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_2488 : Excluded a [7,3,8,6,0,1,4] :=
  source_excluded a [7,3,8,6,0,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2490 : Excluded a [7,3,8,6,0,1,5,2] :=
  source_excluded a [7,3,8,6,0,1,5,2] 7 0 2 (by decide) (by decide +kernel)

theorem node_2492 : Excluded a [7,3,8,6,0,1,5,4,2] :=
  predecessor_excluded a [7,3,8,6,0,1,5,4,2] 0 2 7 8 (by decide) (by decide +kernel)

theorem node_2491 : Excluded a [7,3,8,6,0,1,5,4] :=
  branch_excluded a [7,3,8,6,0,1,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,6,0,1,5,4,0] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,1,5,4,1] (by decide +kernel))
      node_2492
      (invalid_excluded a [7,3,8,6,0,1,5,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,1,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,1,5,4,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,1,5,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,1,5,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,1,5,4,8] (by decide +kernel)))

theorem node_2489 : Excluded a [7,3,8,6,0,1,5] :=
  branch_excluded a [7,3,8,6,0,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,6,0,1,5,0] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,1,5,1] (by decide +kernel))
      node_2490
      (invalid_excluded a [7,3,8,6,0,1,5,3] (by decide +kernel))
      node_2491
      (invalid_excluded a [7,3,8,6,0,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,1,5,8] (by decide +kernel)))

theorem node_2486 : Excluded a [7,3,8,6,0,1] :=
  branch_excluded a [7,3,8,6,0,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,6,0,1,0] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,1,1] (by decide +kernel))
      node_2487
      (invalid_excluded a [7,3,8,6,0,1,3] (by decide +kernel))
      node_2488
      node_2489
      (invalid_excluded a [7,3,8,6,0,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,1,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,1,8] (by decide +kernel)))

theorem node_2494 : Excluded a [7,3,8,6,0,2,1] :=
  source_excluded a [7,3,8,6,0,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2495 : Excluded a [7,3,8,6,0,2,4] :=
  source_excluded a [7,3,8,6,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2497 : Excluded a [7,3,8,6,0,2,5,1] :=
  source_excluded a [7,3,8,6,0,2,5,1] 0 2 7 (by decide) (by decide +kernel)

def b_2499 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 3
  | 2 => 8
  | 3 => 6
  | 4 => 0
  | 5 => 2
  | 6 => 5
  | 7 => 4
  | 8 => 1
  | _ => 0

def cert_2499 : LosingRegion (edgeOf a b_2499) 0 :=
  losingMask a b_2499 0 1224425002734156590613504
    (by decide +kernel) (by decide +kernel)

theorem node_2499 : Excluded a [7,3,8,6,0,2,5,4,1] :=
  losing_excluded a [7,3,8,6,0,2,5,4,1] (by decide) b_2499 (by decide +kernel) 2 0 0 cert_2499 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2499 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1224425002734156590613504 2 0; decide +kernel)

theorem node_2498 : Excluded a [7,3,8,6,0,2,5,4] :=
  branch_excluded a [7,3,8,6,0,2,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,6,0,2,5,4,0] (by decide +kernel))
      node_2499
      (invalid_excluded a [7,3,8,6,0,2,5,4,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,5,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,5,4,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,5,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,5,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,5,4,8] (by decide +kernel)))

theorem node_2496 : Excluded a [7,3,8,6,0,2,5] :=
  branch_excluded a [7,3,8,6,0,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,6,0,2,5,0] (by decide +kernel))
      node_2497
      (invalid_excluded a [7,3,8,6,0,2,5,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,5,3] (by decide +kernel))
      node_2498
      (invalid_excluded a [7,3,8,6,0,2,5,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,5,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,5,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,5,8] (by decide +kernel)))

theorem node_2493 : Excluded a [7,3,8,6,0,2] :=
  branch_excluded a [7,3,8,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,6,0,2,0] (by decide +kernel))
      node_2494
      (invalid_excluded a [7,3,8,6,0,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,3] (by decide +kernel))
      node_2495
      node_2496
      (invalid_excluded a [7,3,8,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,8] (by decide +kernel)))

theorem node_2500 : Excluded a [7,3,8,6,0,4] :=
  source_excluded a [7,3,8,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2485 : Excluded a [7,3,8,6,0] :=
  branch_excluded a [7,3,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,6,0,0] (by decide +kernel))
      node_2486
      node_2493
      (invalid_excluded a [7,3,8,6,0,3] (by decide +kernel))
      node_2500
      (invalid_excluded a [7,3,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,8] (by decide +kernel)))

theorem node_2501 : Excluded a [7,3,8,6,1] :=
  predecessor_excluded a [7,3,8,6,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_2503 : Excluded a [7,3,8,6,5,0] :=
  predecessor_excluded a [7,3,8,6,5,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2505 : Excluded a [7,3,8,6,5,1,0] :=
  source_excluded a [7,3,8,6,5,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2506 : Excluded a [7,3,8,6,5,1,2] :=
  predecessor_excluded a [7,3,8,6,5,1,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_2507 : Excluded a [7,3,8,6,5,1,4] :=
  source_excluded a [7,3,8,6,5,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2504 : Excluded a [7,3,8,6,5,1] :=
  branch_excluded a [7,3,8,6,5,1] (by decide)
    (fin9_cases _
      node_2505
      (invalid_excluded a [7,3,8,6,5,1,1] (by decide +kernel))
      node_2506
      (invalid_excluded a [7,3,8,6,5,1,3] (by decide +kernel))
      node_2507
      (invalid_excluded a [7,3,8,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,5,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,5,1,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,5,1,8] (by decide +kernel)))

theorem node_2508 : Excluded a [7,3,8,6,5,2] :=
  source_excluded a [7,3,8,6,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2509 : Excluded a [7,3,8,6,5,4] :=
  source_excluded a [7,3,8,6,5,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2502 : Excluded a [7,3,8,6,5] :=
  branch_excluded a [7,3,8,6,5] (by decide)
    (fin9_cases _
      node_2503
      node_2504
      node_2508
      (invalid_excluded a [7,3,8,6,5,3] (by decide +kernel))
      node_2509
      (invalid_excluded a [7,3,8,6,5,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,5,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,5,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,5,8] (by decide +kernel)))

theorem node_2484 : Excluded a [7,3,8,6] :=
  branch_excluded a [7,3,8,6] (by decide)
    (fin9_cases _
      node_2485
      node_2501
      (invalid_excluded a [7,3,8,6,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,4] (by decide +kernel))
      node_2502
      (invalid_excluded a [7,3,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,8] (by decide +kernel)))

theorem node_2479 : Excluded a [7,3,8] :=
  branch_excluded a [7,3,8] (by decide)
    (fin9_cases _
      node_2480
      node_2481
      node_2482
      (invalid_excluded a [7,3,8,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,4] (by decide +kernel))
      node_2483
      node_2484
      (invalid_excluded a [7,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,8] (by decide +kernel)))

theorem node_2389 : Excluded a [7,3] :=
  branch_excluded a [7,3] (by decide)
    (fin9_cases _
      node_2390
      node_2391
      (invalid_excluded a [7,3,2] (by decide +kernel))
      (invalid_excluded a [7,3,3] (by decide +kernel))
      node_2392
      node_2393
      node_2427
      (invalid_excluded a [7,3,7] (by decide +kernel))
      node_2479)

theorem node_2512 : Excluded a [7,4,0,1] :=
  source_excluded a [7,4,0,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2513 : Excluded a [7,4,0,2] :=
  source_excluded a [7,4,0,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2515 : Excluded a [7,4,0,5,1] :=
  predecessor_excluded a [7,4,0,5,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_2516 : Excluded a [7,4,0,5,3] :=
  source_excluded a [7,4,0,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2517 : Excluded a [7,4,0,5,6] :=
  predecessor_excluded a [7,4,0,5,6] 0 6 3 4 (by decide) (by decide +kernel)

theorem node_2521 : Excluded a [7,4,0,5,8,1,2,3] :=
  predecessor_excluded a [7,4,0,5,8,1,2,3] 0 5 7 3 (by decide) (by decide +kernel)

theorem node_2523 : Excluded a [7,4,0,5,8,1,2,6,3] :=
  source_excluded a [7,4,0,5,8,1,2,6,3] 8 0 3 (by decide) (by decide +kernel)

theorem node_2522 : Excluded a [7,4,0,5,8,1,2,6] :=
  branch_excluded a [7,4,0,5,8,1,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,5,8,1,2,6,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,2,6,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,2,6,2] (by decide +kernel))
      node_2523
      (invalid_excluded a [7,4,0,5,8,1,2,6,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,2,6,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,2,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,2,6,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,2,6,8] (by decide +kernel)))

theorem node_2520 : Excluded a [7,4,0,5,8,1,2] :=
  branch_excluded a [7,4,0,5,8,1,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,5,8,1,2,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,2,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,2,2] (by decide +kernel))
      node_2521
      (invalid_excluded a [7,4,0,5,8,1,2,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,2,5] (by decide +kernel))
      node_2522
      (invalid_excluded a [7,4,0,5,8,1,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,2,8] (by decide +kernel)))

theorem node_2525 : Excluded a [7,4,0,5,8,1,3,2] :=
  source_excluded a [7,4,0,5,8,1,3,2] 4 0 7 (by decide) (by decide +kernel)

theorem node_2527 : Excluded a [7,4,0,5,8,1,3,6,2] :=
  source_excluded a [7,4,0,5,8,1,3,6,2] 4 0 8 (by decide) (by decide +kernel)

theorem node_2526 : Excluded a [7,4,0,5,8,1,3,6] :=
  branch_excluded a [7,4,0,5,8,1,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,5,8,1,3,6,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,3,6,1] (by decide +kernel))
      node_2527
      (invalid_excluded a [7,4,0,5,8,1,3,6,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,3,6,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,3,6,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,3,6,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,3,6,8] (by decide +kernel)))

theorem node_2524 : Excluded a [7,4,0,5,8,1,3] :=
  branch_excluded a [7,4,0,5,8,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,5,8,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,3,1] (by decide +kernel))
      node_2525
      (invalid_excluded a [7,4,0,5,8,1,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,3,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,3,5] (by decide +kernel))
      node_2526
      (invalid_excluded a [7,4,0,5,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,3,8] (by decide +kernel)))

theorem node_2519 : Excluded a [7,4,0,5,8,1] :=
  branch_excluded a [7,4,0,5,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,5,8,1,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,1] (by decide +kernel))
      node_2520
      node_2524
      (invalid_excluded a [7,4,0,5,8,1,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,1,8] (by decide +kernel)))

theorem node_2528 : Excluded a [7,4,0,5,8,2] :=
  predecessor_excluded a [7,4,0,5,8,2] 0 2 3 5 (by decide) (by decide +kernel)

theorem node_2530 : Excluded a [7,4,0,5,8,3,1] :=
  source_excluded a [7,4,0,5,8,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2532 : Excluded a [7,4,0,5,8,3,2,1] :=
  source_excluded a [7,4,0,5,8,3,2,1] 0 2 7 (by decide) (by decide +kernel)

def b_2534 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 4
  | 2 => 0
  | 3 => 5
  | 4 => 8
  | 5 => 3
  | 6 => 2
  | 7 => 6
  | 8 => 1
  | _ => 0

def cert_2534 : LosingRegion (edgeOf a b_2534) 0 :=
  losingMask a b_2534 0 1224477947016458640819200
    (by decide +kernel) (by decide +kernel)

theorem node_2534 : Excluded a [7,4,0,5,8,3,2,6,1] :=
  losing_excluded a [7,4,0,5,8,3,2,6,1] (by decide) b_2534 (by decide +kernel) 3 0 1 cert_2534 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_2534 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1224477947016458640819200 3 1; decide +kernel)

theorem node_2533 : Excluded a [7,4,0,5,8,3,2,6] :=
  branch_excluded a [7,4,0,5,8,3,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,5,8,3,2,6,0] (by decide +kernel))
      node_2534
      (invalid_excluded a [7,4,0,5,8,3,2,6,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,3,2,6,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,3,2,6,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,3,2,6,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,3,2,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,3,2,6,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,3,2,6,8] (by decide +kernel)))

theorem node_2531 : Excluded a [7,4,0,5,8,3,2] :=
  branch_excluded a [7,4,0,5,8,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,5,8,3,2,0] (by decide +kernel))
      node_2532
      (invalid_excluded a [7,4,0,5,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,3,2,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,3,2,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,3,2,5] (by decide +kernel))
      node_2533
      (invalid_excluded a [7,4,0,5,8,3,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,3,2,8] (by decide +kernel)))

theorem node_2529 : Excluded a [7,4,0,5,8,3] :=
  branch_excluded a [7,4,0,5,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,5,8,3,0] (by decide +kernel))
      node_2530
      node_2531
      (invalid_excluded a [7,4,0,5,8,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,3,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,3,8] (by decide +kernel)))

theorem node_2518 : Excluded a [7,4,0,5,8] :=
  branch_excluded a [7,4,0,5,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,5,8,0] (by decide +kernel))
      node_2519
      node_2528
      node_2529
      (invalid_excluded a [7,4,0,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,8,8] (by decide +kernel)))

theorem node_2514 : Excluded a [7,4,0,5] :=
  branch_excluded a [7,4,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,5,0] (by decide +kernel))
      node_2515
      (invalid_excluded a [7,4,0,5,2] (by decide +kernel))
      node_2516
      (invalid_excluded a [7,4,0,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,5,5] (by decide +kernel))
      node_2517
      (invalid_excluded a [7,4,0,5,7] (by decide +kernel))
      node_2518)

theorem node_2536 : Excluded a [7,4,0,6,1] :=
  predecessor_excluded a [7,4,0,6,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_2537 : Excluded a [7,4,0,6,3] :=
  source_excluded a [7,4,0,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2540 : Excluded a [7,4,0,6,5,1,2] :=
  predecessor_excluded a [7,4,0,6,5,1,2] 0 2 3 6 (by decide) (by decide +kernel)

theorem node_2542 : Excluded a [7,4,0,6,5,1,3,2] :=
  branch_excluded a [7,4,0,6,5,1,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,5,1,3,2,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,3,2,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,3,2,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,3,2,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,3,2,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,3,2,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,3,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,3,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,3,2,8] (by decide +kernel)))

theorem node_2541 : Excluded a [7,4,0,6,5,1,3] :=
  branch_excluded a [7,4,0,6,5,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,5,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,3,1] (by decide +kernel))
      node_2542
      (invalid_excluded a [7,4,0,6,5,1,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,3,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,3,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,3,8] (by decide +kernel)))

theorem node_2543 : Excluded a [7,4,0,6,5,1,8] :=
  source_excluded a [7,4,0,6,5,1,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_2539 : Excluded a [7,4,0,6,5,1] :=
  branch_excluded a [7,4,0,6,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,5,1,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,1] (by decide +kernel))
      node_2540
      node_2541
      (invalid_excluded a [7,4,0,6,5,1,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,1,7] (by decide +kernel))
      node_2543)

theorem node_2544 : Excluded a [7,4,0,6,5,2] :=
  source_excluded a [7,4,0,6,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2545 : Excluded a [7,4,0,6,5,3] :=
  source_excluded a [7,4,0,6,5,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2547 : Excluded a [7,4,0,6,5,8,1] :=
  source_excluded a [7,4,0,6,5,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2548 : Excluded a [7,4,0,6,5,8,2] :=
  predecessor_excluded a [7,4,0,6,5,8,2] 0 2 3 6 (by decide) (by decide +kernel)

theorem node_2550 : Excluded a [7,4,0,6,5,8,3,1] :=
  source_excluded a [7,4,0,6,5,8,3,1] 0 2 7 (by decide) (by decide +kernel)

def b_2552 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 4
  | 2 => 0
  | 3 => 6
  | 4 => 5
  | 5 => 8
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_2552 : LosingRegion (edgeOf a b_2552) 0 :=
  losingMask a b_2552 0 1224314247124976013411328
    (by decide +kernel) (by decide +kernel)

theorem node_2552 : Excluded a [7,4,0,6,5,8,3,2,1] :=
  losing_excluded a [7,4,0,6,5,8,3,2,1] (by decide) b_2552 (by decide +kernel) 3 0 0 cert_2552 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_2552 3 0 ∧ 0 ≠ 3 ∧ maskRegion 1224314247124976013411328 3 0; decide +kernel)

theorem node_2551 : Excluded a [7,4,0,6,5,8,3,2] :=
  branch_excluded a [7,4,0,6,5,8,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,5,8,3,2,0] (by decide +kernel))
      node_2552
      (invalid_excluded a [7,4,0,6,5,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,8,3,2,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,8,3,2,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,8,3,2,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,8,3,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,8,3,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,8,3,2,8] (by decide +kernel)))

theorem node_2549 : Excluded a [7,4,0,6,5,8,3] :=
  branch_excluded a [7,4,0,6,5,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,5,8,3,0] (by decide +kernel))
      node_2550
      node_2551
      (invalid_excluded a [7,4,0,6,5,8,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,8,3,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,8,3,8] (by decide +kernel)))

theorem node_2546 : Excluded a [7,4,0,6,5,8] :=
  branch_excluded a [7,4,0,6,5,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,5,8,0] (by decide +kernel))
      node_2547
      node_2548
      node_2549
      (invalid_excluded a [7,4,0,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,8,8] (by decide +kernel)))

theorem node_2538 : Excluded a [7,4,0,6,5] :=
  branch_excluded a [7,4,0,6,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,5,0] (by decide +kernel))
      node_2539
      node_2544
      node_2545
      (invalid_excluded a [7,4,0,6,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5,7] (by decide +kernel))
      node_2546)

theorem node_2555 : Excluded a [7,4,0,6,8,1,2] :=
  predecessor_excluded a [7,4,0,6,8,1,2] 0 2 3 6 (by decide) (by decide +kernel)

theorem node_2557 : Excluded a [7,4,0,6,8,1,3,2] :=
  source_excluded a [7,4,0,6,8,1,3,2] 4 0 7 (by decide) (by decide +kernel)

theorem node_2558 : Excluded a [7,4,0,6,8,1,3,5] :=
  source_excluded a [7,4,0,6,8,1,3,5] 7 0 8 (by decide) (by decide +kernel)

theorem node_2556 : Excluded a [7,4,0,6,8,1,3] :=
  branch_excluded a [7,4,0,6,8,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,8,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,3,1] (by decide +kernel))
      node_2557
      (invalid_excluded a [7,4,0,6,8,1,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,3,4] (by decide +kernel))
      node_2558
      (invalid_excluded a [7,4,0,6,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,3,8] (by decide +kernel)))

theorem node_2560 : Excluded a [7,4,0,6,8,1,5,2] :=
  source_excluded a [7,4,0,6,8,1,5,2] 4 0 7 (by decide) (by decide +kernel)

theorem node_2562 : Excluded a [7,4,0,6,8,1,5,3,2] :=
  source_excluded a [7,4,0,6,8,1,5,3,2] 4 0 8 (by decide) (by decide +kernel)

theorem node_2561 : Excluded a [7,4,0,6,8,1,5,3] :=
  branch_excluded a [7,4,0,6,8,1,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,8,1,5,3,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,5,3,1] (by decide +kernel))
      node_2562
      (invalid_excluded a [7,4,0,6,8,1,5,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,5,3,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,5,3,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,5,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,5,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,5,3,8] (by decide +kernel)))

theorem node_2559 : Excluded a [7,4,0,6,8,1,5] :=
  branch_excluded a [7,4,0,6,8,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,8,1,5,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,5,1] (by decide +kernel))
      node_2560
      node_2561
      (invalid_excluded a [7,4,0,6,8,1,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,5,8] (by decide +kernel)))

theorem node_2554 : Excluded a [7,4,0,6,8,1] :=
  branch_excluded a [7,4,0,6,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,8,1,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,1] (by decide +kernel))
      node_2555
      node_2556
      (invalid_excluded a [7,4,0,6,8,1,4] (by decide +kernel))
      node_2559
      (invalid_excluded a [7,4,0,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,8] (by decide +kernel)))

theorem node_2564 : Excluded a [7,4,0,6,8,2,1] :=
  source_excluded a [7,4,0,6,8,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2565 : Excluded a [7,4,0,6,8,2,3] :=
  predecessor_excluded a [7,4,0,6,8,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_2567 : Excluded a [7,4,0,6,8,2,5,1] :=
  source_excluded a [7,4,0,6,8,2,5,1] 0 2 7 (by decide) (by decide +kernel)

def b_2569 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 4
  | 2 => 0
  | 3 => 6
  | 4 => 8
  | 5 => 2
  | 6 => 5
  | 7 => 3
  | 8 => 1
  | _ => 0

def cert_2569 : LosingRegion (edgeOf a b_2569) 0 :=
  losingMask a b_2569 0 1222093878381389609436160
    (by decide +kernel) (by decide +kernel)

theorem node_2569 : Excluded a [7,4,0,6,8,2,5,3,1] :=
  losing_excluded a [7,4,0,6,8,2,5,3,1] (by decide) b_2569 (by decide +kernel) 3 0 1 cert_2569 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_2569 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1222093878381389609436160 3 1; decide +kernel)

theorem node_2568 : Excluded a [7,4,0,6,8,2,5,3] :=
  branch_excluded a [7,4,0,6,8,2,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,8,2,5,3,0] (by decide +kernel))
      node_2569
      (invalid_excluded a [7,4,0,6,8,2,5,3,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,2,5,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,2,5,3,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,2,5,3,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,2,5,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,2,5,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,2,5,3,8] (by decide +kernel)))

theorem node_2566 : Excluded a [7,4,0,6,8,2,5] :=
  branch_excluded a [7,4,0,6,8,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,8,2,5,0] (by decide +kernel))
      node_2567
      (invalid_excluded a [7,4,0,6,8,2,5,2] (by decide +kernel))
      node_2568
      (invalid_excluded a [7,4,0,6,8,2,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,2,5,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,2,5,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,2,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,2,5,8] (by decide +kernel)))

theorem node_2563 : Excluded a [7,4,0,6,8,2] :=
  branch_excluded a [7,4,0,6,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,8,2,0] (by decide +kernel))
      node_2564
      (invalid_excluded a [7,4,0,6,8,2,2] (by decide +kernel))
      node_2565
      (invalid_excluded a [7,4,0,6,8,2,4] (by decide +kernel))
      node_2566
      (invalid_excluded a [7,4,0,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,2,8] (by decide +kernel)))

theorem node_2570 : Excluded a [7,4,0,6,8,3] :=
  source_excluded a [7,4,0,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2553 : Excluded a [7,4,0,6,8] :=
  branch_excluded a [7,4,0,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,8,0] (by decide +kernel))
      node_2554
      node_2563
      node_2570
      (invalid_excluded a [7,4,0,6,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,8] (by decide +kernel)))

theorem node_2535 : Excluded a [7,4,0,6] :=
  branch_excluded a [7,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,0] (by decide +kernel))
      node_2536
      (invalid_excluded a [7,4,0,6,2] (by decide +kernel))
      node_2537
      (invalid_excluded a [7,4,0,6,4] (by decide +kernel))
      node_2538
      (invalid_excluded a [7,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,7] (by decide +kernel))
      node_2553)

theorem node_2572 : Excluded a [7,4,0,8,1] :=
  predecessor_excluded a [7,4,0,8,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_2573 : Excluded a [7,4,0,8,3] :=
  source_excluded a [7,4,0,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2574 : Excluded a [7,4,0,8,5] :=
  predecessor_excluded a [7,4,0,8,5] 0 5 3 4 (by decide) (by decide +kernel)

theorem node_2577 : Excluded a [7,4,0,8,6,1,2] :=
  source_excluded a [7,4,0,8,6,1,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_2578 : Excluded a [7,4,0,8,6,1,3] :=
  predecessor_excluded a [7,4,0,8,6,1,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_2581 : Excluded a [7,4,0,8,6,1,5,2,3] :=
  predecessor_excluded a [7,4,0,8,6,1,5,2,3] 0 3 7 8 (by decide) (by decide +kernel)

theorem node_2580 : Excluded a [7,4,0,8,6,1,5,2] :=
  branch_excluded a [7,4,0,8,6,1,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,6,1,5,2,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,1,5,2,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,1,5,2,2] (by decide +kernel))
      node_2581
      (invalid_excluded a [7,4,0,8,6,1,5,2,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,1,5,2,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,1,5,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,1,5,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,1,5,2,8] (by decide +kernel)))

theorem node_2582 : Excluded a [7,4,0,8,6,1,5,3] :=
  source_excluded a [7,4,0,8,6,1,5,3] 7 0 3 (by decide) (by decide +kernel)

theorem node_2579 : Excluded a [7,4,0,8,6,1,5] :=
  branch_excluded a [7,4,0,8,6,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,6,1,5,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,1,5,1] (by decide +kernel))
      node_2580
      node_2582
      (invalid_excluded a [7,4,0,8,6,1,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,1,5,8] (by decide +kernel)))

theorem node_2576 : Excluded a [7,4,0,8,6,1] :=
  branch_excluded a [7,4,0,8,6,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,6,1,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,1,1] (by decide +kernel))
      node_2577
      node_2578
      (invalid_excluded a [7,4,0,8,6,1,4] (by decide +kernel))
      node_2579
      (invalid_excluded a [7,4,0,8,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,1,8] (by decide +kernel)))

theorem node_2583 : Excluded a [7,4,0,8,6,2] :=
  source_excluded a [7,4,0,8,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2585 : Excluded a [7,4,0,8,6,3,1] :=
  source_excluded a [7,4,0,8,6,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2586 : Excluded a [7,4,0,8,6,3,2] :=
  source_excluded a [7,4,0,8,6,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_2588 : Excluded a [7,4,0,8,6,3,5,1] :=
  source_excluded a [7,4,0,8,6,3,5,1] 0 2 7 (by decide) (by decide +kernel)

def b_2590 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 4
  | 2 => 0
  | 3 => 8
  | 4 => 6
  | 5 => 3
  | 6 => 5
  | 7 => 2
  | 8 => 1
  | _ => 0

def cert_2590 : LosingRegion (edgeOf a b_2590) 0 :=
  losingMask a b_2590 0 1224314250221190019810304
    (by decide +kernel) (by decide +kernel)

theorem node_2590 : Excluded a [7,4,0,8,6,3,5,2,1] :=
  losing_excluded a [7,4,0,8,6,3,5,2,1] (by decide) b_2590 (by decide +kernel) 3 0 0 cert_2590 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_2590 3 0 ∧ 0 ≠ 3 ∧ maskRegion 1224314250221190019810304 3 0; decide +kernel)

theorem node_2589 : Excluded a [7,4,0,8,6,3,5,2] :=
  branch_excluded a [7,4,0,8,6,3,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,6,3,5,2,0] (by decide +kernel))
      node_2590
      (invalid_excluded a [7,4,0,8,6,3,5,2,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,3,5,2,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,3,5,2,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,3,5,2,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,3,5,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,3,5,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,3,5,2,8] (by decide +kernel)))

theorem node_2587 : Excluded a [7,4,0,8,6,3,5] :=
  branch_excluded a [7,4,0,8,6,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,6,3,5,0] (by decide +kernel))
      node_2588
      node_2589
      (invalid_excluded a [7,4,0,8,6,3,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,3,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,3,5,8] (by decide +kernel)))

theorem node_2584 : Excluded a [7,4,0,8,6,3] :=
  branch_excluded a [7,4,0,8,6,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,6,3,0] (by decide +kernel))
      node_2585
      node_2586
      (invalid_excluded a [7,4,0,8,6,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,3,4] (by decide +kernel))
      node_2587
      (invalid_excluded a [7,4,0,8,6,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,3,8] (by decide +kernel)))

theorem node_2575 : Excluded a [7,4,0,8,6] :=
  branch_excluded a [7,4,0,8,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,6,0] (by decide +kernel))
      node_2576
      node_2583
      node_2584
      (invalid_excluded a [7,4,0,8,6,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,6,8] (by decide +kernel)))

theorem node_2571 : Excluded a [7,4,0,8] :=
  branch_excluded a [7,4,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,0] (by decide +kernel))
      node_2572
      (invalid_excluded a [7,4,0,8,2] (by decide +kernel))
      node_2573
      (invalid_excluded a [7,4,0,8,4] (by decide +kernel))
      node_2574
      node_2575
      (invalid_excluded a [7,4,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,8] (by decide +kernel)))

theorem node_2511 : Excluded a [7,4,0] :=
  branch_excluded a [7,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,0] (by decide +kernel))
      node_2512
      node_2513
      (invalid_excluded a [7,4,0,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,4] (by decide +kernel))
      node_2514
      node_2535
      (invalid_excluded a [7,4,0,7] (by decide +kernel))
      node_2571)

theorem node_2591 : Excluded a [7,4,1] :=
  predecessor_excluded a [7,4,1] 0 4 2 1 (by decide) (by decide +kernel)

theorem node_2593 : Excluded a [7,4,5,0] :=
  source_excluded a [7,4,5,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2594 : Excluded a [7,4,5,1] :=
  source_excluded a [7,4,5,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2595 : Excluded a [7,4,5,2] :=
  source_excluded a [7,4,5,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2596 : Excluded a [7,4,5,6] :=
  predecessor_excluded a [7,4,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_2598 : Excluded a [7,4,5,8,0] :=
  source_excluded a [7,4,5,8,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2599 : Excluded a [7,4,5,8,1] :=
  predecessor_excluded a [7,4,5,8,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2600 : Excluded a [7,4,5,8,3] :=
  source_excluded a [7,4,5,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2602 : Excluded a [7,4,5,8,6,0] :=
  predecessor_excluded a [7,4,5,8,6,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2604 : Excluded a [7,4,5,8,6,1,0] :=
  source_excluded a [7,4,5,8,6,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2605 : Excluded a [7,4,5,8,6,1,2] :=
  source_excluded a [7,4,5,8,6,1,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_2606 : Excluded a [7,4,5,8,6,1,3] :=
  predecessor_excluded a [7,4,5,8,6,1,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_2603 : Excluded a [7,4,5,8,6,1] :=
  branch_excluded a [7,4,5,8,6,1] (by decide)
    (fin9_cases _
      node_2604
      (invalid_excluded a [7,4,5,8,6,1,1] (by decide +kernel))
      node_2605
      node_2606
      (invalid_excluded a [7,4,5,8,6,1,4] (by decide +kernel))
      (invalid_excluded a [7,4,5,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,4,5,8,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,5,8,6,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,5,8,6,1,8] (by decide +kernel)))

theorem node_2607 : Excluded a [7,4,5,8,6,2] :=
  source_excluded a [7,4,5,8,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2608 : Excluded a [7,4,5,8,6,3] :=
  source_excluded a [7,4,5,8,6,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2601 : Excluded a [7,4,5,8,6] :=
  branch_excluded a [7,4,5,8,6] (by decide)
    (fin9_cases _
      node_2602
      node_2603
      node_2607
      node_2608
      (invalid_excluded a [7,4,5,8,6,4] (by decide +kernel))
      (invalid_excluded a [7,4,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,4,5,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,5,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,4,5,8,6,8] (by decide +kernel)))

theorem node_2597 : Excluded a [7,4,5,8] :=
  branch_excluded a [7,4,5,8] (by decide)
    (fin9_cases _
      node_2598
      node_2599
      (invalid_excluded a [7,4,5,8,2] (by decide +kernel))
      node_2600
      (invalid_excluded a [7,4,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,5,8,5] (by decide +kernel))
      node_2601
      (invalid_excluded a [7,4,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,5,8,8] (by decide +kernel)))

theorem node_2592 : Excluded a [7,4,5] :=
  branch_excluded a [7,4,5] (by decide)
    (fin9_cases _
      node_2593
      node_2594
      node_2595
      (invalid_excluded a [7,4,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,5,5] (by decide +kernel))
      node_2596
      (invalid_excluded a [7,4,5,7] (by decide +kernel))
      node_2597)

theorem node_2610 : Excluded a [7,4,6,0] :=
  source_excluded a [7,4,6,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2611 : Excluded a [7,4,6,1] :=
  source_excluded a [7,4,6,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2612 : Excluded a [7,4,6,2] :=
  source_excluded a [7,4,6,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2614 : Excluded a [7,4,6,5,0] :=
  source_excluded a [7,4,6,5,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2615 : Excluded a [7,4,6,5,1] :=
  predecessor_excluded a [7,4,6,5,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2616 : Excluded a [7,4,6,5,3] :=
  source_excluded a [7,4,6,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2618 : Excluded a [7,4,6,5,8,0] :=
  predecessor_excluded a [7,4,6,5,8,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2620 : Excluded a [7,4,6,5,8,1,0] :=
  source_excluded a [7,4,6,5,8,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2622 : Excluded a [7,4,6,5,8,1,2,0] :=
  predecessor_excluded a [7,4,6,5,8,1,2,0] 2 0 0 7 (by decide) (by decide +kernel)

theorem node_2623 : Excluded a [7,4,6,5,8,1,2,3] :=
  predecessor_excluded a [7,4,6,5,8,1,2,3] 0 5 7 3 (by decide) (by decide +kernel)

theorem node_2621 : Excluded a [7,4,6,5,8,1,2] :=
  branch_excluded a [7,4,6,5,8,1,2] (by decide)
    (fin9_cases _
      node_2622
      (invalid_excluded a [7,4,6,5,8,1,2,1] (by decide +kernel))
      (invalid_excluded a [7,4,6,5,8,1,2,2] (by decide +kernel))
      node_2623
      (invalid_excluded a [7,4,6,5,8,1,2,4] (by decide +kernel))
      (invalid_excluded a [7,4,6,5,8,1,2,5] (by decide +kernel))
      (invalid_excluded a [7,4,6,5,8,1,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,5,8,1,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,5,8,1,2,8] (by decide +kernel)))

theorem node_2624 : Excluded a [7,4,6,5,8,1,3] :=
  source_excluded a [7,4,6,5,8,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2619 : Excluded a [7,4,6,5,8,1] :=
  branch_excluded a [7,4,6,5,8,1] (by decide)
    (fin9_cases _
      node_2620
      (invalid_excluded a [7,4,6,5,8,1,1] (by decide +kernel))
      node_2621
      node_2624
      (invalid_excluded a [7,4,6,5,8,1,4] (by decide +kernel))
      (invalid_excluded a [7,4,6,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,4,6,5,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,5,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,5,8,1,8] (by decide +kernel)))

theorem node_2625 : Excluded a [7,4,6,5,8,2] :=
  source_excluded a [7,4,6,5,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2626 : Excluded a [7,4,6,5,8,3] :=
  source_excluded a [7,4,6,5,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2617 : Excluded a [7,4,6,5,8] :=
  branch_excluded a [7,4,6,5,8] (by decide)
    (fin9_cases _
      node_2618
      node_2619
      node_2625
      node_2626
      (invalid_excluded a [7,4,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [7,4,6,5,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,5,8,8] (by decide +kernel)))

theorem node_2613 : Excluded a [7,4,6,5] :=
  branch_excluded a [7,4,6,5] (by decide)
    (fin9_cases _
      node_2614
      node_2615
      (invalid_excluded a [7,4,6,5,2] (by decide +kernel))
      node_2616
      (invalid_excluded a [7,4,6,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,6,5,5] (by decide +kernel))
      (invalid_excluded a [7,4,6,5,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,5,7] (by decide +kernel))
      node_2617)

theorem node_2628 : Excluded a [7,4,6,8,0] :=
  source_excluded a [7,4,6,8,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2629 : Excluded a [7,4,6,8,1] :=
  predecessor_excluded a [7,4,6,8,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2630 : Excluded a [7,4,6,8,3] :=
  source_excluded a [7,4,6,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2631 : Excluded a [7,4,6,8,5] :=
  predecessor_excluded a [7,4,6,8,5] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_2627 : Excluded a [7,4,6,8] :=
  branch_excluded a [7,4,6,8] (by decide)
    (fin9_cases _
      node_2628
      node_2629
      (invalid_excluded a [7,4,6,8,2] (by decide +kernel))
      node_2630
      (invalid_excluded a [7,4,6,8,4] (by decide +kernel))
      node_2631
      (invalid_excluded a [7,4,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,8] (by decide +kernel)))

theorem node_2609 : Excluded a [7,4,6] :=
  branch_excluded a [7,4,6] (by decide)
    (fin9_cases _
      node_2610
      node_2611
      node_2612
      (invalid_excluded a [7,4,6,3] (by decide +kernel))
      (invalid_excluded a [7,4,6,4] (by decide +kernel))
      node_2613
      (invalid_excluded a [7,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,7] (by decide +kernel))
      node_2627)

theorem node_2633 : Excluded a [7,4,8,0] :=
  source_excluded a [7,4,8,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2634 : Excluded a [7,4,8,1] :=
  source_excluded a [7,4,8,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2635 : Excluded a [7,4,8,2] :=
  source_excluded a [7,4,8,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2636 : Excluded a [7,4,8,5] :=
  predecessor_excluded a [7,4,8,5] 0 5 2 3 (by decide) (by decide +kernel)

theorem node_2638 : Excluded a [7,4,8,6,0] :=
  source_excluded a [7,4,8,6,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2639 : Excluded a [7,4,8,6,1] :=
  predecessor_excluded a [7,4,8,6,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2640 : Excluded a [7,4,8,6,3] :=
  source_excluded a [7,4,8,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2642 : Excluded a [7,4,8,6,5,0] :=
  predecessor_excluded a [7,4,8,6,5,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2644 : Excluded a [7,4,8,6,5,1,0] :=
  source_excluded a [7,4,8,6,5,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2645 : Excluded a [7,4,8,6,5,1,2] :=
  predecessor_excluded a [7,4,8,6,5,1,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_2647 : Excluded a [7,4,8,6,5,1,3,0] :=
  predecessor_excluded a [7,4,8,6,5,1,3,0] 2 0 0 7 (by decide) (by decide +kernel)

theorem node_2648 : Excluded a [7,4,8,6,5,1,3,2] :=
  source_excluded a [7,4,8,6,5,1,3,2] 7 0 2 (by decide) (by decide +kernel)

theorem node_2646 : Excluded a [7,4,8,6,5,1,3] :=
  branch_excluded a [7,4,8,6,5,1,3] (by decide)
    (fin9_cases _
      node_2647
      (invalid_excluded a [7,4,8,6,5,1,3,1] (by decide +kernel))
      node_2648
      (invalid_excluded a [7,4,8,6,5,1,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5,1,3,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5,1,3,5] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5,1,3,8] (by decide +kernel)))

theorem node_2643 : Excluded a [7,4,8,6,5,1] :=
  branch_excluded a [7,4,8,6,5,1] (by decide)
    (fin9_cases _
      node_2644
      (invalid_excluded a [7,4,8,6,5,1,1] (by decide +kernel))
      node_2645
      node_2646
      (invalid_excluded a [7,4,8,6,5,1,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5,1,8] (by decide +kernel)))

theorem node_2649 : Excluded a [7,4,8,6,5,2] :=
  source_excluded a [7,4,8,6,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2650 : Excluded a [7,4,8,6,5,3] :=
  source_excluded a [7,4,8,6,5,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2641 : Excluded a [7,4,8,6,5] :=
  branch_excluded a [7,4,8,6,5] (by decide)
    (fin9_cases _
      node_2642
      node_2643
      node_2649
      node_2650
      (invalid_excluded a [7,4,8,6,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5,5] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5,8] (by decide +kernel)))

theorem node_2637 : Excluded a [7,4,8,6] :=
  branch_excluded a [7,4,8,6] (by decide)
    (fin9_cases _
      node_2638
      node_2639
      (invalid_excluded a [7,4,8,6,2] (by decide +kernel))
      node_2640
      (invalid_excluded a [7,4,8,6,4] (by decide +kernel))
      node_2641
      (invalid_excluded a [7,4,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,8] (by decide +kernel)))

theorem node_2632 : Excluded a [7,4,8] :=
  branch_excluded a [7,4,8] (by decide)
    (fin9_cases _
      node_2633
      node_2634
      node_2635
      (invalid_excluded a [7,4,8,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,4] (by decide +kernel))
      node_2636
      node_2637
      (invalid_excluded a [7,4,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,8] (by decide +kernel)))

theorem node_2510 : Excluded a [7,4] :=
  branch_excluded a [7,4] (by decide)
    (fin9_cases _
      node_2511
      node_2591
      (invalid_excluded a [7,4,2] (by decide +kernel))
      (invalid_excluded a [7,4,3] (by decide +kernel))
      (invalid_excluded a [7,4,4] (by decide +kernel))
      node_2592
      node_2609
      (invalid_excluded a [7,4,7] (by decide +kernel))
      node_2632)

theorem node_2653 : Excluded a [7,5,0,1] :=
  predecessor_excluded a [7,5,0,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_2654 : Excluded a [7,5,0,2] :=
  source_excluded a [7,5,0,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2656 : Excluded a [7,5,0,6,1] :=
  predecessor_excluded a [7,5,0,6,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_2657 : Excluded a [7,5,0,6,3] :=
  source_excluded a [7,5,0,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2659 : Excluded a [7,5,0,6,8,1] :=
  predecessor_excluded a [7,5,0,6,8,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_2661 : Excluded a [7,5,0,6,8,2,1] :=
  source_excluded a [7,5,0,6,8,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2662 : Excluded a [7,5,0,6,8,2,3] :=
  predecessor_excluded a [7,5,0,6,8,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_2663 : Excluded a [7,5,0,6,8,2,4] :=
  source_excluded a [7,5,0,6,8,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2660 : Excluded a [7,5,0,6,8,2] :=
  branch_excluded a [7,5,0,6,8,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,6,8,2,0] (by decide +kernel))
      node_2661
      (invalid_excluded a [7,5,0,6,8,2,2] (by decide +kernel))
      node_2662
      node_2663
      (invalid_excluded a [7,5,0,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,2,8] (by decide +kernel)))

theorem node_2664 : Excluded a [7,5,0,6,8,3] :=
  source_excluded a [7,5,0,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2665 : Excluded a [7,5,0,6,8,4] :=
  source_excluded a [7,5,0,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2658 : Excluded a [7,5,0,6,8] :=
  branch_excluded a [7,5,0,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,6,8,0] (by decide +kernel))
      node_2659
      node_2660
      node_2664
      node_2665
      (invalid_excluded a [7,5,0,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,8] (by decide +kernel)))

theorem node_2655 : Excluded a [7,5,0,6] :=
  branch_excluded a [7,5,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,6,0] (by decide +kernel))
      node_2656
      (invalid_excluded a [7,5,0,6,2] (by decide +kernel))
      node_2657
      (invalid_excluded a [7,5,0,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,7] (by decide +kernel))
      node_2658)

theorem node_2667 : Excluded a [7,5,0,8,1] :=
  predecessor_excluded a [7,5,0,8,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_2668 : Excluded a [7,5,0,8,3] :=
  source_excluded a [7,5,0,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2670 : Excluded a [7,5,0,8,6,1] :=
  predecessor_excluded a [7,5,0,8,6,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_2671 : Excluded a [7,5,0,8,6,2] :=
  source_excluded a [7,5,0,8,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2673 : Excluded a [7,5,0,8,6,3,1] :=
  source_excluded a [7,5,0,8,6,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2674 : Excluded a [7,5,0,8,6,3,2] :=
  source_excluded a [7,5,0,8,6,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_2675 : Excluded a [7,5,0,8,6,3,4] :=
  predecessor_excluded a [7,5,0,8,6,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_2672 : Excluded a [7,5,0,8,6,3] :=
  branch_excluded a [7,5,0,8,6,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,8,6,3,0] (by decide +kernel))
      node_2673
      node_2674
      (invalid_excluded a [7,5,0,8,6,3,3] (by decide +kernel))
      node_2675
      (invalid_excluded a [7,5,0,8,6,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,6,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,6,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,6,3,8] (by decide +kernel)))

theorem node_2676 : Excluded a [7,5,0,8,6,4] :=
  source_excluded a [7,5,0,8,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_2669 : Excluded a [7,5,0,8,6] :=
  branch_excluded a [7,5,0,8,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,8,6,0] (by decide +kernel))
      node_2670
      node_2671
      node_2672
      node_2676
      (invalid_excluded a [7,5,0,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,6,8] (by decide +kernel)))

theorem node_2666 : Excluded a [7,5,0,8] :=
  branch_excluded a [7,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,8,0] (by decide +kernel))
      node_2667
      (invalid_excluded a [7,5,0,8,2] (by decide +kernel))
      node_2668
      (invalid_excluded a [7,5,0,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,5] (by decide +kernel))
      node_2669
      (invalid_excluded a [7,5,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,8] (by decide +kernel)))

theorem node_2652 : Excluded a [7,5,0] :=
  branch_excluded a [7,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,0] (by decide +kernel))
      node_2653
      node_2654
      (invalid_excluded a [7,5,0,3] (by decide +kernel))
      (invalid_excluded a [7,5,0,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,5] (by decide +kernel))
      node_2655
      (invalid_excluded a [7,5,0,7] (by decide +kernel))
      node_2666)

theorem node_2678 : Excluded a [7,5,1,0] :=
  predecessor_excluded a [7,5,1,0] 4 0 2 3 (by decide) (by decide +kernel)

theorem node_2679 : Excluded a [7,5,1,2] :=
  source_excluded a [7,5,1,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2681 : Excluded a [7,5,1,6,0] :=
  predecessor_excluded a [7,5,1,6,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_2682 : Excluded a [7,5,1,6,3] :=
  source_excluded a [7,5,1,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2684 : Excluded a [7,5,1,6,8,0] :=
  source_excluded a [7,5,1,6,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_2686 : Excluded a [7,5,1,6,8,2,0] :=
  source_excluded a [7,5,1,6,8,2,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2687 : Excluded a [7,5,1,6,8,2,3] :=
  predecessor_excluded a [7,5,1,6,8,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_2688 : Excluded a [7,5,1,6,8,2,4] :=
  source_excluded a [7,5,1,6,8,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2685 : Excluded a [7,5,1,6,8,2] :=
  branch_excluded a [7,5,1,6,8,2] (by decide)
    (fin9_cases _
      node_2686
      (invalid_excluded a [7,5,1,6,8,2,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,8,2,2] (by decide +kernel))
      node_2687
      node_2688
      (invalid_excluded a [7,5,1,6,8,2,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,8,2,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,8,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,8,2,8] (by decide +kernel)))

theorem node_2689 : Excluded a [7,5,1,6,8,3] :=
  source_excluded a [7,5,1,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2690 : Excluded a [7,5,1,6,8,4] :=
  source_excluded a [7,5,1,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2683 : Excluded a [7,5,1,6,8] :=
  branch_excluded a [7,5,1,6,8] (by decide)
    (fin9_cases _
      node_2684
      (invalid_excluded a [7,5,1,6,8,1] (by decide +kernel))
      node_2685
      node_2689
      node_2690
      (invalid_excluded a [7,5,1,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,8,8] (by decide +kernel)))

theorem node_2680 : Excluded a [7,5,1,6] :=
  branch_excluded a [7,5,1,6] (by decide)
    (fin9_cases _
      node_2681
      (invalid_excluded a [7,5,1,6,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,2] (by decide +kernel))
      node_2682
      (invalid_excluded a [7,5,1,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,7] (by decide +kernel))
      node_2683)

theorem node_2692 : Excluded a [7,5,1,8,0] :=
  predecessor_excluded a [7,5,1,8,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_2693 : Excluded a [7,5,1,8,3] :=
  source_excluded a [7,5,1,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2695 : Excluded a [7,5,1,8,6,0] :=
  source_excluded a [7,5,1,8,6,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_2696 : Excluded a [7,5,1,8,6,2] :=
  source_excluded a [7,5,1,8,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2698 : Excluded a [7,5,1,8,6,3,0] :=
  source_excluded a [7,5,1,8,6,3,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2699 : Excluded a [7,5,1,8,6,3,2] :=
  source_excluded a [7,5,1,8,6,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_2700 : Excluded a [7,5,1,8,6,3,4] :=
  predecessor_excluded a [7,5,1,8,6,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_2697 : Excluded a [7,5,1,8,6,3] :=
  branch_excluded a [7,5,1,8,6,3] (by decide)
    (fin9_cases _
      node_2698
      (invalid_excluded a [7,5,1,8,6,3,1] (by decide +kernel))
      node_2699
      (invalid_excluded a [7,5,1,8,6,3,3] (by decide +kernel))
      node_2700
      (invalid_excluded a [7,5,1,8,6,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,6,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,6,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,6,3,8] (by decide +kernel)))

theorem node_2701 : Excluded a [7,5,1,8,6,4] :=
  source_excluded a [7,5,1,8,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_2694 : Excluded a [7,5,1,8,6] :=
  branch_excluded a [7,5,1,8,6] (by decide)
    (fin9_cases _
      node_2695
      (invalid_excluded a [7,5,1,8,6,1] (by decide +kernel))
      node_2696
      node_2697
      node_2701
      (invalid_excluded a [7,5,1,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,6,8] (by decide +kernel)))

theorem node_2691 : Excluded a [7,5,1,8] :=
  branch_excluded a [7,5,1,8] (by decide)
    (fin9_cases _
      node_2692
      (invalid_excluded a [7,5,1,8,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,2] (by decide +kernel))
      node_2693
      (invalid_excluded a [7,5,1,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,5] (by decide +kernel))
      node_2694
      (invalid_excluded a [7,5,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,8] (by decide +kernel)))

theorem node_2677 : Excluded a [7,5,1] :=
  branch_excluded a [7,5,1] (by decide)
    (fin9_cases _
      node_2678
      (invalid_excluded a [7,5,1,1] (by decide +kernel))
      node_2679
      (invalid_excluded a [7,5,1,3] (by decide +kernel))
      (invalid_excluded a [7,5,1,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,5] (by decide +kernel))
      node_2680
      (invalid_excluded a [7,5,1,7] (by decide +kernel))
      node_2691)

theorem node_2702 : Excluded a [7,5,4] :=
  source_excluded a [7,5,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_2705 : Excluded a [7,5,6,0,1] :=
  predecessor_excluded a [7,5,6,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2706 : Excluded a [7,5,6,0,3] :=
  source_excluded a [7,5,6,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2708 : Excluded a [7,5,6,0,8,1] :=
  predecessor_excluded a [7,5,6,0,8,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_2709 : Excluded a [7,5,6,0,8,2] :=
  source_excluded a [7,5,6,0,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2710 : Excluded a [7,5,6,0,8,3] :=
  source_excluded a [7,5,6,0,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2712 : Excluded a [7,5,6,0,8,4,1] :=
  source_excluded a [7,5,6,0,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2713 : Excluded a [7,5,6,0,8,4,2] :=
  predecessor_excluded a [7,5,6,0,8,4,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2714 : Excluded a [7,5,6,0,8,4,3] :=
  source_excluded a [7,5,6,0,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2711 : Excluded a [7,5,6,0,8,4] :=
  branch_excluded a [7,5,6,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,6,0,8,4,0] (by decide +kernel))
      node_2712
      node_2713
      node_2714
      (invalid_excluded a [7,5,6,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,4,8] (by decide +kernel)))

theorem node_2707 : Excluded a [7,5,6,0,8] :=
  branch_excluded a [7,5,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,6,0,8,0] (by decide +kernel))
      node_2708
      node_2709
      node_2710
      node_2711
      (invalid_excluded a [7,5,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,8] (by decide +kernel)))

theorem node_2704 : Excluded a [7,5,6,0] :=
  branch_excluded a [7,5,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,6,0,0] (by decide +kernel))
      node_2705
      (invalid_excluded a [7,5,6,0,2] (by decide +kernel))
      node_2706
      (invalid_excluded a [7,5,6,0,4] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,7] (by decide +kernel))
      node_2707)

theorem node_2716 : Excluded a [7,5,6,1,0] :=
  predecessor_excluded a [7,5,6,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_2717 : Excluded a [7,5,6,1,3] :=
  source_excluded a [7,5,6,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2719 : Excluded a [7,5,6,1,8,0] :=
  source_excluded a [7,5,6,1,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_2720 : Excluded a [7,5,6,1,8,2] :=
  source_excluded a [7,5,6,1,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2721 : Excluded a [7,5,6,1,8,3] :=
  source_excluded a [7,5,6,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2723 : Excluded a [7,5,6,1,8,4,0] :=
  source_excluded a [7,5,6,1,8,4,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2724 : Excluded a [7,5,6,1,8,4,2] :=
  predecessor_excluded a [7,5,6,1,8,4,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2725 : Excluded a [7,5,6,1,8,4,3] :=
  source_excluded a [7,5,6,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2722 : Excluded a [7,5,6,1,8,4] :=
  branch_excluded a [7,5,6,1,8,4] (by decide)
    (fin9_cases _
      node_2723
      (invalid_excluded a [7,5,6,1,8,4,1] (by decide +kernel))
      node_2724
      node_2725
      (invalid_excluded a [7,5,6,1,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,6,1,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,1,8,4,8] (by decide +kernel)))

theorem node_2718 : Excluded a [7,5,6,1,8] :=
  branch_excluded a [7,5,6,1,8] (by decide)
    (fin9_cases _
      node_2719
      (invalid_excluded a [7,5,6,1,8,1] (by decide +kernel))
      node_2720
      node_2721
      node_2722
      (invalid_excluded a [7,5,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,1,8,8] (by decide +kernel)))

theorem node_2715 : Excluded a [7,5,6,1] :=
  branch_excluded a [7,5,6,1] (by decide)
    (fin9_cases _
      node_2716
      (invalid_excluded a [7,5,6,1,1] (by decide +kernel))
      (invalid_excluded a [7,5,6,1,2] (by decide +kernel))
      node_2717
      (invalid_excluded a [7,5,6,1,4] (by decide +kernel))
      (invalid_excluded a [7,5,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,1,7] (by decide +kernel))
      node_2718)

theorem node_2726 : Excluded a [7,5,6,2] :=
  source_excluded a [7,5,6,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2729 : Excluded a [7,5,6,8,0,1] :=
  predecessor_excluded a [7,5,6,8,0,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_2730 : Excluded a [7,5,6,8,0,2] :=
  source_excluded a [7,5,6,8,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2731 : Excluded a [7,5,6,8,0,3] :=
  source_excluded a [7,5,6,8,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2733 : Excluded a [7,5,6,8,0,4,1] :=
  source_excluded a [7,5,6,8,0,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2734 : Excluded a [7,5,6,8,0,4,2] :=
  predecessor_excluded a [7,5,6,8,0,4,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2735 : Excluded a [7,5,6,8,0,4,3] :=
  source_excluded a [7,5,6,8,0,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2732 : Excluded a [7,5,6,8,0,4] :=
  branch_excluded a [7,5,6,8,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,6,8,0,4,0] (by decide +kernel))
      node_2733
      node_2734
      node_2735
      (invalid_excluded a [7,5,6,8,0,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,0,4,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,0,4,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,0,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,0,4,8] (by decide +kernel)))

theorem node_2728 : Excluded a [7,5,6,8,0] :=
  branch_excluded a [7,5,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,6,8,0,0] (by decide +kernel))
      node_2729
      node_2730
      node_2731
      node_2732
      (invalid_excluded a [7,5,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,0,8] (by decide +kernel)))

theorem node_2737 : Excluded a [7,5,6,8,1,0] :=
  source_excluded a [7,5,6,8,1,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_2738 : Excluded a [7,5,6,8,1,2] :=
  source_excluded a [7,5,6,8,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2739 : Excluded a [7,5,6,8,1,3] :=
  source_excluded a [7,5,6,8,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2741 : Excluded a [7,5,6,8,1,4,0] :=
  source_excluded a [7,5,6,8,1,4,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2742 : Excluded a [7,5,6,8,1,4,2] :=
  predecessor_excluded a [7,5,6,8,1,4,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2743 : Excluded a [7,5,6,8,1,4,3] :=
  source_excluded a [7,5,6,8,1,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2740 : Excluded a [7,5,6,8,1,4] :=
  branch_excluded a [7,5,6,8,1,4] (by decide)
    (fin9_cases _
      node_2741
      (invalid_excluded a [7,5,6,8,1,4,1] (by decide +kernel))
      node_2742
      node_2743
      (invalid_excluded a [7,5,6,8,1,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,1,4,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,1,4,8] (by decide +kernel)))

theorem node_2736 : Excluded a [7,5,6,8,1] :=
  branch_excluded a [7,5,6,8,1] (by decide)
    (fin9_cases _
      node_2737
      (invalid_excluded a [7,5,6,8,1,1] (by decide +kernel))
      node_2738
      node_2739
      node_2740
      (invalid_excluded a [7,5,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,1,8] (by decide +kernel)))

theorem node_2744 : Excluded a [7,5,6,8,3] :=
  source_excluded a [7,5,6,8,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2727 : Excluded a [7,5,6,8] :=
  branch_excluded a [7,5,6,8] (by decide)
    (fin9_cases _
      node_2728
      node_2736
      (invalid_excluded a [7,5,6,8,2] (by decide +kernel))
      node_2744
      (invalid_excluded a [7,5,6,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,8] (by decide +kernel)))

theorem node_2703 : Excluded a [7,5,6] :=
  branch_excluded a [7,5,6] (by decide)
    (fin9_cases _
      node_2704
      node_2715
      node_2726
      (invalid_excluded a [7,5,6,3] (by decide +kernel))
      (invalid_excluded a [7,5,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,7] (by decide +kernel))
      node_2727)

theorem node_2747 : Excluded a [7,5,8,0,1] :=
  predecessor_excluded a [7,5,8,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2748 : Excluded a [7,5,8,0,3] :=
  source_excluded a [7,5,8,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2750 : Excluded a [7,5,8,0,6,1] :=
  predecessor_excluded a [7,5,8,0,6,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_2751 : Excluded a [7,5,8,0,6,2] :=
  source_excluded a [7,5,8,0,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2753 : Excluded a [7,5,8,0,6,3,1] :=
  source_excluded a [7,5,8,0,6,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2754 : Excluded a [7,5,8,0,6,3,2] :=
  source_excluded a [7,5,8,0,6,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_2755 : Excluded a [7,5,8,0,6,3,4] :=
  predecessor_excluded a [7,5,8,0,6,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_2752 : Excluded a [7,5,8,0,6,3] :=
  branch_excluded a [7,5,8,0,6,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,6,3,0] (by decide +kernel))
      node_2753
      node_2754
      (invalid_excluded a [7,5,8,0,6,3,3] (by decide +kernel))
      node_2755
      (invalid_excluded a [7,5,8,0,6,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,3,8] (by decide +kernel)))

theorem node_2756 : Excluded a [7,5,8,0,6,4] :=
  source_excluded a [7,5,8,0,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_2749 : Excluded a [7,5,8,0,6] :=
  branch_excluded a [7,5,8,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,6,0] (by decide +kernel))
      node_2750
      node_2751
      node_2752
      node_2756
      (invalid_excluded a [7,5,8,0,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,6,8] (by decide +kernel)))

theorem node_2746 : Excluded a [7,5,8,0] :=
  branch_excluded a [7,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,0] (by decide +kernel))
      node_2747
      (invalid_excluded a [7,5,8,0,2] (by decide +kernel))
      node_2748
      (invalid_excluded a [7,5,8,0,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,5] (by decide +kernel))
      node_2749
      (invalid_excluded a [7,5,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,8] (by decide +kernel)))

theorem node_2758 : Excluded a [7,5,8,1,0] :=
  predecessor_excluded a [7,5,8,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_2759 : Excluded a [7,5,8,1,3] :=
  source_excluded a [7,5,8,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2761 : Excluded a [7,5,8,1,6,0] :=
  source_excluded a [7,5,8,1,6,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_2762 : Excluded a [7,5,8,1,6,2] :=
  source_excluded a [7,5,8,1,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2764 : Excluded a [7,5,8,1,6,3,0] :=
  source_excluded a [7,5,8,1,6,3,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2765 : Excluded a [7,5,8,1,6,3,2] :=
  source_excluded a [7,5,8,1,6,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_2766 : Excluded a [7,5,8,1,6,3,4] :=
  predecessor_excluded a [7,5,8,1,6,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_2763 : Excluded a [7,5,8,1,6,3] :=
  branch_excluded a [7,5,8,1,6,3] (by decide)
    (fin9_cases _
      node_2764
      (invalid_excluded a [7,5,8,1,6,3,1] (by decide +kernel))
      node_2765
      (invalid_excluded a [7,5,8,1,6,3,3] (by decide +kernel))
      node_2766
      (invalid_excluded a [7,5,8,1,6,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,1,6,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,1,6,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,1,6,3,8] (by decide +kernel)))

theorem node_2767 : Excluded a [7,5,8,1,6,4] :=
  source_excluded a [7,5,8,1,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_2760 : Excluded a [7,5,8,1,6] :=
  branch_excluded a [7,5,8,1,6] (by decide)
    (fin9_cases _
      node_2761
      (invalid_excluded a [7,5,8,1,6,1] (by decide +kernel))
      node_2762
      node_2763
      node_2767
      (invalid_excluded a [7,5,8,1,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,1,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,1,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,1,6,8] (by decide +kernel)))

theorem node_2757 : Excluded a [7,5,8,1] :=
  branch_excluded a [7,5,8,1] (by decide)
    (fin9_cases _
      node_2758
      (invalid_excluded a [7,5,8,1,1] (by decide +kernel))
      (invalid_excluded a [7,5,8,1,2] (by decide +kernel))
      node_2759
      (invalid_excluded a [7,5,8,1,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,1,5] (by decide +kernel))
      node_2760
      (invalid_excluded a [7,5,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,1,8] (by decide +kernel)))

theorem node_2768 : Excluded a [7,5,8,2] :=
  source_excluded a [7,5,8,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2771 : Excluded a [7,5,8,6,0,1] :=
  predecessor_excluded a [7,5,8,6,0,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_2773 : Excluded a [7,5,8,6,0,2,1] :=
  source_excluded a [7,5,8,6,0,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2774 : Excluded a [7,5,8,6,0,2,3] :=
  predecessor_excluded a [7,5,8,6,0,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_2775 : Excluded a [7,5,8,6,0,2,4] :=
  source_excluded a [7,5,8,6,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2772 : Excluded a [7,5,8,6,0,2] :=
  branch_excluded a [7,5,8,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,6,0,2,0] (by decide +kernel))
      node_2773
      (invalid_excluded a [7,5,8,6,0,2,2] (by decide +kernel))
      node_2774
      node_2775
      (invalid_excluded a [7,5,8,6,0,2,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,0,2,8] (by decide +kernel)))

theorem node_2776 : Excluded a [7,5,8,6,0,3] :=
  source_excluded a [7,5,8,6,0,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2777 : Excluded a [7,5,8,6,0,4] :=
  source_excluded a [7,5,8,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2770 : Excluded a [7,5,8,6,0] :=
  branch_excluded a [7,5,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,6,0,0] (by decide +kernel))
      node_2771
      node_2772
      node_2776
      node_2777
      (invalid_excluded a [7,5,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,0,8] (by decide +kernel)))

theorem node_2779 : Excluded a [7,5,8,6,1,0] :=
  source_excluded a [7,5,8,6,1,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_2781 : Excluded a [7,5,8,6,1,2,0] :=
  source_excluded a [7,5,8,6,1,2,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2782 : Excluded a [7,5,8,6,1,2,3] :=
  predecessor_excluded a [7,5,8,6,1,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_2783 : Excluded a [7,5,8,6,1,2,4] :=
  source_excluded a [7,5,8,6,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2780 : Excluded a [7,5,8,6,1,2] :=
  branch_excluded a [7,5,8,6,1,2] (by decide)
    (fin9_cases _
      node_2781
      (invalid_excluded a [7,5,8,6,1,2,1] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,1,2,2] (by decide +kernel))
      node_2782
      node_2783
      (invalid_excluded a [7,5,8,6,1,2,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,1,2,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,1,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,1,2,8] (by decide +kernel)))

theorem node_2784 : Excluded a [7,5,8,6,1,3] :=
  source_excluded a [7,5,8,6,1,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2785 : Excluded a [7,5,8,6,1,4] :=
  source_excluded a [7,5,8,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2778 : Excluded a [7,5,8,6,1] :=
  branch_excluded a [7,5,8,6,1] (by decide)
    (fin9_cases _
      node_2779
      (invalid_excluded a [7,5,8,6,1,1] (by decide +kernel))
      node_2780
      node_2784
      node_2785
      (invalid_excluded a [7,5,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,1,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,1,8] (by decide +kernel)))

theorem node_2786 : Excluded a [7,5,8,6,3] :=
  source_excluded a [7,5,8,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2769 : Excluded a [7,5,8,6] :=
  branch_excluded a [7,5,8,6] (by decide)
    (fin9_cases _
      node_2770
      node_2778
      (invalid_excluded a [7,5,8,6,2] (by decide +kernel))
      node_2786
      (invalid_excluded a [7,5,8,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,8] (by decide +kernel)))

theorem node_2745 : Excluded a [7,5,8] :=
  branch_excluded a [7,5,8] (by decide)
    (fin9_cases _
      node_2746
      node_2757
      node_2768
      (invalid_excluded a [7,5,8,3] (by decide +kernel))
      (invalid_excluded a [7,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,5] (by decide +kernel))
      node_2769
      (invalid_excluded a [7,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,8] (by decide +kernel)))

theorem node_2651 : Excluded a [7,5] :=
  branch_excluded a [7,5] (by decide)
    (fin9_cases _
      node_2652
      node_2677
      (invalid_excluded a [7,5,2] (by decide +kernel))
      (invalid_excluded a [7,5,3] (by decide +kernel))
      node_2702
      (invalid_excluded a [7,5,5] (by decide +kernel))
      node_2703
      (invalid_excluded a [7,5,7] (by decide +kernel))
      node_2745)

theorem node_2787 : Excluded a [7,6] :=
  predecessor_excluded a [7,6] 2 7 1 0 (by decide) (by decide +kernel)

theorem node_2788 : Excluded a [7,8] :=
  predecessor_excluded a [7,8] 2 8 0 1 (by decide) (by decide +kernel)

theorem node_2254 : Excluded a [7] :=
  branch_excluded a [7] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0] (by decide +kernel))
      (invalid_excluded a [7,1] (by decide +kernel))
      node_2255
      node_2389
      node_2510
      node_2651
      node_2787
      (invalid_excluded a [7,7] (by decide +kernel))
      node_2788)

theorem node_2791 : Excluded a [8,2,0] :=
  source_excluded a [8,2,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_2792 : Excluded a [8,2,1] :=
  predecessor_excluded a [8,2,1] 3 1 1 2 (by decide) (by decide +kernel)

theorem node_2793 : Excluded a [8,2,4] :=
  source_excluded a [8,2,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_2796 : Excluded a [8,2,5,0,1] :=
  source_excluded a [8,2,5,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2797 : Excluded a [8,2,5,0,3] :=
  source_excluded a [8,2,5,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2800 : Excluded a [8,2,5,0,6,1,3] :=
  predecessor_excluded a [8,2,5,0,6,1,3] 0 3 4 6 (by decide) (by decide +kernel)

def b_2803 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 2
  | 2 => 5
  | 3 => 0
  | 4 => 6
  | 5 => 1
  | 6 => 4
  | 7 => 3
  | 8 => 7
  | _ => 0

def cert_2803 : LosingRegion (edgeOf a b_2803) 0 :=
  losingMask a b_2803 0 1276338834584763186021376
    (by decide +kernel) (by decide +kernel)

theorem node_2803 : Excluded a [8,2,5,0,6,1,4,3,7] :=
  losing_excluded a [8,2,5,0,6,1,4,3,7] (by decide) b_2803 (by decide +kernel) 2 0 3 cert_2803 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2803 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1276338834584763186021376 2 3; decide +kernel)

theorem node_2802 : Excluded a [8,2,5,0,6,1,4,3] :=
  branch_excluded a [8,2,5,0,6,1,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,5,0,6,1,4,3,0] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,4,3,1] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,4,3,2] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,4,3,3] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,4,3,4] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,4,3,5] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,4,3,6] (by decide +kernel))
      node_2803
      (invalid_excluded a [8,2,5,0,6,1,4,3,8] (by decide +kernel)))

theorem node_2801 : Excluded a [8,2,5,0,6,1,4] :=
  branch_excluded a [8,2,5,0,6,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,5,0,6,1,4,0] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,4,1] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,4,2] (by decide +kernel))
      node_2802
      (invalid_excluded a [8,2,5,0,6,1,4,4] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,4,5] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,4,6] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,4,7] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,4,8] (by decide +kernel)))

theorem node_2799 : Excluded a [8,2,5,0,6,1] :=
  branch_excluded a [8,2,5,0,6,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,5,0,6,1,0] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,1] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,2] (by decide +kernel))
      node_2800
      node_2801
      (invalid_excluded a [8,2,5,0,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,6] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,7] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,1,8] (by decide +kernel)))

theorem node_2804 : Excluded a [8,2,5,0,6,3] :=
  source_excluded a [8,2,5,0,6,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2805 : Excluded a [8,2,5,0,6,4] :=
  source_excluded a [8,2,5,0,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_2806 : Excluded a [8,2,5,0,6,7] :=
  source_excluded a [8,2,5,0,6,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2798 : Excluded a [8,2,5,0,6] :=
  branch_excluded a [8,2,5,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,5,0,6,0] (by decide +kernel))
      node_2799
      (invalid_excluded a [8,2,5,0,6,2] (by decide +kernel))
      node_2804
      node_2805
      (invalid_excluded a [8,2,5,0,6,5] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,6,6] (by decide +kernel))
      node_2806
      (invalid_excluded a [8,2,5,0,6,8] (by decide +kernel)))

theorem node_2810 : Excluded a [8,2,5,0,7,1,3,4] :=
  predecessor_excluded a [8,2,5,0,7,1,3,4] 0 4 6 7 (by decide) (by decide +kernel)

def b_2812 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 2
  | 2 => 5
  | 3 => 0
  | 4 => 7
  | 5 => 1
  | 6 => 3
  | 7 => 6
  | 8 => 4
  | _ => 0

def cert_2812 : LosingRegion (edgeOf a b_2812) 0 :=
  losingMask a b_2812 0 1394851923425616020374528
    (by decide +kernel) (by decide +kernel)

theorem node_2812 : Excluded a [8,2,5,0,7,1,3,6,4] :=
  losing_excluded a [8,2,5,0,7,1,3,6,4] (by decide) b_2812 (by decide +kernel) 4 0 1 cert_2812 (by change 4 ≠ 0 ∧ ¬ edgeOf a b_2812 4 0 ∧ 1 ≠ 4 ∧ maskRegion 1394851923425616020374528 4 1; decide +kernel)

theorem node_2811 : Excluded a [8,2,5,0,7,1,3,6] :=
  branch_excluded a [8,2,5,0,7,1,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,5,0,7,1,3,6,0] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,1,3,6,1] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,1,3,6,2] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,1,3,6,3] (by decide +kernel))
      node_2812
      (invalid_excluded a [8,2,5,0,7,1,3,6,5] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,1,3,6,6] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,1,3,6,7] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,1,3,6,8] (by decide +kernel)))

theorem node_2809 : Excluded a [8,2,5,0,7,1,3] :=
  branch_excluded a [8,2,5,0,7,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,5,0,7,1,3,0] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,1,3,1] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,1,3,2] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,1,3,3] (by decide +kernel))
      node_2810
      (invalid_excluded a [8,2,5,0,7,1,3,5] (by decide +kernel))
      node_2811
      (invalid_excluded a [8,2,5,0,7,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,1,3,8] (by decide +kernel)))

theorem node_2813 : Excluded a [8,2,5,0,7,1,4] :=
  source_excluded a [8,2,5,0,7,1,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2808 : Excluded a [8,2,5,0,7,1] :=
  branch_excluded a [8,2,5,0,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,5,0,7,1,0] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,1,1] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,1,2] (by decide +kernel))
      node_2809
      node_2813
      (invalid_excluded a [8,2,5,0,7,1,5] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,1,8] (by decide +kernel)))

theorem node_2814 : Excluded a [8,2,5,0,7,3] :=
  source_excluded a [8,2,5,0,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2815 : Excluded a [8,2,5,0,7,4] :=
  predecessor_excluded a [8,2,5,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2807 : Excluded a [8,2,5,0,7] :=
  branch_excluded a [8,2,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,5,0,7,0] (by decide +kernel))
      node_2808
      (invalid_excluded a [8,2,5,0,7,2] (by decide +kernel))
      node_2814
      node_2815
      (invalid_excluded a [8,2,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,7,8] (by decide +kernel)))

theorem node_2795 : Excluded a [8,2,5,0] :=
  branch_excluded a [8,2,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,5,0,0] (by decide +kernel))
      node_2796
      (invalid_excluded a [8,2,5,0,2] (by decide +kernel))
      node_2797
      (invalid_excluded a [8,2,5,0,4] (by decide +kernel))
      (invalid_excluded a [8,2,5,0,5] (by decide +kernel))
      node_2798
      node_2807
      (invalid_excluded a [8,2,5,0,8] (by decide +kernel)))

theorem node_2816 : Excluded a [8,2,5,1] :=
  predecessor_excluded a [8,2,5,1] 0 2 3 1 (by decide) (by decide +kernel)

theorem node_2817 : Excluded a [8,2,5,6] :=
  predecessor_excluded a [8,2,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_2819 : Excluded a [8,2,5,7,0] :=
  source_excluded a [8,2,5,7,0] 1 3 4 (by decide) (by decide +kernel)

theorem node_2820 : Excluded a [8,2,5,7,1] :=
  source_excluded a [8,2,5,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2821 : Excluded a [8,2,5,7,3] :=
  source_excluded a [8,2,5,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2824 : Excluded a [8,2,5,7,6,0,1] :=
  predecessor_excluded a [8,2,5,7,6,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_2825 : Excluded a [8,2,5,7,6,0,3] :=
  source_excluded a [8,2,5,7,6,0,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2826 : Excluded a [8,2,5,7,6,0,4] :=
  source_excluded a [8,2,5,7,6,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2823 : Excluded a [8,2,5,7,6,0] :=
  branch_excluded a [8,2,5,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,5,7,6,0,0] (by decide +kernel))
      node_2824
      (invalid_excluded a [8,2,5,7,6,0,2] (by decide +kernel))
      node_2825
      node_2826
      (invalid_excluded a [8,2,5,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,2,5,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [8,2,5,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [8,2,5,7,6,0,8] (by decide +kernel)))

theorem node_2828 : Excluded a [8,2,5,7,6,1,0] :=
  predecessor_excluded a [8,2,5,7,6,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2829 : Excluded a [8,2,5,7,6,1,3] :=
  source_excluded a [8,2,5,7,6,1,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2830 : Excluded a [8,2,5,7,6,1,4] :=
  source_excluded a [8,2,5,7,6,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2827 : Excluded a [8,2,5,7,6,1] :=
  branch_excluded a [8,2,5,7,6,1] (by decide)
    (fin9_cases _
      node_2828
      (invalid_excluded a [8,2,5,7,6,1,1] (by decide +kernel))
      (invalid_excluded a [8,2,5,7,6,1,2] (by decide +kernel))
      node_2829
      node_2830
      (invalid_excluded a [8,2,5,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,2,5,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [8,2,5,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [8,2,5,7,6,1,8] (by decide +kernel)))

theorem node_2831 : Excluded a [8,2,5,7,6,3] :=
  source_excluded a [8,2,5,7,6,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2832 : Excluded a [8,2,5,7,6,4] :=
  source_excluded a [8,2,5,7,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_2822 : Excluded a [8,2,5,7,6] :=
  branch_excluded a [8,2,5,7,6] (by decide)
    (fin9_cases _
      node_2823
      node_2827
      (invalid_excluded a [8,2,5,7,6,2] (by decide +kernel))
      node_2831
      node_2832
      (invalid_excluded a [8,2,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [8,2,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,2,5,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,2,5,7,6,8] (by decide +kernel)))

theorem node_2818 : Excluded a [8,2,5,7] :=
  branch_excluded a [8,2,5,7] (by decide)
    (fin9_cases _
      node_2819
      node_2820
      (invalid_excluded a [8,2,5,7,2] (by decide +kernel))
      node_2821
      (invalid_excluded a [8,2,5,7,4] (by decide +kernel))
      (invalid_excluded a [8,2,5,7,5] (by decide +kernel))
      node_2822
      (invalid_excluded a [8,2,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,2,5,7,8] (by decide +kernel)))

theorem node_2794 : Excluded a [8,2,5] :=
  branch_excluded a [8,2,5] (by decide)
    (fin9_cases _
      node_2795
      node_2816
      (invalid_excluded a [8,2,5,2] (by decide +kernel))
      (invalid_excluded a [8,2,5,3] (by decide +kernel))
      (invalid_excluded a [8,2,5,4] (by decide +kernel))
      (invalid_excluded a [8,2,5,5] (by decide +kernel))
      node_2817
      node_2818
      (invalid_excluded a [8,2,5,8] (by decide +kernel)))

theorem node_2835 : Excluded a [8,2,6,0,1] :=
  source_excluded a [8,2,6,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2836 : Excluded a [8,2,6,0,3] :=
  source_excluded a [8,2,6,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2837 : Excluded a [8,2,6,0,5] :=
  predecessor_excluded a [8,2,6,0,5] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_2840 : Excluded a [8,2,6,0,7,1,3] :=
  source_excluded a [8,2,6,0,7,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2841 : Excluded a [8,2,6,0,7,1,4] :=
  source_excluded a [8,2,6,0,7,1,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2843 : Excluded a [8,2,6,0,7,1,5,3] :=
  predecessor_excluded a [8,2,6,0,7,1,5,3] 0 3 4 7 (by decide) (by decide +kernel)

def b_2845 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 2
  | 2 => 6
  | 3 => 0
  | 4 => 7
  | 5 => 1
  | 6 => 5
  | 7 => 4
  | 8 => 3
  | _ => 0

def cert_2845 : LosingRegion (edgeOf a b_2845) 0 :=
  losingMask a b_2845 0 1250372394202097070900224
    (by decide +kernel) (by decide +kernel)

theorem node_2845 : Excluded a [8,2,6,0,7,1,5,4,3] :=
  losing_excluded a [8,2,6,0,7,1,5,4,3] (by decide) b_2845 (by decide +kernel) 2 0 3 cert_2845 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2845 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1250372394202097070900224 2 3; decide +kernel)

theorem node_2844 : Excluded a [8,2,6,0,7,1,5,4] :=
  branch_excluded a [8,2,6,0,7,1,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,6,0,7,1,5,4,0] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,1,5,4,1] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,1,5,4,2] (by decide +kernel))
      node_2845
      (invalid_excluded a [8,2,6,0,7,1,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,1,5,4,5] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,1,5,4,6] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,1,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,1,5,4,8] (by decide +kernel)))

theorem node_2842 : Excluded a [8,2,6,0,7,1,5] :=
  branch_excluded a [8,2,6,0,7,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,6,0,7,1,5,0] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,1,5,1] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,1,5,2] (by decide +kernel))
      node_2843
      node_2844
      (invalid_excluded a [8,2,6,0,7,1,5,5] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,1,5,6] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,1,5,7] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,1,5,8] (by decide +kernel)))

theorem node_2839 : Excluded a [8,2,6,0,7,1] :=
  branch_excluded a [8,2,6,0,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,6,0,7,1,0] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,1,1] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,1,2] (by decide +kernel))
      node_2840
      node_2841
      node_2842
      (invalid_excluded a [8,2,6,0,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,1,8] (by decide +kernel)))

theorem node_2846 : Excluded a [8,2,6,0,7,3] :=
  source_excluded a [8,2,6,0,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2847 : Excluded a [8,2,6,0,7,4] :=
  predecessor_excluded a [8,2,6,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2838 : Excluded a [8,2,6,0,7] :=
  branch_excluded a [8,2,6,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,6,0,7,0] (by decide +kernel))
      node_2839
      (invalid_excluded a [8,2,6,0,7,2] (by decide +kernel))
      node_2846
      node_2847
      (invalid_excluded a [8,2,6,0,7,5] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,2,6,0,7,8] (by decide +kernel)))

theorem node_2834 : Excluded a [8,2,6,0] :=
  branch_excluded a [8,2,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,6,0,0] (by decide +kernel))
      node_2835
      (invalid_excluded a [8,2,6,0,2] (by decide +kernel))
      node_2836
      (invalid_excluded a [8,2,6,0,4] (by decide +kernel))
      node_2837
      (invalid_excluded a [8,2,6,0,6] (by decide +kernel))
      node_2838
      (invalid_excluded a [8,2,6,0,8] (by decide +kernel)))

theorem node_2848 : Excluded a [8,2,6,1] :=
  predecessor_excluded a [8,2,6,1] 0 2 3 1 (by decide) (by decide +kernel)

theorem node_2850 : Excluded a [8,2,6,5,0] :=
  source_excluded a [8,2,6,5,0] 1 3 4 (by decide) (by decide +kernel)

theorem node_2851 : Excluded a [8,2,6,5,1] :=
  source_excluded a [8,2,6,5,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2852 : Excluded a [8,2,6,5,3] :=
  source_excluded a [8,2,6,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2855 : Excluded a [8,2,6,5,7,0,1] :=
  predecessor_excluded a [8,2,6,5,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_2856 : Excluded a [8,2,6,5,7,0,3] :=
  source_excluded a [8,2,6,5,7,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2857 : Excluded a [8,2,6,5,7,0,4] :=
  source_excluded a [8,2,6,5,7,0,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2854 : Excluded a [8,2,6,5,7,0] :=
  branch_excluded a [8,2,6,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,6,5,7,0,0] (by decide +kernel))
      node_2855
      (invalid_excluded a [8,2,6,5,7,0,2] (by decide +kernel))
      node_2856
      node_2857
      (invalid_excluded a [8,2,6,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,2,6,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,2,6,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,2,6,5,7,0,8] (by decide +kernel)))

theorem node_2859 : Excluded a [8,2,6,5,7,1,0] :=
  predecessor_excluded a [8,2,6,5,7,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2860 : Excluded a [8,2,6,5,7,1,3] :=
  source_excluded a [8,2,6,5,7,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2861 : Excluded a [8,2,6,5,7,1,4] :=
  source_excluded a [8,2,6,5,7,1,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2858 : Excluded a [8,2,6,5,7,1] :=
  branch_excluded a [8,2,6,5,7,1] (by decide)
    (fin9_cases _
      node_2859
      (invalid_excluded a [8,2,6,5,7,1,1] (by decide +kernel))
      (invalid_excluded a [8,2,6,5,7,1,2] (by decide +kernel))
      node_2860
      node_2861
      (invalid_excluded a [8,2,6,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [8,2,6,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,2,6,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,2,6,5,7,1,8] (by decide +kernel)))

theorem node_2862 : Excluded a [8,2,6,5,7,3] :=
  source_excluded a [8,2,6,5,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2863 : Excluded a [8,2,6,5,7,4] :=
  source_excluded a [8,2,6,5,7,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2853 : Excluded a [8,2,6,5,7] :=
  branch_excluded a [8,2,6,5,7] (by decide)
    (fin9_cases _
      node_2854
      node_2858
      (invalid_excluded a [8,2,6,5,7,2] (by decide +kernel))
      node_2862
      node_2863
      (invalid_excluded a [8,2,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [8,2,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [8,2,6,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,2,6,5,7,8] (by decide +kernel)))

theorem node_2849 : Excluded a [8,2,6,5] :=
  branch_excluded a [8,2,6,5] (by decide)
    (fin9_cases _
      node_2850
      node_2851
      (invalid_excluded a [8,2,6,5,2] (by decide +kernel))
      node_2852
      (invalid_excluded a [8,2,6,5,4] (by decide +kernel))
      (invalid_excluded a [8,2,6,5,5] (by decide +kernel))
      (invalid_excluded a [8,2,6,5,6] (by decide +kernel))
      node_2853
      (invalid_excluded a [8,2,6,5,8] (by decide +kernel)))

theorem node_2864 : Excluded a [8,2,6,7] :=
  predecessor_excluded a [8,2,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_2833 : Excluded a [8,2,6] :=
  branch_excluded a [8,2,6] (by decide)
    (fin9_cases _
      node_2834
      node_2848
      (invalid_excluded a [8,2,6,2] (by decide +kernel))
      (invalid_excluded a [8,2,6,3] (by decide +kernel))
      (invalid_excluded a [8,2,6,4] (by decide +kernel))
      node_2849
      (invalid_excluded a [8,2,6,6] (by decide +kernel))
      node_2864
      (invalid_excluded a [8,2,6,8] (by decide +kernel)))

theorem node_2867 : Excluded a [8,2,7,0,1] :=
  source_excluded a [8,2,7,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2868 : Excluded a [8,2,7,0,3] :=
  source_excluded a [8,2,7,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2871 : Excluded a [8,2,7,0,5,1,3] :=
  source_excluded a [8,2,7,0,5,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2873 : Excluded a [8,2,7,0,5,1,4,3] :=
  source_excluded a [8,2,7,0,5,1,4,3] 2 0 7 (by decide) (by decide +kernel)

def b_2875 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 2
  | 2 => 7
  | 3 => 0
  | 4 => 5
  | 5 => 1
  | 6 => 4
  | 7 => 6
  | 8 => 3
  | _ => 0

def cert_2875 : LosingRegion (edgeOf a b_2875) 0 :=
  losingMask a b_2875 0 1250375060324005503304704
    (by decide +kernel) (by decide +kernel)

theorem node_2875 : Excluded a [8,2,7,0,5,1,4,6,3] :=
  losing_excluded a [8,2,7,0,5,1,4,6,3] (by decide) b_2875 (by decide +kernel) 2 0 3 cert_2875 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2875 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1250375060324005503304704 2 3; decide +kernel)

theorem node_2874 : Excluded a [8,2,7,0,5,1,4,6] :=
  branch_excluded a [8,2,7,0,5,1,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,7,0,5,1,4,6,0] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,1,4,6,1] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,1,4,6,2] (by decide +kernel))
      node_2875
      (invalid_excluded a [8,2,7,0,5,1,4,6,4] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,1,4,6,5] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,1,4,6,6] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,1,4,6,7] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,1,4,6,8] (by decide +kernel)))

theorem node_2872 : Excluded a [8,2,7,0,5,1,4] :=
  branch_excluded a [8,2,7,0,5,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,7,0,5,1,4,0] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,1,4,1] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,1,4,2] (by decide +kernel))
      node_2873
      (invalid_excluded a [8,2,7,0,5,1,4,4] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,1,4,5] (by decide +kernel))
      node_2874
      (invalid_excluded a [8,2,7,0,5,1,4,7] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,1,4,8] (by decide +kernel)))

theorem node_2870 : Excluded a [8,2,7,0,5,1] :=
  branch_excluded a [8,2,7,0,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,7,0,5,1,0] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,1,1] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,1,2] (by decide +kernel))
      node_2871
      node_2872
      (invalid_excluded a [8,2,7,0,5,1,5] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,1,6] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,1,7] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,1,8] (by decide +kernel)))

theorem node_2876 : Excluded a [8,2,7,0,5,3] :=
  predecessor_excluded a [8,2,7,0,5,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_2879 : Excluded a [8,2,7,0,5,4,1,3] :=
  source_excluded a [8,2,7,0,5,4,1,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_2881 : Excluded a [8,2,7,0,5,4,1,6,3] :=
  predecessor_excluded a [8,2,7,0,5,4,1,6,3] 0 4 8 5 (by decide) (by decide +kernel)

theorem node_2880 : Excluded a [8,2,7,0,5,4,1,6] :=
  branch_excluded a [8,2,7,0,5,4,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,7,0,5,4,1,6,0] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,4,1,6,1] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,4,1,6,2] (by decide +kernel))
      node_2881
      (invalid_excluded a [8,2,7,0,5,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,4,1,6,8] (by decide +kernel)))

theorem node_2878 : Excluded a [8,2,7,0,5,4,1] :=
  branch_excluded a [8,2,7,0,5,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,7,0,5,4,1,0] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,4,1,1] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,4,1,2] (by decide +kernel))
      node_2879
      (invalid_excluded a [8,2,7,0,5,4,1,4] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,4,1,5] (by decide +kernel))
      node_2880
      (invalid_excluded a [8,2,7,0,5,4,1,7] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,4,1,8] (by decide +kernel)))

theorem node_2882 : Excluded a [8,2,7,0,5,4,3] :=
  source_excluded a [8,2,7,0,5,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2877 : Excluded a [8,2,7,0,5,4] :=
  branch_excluded a [8,2,7,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,7,0,5,4,0] (by decide +kernel))
      node_2878
      (invalid_excluded a [8,2,7,0,5,4,2] (by decide +kernel))
      node_2882
      (invalid_excluded a [8,2,7,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,4,5] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,4,6] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,4,8] (by decide +kernel)))

theorem node_2869 : Excluded a [8,2,7,0,5] :=
  branch_excluded a [8,2,7,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,7,0,5,0] (by decide +kernel))
      node_2870
      (invalid_excluded a [8,2,7,0,5,2] (by decide +kernel))
      node_2876
      node_2877
      (invalid_excluded a [8,2,7,0,5,5] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,6] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,7] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,5,8] (by decide +kernel)))

theorem node_2883 : Excluded a [8,2,7,0,6] :=
  predecessor_excluded a [8,2,7,0,6] 0 7 4 2 (by decide) (by decide +kernel)

theorem node_2866 : Excluded a [8,2,7,0] :=
  branch_excluded a [8,2,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,7,0,0] (by decide +kernel))
      node_2867
      (invalid_excluded a [8,2,7,0,2] (by decide +kernel))
      node_2868
      (invalid_excluded a [8,2,7,0,4] (by decide +kernel))
      node_2869
      node_2883
      (invalid_excluded a [8,2,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,2,7,0,8] (by decide +kernel)))

theorem node_2884 : Excluded a [8,2,7,1] :=
  predecessor_excluded a [8,2,7,1] 0 2 3 1 (by decide) (by decide +kernel)

theorem node_2886 : Excluded a [8,2,7,5,0] :=
  source_excluded a [8,2,7,5,0] 1 3 4 (by decide) (by decide +kernel)

theorem node_2887 : Excluded a [8,2,7,5,1] :=
  source_excluded a [8,2,7,5,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2888 : Excluded a [8,2,7,5,3] :=
  source_excluded a [8,2,7,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2889 : Excluded a [8,2,7,5,6] :=
  predecessor_excluded a [8,2,7,5,6] 0 7 4 2 (by decide) (by decide +kernel)

theorem node_2885 : Excluded a [8,2,7,5] :=
  branch_excluded a [8,2,7,5] (by decide)
    (fin9_cases _
      node_2886
      node_2887
      (invalid_excluded a [8,2,7,5,2] (by decide +kernel))
      node_2888
      (invalid_excluded a [8,2,7,5,4] (by decide +kernel))
      (invalid_excluded a [8,2,7,5,5] (by decide +kernel))
      node_2889
      (invalid_excluded a [8,2,7,5,7] (by decide +kernel))
      (invalid_excluded a [8,2,7,5,8] (by decide +kernel)))

theorem node_2891 : Excluded a [8,2,7,6,0] :=
  source_excluded a [8,2,7,6,0] 1 3 4 (by decide) (by decide +kernel)

theorem node_2892 : Excluded a [8,2,7,6,1] :=
  source_excluded a [8,2,7,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2893 : Excluded a [8,2,7,6,3] :=
  source_excluded a [8,2,7,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_2896 : Excluded a [8,2,7,6,5,0,1] :=
  predecessor_excluded a [8,2,7,6,5,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_2897 : Excluded a [8,2,7,6,5,0,3] :=
  source_excluded a [8,2,7,6,5,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2898 : Excluded a [8,2,7,6,5,0,4] :=
  source_excluded a [8,2,7,6,5,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2895 : Excluded a [8,2,7,6,5,0] :=
  branch_excluded a [8,2,7,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,2,7,6,5,0,0] (by decide +kernel))
      node_2896
      (invalid_excluded a [8,2,7,6,5,0,2] (by decide +kernel))
      node_2897
      node_2898
      (invalid_excluded a [8,2,7,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [8,2,7,6,5,0,6] (by decide +kernel))
      (invalid_excluded a [8,2,7,6,5,0,7] (by decide +kernel))
      (invalid_excluded a [8,2,7,6,5,0,8] (by decide +kernel)))

theorem node_2900 : Excluded a [8,2,7,6,5,1,0] :=
  predecessor_excluded a [8,2,7,6,5,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2901 : Excluded a [8,2,7,6,5,1,3] :=
  source_excluded a [8,2,7,6,5,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2902 : Excluded a [8,2,7,6,5,1,4] :=
  source_excluded a [8,2,7,6,5,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2899 : Excluded a [8,2,7,6,5,1] :=
  branch_excluded a [8,2,7,6,5,1] (by decide)
    (fin9_cases _
      node_2900
      (invalid_excluded a [8,2,7,6,5,1,1] (by decide +kernel))
      (invalid_excluded a [8,2,7,6,5,1,2] (by decide +kernel))
      node_2901
      node_2902
      (invalid_excluded a [8,2,7,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [8,2,7,6,5,1,6] (by decide +kernel))
      (invalid_excluded a [8,2,7,6,5,1,7] (by decide +kernel))
      (invalid_excluded a [8,2,7,6,5,1,8] (by decide +kernel)))

theorem node_2903 : Excluded a [8,2,7,6,5,3] :=
  source_excluded a [8,2,7,6,5,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2904 : Excluded a [8,2,7,6,5,4] :=
  source_excluded a [8,2,7,6,5,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2894 : Excluded a [8,2,7,6,5] :=
  branch_excluded a [8,2,7,6,5] (by decide)
    (fin9_cases _
      node_2895
      node_2899
      (invalid_excluded a [8,2,7,6,5,2] (by decide +kernel))
      node_2903
      node_2904
      (invalid_excluded a [8,2,7,6,5,5] (by decide +kernel))
      (invalid_excluded a [8,2,7,6,5,6] (by decide +kernel))
      (invalid_excluded a [8,2,7,6,5,7] (by decide +kernel))
      (invalid_excluded a [8,2,7,6,5,8] (by decide +kernel)))

theorem node_2890 : Excluded a [8,2,7,6] :=
  branch_excluded a [8,2,7,6] (by decide)
    (fin9_cases _
      node_2891
      node_2892
      (invalid_excluded a [8,2,7,6,2] (by decide +kernel))
      node_2893
      (invalid_excluded a [8,2,7,6,4] (by decide +kernel))
      node_2894
      (invalid_excluded a [8,2,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,2,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,2,7,6,8] (by decide +kernel)))

theorem node_2865 : Excluded a [8,2,7] :=
  branch_excluded a [8,2,7] (by decide)
    (fin9_cases _
      node_2866
      node_2884
      (invalid_excluded a [8,2,7,2] (by decide +kernel))
      (invalid_excluded a [8,2,7,3] (by decide +kernel))
      (invalid_excluded a [8,2,7,4] (by decide +kernel))
      node_2885
      node_2890
      (invalid_excluded a [8,2,7,7] (by decide +kernel))
      (invalid_excluded a [8,2,7,8] (by decide +kernel)))

theorem node_2790 : Excluded a [8,2] :=
  branch_excluded a [8,2] (by decide)
    (fin9_cases _
      node_2791
      node_2792
      (invalid_excluded a [8,2,2] (by decide +kernel))
      (invalid_excluded a [8,2,3] (by decide +kernel))
      node_2793
      node_2794
      node_2833
      node_2865
      (invalid_excluded a [8,2,8] (by decide +kernel)))

theorem node_2906 : Excluded a [8,3,0] :=
  source_excluded a [8,3,0] 1 2 2 (by decide) (by decide +kernel)

theorem node_2907 : Excluded a [8,3,1] :=
  source_excluded a [8,3,1] 2 0 1 (by decide) (by decide +kernel)

theorem node_2908 : Excluded a [8,3,4] :=
  source_excluded a [8,3,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_2910 : Excluded a [8,3,5,0] :=
  source_excluded a [8,3,5,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2911 : Excluded a [8,3,5,1] :=
  predecessor_excluded a [8,3,5,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_2912 : Excluded a [8,3,5,2] :=
  source_excluded a [8,3,5,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2913 : Excluded a [8,3,5,6] :=
  predecessor_excluded a [8,3,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_2918 : Excluded a [8,3,5,7,0,1,2,4] :=
  source_excluded a [8,3,5,7,0,1,2,4] 3 0 7 (by decide) (by decide +kernel)

def b_2920 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 0
  | 5 => 1
  | 6 => 2
  | 7 => 6
  | 8 => 4
  | _ => 0

def cert_2920 : LosingRegion (edgeOf a b_2920) 0 :=
  losingMask a b_2920 0 1288264672633093332141056
    (by decide +kernel) (by decide +kernel)

theorem node_2920 : Excluded a [8,3,5,7,0,1,2,6,4] :=
  losing_excluded a [8,3,5,7,0,1,2,6,4] (by decide) b_2920 (by decide +kernel) 2 0 0 cert_2920 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2920 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1288264672633093332141056 2 0; decide +kernel)

theorem node_2919 : Excluded a [8,3,5,7,0,1,2,6] :=
  branch_excluded a [8,3,5,7,0,1,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,5,7,0,1,2,6,0] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,1,2,6,1] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,1,2,6,2] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,1,2,6,3] (by decide +kernel))
      node_2920
      (invalid_excluded a [8,3,5,7,0,1,2,6,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,1,2,6,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,1,2,6,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,1,2,6,8] (by decide +kernel)))

theorem node_2917 : Excluded a [8,3,5,7,0,1,2] :=
  branch_excluded a [8,3,5,7,0,1,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,5,7,0,1,2,0] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,1,2,1] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,1,2,2] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,1,2,3] (by decide +kernel))
      node_2918
      (invalid_excluded a [8,3,5,7,0,1,2,5] (by decide +kernel))
      node_2919
      (invalid_excluded a [8,3,5,7,0,1,2,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,1,2,8] (by decide +kernel)))

theorem node_2921 : Excluded a [8,3,5,7,0,1,4] :=
  source_excluded a [8,3,5,7,0,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2916 : Excluded a [8,3,5,7,0,1] :=
  branch_excluded a [8,3,5,7,0,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,5,7,0,1,0] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,1,1] (by decide +kernel))
      node_2917
      (invalid_excluded a [8,3,5,7,0,1,3] (by decide +kernel))
      node_2921
      (invalid_excluded a [8,3,5,7,0,1,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,1,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,1,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,1,8] (by decide +kernel)))

theorem node_2924 : Excluded a [8,3,5,7,0,2,1,4] :=
  source_excluded a [8,3,5,7,0,2,1,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_2926 : Excluded a [8,3,5,7,0,2,1,6,4] :=
  predecessor_excluded a [8,3,5,7,0,2,1,6,4] 0 2 8 5 (by decide) (by decide +kernel)

theorem node_2925 : Excluded a [8,3,5,7,0,2,1,6] :=
  branch_excluded a [8,3,5,7,0,2,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,5,7,0,2,1,6,0] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,6,1] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,6,2] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,6,3] (by decide +kernel))
      node_2926
      (invalid_excluded a [8,3,5,7,0,2,1,6,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,6,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,6,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,6,8] (by decide +kernel)))

theorem node_2923 : Excluded a [8,3,5,7,0,2,1] :=
  branch_excluded a [8,3,5,7,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,5,7,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,2] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,3] (by decide +kernel))
      node_2924
      (invalid_excluded a [8,3,5,7,0,2,1,5] (by decide +kernel))
      node_2925
      (invalid_excluded a [8,3,5,7,0,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,8] (by decide +kernel)))

theorem node_2927 : Excluded a [8,3,5,7,0,2,4] :=
  source_excluded a [8,3,5,7,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2922 : Excluded a [8,3,5,7,0,2] :=
  branch_excluded a [8,3,5,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,5,7,0,2,0] (by decide +kernel))
      node_2923
      (invalid_excluded a [8,3,5,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,3] (by decide +kernel))
      node_2927
      (invalid_excluded a [8,3,5,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,8] (by decide +kernel)))

theorem node_2928 : Excluded a [8,3,5,7,0,4] :=
  predecessor_excluded a [8,3,5,7,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2915 : Excluded a [8,3,5,7,0] :=
  branch_excluded a [8,3,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,5,7,0,0] (by decide +kernel))
      node_2916
      node_2922
      (invalid_excluded a [8,3,5,7,0,3] (by decide +kernel))
      node_2928
      (invalid_excluded a [8,3,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,8] (by decide +kernel)))

theorem node_2929 : Excluded a [8,3,5,7,1] :=
  predecessor_excluded a [8,3,5,7,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_2932 : Excluded a [8,3,5,7,6,0,1] :=
  predecessor_excluded a [8,3,5,7,6,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_2933 : Excluded a [8,3,5,7,6,0,2] :=
  source_excluded a [8,3,5,7,6,0,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_2934 : Excluded a [8,3,5,7,6,0,4] :=
  source_excluded a [8,3,5,7,6,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2931 : Excluded a [8,3,5,7,6,0] :=
  branch_excluded a [8,3,5,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,5,7,6,0,0] (by decide +kernel))
      node_2932
      node_2933
      (invalid_excluded a [8,3,5,7,6,0,3] (by decide +kernel))
      node_2934
      (invalid_excluded a [8,3,5,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,6,0,8] (by decide +kernel)))

theorem node_2936 : Excluded a [8,3,5,7,6,1,0] :=
  predecessor_excluded a [8,3,5,7,6,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2937 : Excluded a [8,3,5,7,6,1,2] :=
  source_excluded a [8,3,5,7,6,1,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_2938 : Excluded a [8,3,5,7,6,1,4] :=
  source_excluded a [8,3,5,7,6,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2935 : Excluded a [8,3,5,7,6,1] :=
  branch_excluded a [8,3,5,7,6,1] (by decide)
    (fin9_cases _
      node_2936
      (invalid_excluded a [8,3,5,7,6,1,1] (by decide +kernel))
      node_2937
      (invalid_excluded a [8,3,5,7,6,1,3] (by decide +kernel))
      node_2938
      (invalid_excluded a [8,3,5,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,6,1,8] (by decide +kernel)))

theorem node_2939 : Excluded a [8,3,5,7,6,2] :=
  source_excluded a [8,3,5,7,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_2940 : Excluded a [8,3,5,7,6,4] :=
  source_excluded a [8,3,5,7,6,4] 5 0 4 (by decide) (by decide +kernel)

theorem node_2930 : Excluded a [8,3,5,7,6] :=
  branch_excluded a [8,3,5,7,6] (by decide)
    (fin9_cases _
      node_2931
      node_2935
      node_2939
      (invalid_excluded a [8,3,5,7,6,3] (by decide +kernel))
      node_2940
      (invalid_excluded a [8,3,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,6,8] (by decide +kernel)))

theorem node_2914 : Excluded a [8,3,5,7] :=
  branch_excluded a [8,3,5,7] (by decide)
    (fin9_cases _
      node_2915
      node_2929
      (invalid_excluded a [8,3,5,7,2] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,3] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,4] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,5] (by decide +kernel))
      node_2930
      (invalid_excluded a [8,3,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,8] (by decide +kernel)))

theorem node_2909 : Excluded a [8,3,5] :=
  branch_excluded a [8,3,5] (by decide)
    (fin9_cases _
      node_2910
      node_2911
      node_2912
      (invalid_excluded a [8,3,5,3] (by decide +kernel))
      (invalid_excluded a [8,3,5,4] (by decide +kernel))
      (invalid_excluded a [8,3,5,5] (by decide +kernel))
      node_2913
      node_2914
      (invalid_excluded a [8,3,5,8] (by decide +kernel)))

theorem node_2942 : Excluded a [8,3,6,0] :=
  source_excluded a [8,3,6,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2943 : Excluded a [8,3,6,1] :=
  predecessor_excluded a [8,3,6,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_2944 : Excluded a [8,3,6,2] :=
  source_excluded a [8,3,6,2] 3 0 4 (by decide) (by decide +kernel)

def b_2950 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 3
  | 2 => 6
  | 3 => 5
  | 4 => 0
  | 5 => 1
  | 6 => 2
  | 7 => 4
  | 8 => 7
  | _ => 0

def cert_2950 : LosingRegion (edgeOf a b_2950) 0 :=
  losingMask a b_2950 0 1333117912833885205955584
    (by decide +kernel) (by decide +kernel)

theorem node_2950 : Excluded a [8,3,6,5,0,1,2,4,7] :=
  losing_excluded a [8,3,6,5,0,1,2,4,7] (by decide) b_2950 (by decide +kernel) 2 0 1 cert_2950 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2950 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1333117912833885205955584 2 1; decide +kernel)

theorem node_2949 : Excluded a [8,3,6,5,0,1,2,4] :=
  branch_excluded a [8,3,6,5,0,1,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,6,5,0,1,2,4,0] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,1,2,4,1] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,1,2,4,2] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,1,2,4,3] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,1,2,4,4] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,1,2,4,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,1,2,4,6] (by decide +kernel))
      node_2950
      (invalid_excluded a [8,3,6,5,0,1,2,4,8] (by decide +kernel)))

theorem node_2948 : Excluded a [8,3,6,5,0,1,2] :=
  branch_excluded a [8,3,6,5,0,1,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,6,5,0,1,2,0] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,1,2,1] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,1,2,2] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,1,2,3] (by decide +kernel))
      node_2949
      (invalid_excluded a [8,3,6,5,0,1,2,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,1,2,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,1,2,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,1,2,8] (by decide +kernel)))

theorem node_2951 : Excluded a [8,3,6,5,0,1,4] :=
  predecessor_excluded a [8,3,6,5,0,1,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_2947 : Excluded a [8,3,6,5,0,1] :=
  branch_excluded a [8,3,6,5,0,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,6,5,0,1,0] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,1,1] (by decide +kernel))
      node_2948
      (invalid_excluded a [8,3,6,5,0,1,3] (by decide +kernel))
      node_2951
      (invalid_excluded a [8,3,6,5,0,1,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,1,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,1,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,1,8] (by decide +kernel)))

theorem node_2952 : Excluded a [8,3,6,5,0,2] :=
  source_excluded a [8,3,6,5,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2953 : Excluded a [8,3,6,5,0,4] :=
  source_excluded a [8,3,6,5,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2954 : Excluded a [8,3,6,5,0,7] :=
  source_excluded a [8,3,6,5,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2946 : Excluded a [8,3,6,5,0] :=
  branch_excluded a [8,3,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,6,5,0,0] (by decide +kernel))
      node_2947
      node_2952
      (invalid_excluded a [8,3,6,5,0,3] (by decide +kernel))
      node_2953
      (invalid_excluded a [8,3,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,0,6] (by decide +kernel))
      node_2954
      (invalid_excluded a [8,3,6,5,0,8] (by decide +kernel)))

theorem node_2955 : Excluded a [8,3,6,5,1] :=
  predecessor_excluded a [8,3,6,5,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_2958 : Excluded a [8,3,6,5,7,0,1] :=
  predecessor_excluded a [8,3,6,5,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_2959 : Excluded a [8,3,6,5,7,0,2] :=
  source_excluded a [8,3,6,5,7,0,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_2960 : Excluded a [8,3,6,5,7,0,4] :=
  source_excluded a [8,3,6,5,7,0,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2957 : Excluded a [8,3,6,5,7,0] :=
  branch_excluded a [8,3,6,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,6,5,7,0,0] (by decide +kernel))
      node_2958
      node_2959
      (invalid_excluded a [8,3,6,5,7,0,3] (by decide +kernel))
      node_2960
      (invalid_excluded a [8,3,6,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,7,0,8] (by decide +kernel)))

theorem node_2962 : Excluded a [8,3,6,5,7,1,0] :=
  predecessor_excluded a [8,3,6,5,7,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_2963 : Excluded a [8,3,6,5,7,1,2] :=
  source_excluded a [8,3,6,5,7,1,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_2964 : Excluded a [8,3,6,5,7,1,4] :=
  source_excluded a [8,3,6,5,7,1,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2961 : Excluded a [8,3,6,5,7,1] :=
  branch_excluded a [8,3,6,5,7,1] (by decide)
    (fin9_cases _
      node_2962
      (invalid_excluded a [8,3,6,5,7,1,1] (by decide +kernel))
      node_2963
      (invalid_excluded a [8,3,6,5,7,1,3] (by decide +kernel))
      node_2964
      (invalid_excluded a [8,3,6,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,7,1,8] (by decide +kernel)))

theorem node_2965 : Excluded a [8,3,6,5,7,2] :=
  source_excluded a [8,3,6,5,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2966 : Excluded a [8,3,6,5,7,4] :=
  source_excluded a [8,3,6,5,7,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2956 : Excluded a [8,3,6,5,7] :=
  branch_excluded a [8,3,6,5,7] (by decide)
    (fin9_cases _
      node_2957
      node_2961
      node_2965
      (invalid_excluded a [8,3,6,5,7,3] (by decide +kernel))
      node_2966
      (invalid_excluded a [8,3,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,7,8] (by decide +kernel)))

theorem node_2945 : Excluded a [8,3,6,5] :=
  branch_excluded a [8,3,6,5] (by decide)
    (fin9_cases _
      node_2946
      node_2955
      (invalid_excluded a [8,3,6,5,2] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,3] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,4] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,5,6] (by decide +kernel))
      node_2956
      (invalid_excluded a [8,3,6,5,8] (by decide +kernel)))

theorem node_2967 : Excluded a [8,3,6,7] :=
  predecessor_excluded a [8,3,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_2941 : Excluded a [8,3,6] :=
  branch_excluded a [8,3,6] (by decide)
    (fin9_cases _
      node_2942
      node_2943
      node_2944
      (invalid_excluded a [8,3,6,3] (by decide +kernel))
      (invalid_excluded a [8,3,6,4] (by decide +kernel))
      node_2945
      (invalid_excluded a [8,3,6,6] (by decide +kernel))
      node_2967
      (invalid_excluded a [8,3,6,8] (by decide +kernel)))

theorem node_2969 : Excluded a [8,3,7,0] :=
  source_excluded a [8,3,7,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2970 : Excluded a [8,3,7,1] :=
  predecessor_excluded a [8,3,7,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_2971 : Excluded a [8,3,7,2] :=
  source_excluded a [8,3,7,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_2975 : Excluded a [8,3,7,5,0,1,2] :=
  source_excluded a [8,3,7,5,0,1,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_2977 : Excluded a [8,3,7,5,0,1,4,2] :=
  predecessor_excluded a [8,3,7,5,0,1,4,2] 0 2 6 7 (by decide) (by decide +kernel)

def b_2979 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 3
  | 2 => 7
  | 3 => 5
  | 4 => 0
  | 5 => 1
  | 6 => 4
  | 7 => 6
  | 8 => 2
  | _ => 0

def cert_2979 : LosingRegion (edgeOf a b_2979) 0 :=
  losingMask a b_2979 0 1413741605529464400774144
    (by decide +kernel) (by decide +kernel)

theorem node_2979 : Excluded a [8,3,7,5,0,1,4,6,2] :=
  losing_excluded a [8,3,7,5,0,1,4,6,2] (by decide) b_2979 (by decide +kernel) 2 0 1 cert_2979 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2979 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1413741605529464400774144 2 1; decide +kernel)

theorem node_2978 : Excluded a [8,3,7,5,0,1,4,6] :=
  branch_excluded a [8,3,7,5,0,1,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,7,5,0,1,4,6,0] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,1,4,6,1] (by decide +kernel))
      node_2979
      (invalid_excluded a [8,3,7,5,0,1,4,6,3] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,1,4,6,4] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,1,4,6,5] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,1,4,6,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,1,4,6,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,1,4,6,8] (by decide +kernel)))

theorem node_2976 : Excluded a [8,3,7,5,0,1,4] :=
  branch_excluded a [8,3,7,5,0,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,7,5,0,1,4,0] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,1,4,1] (by decide +kernel))
      node_2977
      (invalid_excluded a [8,3,7,5,0,1,4,3] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,1,4,4] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,1,4,5] (by decide +kernel))
      node_2978
      (invalid_excluded a [8,3,7,5,0,1,4,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,1,4,8] (by decide +kernel)))

theorem node_2974 : Excluded a [8,3,7,5,0,1] :=
  branch_excluded a [8,3,7,5,0,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,7,5,0,1,0] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,1,1] (by decide +kernel))
      node_2975
      (invalid_excluded a [8,3,7,5,0,1,3] (by decide +kernel))
      node_2976
      (invalid_excluded a [8,3,7,5,0,1,5] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,1,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,1,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,1,8] (by decide +kernel)))

theorem node_2980 : Excluded a [8,3,7,5,0,2] :=
  predecessor_excluded a [8,3,7,5,0,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_2981 : Excluded a [8,3,7,5,0,4] :=
  source_excluded a [8,3,7,5,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2973 : Excluded a [8,3,7,5,0] :=
  branch_excluded a [8,3,7,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,7,5,0,0] (by decide +kernel))
      node_2974
      node_2980
      (invalid_excluded a [8,3,7,5,0,3] (by decide +kernel))
      node_2981
      (invalid_excluded a [8,3,7,5,0,5] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,0,8] (by decide +kernel)))

theorem node_2982 : Excluded a [8,3,7,5,1] :=
  predecessor_excluded a [8,3,7,5,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_2983 : Excluded a [8,3,7,5,6] :=
  predecessor_excluded a [8,3,7,5,6] 0 7 4 2 (by decide) (by decide +kernel)

theorem node_2972 : Excluded a [8,3,7,5] :=
  branch_excluded a [8,3,7,5] (by decide)
    (fin9_cases _
      node_2973
      node_2982
      (invalid_excluded a [8,3,7,5,2] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,3] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,4] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,5] (by decide +kernel))
      node_2983
      (invalid_excluded a [8,3,7,5,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,5,8] (by decide +kernel)))

theorem node_2987 : Excluded a [8,3,7,6,0,1,2] :=
  source_excluded a [8,3,7,6,0,1,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_2988 : Excluded a [8,3,7,6,0,1,4] :=
  source_excluded a [8,3,7,6,0,1,4] 3 0 6 (by decide) (by decide +kernel)

def b_2991 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 3
  | 2 => 7
  | 3 => 6
  | 4 => 0
  | 5 => 1
  | 6 => 5
  | 7 => 2
  | 8 => 4
  | _ => 0

def cert_2991 : LosingRegion (edgeOf a b_2991) 0 :=
  losingMask a b_2991 0 1288262150617302040314880
    (by decide +kernel) (by decide +kernel)

theorem node_2991 : Excluded a [8,3,7,6,0,1,5,2,4] :=
  losing_excluded a [8,3,7,6,0,1,5,2,4] (by decide) b_2991 (by decide +kernel) 2 0 0 cert_2991 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2991 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1288262150617302040314880 2 0; decide +kernel)

theorem node_2990 : Excluded a [8,3,7,6,0,1,5,2] :=
  branch_excluded a [8,3,7,6,0,1,5,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,7,6,0,1,5,2,0] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,1,5,2,1] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,1,5,2,2] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,1,5,2,3] (by decide +kernel))
      node_2991
      (invalid_excluded a [8,3,7,6,0,1,5,2,5] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,1,5,2,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,1,5,2,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,1,5,2,8] (by decide +kernel)))

theorem node_2992 : Excluded a [8,3,7,6,0,1,5,4] :=
  predecessor_excluded a [8,3,7,6,0,1,5,4] 0 4 2 7 (by decide) (by decide +kernel)

theorem node_2989 : Excluded a [8,3,7,6,0,1,5] :=
  branch_excluded a [8,3,7,6,0,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,7,6,0,1,5,0] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,1,5,1] (by decide +kernel))
      node_2990
      (invalid_excluded a [8,3,7,6,0,1,5,3] (by decide +kernel))
      node_2992
      (invalid_excluded a [8,3,7,6,0,1,5,5] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,1,5,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,1,5,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,1,5,8] (by decide +kernel)))

theorem node_2986 : Excluded a [8,3,7,6,0,1] :=
  branch_excluded a [8,3,7,6,0,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,7,6,0,1,0] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,1,1] (by decide +kernel))
      node_2987
      (invalid_excluded a [8,3,7,6,0,1,3] (by decide +kernel))
      node_2988
      node_2989
      (invalid_excluded a [8,3,7,6,0,1,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,1,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,1,8] (by decide +kernel)))

theorem node_2993 : Excluded a [8,3,7,6,0,2] :=
  predecessor_excluded a [8,3,7,6,0,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_2994 : Excluded a [8,3,7,6,0,4] :=
  source_excluded a [8,3,7,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2985 : Excluded a [8,3,7,6,0] :=
  branch_excluded a [8,3,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,7,6,0,0] (by decide +kernel))
      node_2986
      node_2993
      (invalid_excluded a [8,3,7,6,0,3] (by decide +kernel))
      node_2994
      (invalid_excluded a [8,3,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,8] (by decide +kernel)))

theorem node_2995 : Excluded a [8,3,7,6,1] :=
  predecessor_excluded a [8,3,7,6,1] 0 3 4 1 (by decide) (by decide +kernel)

theorem node_2998 : Excluded a [8,3,7,6,5,0,1] :=
  predecessor_excluded a [8,3,7,6,5,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_2999 : Excluded a [8,3,7,6,5,0,2] :=
  source_excluded a [8,3,7,6,5,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_3000 : Excluded a [8,3,7,6,5,0,4] :=
  source_excluded a [8,3,7,6,5,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2997 : Excluded a [8,3,7,6,5,0] :=
  branch_excluded a [8,3,7,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,7,6,5,0,0] (by decide +kernel))
      node_2998
      node_2999
      (invalid_excluded a [8,3,7,6,5,0,3] (by decide +kernel))
      node_3000
      (invalid_excluded a [8,3,7,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,5,0,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,5,0,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,5,0,8] (by decide +kernel)))

theorem node_3002 : Excluded a [8,3,7,6,5,1,0] :=
  predecessor_excluded a [8,3,7,6,5,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_3003 : Excluded a [8,3,7,6,5,1,2] :=
  source_excluded a [8,3,7,6,5,1,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_3004 : Excluded a [8,3,7,6,5,1,4] :=
  source_excluded a [8,3,7,6,5,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_3001 : Excluded a [8,3,7,6,5,1] :=
  branch_excluded a [8,3,7,6,5,1] (by decide)
    (fin9_cases _
      node_3002
      (invalid_excluded a [8,3,7,6,5,1,1] (by decide +kernel))
      node_3003
      (invalid_excluded a [8,3,7,6,5,1,3] (by decide +kernel))
      node_3004
      (invalid_excluded a [8,3,7,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,5,1,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,5,1,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,5,1,8] (by decide +kernel)))

theorem node_3005 : Excluded a [8,3,7,6,5,2] :=
  source_excluded a [8,3,7,6,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_3006 : Excluded a [8,3,7,6,5,4] :=
  source_excluded a [8,3,7,6,5,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2996 : Excluded a [8,3,7,6,5] :=
  branch_excluded a [8,3,7,6,5] (by decide)
    (fin9_cases _
      node_2997
      node_3001
      node_3005
      (invalid_excluded a [8,3,7,6,5,3] (by decide +kernel))
      node_3006
      (invalid_excluded a [8,3,7,6,5,5] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,5,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,5,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,5,8] (by decide +kernel)))

theorem node_2984 : Excluded a [8,3,7,6] :=
  branch_excluded a [8,3,7,6] (by decide)
    (fin9_cases _
      node_2985
      node_2995
      (invalid_excluded a [8,3,7,6,2] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,3] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,4] (by decide +kernel))
      node_2996
      (invalid_excluded a [8,3,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,8] (by decide +kernel)))

theorem node_2968 : Excluded a [8,3,7] :=
  branch_excluded a [8,3,7] (by decide)
    (fin9_cases _
      node_2969
      node_2970
      node_2971
      (invalid_excluded a [8,3,7,3] (by decide +kernel))
      (invalid_excluded a [8,3,7,4] (by decide +kernel))
      node_2972
      node_2984
      (invalid_excluded a [8,3,7,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,8] (by decide +kernel)))

theorem node_2905 : Excluded a [8,3] :=
  branch_excluded a [8,3] (by decide)
    (fin9_cases _
      node_2906
      node_2907
      (invalid_excluded a [8,3,2] (by decide +kernel))
      (invalid_excluded a [8,3,3] (by decide +kernel))
      node_2908
      node_2909
      node_2941
      node_2968
      (invalid_excluded a [8,3,8] (by decide +kernel)))

theorem node_3009 : Excluded a [8,4,0,1] :=
  source_excluded a [8,4,0,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_3010 : Excluded a [8,4,0,2] :=
  source_excluded a [8,4,0,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_3012 : Excluded a [8,4,0,5,1] :=
  predecessor_excluded a [8,4,0,5,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_3013 : Excluded a [8,4,0,5,3] :=
  source_excluded a [8,4,0,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3014 : Excluded a [8,4,0,5,6] :=
  predecessor_excluded a [8,4,0,5,6] 0 6 3 4 (by decide) (by decide +kernel)

theorem node_3017 : Excluded a [8,4,0,5,7,1,2] :=
  source_excluded a [8,4,0,5,7,1,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_3019 : Excluded a [8,4,0,5,7,1,3,2] :=
  source_excluded a [8,4,0,5,7,1,3,2] 4 0 7 (by decide) (by decide +kernel)

def b_3021 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 4
  | 2 => 0
  | 3 => 5
  | 4 => 7
  | 5 => 1
  | 6 => 3
  | 7 => 6
  | 8 => 2
  | _ => 0

def cert_3021 : LosingRegion (edgeOf a b_3021) 0 :=
  losingMask a b_3021 0 1231559381368375954375680
    (by decide +kernel) (by decide +kernel)

theorem node_3021 : Excluded a [8,4,0,5,7,1,3,6,2] :=
  losing_excluded a [8,4,0,5,7,1,3,6,2] (by decide) b_3021 (by decide +kernel) 3 0 0 cert_3021 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_3021 3 0 ∧ 0 ≠ 3 ∧ maskRegion 1231559381368375954375680 3 0; decide +kernel)

theorem node_3020 : Excluded a [8,4,0,5,7,1,3,6] :=
  branch_excluded a [8,4,0,5,7,1,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,5,7,1,3,6,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,1,3,6,1] (by decide +kernel))
      node_3021
      (invalid_excluded a [8,4,0,5,7,1,3,6,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,1,3,6,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,1,3,6,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,1,3,6,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,1,3,6,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,1,3,6,8] (by decide +kernel)))

theorem node_3018 : Excluded a [8,4,0,5,7,1,3] :=
  branch_excluded a [8,4,0,5,7,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,5,7,1,3,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,1,3,1] (by decide +kernel))
      node_3019
      (invalid_excluded a [8,4,0,5,7,1,3,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,1,3,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,1,3,5] (by decide +kernel))
      node_3020
      (invalid_excluded a [8,4,0,5,7,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,1,3,8] (by decide +kernel)))

theorem node_3016 : Excluded a [8,4,0,5,7,1] :=
  branch_excluded a [8,4,0,5,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,5,7,1,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,1,1] (by decide +kernel))
      node_3017
      node_3018
      (invalid_excluded a [8,4,0,5,7,1,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,1,8] (by decide +kernel)))

theorem node_3022 : Excluded a [8,4,0,5,7,2] :=
  predecessor_excluded a [8,4,0,5,7,2] 0 2 3 5 (by decide) (by decide +kernel)

theorem node_3025 : Excluded a [8,4,0,5,7,3,1,2] :=
  source_excluded a [8,4,0,5,7,3,1,2] 4 0 7 (by decide) (by decide +kernel)

theorem node_3027 : Excluded a [8,4,0,5,7,3,1,6,2] :=
  predecessor_excluded a [8,4,0,5,7,3,1,6,2] 0 3 8 5 (by decide) (by decide +kernel)

theorem node_3026 : Excluded a [8,4,0,5,7,3,1,6] :=
  branch_excluded a [8,4,0,5,7,3,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,5,7,3,1,6,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,3,1,6,1] (by decide +kernel))
      node_3027
      (invalid_excluded a [8,4,0,5,7,3,1,6,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,3,1,6,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,3,1,6,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,3,1,6,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,3,1,6,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,3,1,6,8] (by decide +kernel)))

theorem node_3024 : Excluded a [8,4,0,5,7,3,1] :=
  branch_excluded a [8,4,0,5,7,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,5,7,3,1,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,3,1,1] (by decide +kernel))
      node_3025
      (invalid_excluded a [8,4,0,5,7,3,1,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,3,1,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,3,1,5] (by decide +kernel))
      node_3026
      (invalid_excluded a [8,4,0,5,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,3,1,8] (by decide +kernel)))

theorem node_3028 : Excluded a [8,4,0,5,7,3,2] :=
  source_excluded a [8,4,0,5,7,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_3023 : Excluded a [8,4,0,5,7,3] :=
  branch_excluded a [8,4,0,5,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,5,7,3,0] (by decide +kernel))
      node_3024
      node_3028
      (invalid_excluded a [8,4,0,5,7,3,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,3,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,3,8] (by decide +kernel)))

theorem node_3015 : Excluded a [8,4,0,5,7] :=
  branch_excluded a [8,4,0,5,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,5,7,0] (by decide +kernel))
      node_3016
      node_3022
      node_3023
      (invalid_excluded a [8,4,0,5,7,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,7,8] (by decide +kernel)))

theorem node_3011 : Excluded a [8,4,0,5] :=
  branch_excluded a [8,4,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,5,0] (by decide +kernel))
      node_3012
      (invalid_excluded a [8,4,0,5,2] (by decide +kernel))
      node_3013
      (invalid_excluded a [8,4,0,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,5,5] (by decide +kernel))
      node_3014
      node_3015
      (invalid_excluded a [8,4,0,5,8] (by decide +kernel)))

theorem node_3030 : Excluded a [8,4,0,6,1] :=
  predecessor_excluded a [8,4,0,6,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_3031 : Excluded a [8,4,0,6,3] :=
  source_excluded a [8,4,0,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3034 : Excluded a [8,4,0,6,5,1,2] :=
  predecessor_excluded a [8,4,0,6,5,1,2] 0 2 3 6 (by decide) (by decide +kernel)

def b_3037 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 4
  | 2 => 0
  | 3 => 6
  | 4 => 5
  | 5 => 1
  | 6 => 3
  | 7 => 2
  | 8 => 7
  | _ => 0

def cert_3037 : LosingRegion (edgeOf a b_3037) 0 :=
  losingMask a b_3037 0 1314191553414552028709888
    (by decide +kernel) (by decide +kernel)

theorem node_3037 : Excluded a [8,4,0,6,5,1,3,2,7] :=
  losing_excluded a [8,4,0,6,5,1,3,2,7] (by decide) b_3037 (by decide +kernel) 3 0 1 cert_3037 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_3037 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1314191553414552028709888 3 1; decide +kernel)

theorem node_3036 : Excluded a [8,4,0,6,5,1,3,2] :=
  branch_excluded a [8,4,0,6,5,1,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,6,5,1,3,2,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,3,2,1] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,3,2,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,3,2,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,3,2,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,3,2,6] (by decide +kernel))
      node_3037
      (invalid_excluded a [8,4,0,6,5,1,3,2,8] (by decide +kernel)))

theorem node_3035 : Excluded a [8,4,0,6,5,1,3] :=
  branch_excluded a [8,4,0,6,5,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,6,5,1,3,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,3,1] (by decide +kernel))
      node_3036
      (invalid_excluded a [8,4,0,6,5,1,3,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,3,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,3,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,3,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,3,8] (by decide +kernel)))

theorem node_3033 : Excluded a [8,4,0,6,5,1] :=
  branch_excluded a [8,4,0,6,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,6,5,1,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,1] (by decide +kernel))
      node_3034
      node_3035
      (invalid_excluded a [8,4,0,6,5,1,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,1,8] (by decide +kernel)))

theorem node_3038 : Excluded a [8,4,0,6,5,2] :=
  source_excluded a [8,4,0,6,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_3039 : Excluded a [8,4,0,6,5,3] :=
  source_excluded a [8,4,0,6,5,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_3040 : Excluded a [8,4,0,6,5,7] :=
  source_excluded a [8,4,0,6,5,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_3032 : Excluded a [8,4,0,6,5] :=
  branch_excluded a [8,4,0,6,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,6,5,0] (by decide +kernel))
      node_3033
      node_3038
      node_3039
      (invalid_excluded a [8,4,0,6,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5,6] (by decide +kernel))
      node_3040
      (invalid_excluded a [8,4,0,6,5,8] (by decide +kernel)))

theorem node_3041 : Excluded a [8,4,0,6,7] :=
  predecessor_excluded a [8,4,0,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_3029 : Excluded a [8,4,0,6] :=
  branch_excluded a [8,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,6,0] (by decide +kernel))
      node_3030
      (invalid_excluded a [8,4,0,6,2] (by decide +kernel))
      node_3031
      (invalid_excluded a [8,4,0,6,4] (by decide +kernel))
      node_3032
      (invalid_excluded a [8,4,0,6,6] (by decide +kernel))
      node_3041
      (invalid_excluded a [8,4,0,6,8] (by decide +kernel)))

theorem node_3043 : Excluded a [8,4,0,7,1] :=
  predecessor_excluded a [8,4,0,7,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_3044 : Excluded a [8,4,0,7,3] :=
  source_excluded a [8,4,0,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3048 : Excluded a [8,4,0,7,5,1,2,3] :=
  predecessor_excluded a [8,4,0,7,5,1,2,3] 0 3 6 7 (by decide) (by decide +kernel)

def b_3050 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 4
  | 2 => 0
  | 3 => 7
  | 4 => 5
  | 5 => 1
  | 6 => 2
  | 7 => 6
  | 8 => 3
  | _ => 0

def cert_3050 : LosingRegion (edgeOf a b_3050) 0 :=
  losingMask a b_3050 0 1451520465334829937853440
    (by decide +kernel) (by decide +kernel)

theorem node_3050 : Excluded a [8,4,0,7,5,1,2,6,3] :=
  losing_excluded a [8,4,0,7,5,1,2,6,3] (by decide) b_3050 (by decide +kernel) 3 0 1 cert_3050 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_3050 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1451520465334829937853440 3 1; decide +kernel)

theorem node_3049 : Excluded a [8,4,0,7,5,1,2,6] :=
  branch_excluded a [8,4,0,7,5,1,2,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,5,1,2,6,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,1,2,6,1] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,1,2,6,2] (by decide +kernel))
      node_3050
      (invalid_excluded a [8,4,0,7,5,1,2,6,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,1,2,6,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,1,2,6,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,1,2,6,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,1,2,6,8] (by decide +kernel)))

theorem node_3047 : Excluded a [8,4,0,7,5,1,2] :=
  branch_excluded a [8,4,0,7,5,1,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,5,1,2,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,1,2,1] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,1,2,2] (by decide +kernel))
      node_3048
      (invalid_excluded a [8,4,0,7,5,1,2,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,1,2,5] (by decide +kernel))
      node_3049
      (invalid_excluded a [8,4,0,7,5,1,2,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,1,2,8] (by decide +kernel)))

theorem node_3051 : Excluded a [8,4,0,7,5,1,3] :=
  source_excluded a [8,4,0,7,5,1,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_3046 : Excluded a [8,4,0,7,5,1] :=
  branch_excluded a [8,4,0,7,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,5,1,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,1,1] (by decide +kernel))
      node_3047
      node_3051
      (invalid_excluded a [8,4,0,7,5,1,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,1,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,1,8] (by decide +kernel)))

theorem node_3052 : Excluded a [8,4,0,7,5,2] :=
  source_excluded a [8,4,0,7,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_3053 : Excluded a [8,4,0,7,5,3] :=
  predecessor_excluded a [8,4,0,7,5,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_3045 : Excluded a [8,4,0,7,5] :=
  branch_excluded a [8,4,0,7,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,5,0] (by decide +kernel))
      node_3046
      node_3052
      node_3053
      (invalid_excluded a [8,4,0,7,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5,8] (by decide +kernel)))

theorem node_3056 : Excluded a [8,4,0,7,6,1,2] :=
  source_excluded a [8,4,0,7,6,1,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_3057 : Excluded a [8,4,0,7,6,1,3] :=
  source_excluded a [8,4,0,7,6,1,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_3059 : Excluded a [8,4,0,7,6,1,5,2] :=
  predecessor_excluded a [8,4,0,7,6,1,5,2] 0 2 3 7 (by decide) (by decide +kernel)

def b_3061 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 4
  | 2 => 0
  | 3 => 7
  | 4 => 6
  | 5 => 1
  | 6 => 5
  | 7 => 3
  | 8 => 2
  | _ => 0

def cert_3061 : LosingRegion (edgeOf a b_3061) 0 :=
  losingMask a b_3061 0 1231556643179821840466944
    (by decide +kernel) (by decide +kernel)

theorem node_3061 : Excluded a [8,4,0,7,6,1,5,3,2] :=
  losing_excluded a [8,4,0,7,6,1,5,3,2] (by decide) b_3061 (by decide +kernel) 3 0 0 cert_3061 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_3061 3 0 ∧ 0 ≠ 3 ∧ maskRegion 1231556643179821840466944 3 0; decide +kernel)

theorem node_3060 : Excluded a [8,4,0,7,6,1,5,3] :=
  branch_excluded a [8,4,0,7,6,1,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,6,1,5,3,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,1,5,3,1] (by decide +kernel))
      node_3061
      (invalid_excluded a [8,4,0,7,6,1,5,3,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,1,5,3,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,1,5,3,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,1,5,3,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,1,5,3,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,1,5,3,8] (by decide +kernel)))

theorem node_3058 : Excluded a [8,4,0,7,6,1,5] :=
  branch_excluded a [8,4,0,7,6,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,6,1,5,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,1,5,1] (by decide +kernel))
      node_3059
      node_3060
      (invalid_excluded a [8,4,0,7,6,1,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,1,5,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,1,5,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,1,5,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,1,5,8] (by decide +kernel)))

theorem node_3055 : Excluded a [8,4,0,7,6,1] :=
  branch_excluded a [8,4,0,7,6,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,6,1,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,1,1] (by decide +kernel))
      node_3056
      node_3057
      (invalid_excluded a [8,4,0,7,6,1,4] (by decide +kernel))
      node_3058
      (invalid_excluded a [8,4,0,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,1,8] (by decide +kernel)))

theorem node_3062 : Excluded a [8,4,0,7,6,2] :=
  source_excluded a [8,4,0,7,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_3063 : Excluded a [8,4,0,7,6,3] :=
  predecessor_excluded a [8,4,0,7,6,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_3054 : Excluded a [8,4,0,7,6] :=
  branch_excluded a [8,4,0,7,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,6,0] (by decide +kernel))
      node_3055
      node_3062
      node_3063
      (invalid_excluded a [8,4,0,7,6,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,6,8] (by decide +kernel)))

theorem node_3042 : Excluded a [8,4,0,7] :=
  branch_excluded a [8,4,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,0] (by decide +kernel))
      node_3043
      (invalid_excluded a [8,4,0,7,2] (by decide +kernel))
      node_3044
      (invalid_excluded a [8,4,0,7,4] (by decide +kernel))
      node_3045
      node_3054
      (invalid_excluded a [8,4,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,8] (by decide +kernel)))

theorem node_3008 : Excluded a [8,4,0] :=
  branch_excluded a [8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,0] (by decide +kernel))
      node_3009
      node_3010
      (invalid_excluded a [8,4,0,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,4] (by decide +kernel))
      node_3011
      node_3029
      node_3042
      (invalid_excluded a [8,4,0,8] (by decide +kernel)))

theorem node_3064 : Excluded a [8,4,1] :=
  predecessor_excluded a [8,4,1] 0 4 2 1 (by decide) (by decide +kernel)

theorem node_3066 : Excluded a [8,4,5,0] :=
  source_excluded a [8,4,5,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_3067 : Excluded a [8,4,5,1] :=
  source_excluded a [8,4,5,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_3068 : Excluded a [8,4,5,2] :=
  source_excluded a [8,4,5,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_3069 : Excluded a [8,4,5,6] :=
  predecessor_excluded a [8,4,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_3071 : Excluded a [8,4,5,7,0] :=
  source_excluded a [8,4,5,7,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_3072 : Excluded a [8,4,5,7,1] :=
  predecessor_excluded a [8,4,5,7,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_3073 : Excluded a [8,4,5,7,3] :=
  source_excluded a [8,4,5,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3076 : Excluded a [8,4,5,7,6,0,1] :=
  predecessor_excluded a [8,4,5,7,6,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_3077 : Excluded a [8,4,5,7,6,0,2] :=
  source_excluded a [8,4,5,7,6,0,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_3078 : Excluded a [8,4,5,7,6,0,3] :=
  source_excluded a [8,4,5,7,6,0,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_3075 : Excluded a [8,4,5,7,6,0] :=
  branch_excluded a [8,4,5,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,5,7,6,0,0] (by decide +kernel))
      node_3076
      node_3077
      node_3078
      (invalid_excluded a [8,4,5,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [8,4,5,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,4,5,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [8,4,5,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [8,4,5,7,6,0,8] (by decide +kernel)))

theorem node_3080 : Excluded a [8,4,5,7,6,1,0] :=
  predecessor_excluded a [8,4,5,7,6,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_3081 : Excluded a [8,4,5,7,6,1,2] :=
  source_excluded a [8,4,5,7,6,1,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_3082 : Excluded a [8,4,5,7,6,1,3] :=
  source_excluded a [8,4,5,7,6,1,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_3079 : Excluded a [8,4,5,7,6,1] :=
  branch_excluded a [8,4,5,7,6,1] (by decide)
    (fin9_cases _
      node_3080
      (invalid_excluded a [8,4,5,7,6,1,1] (by decide +kernel))
      node_3081
      node_3082
      (invalid_excluded a [8,4,5,7,6,1,4] (by decide +kernel))
      (invalid_excluded a [8,4,5,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,4,5,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,5,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,5,7,6,1,8] (by decide +kernel)))

theorem node_3083 : Excluded a [8,4,5,7,6,2] :=
  source_excluded a [8,4,5,7,6,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_3084 : Excluded a [8,4,5,7,6,3] :=
  source_excluded a [8,4,5,7,6,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_3074 : Excluded a [8,4,5,7,6] :=
  branch_excluded a [8,4,5,7,6] (by decide)
    (fin9_cases _
      node_3075
      node_3079
      node_3083
      node_3084
      (invalid_excluded a [8,4,5,7,6,4] (by decide +kernel))
      (invalid_excluded a [8,4,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [8,4,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,4,5,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,4,5,7,6,8] (by decide +kernel)))

theorem node_3070 : Excluded a [8,4,5,7] :=
  branch_excluded a [8,4,5,7] (by decide)
    (fin9_cases _
      node_3071
      node_3072
      (invalid_excluded a [8,4,5,7,2] (by decide +kernel))
      node_3073
      (invalid_excluded a [8,4,5,7,4] (by decide +kernel))
      (invalid_excluded a [8,4,5,7,5] (by decide +kernel))
      node_3074
      (invalid_excluded a [8,4,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,5,7,8] (by decide +kernel)))

theorem node_3065 : Excluded a [8,4,5] :=
  branch_excluded a [8,4,5] (by decide)
    (fin9_cases _
      node_3066
      node_3067
      node_3068
      (invalid_excluded a [8,4,5,3] (by decide +kernel))
      (invalid_excluded a [8,4,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,5,5] (by decide +kernel))
      node_3069
      node_3070
      (invalid_excluded a [8,4,5,8] (by decide +kernel)))

theorem node_3086 : Excluded a [8,4,6,0] :=
  source_excluded a [8,4,6,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_3087 : Excluded a [8,4,6,1] :=
  source_excluded a [8,4,6,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_3088 : Excluded a [8,4,6,2] :=
  source_excluded a [8,4,6,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_3090 : Excluded a [8,4,6,5,0] :=
  source_excluded a [8,4,6,5,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_3091 : Excluded a [8,4,6,5,1] :=
  predecessor_excluded a [8,4,6,5,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_3092 : Excluded a [8,4,6,5,3] :=
  source_excluded a [8,4,6,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3095 : Excluded a [8,4,6,5,7,0,1] :=
  predecessor_excluded a [8,4,6,5,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_3096 : Excluded a [8,4,6,5,7,0,2] :=
  source_excluded a [8,4,6,5,7,0,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_3097 : Excluded a [8,4,6,5,7,0,3] :=
  source_excluded a [8,4,6,5,7,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_3094 : Excluded a [8,4,6,5,7,0] :=
  branch_excluded a [8,4,6,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,5,7,0,0] (by decide +kernel))
      node_3095
      node_3096
      node_3097
      (invalid_excluded a [8,4,6,5,7,0,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,5,7,0,8] (by decide +kernel)))

theorem node_3099 : Excluded a [8,4,6,5,7,1,0] :=
  predecessor_excluded a [8,4,6,5,7,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_3100 : Excluded a [8,4,6,5,7,1,2] :=
  source_excluded a [8,4,6,5,7,1,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_3101 : Excluded a [8,4,6,5,7,1,3] :=
  source_excluded a [8,4,6,5,7,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_3098 : Excluded a [8,4,6,5,7,1] :=
  branch_excluded a [8,4,6,5,7,1] (by decide)
    (fin9_cases _
      node_3099
      (invalid_excluded a [8,4,6,5,7,1,1] (by decide +kernel))
      node_3100
      node_3101
      (invalid_excluded a [8,4,6,5,7,1,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,5,7,1,8] (by decide +kernel)))

theorem node_3102 : Excluded a [8,4,6,5,7,2] :=
  source_excluded a [8,4,6,5,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_3103 : Excluded a [8,4,6,5,7,3] :=
  source_excluded a [8,4,6,5,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_3093 : Excluded a [8,4,6,5,7] :=
  branch_excluded a [8,4,6,5,7] (by decide)
    (fin9_cases _
      node_3094
      node_3098
      node_3102
      node_3103
      (invalid_excluded a [8,4,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,5,7,8] (by decide +kernel)))

theorem node_3089 : Excluded a [8,4,6,5] :=
  branch_excluded a [8,4,6,5] (by decide)
    (fin9_cases _
      node_3090
      node_3091
      (invalid_excluded a [8,4,6,5,2] (by decide +kernel))
      node_3092
      (invalid_excluded a [8,4,6,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,5,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,5,6] (by decide +kernel))
      node_3093
      (invalid_excluded a [8,4,6,5,8] (by decide +kernel)))

theorem node_3104 : Excluded a [8,4,6,7] :=
  predecessor_excluded a [8,4,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_3085 : Excluded a [8,4,6] :=
  branch_excluded a [8,4,6] (by decide)
    (fin9_cases _
      node_3086
      node_3087
      node_3088
      (invalid_excluded a [8,4,6,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,4] (by decide +kernel))
      node_3089
      (invalid_excluded a [8,4,6,6] (by decide +kernel))
      node_3104
      (invalid_excluded a [8,4,6,8] (by decide +kernel)))

theorem node_3106 : Excluded a [8,4,7,0] :=
  source_excluded a [8,4,7,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_3107 : Excluded a [8,4,7,1] :=
  source_excluded a [8,4,7,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_3108 : Excluded a [8,4,7,2] :=
  source_excluded a [8,4,7,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_3110 : Excluded a [8,4,7,5,0] :=
  source_excluded a [8,4,7,5,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_3111 : Excluded a [8,4,7,5,1] :=
  predecessor_excluded a [8,4,7,5,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_3112 : Excluded a [8,4,7,5,3] :=
  source_excluded a [8,4,7,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3113 : Excluded a [8,4,7,5,6] :=
  predecessor_excluded a [8,4,7,5,6] 0 7 4 2 (by decide) (by decide +kernel)

theorem node_3109 : Excluded a [8,4,7,5] :=
  branch_excluded a [8,4,7,5] (by decide)
    (fin9_cases _
      node_3110
      node_3111
      (invalid_excluded a [8,4,7,5,2] (by decide +kernel))
      node_3112
      (invalid_excluded a [8,4,7,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,7,5,5] (by decide +kernel))
      node_3113
      (invalid_excluded a [8,4,7,5,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,5,8] (by decide +kernel)))

theorem node_3115 : Excluded a [8,4,7,6,0] :=
  source_excluded a [8,4,7,6,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_3116 : Excluded a [8,4,7,6,1] :=
  predecessor_excluded a [8,4,7,6,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_3117 : Excluded a [8,4,7,6,3] :=
  source_excluded a [8,4,7,6,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3120 : Excluded a [8,4,7,6,5,0,1] :=
  predecessor_excluded a [8,4,7,6,5,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_3121 : Excluded a [8,4,7,6,5,0,2] :=
  source_excluded a [8,4,7,6,5,0,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_3122 : Excluded a [8,4,7,6,5,0,3] :=
  source_excluded a [8,4,7,6,5,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_3119 : Excluded a [8,4,7,6,5,0] :=
  branch_excluded a [8,4,7,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,7,6,5,0,0] (by decide +kernel))
      node_3120
      node_3121
      node_3122
      (invalid_excluded a [8,4,7,6,5,0,4] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,5,0,6] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,5,0,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,5,0,8] (by decide +kernel)))

theorem node_3124 : Excluded a [8,4,7,6,5,1,0] :=
  predecessor_excluded a [8,4,7,6,5,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_3125 : Excluded a [8,4,7,6,5,1,2] :=
  source_excluded a [8,4,7,6,5,1,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_3126 : Excluded a [8,4,7,6,5,1,3] :=
  source_excluded a [8,4,7,6,5,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_3123 : Excluded a [8,4,7,6,5,1] :=
  branch_excluded a [8,4,7,6,5,1] (by decide)
    (fin9_cases _
      node_3124
      (invalid_excluded a [8,4,7,6,5,1,1] (by decide +kernel))
      node_3125
      node_3126
      (invalid_excluded a [8,4,7,6,5,1,4] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,5,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,5,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,5,1,8] (by decide +kernel)))

theorem node_3127 : Excluded a [8,4,7,6,5,2] :=
  source_excluded a [8,4,7,6,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_3128 : Excluded a [8,4,7,6,5,3] :=
  source_excluded a [8,4,7,6,5,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_3118 : Excluded a [8,4,7,6,5] :=
  branch_excluded a [8,4,7,6,5] (by decide)
    (fin9_cases _
      node_3119
      node_3123
      node_3127
      node_3128
      (invalid_excluded a [8,4,7,6,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,5,5] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,5,6] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,5,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,5,8] (by decide +kernel)))

theorem node_3114 : Excluded a [8,4,7,6] :=
  branch_excluded a [8,4,7,6] (by decide)
    (fin9_cases _
      node_3115
      node_3116
      (invalid_excluded a [8,4,7,6,2] (by decide +kernel))
      node_3117
      (invalid_excluded a [8,4,7,6,4] (by decide +kernel))
      node_3118
      (invalid_excluded a [8,4,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,8] (by decide +kernel)))

theorem node_3105 : Excluded a [8,4,7] :=
  branch_excluded a [8,4,7] (by decide)
    (fin9_cases _
      node_3106
      node_3107
      node_3108
      (invalid_excluded a [8,4,7,3] (by decide +kernel))
      (invalid_excluded a [8,4,7,4] (by decide +kernel))
      node_3109
      node_3114
      (invalid_excluded a [8,4,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,8] (by decide +kernel)))

theorem node_3007 : Excluded a [8,4] :=
  branch_excluded a [8,4] (by decide)
    (fin9_cases _
      node_3008
      node_3064
      (invalid_excluded a [8,4,2] (by decide +kernel))
      (invalid_excluded a [8,4,3] (by decide +kernel))
      (invalid_excluded a [8,4,4] (by decide +kernel))
      node_3065
      node_3085
      node_3105
      (invalid_excluded a [8,4,8] (by decide +kernel)))

theorem node_3129 : Excluded a [8,5] :=
  predecessor_excluded a [8,5] 2 5 0 1 (by decide) (by decide +kernel)

theorem node_3132 : Excluded a [8,6,0,1] :=
  predecessor_excluded a [8,6,0,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_3133 : Excluded a [8,6,0,2] :=
  source_excluded a [8,6,0,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_3135 : Excluded a [8,6,0,5,1] :=
  predecessor_excluded a [8,6,0,5,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_3136 : Excluded a [8,6,0,5,3] :=
  source_excluded a [8,6,0,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3138 : Excluded a [8,6,0,5,7,1] :=
  source_excluded a [8,6,0,5,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_3139 : Excluded a [8,6,0,5,7,2] :=
  predecessor_excluded a [8,6,0,5,7,2] 0 2 3 5 (by decide) (by decide +kernel)

theorem node_3141 : Excluded a [8,6,0,5,7,3,1] :=
  predecessor_excluded a [8,6,0,5,7,3,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_3142 : Excluded a [8,6,0,5,7,3,2] :=
  source_excluded a [8,6,0,5,7,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_3143 : Excluded a [8,6,0,5,7,3,4] :=
  source_excluded a [8,6,0,5,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_3140 : Excluded a [8,6,0,5,7,3] :=
  branch_excluded a [8,6,0,5,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,5,7,3,0] (by decide +kernel))
      node_3141
      node_3142
      (invalid_excluded a [8,6,0,5,7,3,3] (by decide +kernel))
      node_3143
      (invalid_excluded a [8,6,0,5,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,0,5,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,5,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,5,7,3,8] (by decide +kernel)))

theorem node_3144 : Excluded a [8,6,0,5,7,4] :=
  source_excluded a [8,6,0,5,7,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_3137 : Excluded a [8,6,0,5,7] :=
  branch_excluded a [8,6,0,5,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,5,7,0] (by decide +kernel))
      node_3138
      node_3139
      node_3140
      node_3144
      (invalid_excluded a [8,6,0,5,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,0,5,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,5,7,8] (by decide +kernel)))

theorem node_3134 : Excluded a [8,6,0,5] :=
  branch_excluded a [8,6,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,5,0] (by decide +kernel))
      node_3135
      (invalid_excluded a [8,6,0,5,2] (by decide +kernel))
      node_3136
      (invalid_excluded a [8,6,0,5,4] (by decide +kernel))
      (invalid_excluded a [8,6,0,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,0,5,6] (by decide +kernel))
      node_3137
      (invalid_excluded a [8,6,0,5,8] (by decide +kernel)))

theorem node_3146 : Excluded a [8,6,0,7,1] :=
  predecessor_excluded a [8,6,0,7,1] 3 0 4 2 (by decide) (by decide +kernel)

theorem node_3147 : Excluded a [8,6,0,7,3] :=
  source_excluded a [8,6,0,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3149 : Excluded a [8,6,0,7,5,1] :=
  source_excluded a [8,6,0,7,5,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_3150 : Excluded a [8,6,0,7,5,2] :=
  source_excluded a [8,6,0,7,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_3151 : Excluded a [8,6,0,7,5,3] :=
  predecessor_excluded a [8,6,0,7,5,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_3153 : Excluded a [8,6,0,7,5,4,1] :=
  predecessor_excluded a [8,6,0,7,5,4,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_3154 : Excluded a [8,6,0,7,5,4,2] :=
  predecessor_excluded a [8,6,0,7,5,4,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_3155 : Excluded a [8,6,0,7,5,4,3] :=
  source_excluded a [8,6,0,7,5,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_3152 : Excluded a [8,6,0,7,5,4] :=
  branch_excluded a [8,6,0,7,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,7,5,4,0] (by decide +kernel))
      node_3153
      node_3154
      node_3155
      (invalid_excluded a [8,6,0,7,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,5,4,5] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,5,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,5,4,8] (by decide +kernel)))

theorem node_3148 : Excluded a [8,6,0,7,5] :=
  branch_excluded a [8,6,0,7,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,7,5,0] (by decide +kernel))
      node_3149
      node_3150
      node_3151
      node_3152
      (invalid_excluded a [8,6,0,7,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,5,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,5,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,5,8] (by decide +kernel)))

theorem node_3145 : Excluded a [8,6,0,7] :=
  branch_excluded a [8,6,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,7,0] (by decide +kernel))
      node_3146
      (invalid_excluded a [8,6,0,7,2] (by decide +kernel))
      node_3147
      (invalid_excluded a [8,6,0,7,4] (by decide +kernel))
      node_3148
      (invalid_excluded a [8,6,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,8] (by decide +kernel)))

theorem node_3131 : Excluded a [8,6,0] :=
  branch_excluded a [8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,0] (by decide +kernel))
      node_3132
      node_3133
      (invalid_excluded a [8,6,0,3] (by decide +kernel))
      (invalid_excluded a [8,6,0,4] (by decide +kernel))
      node_3134
      (invalid_excluded a [8,6,0,6] (by decide +kernel))
      node_3145
      (invalid_excluded a [8,6,0,8] (by decide +kernel)))

theorem node_3157 : Excluded a [8,6,1,0] :=
  predecessor_excluded a [8,6,1,0] 4 0 2 3 (by decide) (by decide +kernel)

theorem node_3158 : Excluded a [8,6,1,2] :=
  source_excluded a [8,6,1,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_3160 : Excluded a [8,6,1,5,0] :=
  predecessor_excluded a [8,6,1,5,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_3161 : Excluded a [8,6,1,5,3] :=
  source_excluded a [8,6,1,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3163 : Excluded a [8,6,1,5,7,0] :=
  source_excluded a [8,6,1,5,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3164 : Excluded a [8,6,1,5,7,2] :=
  predecessor_excluded a [8,6,1,5,7,2] 0 2 3 5 (by decide) (by decide +kernel)

theorem node_3166 : Excluded a [8,6,1,5,7,3,0] :=
  source_excluded a [8,6,1,5,7,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_3167 : Excluded a [8,6,1,5,7,3,2] :=
  source_excluded a [8,6,1,5,7,3,2] 4 0 6 (by decide) (by decide +kernel)

theorem node_3168 : Excluded a [8,6,1,5,7,3,4] :=
  source_excluded a [8,6,1,5,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_3165 : Excluded a [8,6,1,5,7,3] :=
  branch_excluded a [8,6,1,5,7,3] (by decide)
    (fin9_cases _
      node_3166
      (invalid_excluded a [8,6,1,5,7,3,1] (by decide +kernel))
      node_3167
      (invalid_excluded a [8,6,1,5,7,3,3] (by decide +kernel))
      node_3168
      (invalid_excluded a [8,6,1,5,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,5,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,5,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,5,7,3,8] (by decide +kernel)))

theorem node_3169 : Excluded a [8,6,1,5,7,4] :=
  source_excluded a [8,6,1,5,7,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_3162 : Excluded a [8,6,1,5,7] :=
  branch_excluded a [8,6,1,5,7] (by decide)
    (fin9_cases _
      node_3163
      (invalid_excluded a [8,6,1,5,7,1] (by decide +kernel))
      node_3164
      node_3165
      node_3169
      (invalid_excluded a [8,6,1,5,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,5,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,5,7,8] (by decide +kernel)))

theorem node_3159 : Excluded a [8,6,1,5] :=
  branch_excluded a [8,6,1,5] (by decide)
    (fin9_cases _
      node_3160
      (invalid_excluded a [8,6,1,5,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,5,2] (by decide +kernel))
      node_3161
      (invalid_excluded a [8,6,1,5,4] (by decide +kernel))
      (invalid_excluded a [8,6,1,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,5,6] (by decide +kernel))
      node_3162
      (invalid_excluded a [8,6,1,5,8] (by decide +kernel)))

theorem node_3171 : Excluded a [8,6,1,7,0] :=
  predecessor_excluded a [8,6,1,7,0] 3 1 4 2 (by decide) (by decide +kernel)

theorem node_3172 : Excluded a [8,6,1,7,3] :=
  source_excluded a [8,6,1,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3174 : Excluded a [8,6,1,7,5,0] :=
  source_excluded a [8,6,1,7,5,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3175 : Excluded a [8,6,1,7,5,2] :=
  source_excluded a [8,6,1,7,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_3176 : Excluded a [8,6,1,7,5,3] :=
  predecessor_excluded a [8,6,1,7,5,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_3178 : Excluded a [8,6,1,7,5,4,0] :=
  source_excluded a [8,6,1,7,5,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_3179 : Excluded a [8,6,1,7,5,4,2] :=
  predecessor_excluded a [8,6,1,7,5,4,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_3180 : Excluded a [8,6,1,7,5,4,3] :=
  source_excluded a [8,6,1,7,5,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_3177 : Excluded a [8,6,1,7,5,4] :=
  branch_excluded a [8,6,1,7,5,4] (by decide)
    (fin9_cases _
      node_3178
      (invalid_excluded a [8,6,1,7,5,4,1] (by decide +kernel))
      node_3179
      node_3180
      (invalid_excluded a [8,6,1,7,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,5,4,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,5,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,5,4,8] (by decide +kernel)))

theorem node_3173 : Excluded a [8,6,1,7,5] :=
  branch_excluded a [8,6,1,7,5] (by decide)
    (fin9_cases _
      node_3174
      (invalid_excluded a [8,6,1,7,5,1] (by decide +kernel))
      node_3175
      node_3176
      node_3177
      (invalid_excluded a [8,6,1,7,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,5,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,5,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,5,8] (by decide +kernel)))

theorem node_3170 : Excluded a [8,6,1,7] :=
  branch_excluded a [8,6,1,7] (by decide)
    (fin9_cases _
      node_3171
      (invalid_excluded a [8,6,1,7,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2] (by decide +kernel))
      node_3172
      (invalid_excluded a [8,6,1,7,4] (by decide +kernel))
      node_3173
      (invalid_excluded a [8,6,1,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,8] (by decide +kernel)))

theorem node_3156 : Excluded a [8,6,1] :=
  branch_excluded a [8,6,1] (by decide)
    (fin9_cases _
      node_3157
      (invalid_excluded a [8,6,1,1] (by decide +kernel))
      node_3158
      (invalid_excluded a [8,6,1,3] (by decide +kernel))
      (invalid_excluded a [8,6,1,4] (by decide +kernel))
      node_3159
      (invalid_excluded a [8,6,1,6] (by decide +kernel))
      node_3170
      (invalid_excluded a [8,6,1,8] (by decide +kernel)))

theorem node_3181 : Excluded a [8,6,4] :=
  source_excluded a [8,6,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_3184 : Excluded a [8,6,5,0,1] :=
  predecessor_excluded a [8,6,5,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_3185 : Excluded a [8,6,5,0,3] :=
  source_excluded a [8,6,5,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3187 : Excluded a [8,6,5,0,7,1] :=
  source_excluded a [8,6,5,0,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_3189 : Excluded a [8,6,5,0,7,2,1] :=
  predecessor_excluded a [8,6,5,0,7,2,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_3190 : Excluded a [8,6,5,0,7,2,3] :=
  predecessor_excluded a [8,6,5,0,7,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_3191 : Excluded a [8,6,5,0,7,2,4] :=
  source_excluded a [8,6,5,0,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_3188 : Excluded a [8,6,5,0,7,2] :=
  branch_excluded a [8,6,5,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,0,7,2,0] (by decide +kernel))
      node_3189
      (invalid_excluded a [8,6,5,0,7,2,2] (by decide +kernel))
      node_3190
      node_3191
      (invalid_excluded a [8,6,5,0,7,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,2,8] (by decide +kernel)))

theorem node_3192 : Excluded a [8,6,5,0,7,3] :=
  source_excluded a [8,6,5,0,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_3193 : Excluded a [8,6,5,0,7,4] :=
  predecessor_excluded a [8,6,5,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_3186 : Excluded a [8,6,5,0,7] :=
  branch_excluded a [8,6,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,0,7,0] (by decide +kernel))
      node_3187
      node_3188
      node_3192
      node_3193
      (invalid_excluded a [8,6,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,8] (by decide +kernel)))

theorem node_3183 : Excluded a [8,6,5,0] :=
  branch_excluded a [8,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,0,0] (by decide +kernel))
      node_3184
      (invalid_excluded a [8,6,5,0,2] (by decide +kernel))
      node_3185
      (invalid_excluded a [8,6,5,0,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,6] (by decide +kernel))
      node_3186
      (invalid_excluded a [8,6,5,0,8] (by decide +kernel)))

theorem node_3195 : Excluded a [8,6,5,1,0] :=
  predecessor_excluded a [8,6,5,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_3196 : Excluded a [8,6,5,1,3] :=
  source_excluded a [8,6,5,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3198 : Excluded a [8,6,5,1,7,0] :=
  source_excluded a [8,6,5,1,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3200 : Excluded a [8,6,5,1,7,2,0] :=
  source_excluded a [8,6,5,1,7,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_3201 : Excluded a [8,6,5,1,7,2,3] :=
  predecessor_excluded a [8,6,5,1,7,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_3202 : Excluded a [8,6,5,1,7,2,4] :=
  source_excluded a [8,6,5,1,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_3199 : Excluded a [8,6,5,1,7,2] :=
  branch_excluded a [8,6,5,1,7,2] (by decide)
    (fin9_cases _
      node_3200
      (invalid_excluded a [8,6,5,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,2,2] (by decide +kernel))
      node_3201
      node_3202
      (invalid_excluded a [8,6,5,1,7,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,2,8] (by decide +kernel)))

theorem node_3203 : Excluded a [8,6,5,1,7,3] :=
  source_excluded a [8,6,5,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_3204 : Excluded a [8,6,5,1,7,4] :=
  predecessor_excluded a [8,6,5,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_3197 : Excluded a [8,6,5,1,7] :=
  branch_excluded a [8,6,5,1,7] (by decide)
    (fin9_cases _
      node_3198
      (invalid_excluded a [8,6,5,1,7,1] (by decide +kernel))
      node_3199
      node_3203
      node_3204
      (invalid_excluded a [8,6,5,1,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,8] (by decide +kernel)))

theorem node_3194 : Excluded a [8,6,5,1] :=
  branch_excluded a [8,6,5,1] (by decide)
    (fin9_cases _
      node_3195
      (invalid_excluded a [8,6,5,1,1] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,2] (by decide +kernel))
      node_3196
      (invalid_excluded a [8,6,5,1,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,6] (by decide +kernel))
      node_3197
      (invalid_excluded a [8,6,5,1,8] (by decide +kernel)))

theorem node_3205 : Excluded a [8,6,5,2] :=
  source_excluded a [8,6,5,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_3208 : Excluded a [8,6,5,7,0,1] :=
  source_excluded a [8,6,5,7,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_3210 : Excluded a [8,6,5,7,0,2,1] :=
  predecessor_excluded a [8,6,5,7,0,2,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_3211 : Excluded a [8,6,5,7,0,2,3] :=
  source_excluded a [8,6,5,7,0,2,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_3212 : Excluded a [8,6,5,7,0,2,4] :=
  source_excluded a [8,6,5,7,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_3209 : Excluded a [8,6,5,7,0,2] :=
  branch_excluded a [8,6,5,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,7,0,2,0] (by decide +kernel))
      node_3210
      (invalid_excluded a [8,6,5,7,0,2,2] (by decide +kernel))
      node_3211
      node_3212
      (invalid_excluded a [8,6,5,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,0,2,8] (by decide +kernel)))

theorem node_3213 : Excluded a [8,6,5,7,0,3] :=
  source_excluded a [8,6,5,7,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_3214 : Excluded a [8,6,5,7,0,4] :=
  predecessor_excluded a [8,6,5,7,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_3207 : Excluded a [8,6,5,7,0] :=
  branch_excluded a [8,6,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,7,0,0] (by decide +kernel))
      node_3208
      node_3209
      node_3213
      node_3214
      (invalid_excluded a [8,6,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,0,8] (by decide +kernel)))

theorem node_3216 : Excluded a [8,6,5,7,1,0] :=
  source_excluded a [8,6,5,7,1,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3218 : Excluded a [8,6,5,7,1,2,0] :=
  source_excluded a [8,6,5,7,1,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_3219 : Excluded a [8,6,5,7,1,2,3] :=
  source_excluded a [8,6,5,7,1,2,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_3220 : Excluded a [8,6,5,7,1,2,4] :=
  source_excluded a [8,6,5,7,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_3217 : Excluded a [8,6,5,7,1,2] :=
  branch_excluded a [8,6,5,7,1,2] (by decide)
    (fin9_cases _
      node_3218
      (invalid_excluded a [8,6,5,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,1,2,2] (by decide +kernel))
      node_3219
      node_3220
      (invalid_excluded a [8,6,5,7,1,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,1,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,1,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,1,2,8] (by decide +kernel)))

theorem node_3221 : Excluded a [8,6,5,7,1,3] :=
  source_excluded a [8,6,5,7,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_3222 : Excluded a [8,6,5,7,1,4] :=
  predecessor_excluded a [8,6,5,7,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_3215 : Excluded a [8,6,5,7,1] :=
  branch_excluded a [8,6,5,7,1] (by decide)
    (fin9_cases _
      node_3216
      (invalid_excluded a [8,6,5,7,1,1] (by decide +kernel))
      node_3217
      node_3221
      node_3222
      (invalid_excluded a [8,6,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,1,8] (by decide +kernel)))

theorem node_3223 : Excluded a [8,6,5,7,3] :=
  source_excluded a [8,6,5,7,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3206 : Excluded a [8,6,5,7] :=
  branch_excluded a [8,6,5,7] (by decide)
    (fin9_cases _
      node_3207
      node_3215
      (invalid_excluded a [8,6,5,7,2] (by decide +kernel))
      node_3223
      (invalid_excluded a [8,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,8] (by decide +kernel)))

theorem node_3182 : Excluded a [8,6,5] :=
  branch_excluded a [8,6,5] (by decide)
    (fin9_cases _
      node_3183
      node_3194
      node_3205
      (invalid_excluded a [8,6,5,3] (by decide +kernel))
      (invalid_excluded a [8,6,5,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,6] (by decide +kernel))
      node_3206
      (invalid_excluded a [8,6,5,8] (by decide +kernel)))

theorem node_3226 : Excluded a [8,6,7,0,1] :=
  predecessor_excluded a [8,6,7,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_3227 : Excluded a [8,6,7,0,3] :=
  source_excluded a [8,6,7,0,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3229 : Excluded a [8,6,7,0,5,1] :=
  source_excluded a [8,6,7,0,5,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_3230 : Excluded a [8,6,7,0,5,2] :=
  source_excluded a [8,6,7,0,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_3231 : Excluded a [8,6,7,0,5,3] :=
  predecessor_excluded a [8,6,7,0,5,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_3233 : Excluded a [8,6,7,0,5,4,1] :=
  predecessor_excluded a [8,6,7,0,5,4,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_3234 : Excluded a [8,6,7,0,5,4,2] :=
  source_excluded a [8,6,7,0,5,4,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_3235 : Excluded a [8,6,7,0,5,4,3] :=
  source_excluded a [8,6,7,0,5,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_3232 : Excluded a [8,6,7,0,5,4] :=
  branch_excluded a [8,6,7,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,7,0,5,4,0] (by decide +kernel))
      node_3233
      node_3234
      node_3235
      (invalid_excluded a [8,6,7,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,5,4,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,5,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,5,4,8] (by decide +kernel)))

theorem node_3228 : Excluded a [8,6,7,0,5] :=
  branch_excluded a [8,6,7,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,7,0,5,0] (by decide +kernel))
      node_3229
      node_3230
      node_3231
      node_3232
      (invalid_excluded a [8,6,7,0,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,5,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,5,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,5,8] (by decide +kernel)))

theorem node_3225 : Excluded a [8,6,7,0] :=
  branch_excluded a [8,6,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,7,0,0] (by decide +kernel))
      node_3226
      (invalid_excluded a [8,6,7,0,2] (by decide +kernel))
      node_3227
      (invalid_excluded a [8,6,7,0,4] (by decide +kernel))
      node_3228
      (invalid_excluded a [8,6,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,8] (by decide +kernel)))

theorem node_3237 : Excluded a [8,6,7,1,0] :=
  predecessor_excluded a [8,6,7,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_3238 : Excluded a [8,6,7,1,3] :=
  source_excluded a [8,6,7,1,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3240 : Excluded a [8,6,7,1,5,0] :=
  source_excluded a [8,6,7,1,5,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3241 : Excluded a [8,6,7,1,5,2] :=
  source_excluded a [8,6,7,1,5,2] 4 0 5 (by decide) (by decide +kernel)

theorem node_3242 : Excluded a [8,6,7,1,5,3] :=
  predecessor_excluded a [8,6,7,1,5,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_3244 : Excluded a [8,6,7,1,5,4,0] :=
  source_excluded a [8,6,7,1,5,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_3245 : Excluded a [8,6,7,1,5,4,2] :=
  source_excluded a [8,6,7,1,5,4,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_3246 : Excluded a [8,6,7,1,5,4,3] :=
  source_excluded a [8,6,7,1,5,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_3243 : Excluded a [8,6,7,1,5,4] :=
  branch_excluded a [8,6,7,1,5,4] (by decide)
    (fin9_cases _
      node_3244
      (invalid_excluded a [8,6,7,1,5,4,1] (by decide +kernel))
      node_3245
      node_3246
      (invalid_excluded a [8,6,7,1,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,5,4,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,5,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,5,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,5,4,8] (by decide +kernel)))

theorem node_3239 : Excluded a [8,6,7,1,5] :=
  branch_excluded a [8,6,7,1,5] (by decide)
    (fin9_cases _
      node_3240
      (invalid_excluded a [8,6,7,1,5,1] (by decide +kernel))
      node_3241
      node_3242
      node_3243
      (invalid_excluded a [8,6,7,1,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,5,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,5,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,5,8] (by decide +kernel)))

theorem node_3236 : Excluded a [8,6,7,1] :=
  branch_excluded a [8,6,7,1] (by decide)
    (fin9_cases _
      node_3237
      (invalid_excluded a [8,6,7,1,1] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,2] (by decide +kernel))
      node_3238
      (invalid_excluded a [8,6,7,1,4] (by decide +kernel))
      node_3239
      (invalid_excluded a [8,6,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,8] (by decide +kernel)))

theorem node_3247 : Excluded a [8,6,7,2] :=
  source_excluded a [8,6,7,2] 3 0 4 (by decide) (by decide +kernel)

theorem node_3250 : Excluded a [8,6,7,5,0,1] :=
  source_excluded a [8,6,7,5,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_3251 : Excluded a [8,6,7,5,0,2] :=
  predecessor_excluded a [8,6,7,5,0,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_3253 : Excluded a [8,6,7,5,0,3,1] :=
  predecessor_excluded a [8,6,7,5,0,3,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_3254 : Excluded a [8,6,7,5,0,3,2] :=
  source_excluded a [8,6,7,5,0,3,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_3255 : Excluded a [8,6,7,5,0,3,4] :=
  predecessor_excluded a [8,6,7,5,0,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_3252 : Excluded a [8,6,7,5,0,3] :=
  branch_excluded a [8,6,7,5,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,7,5,0,3,0] (by decide +kernel))
      node_3253
      node_3254
      (invalid_excluded a [8,6,7,5,0,3,3] (by decide +kernel))
      node_3255
      (invalid_excluded a [8,6,7,5,0,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,5,0,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,5,0,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,5,0,3,8] (by decide +kernel)))

theorem node_3256 : Excluded a [8,6,7,5,0,4] :=
  source_excluded a [8,6,7,5,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_3249 : Excluded a [8,6,7,5,0] :=
  branch_excluded a [8,6,7,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,7,5,0,0] (by decide +kernel))
      node_3250
      node_3251
      node_3252
      node_3256
      (invalid_excluded a [8,6,7,5,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,5,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,5,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,5,0,8] (by decide +kernel)))

theorem node_3258 : Excluded a [8,6,7,5,1,0] :=
  source_excluded a [8,6,7,5,1,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3259 : Excluded a [8,6,7,5,1,2] :=
  predecessor_excluded a [8,6,7,5,1,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_3261 : Excluded a [8,6,7,5,1,3,0] :=
  source_excluded a [8,6,7,5,1,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_3262 : Excluded a [8,6,7,5,1,3,2] :=
  source_excluded a [8,6,7,5,1,3,2] 6 0 2 (by decide) (by decide +kernel)

theorem node_3263 : Excluded a [8,6,7,5,1,3,4] :=
  predecessor_excluded a [8,6,7,5,1,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_3260 : Excluded a [8,6,7,5,1,3] :=
  branch_excluded a [8,6,7,5,1,3] (by decide)
    (fin9_cases _
      node_3261
      (invalid_excluded a [8,6,7,5,1,3,1] (by decide +kernel))
      node_3262
      (invalid_excluded a [8,6,7,5,1,3,3] (by decide +kernel))
      node_3263
      (invalid_excluded a [8,6,7,5,1,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,5,1,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,5,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,5,1,3,8] (by decide +kernel)))

theorem node_3264 : Excluded a [8,6,7,5,1,4] :=
  source_excluded a [8,6,7,5,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_3257 : Excluded a [8,6,7,5,1] :=
  branch_excluded a [8,6,7,5,1] (by decide)
    (fin9_cases _
      node_3258
      (invalid_excluded a [8,6,7,5,1,1] (by decide +kernel))
      node_3259
      node_3260
      node_3264
      (invalid_excluded a [8,6,7,5,1,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,5,1,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,5,1,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,5,1,8] (by decide +kernel)))

theorem node_3265 : Excluded a [8,6,7,5,3] :=
  source_excluded a [8,6,7,5,3] 4 0 2 (by decide) (by decide +kernel)

theorem node_3248 : Excluded a [8,6,7,5] :=
  branch_excluded a [8,6,7,5] (by decide)
    (fin9_cases _
      node_3249
      node_3257
      (invalid_excluded a [8,6,7,5,2] (by decide +kernel))
      node_3265
      (invalid_excluded a [8,6,7,5,4] (by decide +kernel))
      (invalid_excluded a [8,6,7,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,5,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,5,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,5,8] (by decide +kernel)))

theorem node_3224 : Excluded a [8,6,7] :=
  branch_excluded a [8,6,7] (by decide)
    (fin9_cases _
      node_3225
      node_3236
      node_3247
      (invalid_excluded a [8,6,7,3] (by decide +kernel))
      (invalid_excluded a [8,6,7,4] (by decide +kernel))
      node_3248
      (invalid_excluded a [8,6,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,8] (by decide +kernel)))

theorem node_3130 : Excluded a [8,6] :=
  branch_excluded a [8,6] (by decide)
    (fin9_cases _
      node_3131
      node_3156
      (invalid_excluded a [8,6,2] (by decide +kernel))
      (invalid_excluded a [8,6,3] (by decide +kernel))
      node_3181
      node_3182
      (invalid_excluded a [8,6,6] (by decide +kernel))
      node_3224
      (invalid_excluded a [8,6,8] (by decide +kernel)))

theorem node_3266 : Excluded a [8,7] :=
  predecessor_excluded a [8,7] 2 8 1 0 (by decide) (by decide +kernel)

theorem node_2789 : Excluded a [8] :=
  branch_excluded a [8] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,0] (by decide +kernel))
      (invalid_excluded a [8,1] (by decide +kernel))
      node_2790
      node_2905
      node_3007
      node_3129
      node_3130
      node_3266
      (invalid_excluded a [8,8] (by decide +kernel)))

theorem node_1 : Excluded a [] :=
  branch_excluded a [] (by decide)
    (fin9_cases _
      (invalid_excluded a [0] (by decide +kernel))
      (invalid_excluded a [1] (by decide +kernel))
      node_2
      node_463
      node_872
      node_1361
      node_1788
      node_2254
      node_2789)

theorem every_second_factor_blocked (b : Assignment 9) (valid : Valid a b) : Blocked a b :=
  node_1 b valid (by intro i h; simp at h)

theorem primary_loopless : ∀ i : Fin 9, a i ≠ i := by decide +kernel

#print axioms every_second_factor_blocked
end Delivery.FiniteExclusion.Cycle2x3x4
