import FiniteExclusionKernel

set_option maxRecDepth 4096
set_option maxHeartbeats 20000000

namespace Delivery.FiniteExclusion.Cycle2x7
open FiniteGame Extremal

def a (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 2
  | _ => 0

theorem node_3 : Excluded a [2,3] :=
  predecessor_excluded a [2,3] 4 3 0 1 (by decide) (by decide +kernel)

theorem node_5 : Excluded a [2,4,0] :=
  predecessor_excluded a [2,4,0] 3 0 0 2 (by decide) (by decide +kernel)

theorem node_6 : Excluded a [2,4,1] :=
  source_excluded a [2,4,1] 0 3 2 (by decide) (by decide +kernel)

theorem node_8 : Excluded a [2,4,5,0] :=
  source_excluded a [2,4,5,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_9 : Excluded a [2,4,5,1] :=
  source_excluded a [2,4,5,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_10 : Excluded a [2,4,5,6] :=
  predecessor_excluded a [2,4,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_12 : Excluded a [2,4,5,7,0] :=
  source_excluded a [2,4,5,7,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_13 : Excluded a [2,4,5,7,1] :=
  predecessor_excluded a [2,4,5,7,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_14 : Excluded a [2,4,5,7,3] :=
  source_excluded a [2,4,5,7,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_15 : Excluded a [2,4,5,7,6] :=
  source_excluded a [2,4,5,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_16 : Excluded a [2,4,5,7,8] :=
  predecessor_excluded a [2,4,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_11 : Excluded a [2,4,5,7] :=
  branch_excluded a [2,4,5,7] (by decide)
    (fin9_cases _
      node_12
      node_13
      (invalid_excluded a [2,4,5,7,2] (by decide +kernel))
      node_14
      (invalid_excluded a [2,4,5,7,4] (by decide +kernel))
      (invalid_excluded a [2,4,5,7,5] (by decide +kernel))
      node_15
      (invalid_excluded a [2,4,5,7,7] (by decide +kernel))
      node_16)

theorem node_18 : Excluded a [2,4,5,8,0] :=
  source_excluded a [2,4,5,8,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_19 : Excluded a [2,4,5,8,1] :=
  predecessor_excluded a [2,4,5,8,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_20 : Excluded a [2,4,5,8,3] :=
  source_excluded a [2,4,5,8,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_21 : Excluded a [2,4,5,8,6] :=
  source_excluded a [2,4,5,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_24 : Excluded a [2,4,5,8,7,0,1] :=
  predecessor_excluded a [2,4,5,8,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_25 : Excluded a [2,4,5,8,7,0,3] :=
  predecessor_excluded a [2,4,5,8,7,0,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_23 : Excluded a [2,4,5,8,7,0] :=
  branch_excluded a [2,4,5,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,4,5,8,7,0,0] (by decide +kernel))
      node_24
      (invalid_excluded a [2,4,5,8,7,0,2] (by decide +kernel))
      node_25
      (invalid_excluded a [2,4,5,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [2,4,5,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [2,4,5,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [2,4,5,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [2,4,5,8,7,0,8] (by decide +kernel)))

theorem node_27 : Excluded a [2,4,5,8,7,1,0] :=
  predecessor_excluded a [2,4,5,8,7,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_28 : Excluded a [2,4,5,8,7,1,3] :=
  predecessor_excluded a [2,4,5,8,7,1,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_26 : Excluded a [2,4,5,8,7,1] :=
  branch_excluded a [2,4,5,8,7,1] (by decide)
    (fin9_cases _
      node_27
      (invalid_excluded a [2,4,5,8,7,1,1] (by decide +kernel))
      (invalid_excluded a [2,4,5,8,7,1,2] (by decide +kernel))
      node_28
      (invalid_excluded a [2,4,5,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [2,4,5,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [2,4,5,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [2,4,5,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [2,4,5,8,7,1,8] (by decide +kernel)))

theorem node_29 : Excluded a [2,4,5,8,7,3] :=
  source_excluded a [2,4,5,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_22 : Excluded a [2,4,5,8,7] :=
  branch_excluded a [2,4,5,8,7] (by decide)
    (fin9_cases _
      node_23
      node_26
      (invalid_excluded a [2,4,5,8,7,2] (by decide +kernel))
      node_29
      (invalid_excluded a [2,4,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [2,4,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [2,4,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [2,4,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [2,4,5,8,7,8] (by decide +kernel)))

theorem node_17 : Excluded a [2,4,5,8] :=
  branch_excluded a [2,4,5,8] (by decide)
    (fin9_cases _
      node_18
      node_19
      (invalid_excluded a [2,4,5,8,2] (by decide +kernel))
      node_20
      (invalid_excluded a [2,4,5,8,4] (by decide +kernel))
      (invalid_excluded a [2,4,5,8,5] (by decide +kernel))
      node_21
      node_22
      (invalid_excluded a [2,4,5,8,8] (by decide +kernel)))

theorem node_7 : Excluded a [2,4,5] :=
  branch_excluded a [2,4,5] (by decide)
    (fin9_cases _
      node_8
      node_9
      (invalid_excluded a [2,4,5,2] (by decide +kernel))
      (invalid_excluded a [2,4,5,3] (by decide +kernel))
      (invalid_excluded a [2,4,5,4] (by decide +kernel))
      (invalid_excluded a [2,4,5,5] (by decide +kernel))
      node_10
      node_11
      node_17)

theorem node_31 : Excluded a [2,4,6,0] :=
  source_excluded a [2,4,6,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_32 : Excluded a [2,4,6,1] :=
  source_excluded a [2,4,6,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_33 : Excluded a [2,4,6,5] :=
  source_excluded a [2,4,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_34 : Excluded a [2,4,6,7] :=
  predecessor_excluded a [2,4,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_36 : Excluded a [2,4,6,8,0] :=
  source_excluded a [2,4,6,8,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_37 : Excluded a [2,4,6,8,1] :=
  predecessor_excluded a [2,4,6,8,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_40 : Excluded a [2,4,6,8,3,0,1] :=
  predecessor_excluded a [2,4,6,8,3,0,1] 2 1 5 6 (by decide) (by decide +kernel)

def b_43 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 4
  | 2 => 6
  | 3 => 8
  | 4 => 3
  | 5 => 0
  | 6 => 5
  | 7 => 1
  | 8 => 7
  | _ => 0

def cert_43 : LosingRegion (edgeOf a b_43) 0 :=
  losingMask a b_43 0 1677650093671422366843904
    (by decide +kernel) (by decide +kernel)

theorem node_43 : Excluded a [2,4,6,8,3,0,5,1,7] :=
  losing_excluded a [2,4,6,8,3,0,5,1,7] (by decide) b_43 (by decide +kernel) 2 0 4 cert_43 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_43 2 0 ∧ 4 ≠ 2 ∧ maskRegion 1677650093671422366843904 2 4; decide +kernel)

theorem node_42 : Excluded a [2,4,6,8,3,0,5,1] :=
  branch_excluded a [2,4,6,8,3,0,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,4,6,8,3,0,5,1,0] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,0,5,1,1] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,0,5,1,2] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,0,5,1,3] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,0,5,1,4] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,0,5,1,5] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,0,5,1,6] (by decide +kernel))
      node_43
      (invalid_excluded a [2,4,6,8,3,0,5,1,8] (by decide +kernel)))

theorem node_41 : Excluded a [2,4,6,8,3,0,5] :=
  branch_excluded a [2,4,6,8,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,4,6,8,3,0,5,0] (by decide +kernel))
      node_42
      (invalid_excluded a [2,4,6,8,3,0,5,2] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,0,5,5] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,0,5,6] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,0,5,8] (by decide +kernel)))

theorem node_39 : Excluded a [2,4,6,8,3,0] :=
  branch_excluded a [2,4,6,8,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,4,6,8,3,0,0] (by decide +kernel))
      node_40
      (invalid_excluded a [2,4,6,8,3,0,2] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,0,3] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,0,4] (by decide +kernel))
      node_41
      (invalid_excluded a [2,4,6,8,3,0,6] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,0,7] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,0,8] (by decide +kernel)))

theorem node_45 : Excluded a [2,4,6,8,3,1,0] :=
  predecessor_excluded a [2,4,6,8,3,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_47 : Excluded a [2,4,6,8,3,1,5,0] :=
  predecessor_excluded a [2,4,6,8,3,1,5,0] 1 2 7 0 (by decide) (by decide +kernel)

theorem node_46 : Excluded a [2,4,6,8,3,1,5] :=
  branch_excluded a [2,4,6,8,3,1,5] (by decide)
    (fin9_cases _
      node_47
      (invalid_excluded a [2,4,6,8,3,1,5,1] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,1,5,2] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,1,5,3] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,1,5,4] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,1,5,5] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,1,5,6] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,1,5,8] (by decide +kernel)))

theorem node_44 : Excluded a [2,4,6,8,3,1] :=
  branch_excluded a [2,4,6,8,3,1] (by decide)
    (fin9_cases _
      node_45
      (invalid_excluded a [2,4,6,8,3,1,1] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,1,2] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,1,3] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,1,4] (by decide +kernel))
      node_46
      (invalid_excluded a [2,4,6,8,3,1,6] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,1,7] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,1,8] (by decide +kernel)))

theorem node_48 : Excluded a [2,4,6,8,3,7] :=
  source_excluded a [2,4,6,8,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_38 : Excluded a [2,4,6,8,3] :=
  branch_excluded a [2,4,6,8,3] (by decide)
    (fin9_cases _
      node_39
      node_44
      (invalid_excluded a [2,4,6,8,3,2] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,3] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,4] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,5] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,3,6] (by decide +kernel))
      node_48
      (invalid_excluded a [2,4,6,8,3,8] (by decide +kernel)))

theorem node_51 : Excluded a [2,4,6,8,7,0,1] :=
  predecessor_excluded a [2,4,6,8,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_52 : Excluded a [2,4,6,8,7,0,3] :=
  source_excluded a [2,4,6,8,7,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_53 : Excluded a [2,4,6,8,7,0,5] :=
  source_excluded a [2,4,6,8,7,0,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_50 : Excluded a [2,4,6,8,7,0] :=
  branch_excluded a [2,4,6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,4,6,8,7,0,0] (by decide +kernel))
      node_51
      (invalid_excluded a [2,4,6,8,7,0,2] (by decide +kernel))
      node_52
      (invalid_excluded a [2,4,6,8,7,0,4] (by decide +kernel))
      node_53
      (invalid_excluded a [2,4,6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,7,0,8] (by decide +kernel)))

theorem node_55 : Excluded a [2,4,6,8,7,1,0] :=
  predecessor_excluded a [2,4,6,8,7,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_56 : Excluded a [2,4,6,8,7,1,3] :=
  source_excluded a [2,4,6,8,7,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_57 : Excluded a [2,4,6,8,7,1,5] :=
  source_excluded a [2,4,6,8,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_54 : Excluded a [2,4,6,8,7,1] :=
  branch_excluded a [2,4,6,8,7,1] (by decide)
    (fin9_cases _
      node_55
      (invalid_excluded a [2,4,6,8,7,1,1] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,7,1,2] (by decide +kernel))
      node_56
      (invalid_excluded a [2,4,6,8,7,1,4] (by decide +kernel))
      node_57
      (invalid_excluded a [2,4,6,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,7,1,8] (by decide +kernel)))

theorem node_58 : Excluded a [2,4,6,8,7,3] :=
  source_excluded a [2,4,6,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_49 : Excluded a [2,4,6,8,7] :=
  branch_excluded a [2,4,6,8,7] (by decide)
    (fin9_cases _
      node_50
      node_54
      (invalid_excluded a [2,4,6,8,7,2] (by decide +kernel))
      node_58
      (invalid_excluded a [2,4,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,7,8] (by decide +kernel)))

theorem node_35 : Excluded a [2,4,6,8] :=
  branch_excluded a [2,4,6,8] (by decide)
    (fin9_cases _
      node_36
      node_37
      (invalid_excluded a [2,4,6,8,2] (by decide +kernel))
      node_38
      (invalid_excluded a [2,4,6,8,4] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,5] (by decide +kernel))
      (invalid_excluded a [2,4,6,8,6] (by decide +kernel))
      node_49
      (invalid_excluded a [2,4,6,8,8] (by decide +kernel)))

theorem node_30 : Excluded a [2,4,6] :=
  branch_excluded a [2,4,6] (by decide)
    (fin9_cases _
      node_31
      node_32
      (invalid_excluded a [2,4,6,2] (by decide +kernel))
      (invalid_excluded a [2,4,6,3] (by decide +kernel))
      (invalid_excluded a [2,4,6,4] (by decide +kernel))
      node_33
      (invalid_excluded a [2,4,6,6] (by decide +kernel))
      node_34
      node_35)

theorem node_60 : Excluded a [2,4,7,0] :=
  source_excluded a [2,4,7,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_61 : Excluded a [2,4,7,1] :=
  source_excluded a [2,4,7,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_62 : Excluded a [2,4,7,5] :=
  source_excluded a [2,4,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_64 : Excluded a [2,4,7,6,0] :=
  source_excluded a [2,4,7,6,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_65 : Excluded a [2,4,7,6,1] :=
  predecessor_excluded a [2,4,7,6,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_66 : Excluded a [2,4,7,6,3] :=
  predecessor_excluded a [2,4,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_69 : Excluded a [2,4,7,6,8,0,1] :=
  predecessor_excluded a [2,4,7,6,8,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_70 : Excluded a [2,4,7,6,8,0,3] :=
  source_excluded a [2,4,7,6,8,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_71 : Excluded a [2,4,7,6,8,0,5] :=
  predecessor_excluded a [2,4,7,6,8,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_68 : Excluded a [2,4,7,6,8,0] :=
  branch_excluded a [2,4,7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,4,7,6,8,0,0] (by decide +kernel))
      node_69
      (invalid_excluded a [2,4,7,6,8,0,2] (by decide +kernel))
      node_70
      (invalid_excluded a [2,4,7,6,8,0,4] (by decide +kernel))
      node_71
      (invalid_excluded a [2,4,7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [2,4,7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [2,4,7,6,8,0,8] (by decide +kernel)))

theorem node_73 : Excluded a [2,4,7,6,8,1,0] :=
  predecessor_excluded a [2,4,7,6,8,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_74 : Excluded a [2,4,7,6,8,1,3] :=
  source_excluded a [2,4,7,6,8,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_75 : Excluded a [2,4,7,6,8,1,5] :=
  predecessor_excluded a [2,4,7,6,8,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_72 : Excluded a [2,4,7,6,8,1] :=
  branch_excluded a [2,4,7,6,8,1] (by decide)
    (fin9_cases _
      node_73
      (invalid_excluded a [2,4,7,6,8,1,1] (by decide +kernel))
      (invalid_excluded a [2,4,7,6,8,1,2] (by decide +kernel))
      node_74
      (invalid_excluded a [2,4,7,6,8,1,4] (by decide +kernel))
      node_75
      (invalid_excluded a [2,4,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [2,4,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [2,4,7,6,8,1,8] (by decide +kernel)))

theorem node_76 : Excluded a [2,4,7,6,8,3] :=
  source_excluded a [2,4,7,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_67 : Excluded a [2,4,7,6,8] :=
  branch_excluded a [2,4,7,6,8] (by decide)
    (fin9_cases _
      node_68
      node_72
      (invalid_excluded a [2,4,7,6,8,2] (by decide +kernel))
      node_76
      (invalid_excluded a [2,4,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [2,4,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [2,4,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [2,4,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [2,4,7,6,8,8] (by decide +kernel)))

theorem node_63 : Excluded a [2,4,7,6] :=
  branch_excluded a [2,4,7,6] (by decide)
    (fin9_cases _
      node_64
      node_65
      (invalid_excluded a [2,4,7,6,2] (by decide +kernel))
      node_66
      (invalid_excluded a [2,4,7,6,4] (by decide +kernel))
      (invalid_excluded a [2,4,7,6,5] (by decide +kernel))
      (invalid_excluded a [2,4,7,6,6] (by decide +kernel))
      (invalid_excluded a [2,4,7,6,7] (by decide +kernel))
      node_67)

theorem node_77 : Excluded a [2,4,7,8] :=
  predecessor_excluded a [2,4,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_59 : Excluded a [2,4,7] :=
  branch_excluded a [2,4,7] (by decide)
    (fin9_cases _
      node_60
      node_61
      (invalid_excluded a [2,4,7,2] (by decide +kernel))
      (invalid_excluded a [2,4,7,3] (by decide +kernel))
      (invalid_excluded a [2,4,7,4] (by decide +kernel))
      node_62
      node_63
      (invalid_excluded a [2,4,7,7] (by decide +kernel))
      node_77)

theorem node_79 : Excluded a [2,4,8,0] :=
  source_excluded a [2,4,8,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_80 : Excluded a [2,4,8,1] :=
  source_excluded a [2,4,8,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_81 : Excluded a [2,4,8,5] :=
  source_excluded a [2,4,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_83 : Excluded a [2,4,8,6,0] :=
  source_excluded a [2,4,8,6,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_84 : Excluded a [2,4,8,6,1] :=
  predecessor_excluded a [2,4,8,6,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_85 : Excluded a [2,4,8,6,3] :=
  predecessor_excluded a [2,4,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_86 : Excluded a [2,4,8,6,7] :=
  predecessor_excluded a [2,4,8,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_82 : Excluded a [2,4,8,6] :=
  branch_excluded a [2,4,8,6] (by decide)
    (fin9_cases _
      node_83
      node_84
      (invalid_excluded a [2,4,8,6,2] (by decide +kernel))
      node_85
      (invalid_excluded a [2,4,8,6,4] (by decide +kernel))
      (invalid_excluded a [2,4,8,6,5] (by decide +kernel))
      (invalid_excluded a [2,4,8,6,6] (by decide +kernel))
      node_86
      (invalid_excluded a [2,4,8,6,8] (by decide +kernel)))

theorem node_88 : Excluded a [2,4,8,7,0] :=
  source_excluded a [2,4,8,7,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_89 : Excluded a [2,4,8,7,1] :=
  predecessor_excluded a [2,4,8,7,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_92 : Excluded a [2,4,8,7,3,0,1] :=
  predecessor_excluded a [2,4,8,7,3,0,1] 2 1 5 6 (by decide) (by decide +kernel)

def b_95 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 4
  | 2 => 8
  | 3 => 7
  | 4 => 3
  | 5 => 0
  | 6 => 5
  | 7 => 1
  | 8 => 6
  | _ => 0

def cert_95 : LosingRegion (edgeOf a b_95) 0 :=
  losingMask a b_95 0 1663454747645943382803456
    (by decide +kernel) (by decide +kernel)

theorem node_95 : Excluded a [2,4,8,7,3,0,5,1,6] :=
  losing_excluded a [2,4,8,7,3,0,5,1,6] (by decide) b_95 (by decide +kernel) 2 0 4 cert_95 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_95 2 0 ∧ 4 ≠ 2 ∧ maskRegion 1663454747645943382803456 2 4; decide +kernel)

theorem node_94 : Excluded a [2,4,8,7,3,0,5,1] :=
  branch_excluded a [2,4,8,7,3,0,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,4,8,7,3,0,5,1,0] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,0,5,1,1] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,0,5,1,2] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,0,5,1,3] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,0,5,1,4] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,0,5,1,5] (by decide +kernel))
      node_95
      (invalid_excluded a [2,4,8,7,3,0,5,1,7] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,0,5,1,8] (by decide +kernel)))

theorem node_96 : Excluded a [2,4,8,7,3,0,5,6] :=
  predecessor_excluded a [2,4,8,7,3,0,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_93 : Excluded a [2,4,8,7,3,0,5] :=
  branch_excluded a [2,4,8,7,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,4,8,7,3,0,5,0] (by decide +kernel))
      node_94
      (invalid_excluded a [2,4,8,7,3,0,5,2] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,0,5,5] (by decide +kernel))
      node_96
      (invalid_excluded a [2,4,8,7,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,0,5,8] (by decide +kernel)))

theorem node_91 : Excluded a [2,4,8,7,3,0] :=
  branch_excluded a [2,4,8,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,4,8,7,3,0,0] (by decide +kernel))
      node_92
      (invalid_excluded a [2,4,8,7,3,0,2] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,0,3] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,0,4] (by decide +kernel))
      node_93
      (invalid_excluded a [2,4,8,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,0,8] (by decide +kernel)))

theorem node_98 : Excluded a [2,4,8,7,3,1,0] :=
  predecessor_excluded a [2,4,8,7,3,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_100 : Excluded a [2,4,8,7,3,1,5,0] :=
  predecessor_excluded a [2,4,8,7,3,1,5,0] 1 2 7 0 (by decide) (by decide +kernel)

theorem node_101 : Excluded a [2,4,8,7,3,1,5,6] :=
  predecessor_excluded a [2,4,8,7,3,1,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_99 : Excluded a [2,4,8,7,3,1,5] :=
  branch_excluded a [2,4,8,7,3,1,5] (by decide)
    (fin9_cases _
      node_100
      (invalid_excluded a [2,4,8,7,3,1,5,1] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,1,5,2] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,1,5,3] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,1,5,4] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,1,5,5] (by decide +kernel))
      node_101
      (invalid_excluded a [2,4,8,7,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,1,5,8] (by decide +kernel)))

theorem node_97 : Excluded a [2,4,8,7,3,1] :=
  branch_excluded a [2,4,8,7,3,1] (by decide)
    (fin9_cases _
      node_98
      (invalid_excluded a [2,4,8,7,3,1,1] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,1,2] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,1,3] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,1,4] (by decide +kernel))
      node_99
      (invalid_excluded a [2,4,8,7,3,1,6] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,1,8] (by decide +kernel)))

theorem node_90 : Excluded a [2,4,8,7,3] :=
  branch_excluded a [2,4,8,7,3] (by decide)
    (fin9_cases _
      node_91
      node_97
      (invalid_excluded a [2,4,8,7,3,2] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,4] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,3,8] (by decide +kernel)))

theorem node_102 : Excluded a [2,4,8,7,6] :=
  source_excluded a [2,4,8,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_87 : Excluded a [2,4,8,7] :=
  branch_excluded a [2,4,8,7] (by decide)
    (fin9_cases _
      node_88
      node_89
      (invalid_excluded a [2,4,8,7,2] (by decide +kernel))
      node_90
      (invalid_excluded a [2,4,8,7,4] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,5] (by decide +kernel))
      node_102
      (invalid_excluded a [2,4,8,7,7] (by decide +kernel))
      (invalid_excluded a [2,4,8,7,8] (by decide +kernel)))

theorem node_78 : Excluded a [2,4,8] :=
  branch_excluded a [2,4,8] (by decide)
    (fin9_cases _
      node_79
      node_80
      (invalid_excluded a [2,4,8,2] (by decide +kernel))
      (invalid_excluded a [2,4,8,3] (by decide +kernel))
      (invalid_excluded a [2,4,8,4] (by decide +kernel))
      node_81
      node_82
      node_87
      (invalid_excluded a [2,4,8,8] (by decide +kernel)))

theorem node_4 : Excluded a [2,4] :=
  branch_excluded a [2,4] (by decide)
    (fin9_cases _
      node_5
      node_6
      (invalid_excluded a [2,4,2] (by decide +kernel))
      (invalid_excluded a [2,4,3] (by decide +kernel))
      (invalid_excluded a [2,4,4] (by decide +kernel))
      node_7
      node_30
      node_59
      node_78)

theorem node_104 : Excluded a [2,5,0] :=
  predecessor_excluded a [2,5,0] 3 0 0 2 (by decide) (by decide +kernel)

theorem node_105 : Excluded a [2,5,1] :=
  source_excluded a [2,5,1] 0 3 2 (by decide) (by decide +kernel)

theorem node_106 : Excluded a [2,5,4] :=
  source_excluded a [2,5,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_109 : Excluded a [2,5,6,0,1] :=
  source_excluded a [2,5,6,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_111 : Excluded a [2,5,6,0,3,1] :=
  predecessor_excluded a [2,5,6,0,3,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_112 : Excluded a [2,5,6,0,3,4] :=
  predecessor_excluded a [2,5,6,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_113 : Excluded a [2,5,6,0,3,7] :=
  source_excluded a [2,5,6,0,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_117 : Excluded a [2,5,6,0,3,8,1,4,7] :=
  predecessor_excluded a [2,5,6,0,3,8,1,4,7] 0 7 5 8 (by decide) (by decide +kernel)

theorem node_116 : Excluded a [2,5,6,0,3,8,1,4] :=
  branch_excluded a [2,5,6,0,3,8,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,6,0,3,8,1,4,0] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,8,1,4,1] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,8,1,4,2] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,8,1,4,3] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,8,1,4,4] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,8,1,4,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,8,1,4,6] (by decide +kernel))
      node_117
      (invalid_excluded a [2,5,6,0,3,8,1,4,8] (by decide +kernel)))

theorem node_115 : Excluded a [2,5,6,0,3,8,1] :=
  branch_excluded a [2,5,6,0,3,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,6,0,3,8,1,0] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,8,1,1] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,8,1,2] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,8,1,3] (by decide +kernel))
      node_116
      (invalid_excluded a [2,5,6,0,3,8,1,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,8,1,6] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,8,1,7] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,8,1,8] (by decide +kernel)))

theorem node_118 : Excluded a [2,5,6,0,3,8,4] :=
  predecessor_excluded a [2,5,6,0,3,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_114 : Excluded a [2,5,6,0,3,8] :=
  branch_excluded a [2,5,6,0,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,6,0,3,8,0] (by decide +kernel))
      node_115
      (invalid_excluded a [2,5,6,0,3,8,2] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,8,3] (by decide +kernel))
      node_118
      (invalid_excluded a [2,5,6,0,3,8,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,8,6] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,8,7] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,8,8] (by decide +kernel)))

theorem node_110 : Excluded a [2,5,6,0,3] :=
  branch_excluded a [2,5,6,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,6,0,3,0] (by decide +kernel))
      node_111
      (invalid_excluded a [2,5,6,0,3,2] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,3] (by decide +kernel))
      node_112
      (invalid_excluded a [2,5,6,0,3,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,3,6] (by decide +kernel))
      node_113
      node_114)

theorem node_120 : Excluded a [2,5,6,0,7,1] :=
  predecessor_excluded a [2,5,6,0,7,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_121 : Excluded a [2,5,6,0,7,3] :=
  source_excluded a [2,5,6,0,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_122 : Excluded a [2,5,6,0,7,4] :=
  predecessor_excluded a [2,5,6,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_123 : Excluded a [2,5,6,0,7,8] :=
  predecessor_excluded a [2,5,6,0,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_119 : Excluded a [2,5,6,0,7] :=
  branch_excluded a [2,5,6,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,6,0,7,0] (by decide +kernel))
      node_120
      (invalid_excluded a [2,5,6,0,7,2] (by decide +kernel))
      node_121
      node_122
      (invalid_excluded a [2,5,6,0,7,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,7,6] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,7,7] (by decide +kernel))
      node_123)

theorem node_125 : Excluded a [2,5,6,0,8,1] :=
  predecessor_excluded a [2,5,6,0,8,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_126 : Excluded a [2,5,6,0,8,3] :=
  source_excluded a [2,5,6,0,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_130 : Excluded a [2,5,6,0,8,4,1,3,7] :=
  predecessor_excluded a [2,5,6,0,8,4,1,3,7] 0 3 8 7 (by decide) (by decide +kernel)

theorem node_129 : Excluded a [2,5,6,0,8,4,1,3] :=
  branch_excluded a [2,5,6,0,8,4,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,6,0,8,4,1,3,0] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,4,1,3,1] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,4,1,3,2] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,4,1,3,3] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,4,1,3,4] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,4,1,3,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,4,1,3,6] (by decide +kernel))
      node_130
      (invalid_excluded a [2,5,6,0,8,4,1,3,8] (by decide +kernel)))

theorem node_128 : Excluded a [2,5,6,0,8,4,1] :=
  branch_excluded a [2,5,6,0,8,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,6,0,8,4,1,0] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,4,1,2] (by decide +kernel))
      node_129
      (invalid_excluded a [2,5,6,0,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,4,1,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,4,1,6] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,4,1,8] (by decide +kernel)))

theorem node_131 : Excluded a [2,5,6,0,8,4,3] :=
  source_excluded a [2,5,6,0,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_127 : Excluded a [2,5,6,0,8,4] :=
  branch_excluded a [2,5,6,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,6,0,8,4,0] (by decide +kernel))
      node_128
      (invalid_excluded a [2,5,6,0,8,4,2] (by decide +kernel))
      node_131
      (invalid_excluded a [2,5,6,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,4,8] (by decide +kernel)))

theorem node_132 : Excluded a [2,5,6,0,8,7] :=
  source_excluded a [2,5,6,0,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_124 : Excluded a [2,5,6,0,8] :=
  branch_excluded a [2,5,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,6,0,8,0] (by decide +kernel))
      node_125
      (invalid_excluded a [2,5,6,0,8,2] (by decide +kernel))
      node_126
      node_127
      (invalid_excluded a [2,5,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,8,6] (by decide +kernel))
      node_132
      (invalid_excluded a [2,5,6,0,8,8] (by decide +kernel)))

theorem node_108 : Excluded a [2,5,6,0] :=
  branch_excluded a [2,5,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,6,0,0] (by decide +kernel))
      node_109
      (invalid_excluded a [2,5,6,0,2] (by decide +kernel))
      node_110
      (invalid_excluded a [2,5,6,0,4] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,0,6] (by decide +kernel))
      node_119
      node_124)

theorem node_133 : Excluded a [2,5,6,1] :=
  predecessor_excluded a [2,5,6,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_134 : Excluded a [2,5,6,7] :=
  predecessor_excluded a [2,5,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_136 : Excluded a [2,5,6,8,0] :=
  source_excluded a [2,5,6,8,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_137 : Excluded a [2,5,6,8,1] :=
  source_excluded a [2,5,6,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_139 : Excluded a [2,5,6,8,3,0] :=
  source_excluded a [2,5,6,8,3,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_140 : Excluded a [2,5,6,8,3,1] :=
  predecessor_excluded a [2,5,6,8,3,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_141 : Excluded a [2,5,6,8,3,4] :=
  predecessor_excluded a [2,5,6,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_142 : Excluded a [2,5,6,8,3,7] :=
  source_excluded a [2,5,6,8,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_138 : Excluded a [2,5,6,8,3] :=
  branch_excluded a [2,5,6,8,3] (by decide)
    (fin9_cases _
      node_139
      node_140
      (invalid_excluded a [2,5,6,8,3,2] (by decide +kernel))
      (invalid_excluded a [2,5,6,8,3,3] (by decide +kernel))
      node_141
      (invalid_excluded a [2,5,6,8,3,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,8,3,6] (by decide +kernel))
      node_142
      (invalid_excluded a [2,5,6,8,3,8] (by decide +kernel)))

theorem node_144 : Excluded a [2,5,6,8,7,0] :=
  source_excluded a [2,5,6,8,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_145 : Excluded a [2,5,6,8,7,1] :=
  predecessor_excluded a [2,5,6,8,7,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_146 : Excluded a [2,5,6,8,7,3] :=
  source_excluded a [2,5,6,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_147 : Excluded a [2,5,6,8,7,4] :=
  predecessor_excluded a [2,5,6,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_143 : Excluded a [2,5,6,8,7] :=
  branch_excluded a [2,5,6,8,7] (by decide)
    (fin9_cases _
      node_144
      node_145
      (invalid_excluded a [2,5,6,8,7,2] (by decide +kernel))
      node_146
      node_147
      (invalid_excluded a [2,5,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [2,5,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [2,5,6,8,7,8] (by decide +kernel)))

theorem node_135 : Excluded a [2,5,6,8] :=
  branch_excluded a [2,5,6,8] (by decide)
    (fin9_cases _
      node_136
      node_137
      (invalid_excluded a [2,5,6,8,2] (by decide +kernel))
      node_138
      (invalid_excluded a [2,5,6,8,4] (by decide +kernel))
      (invalid_excluded a [2,5,6,8,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,8,6] (by decide +kernel))
      node_143
      (invalid_excluded a [2,5,6,8,8] (by decide +kernel)))

theorem node_107 : Excluded a [2,5,6] :=
  branch_excluded a [2,5,6] (by decide)
    (fin9_cases _
      node_108
      node_133
      (invalid_excluded a [2,5,6,2] (by decide +kernel))
      (invalid_excluded a [2,5,6,3] (by decide +kernel))
      (invalid_excluded a [2,5,6,4] (by decide +kernel))
      (invalid_excluded a [2,5,6,5] (by decide +kernel))
      (invalid_excluded a [2,5,6,6] (by decide +kernel))
      node_134
      node_135)

theorem node_150 : Excluded a [2,5,7,0,1] :=
  source_excluded a [2,5,7,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_152 : Excluded a [2,5,7,0,3,1] :=
  predecessor_excluded a [2,5,7,0,3,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_153 : Excluded a [2,5,7,0,3,4] :=
  predecessor_excluded a [2,5,7,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_156 : Excluded a [2,5,7,0,3,8,1,4] :=
  predecessor_excluded a [2,5,7,0,3,8,1,4] 0 4 2 7 (by decide) (by decide +kernel)

theorem node_157 : Excluded a [2,5,7,0,3,8,1,6] :=
  source_excluded a [2,5,7,0,3,8,1,6] 5 0 7 (by decide) (by decide +kernel)

theorem node_155 : Excluded a [2,5,7,0,3,8,1] :=
  branch_excluded a [2,5,7,0,3,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,0,3,8,1,0] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,1,1] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,1,2] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,1,3] (by decide +kernel))
      node_156
      (invalid_excluded a [2,5,7,0,3,8,1,5] (by decide +kernel))
      node_157
      (invalid_excluded a [2,5,7,0,3,8,1,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,1,8] (by decide +kernel)))

theorem node_160 : Excluded a [2,5,7,0,3,8,4,1,6] :=
  source_excluded a [2,5,7,0,3,8,4,1,6] 5 0 8 (by decide) (by decide +kernel)

theorem node_159 : Excluded a [2,5,7,0,3,8,4,1] :=
  branch_excluded a [2,5,7,0,3,8,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,0,3,8,4,1,0] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,4,1,2] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,4,1,3] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,4,1,5] (by decide +kernel))
      node_160
      (invalid_excluded a [2,5,7,0,3,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,4,1,8] (by decide +kernel)))

theorem node_161 : Excluded a [2,5,7,0,3,8,4,6] :=
  source_excluded a [2,5,7,0,3,8,4,6] 5 0 7 (by decide) (by decide +kernel)

theorem node_158 : Excluded a [2,5,7,0,3,8,4] :=
  branch_excluded a [2,5,7,0,3,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,0,3,8,4,0] (by decide +kernel))
      node_159
      (invalid_excluded a [2,5,7,0,3,8,4,2] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,4,4] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,4,5] (by decide +kernel))
      node_161
      (invalid_excluded a [2,5,7,0,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,4,8] (by decide +kernel)))

theorem node_154 : Excluded a [2,5,7,0,3,8] :=
  branch_excluded a [2,5,7,0,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,0,3,8,0] (by decide +kernel))
      node_155
      (invalid_excluded a [2,5,7,0,3,8,2] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,3] (by decide +kernel))
      node_158
      (invalid_excluded a [2,5,7,0,3,8,5] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,6] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,8,8] (by decide +kernel)))

theorem node_151 : Excluded a [2,5,7,0,3] :=
  branch_excluded a [2,5,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,0,3,0] (by decide +kernel))
      node_152
      (invalid_excluded a [2,5,7,0,3,2] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,3] (by decide +kernel))
      node_153
      (invalid_excluded a [2,5,7,0,3,5] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,6] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,3,7] (by decide +kernel))
      node_154)

theorem node_162 : Excluded a [2,5,7,0,6] :=
  source_excluded a [2,5,7,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_164 : Excluded a [2,5,7,0,8,1] :=
  predecessor_excluded a [2,5,7,0,8,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_167 : Excluded a [2,5,7,0,8,3,1,4] :=
  source_excluded a [2,5,7,0,8,3,1,4] 7 0 4 (by decide) (by decide +kernel)

def b_169 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 5
  | 2 => 7
  | 3 => 0
  | 4 => 8
  | 5 => 3
  | 6 => 1
  | 7 => 6
  | 8 => 4
  | _ => 0

def cert_169 : LosingRegion (edgeOf a b_169) 0 :=
  losingMask a b_169 0 1508603608840414407164928
    (by decide +kernel) (by decide +kernel)

theorem node_169 : Excluded a [2,5,7,0,8,3,1,6,4] :=
  losing_excluded a [2,5,7,0,8,3,1,6,4] (by decide) b_169 (by decide +kernel) 2 0 3 cert_169 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_169 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1508603608840414407164928 2 3; decide +kernel)

theorem node_168 : Excluded a [2,5,7,0,8,3,1,6] :=
  branch_excluded a [2,5,7,0,8,3,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,0,8,3,1,6,0] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,3,1,6,1] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,3,1,6,2] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,3,1,6,3] (by decide +kernel))
      node_169
      (invalid_excluded a [2,5,7,0,8,3,1,6,5] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,3,1,6,6] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,3,1,6,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,3,1,6,8] (by decide +kernel)))

theorem node_166 : Excluded a [2,5,7,0,8,3,1] :=
  branch_excluded a [2,5,7,0,8,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,0,8,3,1,0] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,3,1,1] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,3,1,2] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,3,1,3] (by decide +kernel))
      node_167
      (invalid_excluded a [2,5,7,0,8,3,1,5] (by decide +kernel))
      node_168
      (invalid_excluded a [2,5,7,0,8,3,1,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,3,1,8] (by decide +kernel)))

theorem node_170 : Excluded a [2,5,7,0,8,3,4] :=
  predecessor_excluded a [2,5,7,0,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_165 : Excluded a [2,5,7,0,8,3] :=
  branch_excluded a [2,5,7,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,0,8,3,0] (by decide +kernel))
      node_166
      (invalid_excluded a [2,5,7,0,8,3,2] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,3,3] (by decide +kernel))
      node_170
      (invalid_excluded a [2,5,7,0,8,3,5] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,3,6] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,3,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,3,8] (by decide +kernel)))

theorem node_173 : Excluded a [2,5,7,0,8,4,1,3] :=
  source_excluded a [2,5,7,0,8,4,1,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_175 : Excluded a [2,5,7,0,8,4,1,6,3] :=
  source_excluded a [2,5,7,0,8,4,1,6,3] 8 0 2 (by decide) (by decide +kernel)

theorem node_174 : Excluded a [2,5,7,0,8,4,1,6] :=
  branch_excluded a [2,5,7,0,8,4,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,0,8,4,1,6,0] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,4,1,6,1] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,4,1,6,2] (by decide +kernel))
      node_175
      (invalid_excluded a [2,5,7,0,8,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,4,1,6,8] (by decide +kernel)))

theorem node_172 : Excluded a [2,5,7,0,8,4,1] :=
  branch_excluded a [2,5,7,0,8,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,0,8,4,1,0] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,4,1,2] (by decide +kernel))
      node_173
      (invalid_excluded a [2,5,7,0,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,4,1,5] (by decide +kernel))
      node_174
      (invalid_excluded a [2,5,7,0,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,4,1,8] (by decide +kernel)))

theorem node_176 : Excluded a [2,5,7,0,8,4,3] :=
  source_excluded a [2,5,7,0,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_171 : Excluded a [2,5,7,0,8,4] :=
  branch_excluded a [2,5,7,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,0,8,4,0] (by decide +kernel))
      node_172
      (invalid_excluded a [2,5,7,0,8,4,2] (by decide +kernel))
      node_176
      (invalid_excluded a [2,5,7,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,4,8] (by decide +kernel)))

theorem node_163 : Excluded a [2,5,7,0,8] :=
  branch_excluded a [2,5,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,0,8,0] (by decide +kernel))
      node_164
      (invalid_excluded a [2,5,7,0,8,2] (by decide +kernel))
      node_165
      node_171
      (invalid_excluded a [2,5,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,8,8] (by decide +kernel)))

theorem node_149 : Excluded a [2,5,7,0] :=
  branch_excluded a [2,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,7,0,0] (by decide +kernel))
      node_150
      (invalid_excluded a [2,5,7,0,2] (by decide +kernel))
      node_151
      (invalid_excluded a [2,5,7,0,4] (by decide +kernel))
      (invalid_excluded a [2,5,7,0,5] (by decide +kernel))
      node_162
      (invalid_excluded a [2,5,7,0,7] (by decide +kernel))
      node_163)

theorem node_177 : Excluded a [2,5,7,1] :=
  predecessor_excluded a [2,5,7,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_179 : Excluded a [2,5,7,6,0] :=
  source_excluded a [2,5,7,6,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_180 : Excluded a [2,5,7,6,1] :=
  source_excluded a [2,5,7,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_181 : Excluded a [2,5,7,6,3] :=
  predecessor_excluded a [2,5,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_183 : Excluded a [2,5,7,6,8,0] :=
  source_excluded a [2,5,7,6,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_184 : Excluded a [2,5,7,6,8,1] :=
  predecessor_excluded a [2,5,7,6,8,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_185 : Excluded a [2,5,7,6,8,3] :=
  source_excluded a [2,5,7,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_186 : Excluded a [2,5,7,6,8,4] :=
  source_excluded a [2,5,7,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_182 : Excluded a [2,5,7,6,8] :=
  branch_excluded a [2,5,7,6,8] (by decide)
    (fin9_cases _
      node_183
      node_184
      (invalid_excluded a [2,5,7,6,8,2] (by decide +kernel))
      node_185
      node_186
      (invalid_excluded a [2,5,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [2,5,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [2,5,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [2,5,7,6,8,8] (by decide +kernel)))

theorem node_178 : Excluded a [2,5,7,6] :=
  branch_excluded a [2,5,7,6] (by decide)
    (fin9_cases _
      node_179
      node_180
      (invalid_excluded a [2,5,7,6,2] (by decide +kernel))
      node_181
      (invalid_excluded a [2,5,7,6,4] (by decide +kernel))
      (invalid_excluded a [2,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [2,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [2,5,7,6,7] (by decide +kernel))
      node_182)

theorem node_187 : Excluded a [2,5,7,8] :=
  predecessor_excluded a [2,5,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_148 : Excluded a [2,5,7] :=
  branch_excluded a [2,5,7] (by decide)
    (fin9_cases _
      node_149
      node_177
      (invalid_excluded a [2,5,7,2] (by decide +kernel))
      (invalid_excluded a [2,5,7,3] (by decide +kernel))
      (invalid_excluded a [2,5,7,4] (by decide +kernel))
      (invalid_excluded a [2,5,7,5] (by decide +kernel))
      node_178
      (invalid_excluded a [2,5,7,7] (by decide +kernel))
      node_187)

theorem node_190 : Excluded a [2,5,8,0,1] :=
  source_excluded a [2,5,8,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_192 : Excluded a [2,5,8,0,3,1] :=
  predecessor_excluded a [2,5,8,0,3,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_193 : Excluded a [2,5,8,0,3,4] :=
  predecessor_excluded a [2,5,8,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_194 : Excluded a [2,5,8,0,3,7] :=
  source_excluded a [2,5,8,0,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_191 : Excluded a [2,5,8,0,3] :=
  branch_excluded a [2,5,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,8,0,3,0] (by decide +kernel))
      node_192
      (invalid_excluded a [2,5,8,0,3,2] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,3,3] (by decide +kernel))
      node_193
      (invalid_excluded a [2,5,8,0,3,5] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,3,6] (by decide +kernel))
      node_194
      (invalid_excluded a [2,5,8,0,3,8] (by decide +kernel)))

theorem node_195 : Excluded a [2,5,8,0,6] :=
  source_excluded a [2,5,8,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_197 : Excluded a [2,5,8,0,7,1] :=
  predecessor_excluded a [2,5,8,0,7,1] 2 1 1 5 (by decide) (by decide +kernel)

def b_201 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 5
  | 2 => 8
  | 3 => 0
  | 4 => 7
  | 5 => 3
  | 6 => 1
  | 7 => 4
  | 8 => 6
  | _ => 0

def cert_201 : LosingRegion (edgeOf a b_201) 0 :=
  losingMask a b_201 0 1416701929865193421014016
    (by decide +kernel) (by decide +kernel)

theorem node_201 : Excluded a [2,5,8,0,7,3,1,4,6] :=
  losing_excluded a [2,5,8,0,7,3,1,4,6] (by decide) b_201 (by decide +kernel) 2 0 3 cert_201 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_201 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1416701929865193421014016 2 3; decide +kernel)

theorem node_200 : Excluded a [2,5,8,0,7,3,1,4] :=
  branch_excluded a [2,5,8,0,7,3,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,8,0,7,3,1,4,0] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,3,1,4,1] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,3,1,4,2] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,3,1,4,3] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,3,1,4,4] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,3,1,4,5] (by decide +kernel))
      node_201
      (invalid_excluded a [2,5,8,0,7,3,1,4,7] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,3,1,4,8] (by decide +kernel)))

theorem node_202 : Excluded a [2,5,8,0,7,3,1,6] :=
  predecessor_excluded a [2,5,8,0,7,3,1,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_199 : Excluded a [2,5,8,0,7,3,1] :=
  branch_excluded a [2,5,8,0,7,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,8,0,7,3,1,0] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,3,1,1] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,3,1,2] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,3,1,3] (by decide +kernel))
      node_200
      (invalid_excluded a [2,5,8,0,7,3,1,5] (by decide +kernel))
      node_202
      (invalid_excluded a [2,5,8,0,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,3,1,8] (by decide +kernel)))

theorem node_203 : Excluded a [2,5,8,0,7,3,4] :=
  source_excluded a [2,5,8,0,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_198 : Excluded a [2,5,8,0,7,3] :=
  branch_excluded a [2,5,8,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,8,0,7,3,0] (by decide +kernel))
      node_199
      (invalid_excluded a [2,5,8,0,7,3,2] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,3,3] (by decide +kernel))
      node_203
      (invalid_excluded a [2,5,8,0,7,3,5] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,3,7] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,3,8] (by decide +kernel)))

theorem node_204 : Excluded a [2,5,8,0,7,4] :=
  predecessor_excluded a [2,5,8,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_196 : Excluded a [2,5,8,0,7] :=
  branch_excluded a [2,5,8,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,8,0,7,0] (by decide +kernel))
      node_197
      (invalid_excluded a [2,5,8,0,7,2] (by decide +kernel))
      node_198
      node_204
      (invalid_excluded a [2,5,8,0,7,5] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,6] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,7] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,7,8] (by decide +kernel)))

theorem node_189 : Excluded a [2,5,8,0] :=
  branch_excluded a [2,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,5,8,0,0] (by decide +kernel))
      node_190
      (invalid_excluded a [2,5,8,0,2] (by decide +kernel))
      node_191
      (invalid_excluded a [2,5,8,0,4] (by decide +kernel))
      (invalid_excluded a [2,5,8,0,5] (by decide +kernel))
      node_195
      node_196
      (invalid_excluded a [2,5,8,0,8] (by decide +kernel)))

theorem node_205 : Excluded a [2,5,8,1] :=
  predecessor_excluded a [2,5,8,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_207 : Excluded a [2,5,8,6,0] :=
  source_excluded a [2,5,8,6,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_208 : Excluded a [2,5,8,6,1] :=
  source_excluded a [2,5,8,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_209 : Excluded a [2,5,8,6,3] :=
  predecessor_excluded a [2,5,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_210 : Excluded a [2,5,8,6,7] :=
  predecessor_excluded a [2,5,8,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_206 : Excluded a [2,5,8,6] :=
  branch_excluded a [2,5,8,6] (by decide)
    (fin9_cases _
      node_207
      node_208
      (invalid_excluded a [2,5,8,6,2] (by decide +kernel))
      node_209
      (invalid_excluded a [2,5,8,6,4] (by decide +kernel))
      (invalid_excluded a [2,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [2,5,8,6,6] (by decide +kernel))
      node_210
      (invalid_excluded a [2,5,8,6,8] (by decide +kernel)))

theorem node_212 : Excluded a [2,5,8,7,0] :=
  source_excluded a [2,5,8,7,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_213 : Excluded a [2,5,8,7,1] :=
  source_excluded a [2,5,8,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_215 : Excluded a [2,5,8,7,3,0] :=
  source_excluded a [2,5,8,7,3,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_216 : Excluded a [2,5,8,7,3,1] :=
  predecessor_excluded a [2,5,8,7,3,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_217 : Excluded a [2,5,8,7,3,4] :=
  predecessor_excluded a [2,5,8,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_214 : Excluded a [2,5,8,7,3] :=
  branch_excluded a [2,5,8,7,3] (by decide)
    (fin9_cases _
      node_215
      node_216
      (invalid_excluded a [2,5,8,7,3,2] (by decide +kernel))
      (invalid_excluded a [2,5,8,7,3,3] (by decide +kernel))
      node_217
      (invalid_excluded a [2,5,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [2,5,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [2,5,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [2,5,8,7,3,8] (by decide +kernel)))

theorem node_218 : Excluded a [2,5,8,7,6] :=
  source_excluded a [2,5,8,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_211 : Excluded a [2,5,8,7] :=
  branch_excluded a [2,5,8,7] (by decide)
    (fin9_cases _
      node_212
      node_213
      (invalid_excluded a [2,5,8,7,2] (by decide +kernel))
      node_214
      (invalid_excluded a [2,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [2,5,8,7,5] (by decide +kernel))
      node_218
      (invalid_excluded a [2,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [2,5,8,7,8] (by decide +kernel)))

theorem node_188 : Excluded a [2,5,8] :=
  branch_excluded a [2,5,8] (by decide)
    (fin9_cases _
      node_189
      node_205
      (invalid_excluded a [2,5,8,2] (by decide +kernel))
      (invalid_excluded a [2,5,8,3] (by decide +kernel))
      (invalid_excluded a [2,5,8,4] (by decide +kernel))
      (invalid_excluded a [2,5,8,5] (by decide +kernel))
      node_206
      node_211
      (invalid_excluded a [2,5,8,8] (by decide +kernel)))

theorem node_103 : Excluded a [2,5] :=
  branch_excluded a [2,5] (by decide)
    (fin9_cases _
      node_104
      node_105
      (invalid_excluded a [2,5,2] (by decide +kernel))
      (invalid_excluded a [2,5,3] (by decide +kernel))
      node_106
      (invalid_excluded a [2,5,5] (by decide +kernel))
      node_107
      node_148
      node_188)

theorem node_220 : Excluded a [2,6,0] :=
  predecessor_excluded a [2,6,0] 3 0 0 2 (by decide) (by decide +kernel)

theorem node_221 : Excluded a [2,6,1] :=
  source_excluded a [2,6,1] 0 3 2 (by decide) (by decide +kernel)

theorem node_222 : Excluded a [2,6,4] :=
  source_excluded a [2,6,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_225 : Excluded a [2,6,5,0,1] :=
  predecessor_excluded a [2,6,5,0,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_226 : Excluded a [2,6,5,0,3] :=
  source_excluded a [2,6,5,0,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_228 : Excluded a [2,6,5,0,7,1] :=
  source_excluded a [2,6,5,0,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_229 : Excluded a [2,6,5,0,7,3] :=
  source_excluded a [2,6,5,0,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_230 : Excluded a [2,6,5,0,7,4] :=
  predecessor_excluded a [2,6,5,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_231 : Excluded a [2,6,5,0,7,8] :=
  predecessor_excluded a [2,6,5,0,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_227 : Excluded a [2,6,5,0,7] :=
  branch_excluded a [2,6,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,5,0,7,0] (by decide +kernel))
      node_228
      (invalid_excluded a [2,6,5,0,7,2] (by decide +kernel))
      node_229
      node_230
      (invalid_excluded a [2,6,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [2,6,5,0,7,7] (by decide +kernel))
      node_231)

theorem node_233 : Excluded a [2,6,5,0,8,1] :=
  source_excluded a [2,6,5,0,8,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_234 : Excluded a [2,6,5,0,8,3] :=
  source_excluded a [2,6,5,0,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_235 : Excluded a [2,6,5,0,8,4] :=
  predecessor_excluded a [2,6,5,0,8,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_236 : Excluded a [2,6,5,0,8,7] :=
  source_excluded a [2,6,5,0,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_232 : Excluded a [2,6,5,0,8] :=
  branch_excluded a [2,6,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,5,0,8,0] (by decide +kernel))
      node_233
      (invalid_excluded a [2,6,5,0,8,2] (by decide +kernel))
      node_234
      node_235
      (invalid_excluded a [2,6,5,0,8,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,0,8,6] (by decide +kernel))
      node_236
      (invalid_excluded a [2,6,5,0,8,8] (by decide +kernel)))

theorem node_224 : Excluded a [2,6,5,0] :=
  branch_excluded a [2,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,5,0,0] (by decide +kernel))
      node_225
      (invalid_excluded a [2,6,5,0,2] (by decide +kernel))
      node_226
      (invalid_excluded a [2,6,5,0,4] (by decide +kernel))
      (invalid_excluded a [2,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,0,6] (by decide +kernel))
      node_227
      node_232)

theorem node_238 : Excluded a [2,6,5,1,0] :=
  predecessor_excluded a [2,6,5,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_239 : Excluded a [2,6,5,1,3] :=
  source_excluded a [2,6,5,1,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_241 : Excluded a [2,6,5,1,7,0] :=
  source_excluded a [2,6,5,1,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_242 : Excluded a [2,6,5,1,7,3] :=
  source_excluded a [2,6,5,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_243 : Excluded a [2,6,5,1,7,4] :=
  predecessor_excluded a [2,6,5,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_244 : Excluded a [2,6,5,1,7,8] :=
  predecessor_excluded a [2,6,5,1,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_240 : Excluded a [2,6,5,1,7] :=
  branch_excluded a [2,6,5,1,7] (by decide)
    (fin9_cases _
      node_241
      (invalid_excluded a [2,6,5,1,7,1] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,2] (by decide +kernel))
      node_242
      node_243
      (invalid_excluded a [2,6,5,1,7,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,6] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,7,7] (by decide +kernel))
      node_244)

theorem node_246 : Excluded a [2,6,5,1,8,0] :=
  source_excluded a [2,6,5,1,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_247 : Excluded a [2,6,5,1,8,3] :=
  source_excluded a [2,6,5,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_248 : Excluded a [2,6,5,1,8,4] :=
  predecessor_excluded a [2,6,5,1,8,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_249 : Excluded a [2,6,5,1,8,7] :=
  source_excluded a [2,6,5,1,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_245 : Excluded a [2,6,5,1,8] :=
  branch_excluded a [2,6,5,1,8] (by decide)
    (fin9_cases _
      node_246
      (invalid_excluded a [2,6,5,1,8,1] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,8,2] (by decide +kernel))
      node_247
      node_248
      (invalid_excluded a [2,6,5,1,8,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,8,6] (by decide +kernel))
      node_249
      (invalid_excluded a [2,6,5,1,8,8] (by decide +kernel)))

theorem node_237 : Excluded a [2,6,5,1] :=
  branch_excluded a [2,6,5,1] (by decide)
    (fin9_cases _
      node_238
      (invalid_excluded a [2,6,5,1,1] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,2] (by decide +kernel))
      node_239
      (invalid_excluded a [2,6,5,1,4] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,1,6] (by decide +kernel))
      node_240
      node_245)

theorem node_252 : Excluded a [2,6,5,7,0,1] :=
  source_excluded a [2,6,5,7,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_253 : Excluded a [2,6,5,7,0,3] :=
  source_excluded a [2,6,5,7,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_254 : Excluded a [2,6,5,7,0,4] :=
  predecessor_excluded a [2,6,5,7,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_256 : Excluded a [2,6,5,7,0,8,1] :=
  predecessor_excluded a [2,6,5,7,0,8,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_257 : Excluded a [2,6,5,7,0,8,3] :=
  source_excluded a [2,6,5,7,0,8,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_258 : Excluded a [2,6,5,7,0,8,4] :=
  source_excluded a [2,6,5,7,0,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_255 : Excluded a [2,6,5,7,0,8] :=
  branch_excluded a [2,6,5,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,5,7,0,8,0] (by decide +kernel))
      node_256
      (invalid_excluded a [2,6,5,7,0,8,2] (by decide +kernel))
      node_257
      node_258
      (invalid_excluded a [2,6,5,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [2,6,5,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [2,6,5,7,0,8,8] (by decide +kernel)))

theorem node_251 : Excluded a [2,6,5,7,0] :=
  branch_excluded a [2,6,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,5,7,0,0] (by decide +kernel))
      node_252
      (invalid_excluded a [2,6,5,7,0,2] (by decide +kernel))
      node_253
      node_254
      (invalid_excluded a [2,6,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [2,6,5,7,0,7] (by decide +kernel))
      node_255)

theorem node_259 : Excluded a [2,6,5,7,1] :=
  predecessor_excluded a [2,6,5,7,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_260 : Excluded a [2,6,5,7,3] :=
  source_excluded a [2,6,5,7,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_261 : Excluded a [2,6,5,7,8] :=
  predecessor_excluded a [2,6,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_250 : Excluded a [2,6,5,7] :=
  branch_excluded a [2,6,5,7] (by decide)
    (fin9_cases _
      node_251
      node_259
      (invalid_excluded a [2,6,5,7,2] (by decide +kernel))
      node_260
      (invalid_excluded a [2,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [2,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [2,6,5,7,7] (by decide +kernel))
      node_261)

theorem node_264 : Excluded a [2,6,5,8,0,1] :=
  source_excluded a [2,6,5,8,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_265 : Excluded a [2,6,5,8,0,3] :=
  source_excluded a [2,6,5,8,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_266 : Excluded a [2,6,5,8,0,4] :=
  predecessor_excluded a [2,6,5,8,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_267 : Excluded a [2,6,5,8,0,7] :=
  source_excluded a [2,6,5,8,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_263 : Excluded a [2,6,5,8,0] :=
  branch_excluded a [2,6,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,5,8,0,0] (by decide +kernel))
      node_264
      (invalid_excluded a [2,6,5,8,0,2] (by decide +kernel))
      node_265
      node_266
      (invalid_excluded a [2,6,5,8,0,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,8,0,6] (by decide +kernel))
      node_267
      (invalid_excluded a [2,6,5,8,0,8] (by decide +kernel)))

theorem node_268 : Excluded a [2,6,5,8,1] :=
  predecessor_excluded a [2,6,5,8,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_269 : Excluded a [2,6,5,8,3] :=
  source_excluded a [2,6,5,8,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_271 : Excluded a [2,6,5,8,7,0] :=
  source_excluded a [2,6,5,8,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_272 : Excluded a [2,6,5,8,7,1] :=
  source_excluded a [2,6,5,8,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_273 : Excluded a [2,6,5,8,7,3] :=
  source_excluded a [2,6,5,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_274 : Excluded a [2,6,5,8,7,4] :=
  predecessor_excluded a [2,6,5,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_270 : Excluded a [2,6,5,8,7] :=
  branch_excluded a [2,6,5,8,7] (by decide)
    (fin9_cases _
      node_271
      node_272
      (invalid_excluded a [2,6,5,8,7,2] (by decide +kernel))
      node_273
      node_274
      (invalid_excluded a [2,6,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [2,6,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [2,6,5,8,7,8] (by decide +kernel)))

theorem node_262 : Excluded a [2,6,5,8] :=
  branch_excluded a [2,6,5,8] (by decide)
    (fin9_cases _
      node_263
      node_268
      (invalid_excluded a [2,6,5,8,2] (by decide +kernel))
      node_269
      (invalid_excluded a [2,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [2,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,8,6] (by decide +kernel))
      node_270
      (invalid_excluded a [2,6,5,8,8] (by decide +kernel)))

theorem node_223 : Excluded a [2,6,5] :=
  branch_excluded a [2,6,5] (by decide)
    (fin9_cases _
      node_224
      node_237
      (invalid_excluded a [2,6,5,2] (by decide +kernel))
      (invalid_excluded a [2,6,5,3] (by decide +kernel))
      (invalid_excluded a [2,6,5,4] (by decide +kernel))
      (invalid_excluded a [2,6,5,5] (by decide +kernel))
      (invalid_excluded a [2,6,5,6] (by decide +kernel))
      node_250
      node_262)

theorem node_277 : Excluded a [2,6,7,0,1] :=
  predecessor_excluded a [2,6,7,0,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_279 : Excluded a [2,6,7,0,3,1] :=
  source_excluded a [2,6,7,0,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_280 : Excluded a [2,6,7,0,3,4] :=
  predecessor_excluded a [2,6,7,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_282 : Excluded a [2,6,7,0,3,8,1] :=
  predecessor_excluded a [2,6,7,0,3,8,1] 2 1 1 6 (by decide) (by decide +kernel)

def b_285 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 6
  | 2 => 7
  | 3 => 0
  | 4 => 3
  | 5 => 8
  | 6 => 4
  | 7 => 1
  | 8 => 5
  | _ => 0

def cert_285 : LosingRegion (edgeOf a b_285) 0 :=
  losingMask a b_285 0 1347084109940901823906816
    (by decide +kernel) (by decide +kernel)

theorem node_285 : Excluded a [2,6,7,0,3,8,4,1,5] :=
  losing_excluded a [2,6,7,0,3,8,4,1,5] (by decide) b_285 (by decide +kernel) 2 0 3 cert_285 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_285 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1347084109940901823906816 2 3; decide +kernel)

theorem node_284 : Excluded a [2,6,7,0,3,8,4,1] :=
  branch_excluded a [2,6,7,0,3,8,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,7,0,3,8,4,1,0] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,3,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,3,8,4,1,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,3,8,4,1,3] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,3,8,4,1,4] (by decide +kernel))
      node_285
      (invalid_excluded a [2,6,7,0,3,8,4,1,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,3,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,3,8,4,1,8] (by decide +kernel)))

theorem node_286 : Excluded a [2,6,7,0,3,8,4,5] :=
  source_excluded a [2,6,7,0,3,8,4,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_283 : Excluded a [2,6,7,0,3,8,4] :=
  branch_excluded a [2,6,7,0,3,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,7,0,3,8,4,0] (by decide +kernel))
      node_284
      (invalid_excluded a [2,6,7,0,3,8,4,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,3,8,4,4] (by decide +kernel))
      node_286
      (invalid_excluded a [2,6,7,0,3,8,4,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,3,8,4,8] (by decide +kernel)))

theorem node_287 : Excluded a [2,6,7,0,3,8,5] :=
  predecessor_excluded a [2,6,7,0,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_281 : Excluded a [2,6,7,0,3,8] :=
  branch_excluded a [2,6,7,0,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,7,0,3,8,0] (by decide +kernel))
      node_282
      (invalid_excluded a [2,6,7,0,3,8,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,3,8,3] (by decide +kernel))
      node_283
      node_287
      (invalid_excluded a [2,6,7,0,3,8,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,3,8,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,3,8,8] (by decide +kernel)))

theorem node_278 : Excluded a [2,6,7,0,3] :=
  branch_excluded a [2,6,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,7,0,3,0] (by decide +kernel))
      node_279
      (invalid_excluded a [2,6,7,0,3,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,3,3] (by decide +kernel))
      node_280
      (invalid_excluded a [2,6,7,0,3,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,3,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,3,7] (by decide +kernel))
      node_281)

theorem node_289 : Excluded a [2,6,7,0,8,1] :=
  source_excluded a [2,6,7,0,8,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_291 : Excluded a [2,6,7,0,8,3,1] :=
  predecessor_excluded a [2,6,7,0,8,3,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_292 : Excluded a [2,6,7,0,8,3,4] :=
  predecessor_excluded a [2,6,7,0,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

def b_295 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 6
  | 2 => 7
  | 3 => 0
  | 4 => 8
  | 5 => 3
  | 6 => 5
  | 7 => 1
  | 8 => 4
  | _ => 0

def cert_295 : LosingRegion (edgeOf a b_295) 0 :=
  losingMask a b_295 0 1422641961763571984499712
    (by decide +kernel) (by decide +kernel)

theorem node_295 : Excluded a [2,6,7,0,8,3,5,1,4] :=
  losing_excluded a [2,6,7,0,8,3,5,1,4] (by decide) b_295 (by decide +kernel) 2 0 3 cert_295 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_295 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1422641961763571984499712 2 3; decide +kernel)

theorem node_294 : Excluded a [2,6,7,0,8,3,5,1] :=
  branch_excluded a [2,6,7,0,8,3,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,7,0,8,3,5,1,0] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,3,5,1,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,3,5,1,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,3,5,1,3] (by decide +kernel))
      node_295
      (invalid_excluded a [2,6,7,0,8,3,5,1,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,3,5,1,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,3,5,1,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,3,5,1,8] (by decide +kernel)))

theorem node_296 : Excluded a [2,6,7,0,8,3,5,4] :=
  source_excluded a [2,6,7,0,8,3,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_293 : Excluded a [2,6,7,0,8,3,5] :=
  branch_excluded a [2,6,7,0,8,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,7,0,8,3,5,0] (by decide +kernel))
      node_294
      (invalid_excluded a [2,6,7,0,8,3,5,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,3,5,3] (by decide +kernel))
      node_296
      (invalid_excluded a [2,6,7,0,8,3,5,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,3,5,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,3,5,8] (by decide +kernel)))

theorem node_290 : Excluded a [2,6,7,0,8,3] :=
  branch_excluded a [2,6,7,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,7,0,8,3,0] (by decide +kernel))
      node_291
      (invalid_excluded a [2,6,7,0,8,3,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,3,3] (by decide +kernel))
      node_292
      node_293
      (invalid_excluded a [2,6,7,0,8,3,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,3,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,3,8] (by decide +kernel)))

theorem node_298 : Excluded a [2,6,7,0,8,4,1] :=
  predecessor_excluded a [2,6,7,0,8,4,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_299 : Excluded a [2,6,7,0,8,4,3] :=
  source_excluded a [2,6,7,0,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_300 : Excluded a [2,6,7,0,8,4,5] :=
  predecessor_excluded a [2,6,7,0,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_297 : Excluded a [2,6,7,0,8,4] :=
  branch_excluded a [2,6,7,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,7,0,8,4,0] (by decide +kernel))
      node_298
      (invalid_excluded a [2,6,7,0,8,4,2] (by decide +kernel))
      node_299
      (invalid_excluded a [2,6,7,0,8,4,4] (by decide +kernel))
      node_300
      (invalid_excluded a [2,6,7,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,4,8] (by decide +kernel)))

theorem node_288 : Excluded a [2,6,7,0,8] :=
  branch_excluded a [2,6,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,7,0,8,0] (by decide +kernel))
      node_289
      (invalid_excluded a [2,6,7,0,8,2] (by decide +kernel))
      node_290
      node_297
      (invalid_excluded a [2,6,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,8,8] (by decide +kernel)))

theorem node_276 : Excluded a [2,6,7,0] :=
  branch_excluded a [2,6,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,7,0,0] (by decide +kernel))
      node_277
      (invalid_excluded a [2,6,7,0,2] (by decide +kernel))
      node_278
      (invalid_excluded a [2,6,7,0,4] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,0,7] (by decide +kernel))
      node_288)

theorem node_302 : Excluded a [2,6,7,1,0] :=
  predecessor_excluded a [2,6,7,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_304 : Excluded a [2,6,7,1,3,0] :=
  source_excluded a [2,6,7,1,3,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_305 : Excluded a [2,6,7,1,3,4] :=
  predecessor_excluded a [2,6,7,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_307 : Excluded a [2,6,7,1,3,8,0] :=
  source_excluded a [2,6,7,1,3,8,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_309 : Excluded a [2,6,7,1,3,8,4,0] :=
  predecessor_excluded a [2,6,7,1,3,8,4,0] 1 2 7 0 (by decide) (by decide +kernel)

theorem node_310 : Excluded a [2,6,7,1,3,8,4,5] :=
  source_excluded a [2,6,7,1,3,8,4,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_308 : Excluded a [2,6,7,1,3,8,4] :=
  branch_excluded a [2,6,7,1,3,8,4] (by decide)
    (fin9_cases _
      node_309
      (invalid_excluded a [2,6,7,1,3,8,4,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,3,8,4,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,3,8,4,4] (by decide +kernel))
      node_310
      (invalid_excluded a [2,6,7,1,3,8,4,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,3,8,4,8] (by decide +kernel)))

theorem node_311 : Excluded a [2,6,7,1,3,8,5] :=
  predecessor_excluded a [2,6,7,1,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_306 : Excluded a [2,6,7,1,3,8] :=
  branch_excluded a [2,6,7,1,3,8] (by decide)
    (fin9_cases _
      node_307
      (invalid_excluded a [2,6,7,1,3,8,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,3,8,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,3,8,3] (by decide +kernel))
      node_308
      node_311
      (invalid_excluded a [2,6,7,1,3,8,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,3,8,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,3,8,8] (by decide +kernel)))

theorem node_303 : Excluded a [2,6,7,1,3] :=
  branch_excluded a [2,6,7,1,3] (by decide)
    (fin9_cases _
      node_304
      (invalid_excluded a [2,6,7,1,3,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,3,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,3,3] (by decide +kernel))
      node_305
      (invalid_excluded a [2,6,7,1,3,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,3,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,3,7] (by decide +kernel))
      node_306)

theorem node_313 : Excluded a [2,6,7,1,8,0] :=
  source_excluded a [2,6,7,1,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_315 : Excluded a [2,6,7,1,8,3,0] :=
  source_excluded a [2,6,7,1,8,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_316 : Excluded a [2,6,7,1,8,3,4] :=
  predecessor_excluded a [2,6,7,1,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_318 : Excluded a [2,6,7,1,8,3,5,0] :=
  predecessor_excluded a [2,6,7,1,8,3,5,0] 1 2 7 0 (by decide) (by decide +kernel)

theorem node_319 : Excluded a [2,6,7,1,8,3,5,4] :=
  source_excluded a [2,6,7,1,8,3,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_317 : Excluded a [2,6,7,1,8,3,5] :=
  branch_excluded a [2,6,7,1,8,3,5] (by decide)
    (fin9_cases _
      node_318
      (invalid_excluded a [2,6,7,1,8,3,5,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,5,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,5,3] (by decide +kernel))
      node_319
      (invalid_excluded a [2,6,7,1,8,3,5,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,5,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,5,8] (by decide +kernel)))

theorem node_314 : Excluded a [2,6,7,1,8,3] :=
  branch_excluded a [2,6,7,1,8,3] (by decide)
    (fin9_cases _
      node_315
      (invalid_excluded a [2,6,7,1,8,3,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,3] (by decide +kernel))
      node_316
      node_317
      (invalid_excluded a [2,6,7,1,8,3,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,3,8] (by decide +kernel)))

theorem node_321 : Excluded a [2,6,7,1,8,4,0] :=
  source_excluded a [2,6,7,1,8,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_322 : Excluded a [2,6,7,1,8,4,3] :=
  source_excluded a [2,6,7,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_323 : Excluded a [2,6,7,1,8,4,5] :=
  predecessor_excluded a [2,6,7,1,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_320 : Excluded a [2,6,7,1,8,4] :=
  branch_excluded a [2,6,7,1,8,4] (by decide)
    (fin9_cases _
      node_321
      (invalid_excluded a [2,6,7,1,8,4,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,2] (by decide +kernel))
      node_322
      (invalid_excluded a [2,6,7,1,8,4,4] (by decide +kernel))
      node_323
      (invalid_excluded a [2,6,7,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,4,8] (by decide +kernel)))

theorem node_312 : Excluded a [2,6,7,1,8] :=
  branch_excluded a [2,6,7,1,8] (by decide)
    (fin9_cases _
      node_313
      (invalid_excluded a [2,6,7,1,8,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,2] (by decide +kernel))
      node_314
      node_320
      (invalid_excluded a [2,6,7,1,8,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,8,8] (by decide +kernel)))

theorem node_301 : Excluded a [2,6,7,1] :=
  branch_excluded a [2,6,7,1] (by decide)
    (fin9_cases _
      node_302
      (invalid_excluded a [2,6,7,1,1] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,2] (by decide +kernel))
      node_303
      (invalid_excluded a [2,6,7,1,4] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,5] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,1,7] (by decide +kernel))
      node_312)

theorem node_324 : Excluded a [2,6,7,5] :=
  source_excluded a [2,6,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_325 : Excluded a [2,6,7,8] :=
  predecessor_excluded a [2,6,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_275 : Excluded a [2,6,7] :=
  branch_excluded a [2,6,7] (by decide)
    (fin9_cases _
      node_276
      node_301
      (invalid_excluded a [2,6,7,2] (by decide +kernel))
      (invalid_excluded a [2,6,7,3] (by decide +kernel))
      (invalid_excluded a [2,6,7,4] (by decide +kernel))
      node_324
      (invalid_excluded a [2,6,7,6] (by decide +kernel))
      (invalid_excluded a [2,6,7,7] (by decide +kernel))
      node_325)

theorem node_328 : Excluded a [2,6,8,0,1] :=
  predecessor_excluded a [2,6,8,0,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_330 : Excluded a [2,6,8,0,3,1] :=
  source_excluded a [2,6,8,0,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_331 : Excluded a [2,6,8,0,3,4] :=
  predecessor_excluded a [2,6,8,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_332 : Excluded a [2,6,8,0,3,7] :=
  source_excluded a [2,6,8,0,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_329 : Excluded a [2,6,8,0,3] :=
  branch_excluded a [2,6,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,8,0,3,0] (by decide +kernel))
      node_330
      (invalid_excluded a [2,6,8,0,3,2] (by decide +kernel))
      (invalid_excluded a [2,6,8,0,3,3] (by decide +kernel))
      node_331
      (invalid_excluded a [2,6,8,0,3,5] (by decide +kernel))
      (invalid_excluded a [2,6,8,0,3,6] (by decide +kernel))
      node_332
      (invalid_excluded a [2,6,8,0,3,8] (by decide +kernel)))

theorem node_334 : Excluded a [2,6,8,0,7,1] :=
  source_excluded a [2,6,8,0,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_336 : Excluded a [2,6,8,0,7,3,1] :=
  predecessor_excluded a [2,6,8,0,7,3,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_337 : Excluded a [2,6,8,0,7,3,4] :=
  source_excluded a [2,6,8,0,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_338 : Excluded a [2,6,8,0,7,3,5] :=
  source_excluded a [2,6,8,0,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_335 : Excluded a [2,6,8,0,7,3] :=
  branch_excluded a [2,6,8,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,8,0,7,3,0] (by decide +kernel))
      node_336
      (invalid_excluded a [2,6,8,0,7,3,2] (by decide +kernel))
      (invalid_excluded a [2,6,8,0,7,3,3] (by decide +kernel))
      node_337
      node_338
      (invalid_excluded a [2,6,8,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [2,6,8,0,7,3,7] (by decide +kernel))
      (invalid_excluded a [2,6,8,0,7,3,8] (by decide +kernel)))

theorem node_339 : Excluded a [2,6,8,0,7,4] :=
  predecessor_excluded a [2,6,8,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_333 : Excluded a [2,6,8,0,7] :=
  branch_excluded a [2,6,8,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,8,0,7,0] (by decide +kernel))
      node_334
      (invalid_excluded a [2,6,8,0,7,2] (by decide +kernel))
      node_335
      node_339
      (invalid_excluded a [2,6,8,0,7,5] (by decide +kernel))
      (invalid_excluded a [2,6,8,0,7,6] (by decide +kernel))
      (invalid_excluded a [2,6,8,0,7,7] (by decide +kernel))
      (invalid_excluded a [2,6,8,0,7,8] (by decide +kernel)))

theorem node_327 : Excluded a [2,6,8,0] :=
  branch_excluded a [2,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,8,0,0] (by decide +kernel))
      node_328
      (invalid_excluded a [2,6,8,0,2] (by decide +kernel))
      node_329
      (invalid_excluded a [2,6,8,0,4] (by decide +kernel))
      (invalid_excluded a [2,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [2,6,8,0,6] (by decide +kernel))
      node_333
      (invalid_excluded a [2,6,8,0,8] (by decide +kernel)))

theorem node_341 : Excluded a [2,6,8,1,0] :=
  predecessor_excluded a [2,6,8,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_343 : Excluded a [2,6,8,1,3,0] :=
  source_excluded a [2,6,8,1,3,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_344 : Excluded a [2,6,8,1,3,4] :=
  predecessor_excluded a [2,6,8,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_345 : Excluded a [2,6,8,1,3,7] :=
  source_excluded a [2,6,8,1,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_342 : Excluded a [2,6,8,1,3] :=
  branch_excluded a [2,6,8,1,3] (by decide)
    (fin9_cases _
      node_343
      (invalid_excluded a [2,6,8,1,3,1] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,3,2] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,3,3] (by decide +kernel))
      node_344
      (invalid_excluded a [2,6,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,3,6] (by decide +kernel))
      node_345
      (invalid_excluded a [2,6,8,1,3,8] (by decide +kernel)))

theorem node_347 : Excluded a [2,6,8,1,7,0] :=
  source_excluded a [2,6,8,1,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_349 : Excluded a [2,6,8,1,7,3,0] :=
  source_excluded a [2,6,8,1,7,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_350 : Excluded a [2,6,8,1,7,3,4] :=
  source_excluded a [2,6,8,1,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_351 : Excluded a [2,6,8,1,7,3,5] :=
  source_excluded a [2,6,8,1,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_348 : Excluded a [2,6,8,1,7,3] :=
  branch_excluded a [2,6,8,1,7,3] (by decide)
    (fin9_cases _
      node_349
      (invalid_excluded a [2,6,8,1,7,3,1] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,7,3,2] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,7,3,3] (by decide +kernel))
      node_350
      node_351
      (invalid_excluded a [2,6,8,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,7,3,8] (by decide +kernel)))

theorem node_352 : Excluded a [2,6,8,1,7,4] :=
  predecessor_excluded a [2,6,8,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_346 : Excluded a [2,6,8,1,7] :=
  branch_excluded a [2,6,8,1,7] (by decide)
    (fin9_cases _
      node_347
      (invalid_excluded a [2,6,8,1,7,1] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,7,2] (by decide +kernel))
      node_348
      node_352
      (invalid_excluded a [2,6,8,1,7,5] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,7,6] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,7,7] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,7,8] (by decide +kernel)))

theorem node_340 : Excluded a [2,6,8,1] :=
  branch_excluded a [2,6,8,1] (by decide)
    (fin9_cases _
      node_341
      (invalid_excluded a [2,6,8,1,1] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,2] (by decide +kernel))
      node_342
      (invalid_excluded a [2,6,8,1,4] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [2,6,8,1,6] (by decide +kernel))
      node_346
      (invalid_excluded a [2,6,8,1,8] (by decide +kernel)))

theorem node_353 : Excluded a [2,6,8,5] :=
  source_excluded a [2,6,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_356 : Excluded a [2,6,8,7,0,1] :=
  source_excluded a [2,6,8,7,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_357 : Excluded a [2,6,8,7,0,3] :=
  predecessor_excluded a [2,6,8,7,0,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_359 : Excluded a [2,6,8,7,0,4,1] :=
  predecessor_excluded a [2,6,8,7,0,4,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_360 : Excluded a [2,6,8,7,0,4,3] :=
  source_excluded a [2,6,8,7,0,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_361 : Excluded a [2,6,8,7,0,4,5] :=
  predecessor_excluded a [2,6,8,7,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_358 : Excluded a [2,6,8,7,0,4] :=
  branch_excluded a [2,6,8,7,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,8,7,0,4,0] (by decide +kernel))
      node_359
      (invalid_excluded a [2,6,8,7,0,4,2] (by decide +kernel))
      node_360
      (invalid_excluded a [2,6,8,7,0,4,4] (by decide +kernel))
      node_361
      (invalid_excluded a [2,6,8,7,0,4,6] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,0,4,7] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,0,4,8] (by decide +kernel)))

theorem node_355 : Excluded a [2,6,8,7,0] :=
  branch_excluded a [2,6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,6,8,7,0,0] (by decide +kernel))
      node_356
      (invalid_excluded a [2,6,8,7,0,2] (by decide +kernel))
      node_357
      node_358
      (invalid_excluded a [2,6,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,0,8] (by decide +kernel)))

theorem node_362 : Excluded a [2,6,8,7,1] :=
  predecessor_excluded a [2,6,8,7,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_364 : Excluded a [2,6,8,7,3,0] :=
  source_excluded a [2,6,8,7,3,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_365 : Excluded a [2,6,8,7,3,1] :=
  source_excluded a [2,6,8,7,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_366 : Excluded a [2,6,8,7,3,4] :=
  predecessor_excluded a [2,6,8,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_363 : Excluded a [2,6,8,7,3] :=
  branch_excluded a [2,6,8,7,3] (by decide)
    (fin9_cases _
      node_364
      node_365
      (invalid_excluded a [2,6,8,7,3,2] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,3,3] (by decide +kernel))
      node_366
      (invalid_excluded a [2,6,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,3,8] (by decide +kernel)))

theorem node_354 : Excluded a [2,6,8,7] :=
  branch_excluded a [2,6,8,7] (by decide)
    (fin9_cases _
      node_355
      node_362
      (invalid_excluded a [2,6,8,7,2] (by decide +kernel))
      node_363
      (invalid_excluded a [2,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [2,6,8,7,8] (by decide +kernel)))

theorem node_326 : Excluded a [2,6,8] :=
  branch_excluded a [2,6,8] (by decide)
    (fin9_cases _
      node_327
      node_340
      (invalid_excluded a [2,6,8,2] (by decide +kernel))
      (invalid_excluded a [2,6,8,3] (by decide +kernel))
      (invalid_excluded a [2,6,8,4] (by decide +kernel))
      node_353
      (invalid_excluded a [2,6,8,6] (by decide +kernel))
      node_354
      (invalid_excluded a [2,6,8,8] (by decide +kernel)))

theorem node_219 : Excluded a [2,6] :=
  branch_excluded a [2,6] (by decide)
    (fin9_cases _
      node_220
      node_221
      (invalid_excluded a [2,6,2] (by decide +kernel))
      (invalid_excluded a [2,6,3] (by decide +kernel))
      node_222
      node_223
      (invalid_excluded a [2,6,6] (by decide +kernel))
      node_275
      node_326)

theorem node_368 : Excluded a [2,7,0] :=
  predecessor_excluded a [2,7,0] 3 0 0 2 (by decide) (by decide +kernel)

theorem node_369 : Excluded a [2,7,1] :=
  source_excluded a [2,7,1] 0 3 2 (by decide) (by decide +kernel)

theorem node_370 : Excluded a [2,7,4] :=
  source_excluded a [2,7,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_373 : Excluded a [2,7,5,0,1] :=
  predecessor_excluded a [2,7,5,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_374 : Excluded a [2,7,5,0,3] :=
  source_excluded a [2,7,5,0,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_375 : Excluded a [2,7,5,0,6] :=
  source_excluded a [2,7,5,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_377 : Excluded a [2,7,5,0,8,1] :=
  predecessor_excluded a [2,7,5,0,8,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_378 : Excluded a [2,7,5,0,8,3] :=
  source_excluded a [2,7,5,0,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_379 : Excluded a [2,7,5,0,8,4] :=
  predecessor_excluded a [2,7,5,0,8,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_376 : Excluded a [2,7,5,0,8] :=
  branch_excluded a [2,7,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,5,0,8,0] (by decide +kernel))
      node_377
      (invalid_excluded a [2,7,5,0,8,2] (by decide +kernel))
      node_378
      node_379
      (invalid_excluded a [2,7,5,0,8,5] (by decide +kernel))
      (invalid_excluded a [2,7,5,0,8,6] (by decide +kernel))
      (invalid_excluded a [2,7,5,0,8,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,0,8,8] (by decide +kernel)))

theorem node_372 : Excluded a [2,7,5,0] :=
  branch_excluded a [2,7,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,5,0,0] (by decide +kernel))
      node_373
      (invalid_excluded a [2,7,5,0,2] (by decide +kernel))
      node_374
      (invalid_excluded a [2,7,5,0,4] (by decide +kernel))
      (invalid_excluded a [2,7,5,0,5] (by decide +kernel))
      node_375
      (invalid_excluded a [2,7,5,0,7] (by decide +kernel))
      node_376)

theorem node_381 : Excluded a [2,7,5,1,0] :=
  predecessor_excluded a [2,7,5,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_382 : Excluded a [2,7,5,1,3] :=
  source_excluded a [2,7,5,1,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_383 : Excluded a [2,7,5,1,6] :=
  source_excluded a [2,7,5,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_387 : Excluded a [2,7,5,1,8,0,3,4] :=
  source_excluded a [2,7,5,1,8,0,3,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_389 : Excluded a [2,7,5,1,8,0,3,6,4] :=
  predecessor_excluded a [2,7,5,1,8,0,3,6,4] 0 5 8 2 (by decide) (by decide +kernel)

theorem node_388 : Excluded a [2,7,5,1,8,0,3,6] :=
  branch_excluded a [2,7,5,1,8,0,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,5,1,8,0,3,6,0] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,0,3,6,1] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,0,3,6,2] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,0,3,6,3] (by decide +kernel))
      node_389
      (invalid_excluded a [2,7,5,1,8,0,3,6,5] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,0,3,6,6] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,0,3,6,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,0,3,6,8] (by decide +kernel)))

theorem node_386 : Excluded a [2,7,5,1,8,0,3] :=
  branch_excluded a [2,7,5,1,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,5,1,8,0,3,0] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,0,3,1] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,0,3,2] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,0,3,3] (by decide +kernel))
      node_387
      (invalid_excluded a [2,7,5,1,8,0,3,5] (by decide +kernel))
      node_388
      (invalid_excluded a [2,7,5,1,8,0,3,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,0,3,8] (by decide +kernel)))

theorem node_390 : Excluded a [2,7,5,1,8,0,4] :=
  predecessor_excluded a [2,7,5,1,8,0,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_385 : Excluded a [2,7,5,1,8,0] :=
  branch_excluded a [2,7,5,1,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,5,1,8,0,0] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,0,1] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,0,2] (by decide +kernel))
      node_386
      node_390
      (invalid_excluded a [2,7,5,1,8,0,5] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,0,6] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,0,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,0,8] (by decide +kernel)))

theorem node_391 : Excluded a [2,7,5,1,8,3] :=
  source_excluded a [2,7,5,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_392 : Excluded a [2,7,5,1,8,4] :=
  predecessor_excluded a [2,7,5,1,8,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_384 : Excluded a [2,7,5,1,8] :=
  branch_excluded a [2,7,5,1,8] (by decide)
    (fin9_cases _
      node_385
      (invalid_excluded a [2,7,5,1,8,1] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,2] (by decide +kernel))
      node_391
      node_392
      (invalid_excluded a [2,7,5,1,8,5] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,6] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,8,8] (by decide +kernel)))

theorem node_380 : Excluded a [2,7,5,1] :=
  branch_excluded a [2,7,5,1] (by decide)
    (fin9_cases _
      node_381
      (invalid_excluded a [2,7,5,1,1] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,2] (by decide +kernel))
      node_382
      (invalid_excluded a [2,7,5,1,4] (by decide +kernel))
      (invalid_excluded a [2,7,5,1,5] (by decide +kernel))
      node_383
      (invalid_excluded a [2,7,5,1,7] (by decide +kernel))
      node_384)

theorem node_393 : Excluded a [2,7,5,6] :=
  predecessor_excluded a [2,7,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_396 : Excluded a [2,7,5,8,0,1] :=
  predecessor_excluded a [2,7,5,8,0,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_397 : Excluded a [2,7,5,8,0,3] :=
  source_excluded a [2,7,5,8,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_398 : Excluded a [2,7,5,8,0,4] :=
  predecessor_excluded a [2,7,5,8,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_395 : Excluded a [2,7,5,8,0] :=
  branch_excluded a [2,7,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,5,8,0,0] (by decide +kernel))
      node_396
      (invalid_excluded a [2,7,5,8,0,2] (by decide +kernel))
      node_397
      node_398
      (invalid_excluded a [2,7,5,8,0,5] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,0,6] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,0,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,0,8] (by decide +kernel)))

theorem node_400 : Excluded a [2,7,5,8,1,0] :=
  predecessor_excluded a [2,7,5,8,1,0] 2 0 4 5 (by decide) (by decide +kernel)

theorem node_401 : Excluded a [2,7,5,8,1,3] :=
  source_excluded a [2,7,5,8,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_402 : Excluded a [2,7,5,8,1,4] :=
  predecessor_excluded a [2,7,5,8,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_399 : Excluded a [2,7,5,8,1] :=
  branch_excluded a [2,7,5,8,1] (by decide)
    (fin9_cases _
      node_400
      (invalid_excluded a [2,7,5,8,1,1] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,1,2] (by decide +kernel))
      node_401
      node_402
      (invalid_excluded a [2,7,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,1,6] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,1,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,1,8] (by decide +kernel)))

theorem node_403 : Excluded a [2,7,5,8,3] :=
  source_excluded a [2,7,5,8,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_404 : Excluded a [2,7,5,8,6] :=
  source_excluded a [2,7,5,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_394 : Excluded a [2,7,5,8] :=
  branch_excluded a [2,7,5,8] (by decide)
    (fin9_cases _
      node_395
      node_399
      (invalid_excluded a [2,7,5,8,2] (by decide +kernel))
      node_403
      (invalid_excluded a [2,7,5,8,4] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,5] (by decide +kernel))
      node_404
      (invalid_excluded a [2,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [2,7,5,8,8] (by decide +kernel)))

theorem node_371 : Excluded a [2,7,5] :=
  branch_excluded a [2,7,5] (by decide)
    (fin9_cases _
      node_372
      node_380
      (invalid_excluded a [2,7,5,2] (by decide +kernel))
      (invalid_excluded a [2,7,5,3] (by decide +kernel))
      (invalid_excluded a [2,7,5,4] (by decide +kernel))
      (invalid_excluded a [2,7,5,5] (by decide +kernel))
      node_393
      (invalid_excluded a [2,7,5,7] (by decide +kernel))
      node_394)

theorem node_407 : Excluded a [2,7,6,0,1] :=
  predecessor_excluded a [2,7,6,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_409 : Excluded a [2,7,6,0,3,1] :=
  predecessor_excluded a [2,7,6,0,3,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_410 : Excluded a [2,7,6,0,3,4] :=
  predecessor_excluded a [2,7,6,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_412 : Excluded a [2,7,6,0,3,8,1] :=
  source_excluded a [2,7,6,0,3,8,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_413 : Excluded a [2,7,6,0,3,8,4] :=
  predecessor_excluded a [2,7,6,0,3,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_414 : Excluded a [2,7,6,0,3,8,5] :=
  predecessor_excluded a [2,7,6,0,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_411 : Excluded a [2,7,6,0,3,8] :=
  branch_excluded a [2,7,6,0,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,0,3,8,0] (by decide +kernel))
      node_412
      (invalid_excluded a [2,7,6,0,3,8,2] (by decide +kernel))
      (invalid_excluded a [2,7,6,0,3,8,3] (by decide +kernel))
      node_413
      node_414
      (invalid_excluded a [2,7,6,0,3,8,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,0,3,8,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,0,3,8,8] (by decide +kernel)))

theorem node_408 : Excluded a [2,7,6,0,3] :=
  branch_excluded a [2,7,6,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,0,3,0] (by decide +kernel))
      node_409
      (invalid_excluded a [2,7,6,0,3,2] (by decide +kernel))
      (invalid_excluded a [2,7,6,0,3,3] (by decide +kernel))
      node_410
      (invalid_excluded a [2,7,6,0,3,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,0,3,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,0,3,7] (by decide +kernel))
      node_411)

theorem node_416 : Excluded a [2,7,6,0,8,1] :=
  predecessor_excluded a [2,7,6,0,8,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_417 : Excluded a [2,7,6,0,8,3] :=
  source_excluded a [2,7,6,0,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_419 : Excluded a [2,7,6,0,8,4,1] :=
  source_excluded a [2,7,6,0,8,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_420 : Excluded a [2,7,6,0,8,4,3] :=
  source_excluded a [2,7,6,0,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_421 : Excluded a [2,7,6,0,8,4,5] :=
  predecessor_excluded a [2,7,6,0,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_418 : Excluded a [2,7,6,0,8,4] :=
  branch_excluded a [2,7,6,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,0,8,4,0] (by decide +kernel))
      node_419
      (invalid_excluded a [2,7,6,0,8,4,2] (by decide +kernel))
      node_420
      (invalid_excluded a [2,7,6,0,8,4,4] (by decide +kernel))
      node_421
      (invalid_excluded a [2,7,6,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,0,8,4,8] (by decide +kernel)))

theorem node_415 : Excluded a [2,7,6,0,8] :=
  branch_excluded a [2,7,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,0,8,0] (by decide +kernel))
      node_416
      (invalid_excluded a [2,7,6,0,8,2] (by decide +kernel))
      node_417
      node_418
      (invalid_excluded a [2,7,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,0,8,8] (by decide +kernel)))

theorem node_406 : Excluded a [2,7,6,0] :=
  branch_excluded a [2,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,0,0] (by decide +kernel))
      node_407
      (invalid_excluded a [2,7,6,0,2] (by decide +kernel))
      node_408
      (invalid_excluded a [2,7,6,0,4] (by decide +kernel))
      (invalid_excluded a [2,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,0,7] (by decide +kernel))
      node_415)

theorem node_423 : Excluded a [2,7,6,1,0] :=
  predecessor_excluded a [2,7,6,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_426 : Excluded a [2,7,6,1,3,0,4] :=
  predecessor_excluded a [2,7,6,1,3,0,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_428 : Excluded a [2,7,6,1,3,0,5,4] :=
  branch_excluded a [2,7,6,1,3,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,1,3,0,5,4,0] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,5,4,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,5,4,2] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,5,4,3] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,5,4,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,5,4,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,5,4,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,5,4,8] (by decide +kernel)))

theorem node_427 : Excluded a [2,7,6,1,3,0,5] :=
  branch_excluded a [2,7,6,1,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,1,3,0,5,0] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,5,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,5,2] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,5,3] (by decide +kernel))
      node_428
      (invalid_excluded a [2,7,6,1,3,0,5,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,5,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,5,8] (by decide +kernel)))

theorem node_429 : Excluded a [2,7,6,1,3,0,8] :=
  source_excluded a [2,7,6,1,3,0,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_425 : Excluded a [2,7,6,1,3,0] :=
  branch_excluded a [2,7,6,1,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,1,3,0,0] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,2] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,3] (by decide +kernel))
      node_426
      node_427
      (invalid_excluded a [2,7,6,1,3,0,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,0,7] (by decide +kernel))
      node_429)

theorem node_430 : Excluded a [2,7,6,1,3,4] :=
  predecessor_excluded a [2,7,6,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_432 : Excluded a [2,7,6,1,3,8,0] :=
  source_excluded a [2,7,6,1,3,8,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_433 : Excluded a [2,7,6,1,3,8,4] :=
  predecessor_excluded a [2,7,6,1,3,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_434 : Excluded a [2,7,6,1,3,8,5] :=
  predecessor_excluded a [2,7,6,1,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_431 : Excluded a [2,7,6,1,3,8] :=
  branch_excluded a [2,7,6,1,3,8] (by decide)
    (fin9_cases _
      node_432
      (invalid_excluded a [2,7,6,1,3,8,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,8,2] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,8,3] (by decide +kernel))
      node_433
      node_434
      (invalid_excluded a [2,7,6,1,3,8,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,8,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,8,8] (by decide +kernel)))

theorem node_424 : Excluded a [2,7,6,1,3] :=
  branch_excluded a [2,7,6,1,3] (by decide)
    (fin9_cases _
      node_425
      (invalid_excluded a [2,7,6,1,3,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,2] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,3] (by decide +kernel))
      node_430
      (invalid_excluded a [2,7,6,1,3,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,3,7] (by decide +kernel))
      node_431)

theorem node_437 : Excluded a [2,7,6,1,8,0,3] :=
  source_excluded a [2,7,6,1,8,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_438 : Excluded a [2,7,6,1,8,0,4] :=
  predecessor_excluded a [2,7,6,1,8,0,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_441 : Excluded a [2,7,6,1,8,0,5,3,4] :=
  predecessor_excluded a [2,7,6,1,8,0,5,3,4] 0 4 7 8 (by decide) (by decide +kernel)

theorem node_440 : Excluded a [2,7,6,1,8,0,5,3] :=
  branch_excluded a [2,7,6,1,8,0,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,1,8,0,5,3,0] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,3,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,3,2] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,3,3] (by decide +kernel))
      node_441
      (invalid_excluded a [2,7,6,1,8,0,5,3,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,3,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,3,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,3,8] (by decide +kernel)))

theorem node_442 : Excluded a [2,7,6,1,8,0,5,4] :=
  source_excluded a [2,7,6,1,8,0,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_439 : Excluded a [2,7,6,1,8,0,5] :=
  branch_excluded a [2,7,6,1,8,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,1,8,0,5,0] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,2] (by decide +kernel))
      node_440
      node_442
      (invalid_excluded a [2,7,6,1,8,0,5,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,5,8] (by decide +kernel)))

theorem node_436 : Excluded a [2,7,6,1,8,0] :=
  branch_excluded a [2,7,6,1,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,1,8,0,0] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,2] (by decide +kernel))
      node_437
      node_438
      node_439
      (invalid_excluded a [2,7,6,1,8,0,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,0,8] (by decide +kernel)))

theorem node_443 : Excluded a [2,7,6,1,8,3] :=
  source_excluded a [2,7,6,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_445 : Excluded a [2,7,6,1,8,4,0] :=
  source_excluded a [2,7,6,1,8,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_446 : Excluded a [2,7,6,1,8,4,3] :=
  source_excluded a [2,7,6,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_447 : Excluded a [2,7,6,1,8,4,5] :=
  predecessor_excluded a [2,7,6,1,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_444 : Excluded a [2,7,6,1,8,4] :=
  branch_excluded a [2,7,6,1,8,4] (by decide)
    (fin9_cases _
      node_445
      (invalid_excluded a [2,7,6,1,8,4,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,2] (by decide +kernel))
      node_446
      (invalid_excluded a [2,7,6,1,8,4,4] (by decide +kernel))
      node_447
      (invalid_excluded a [2,7,6,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,4,8] (by decide +kernel)))

theorem node_435 : Excluded a [2,7,6,1,8] :=
  branch_excluded a [2,7,6,1,8] (by decide)
    (fin9_cases _
      node_436
      (invalid_excluded a [2,7,6,1,8,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,2] (by decide +kernel))
      node_443
      node_444
      (invalid_excluded a [2,7,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,8,8] (by decide +kernel)))

theorem node_422 : Excluded a [2,7,6,1] :=
  branch_excluded a [2,7,6,1] (by decide)
    (fin9_cases _
      node_423
      (invalid_excluded a [2,7,6,1,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,2] (by decide +kernel))
      node_424
      (invalid_excluded a [2,7,6,1,4] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,1,7] (by decide +kernel))
      node_435)

theorem node_448 : Excluded a [2,7,6,5] :=
  source_excluded a [2,7,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_451 : Excluded a [2,7,6,8,0,1] :=
  predecessor_excluded a [2,7,6,8,0,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_452 : Excluded a [2,7,6,8,0,3] :=
  source_excluded a [2,7,6,8,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_454 : Excluded a [2,7,6,8,0,4,1] :=
  source_excluded a [2,7,6,8,0,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_455 : Excluded a [2,7,6,8,0,4,3] :=
  source_excluded a [2,7,6,8,0,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_456 : Excluded a [2,7,6,8,0,4,5] :=
  predecessor_excluded a [2,7,6,8,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_453 : Excluded a [2,7,6,8,0,4] :=
  branch_excluded a [2,7,6,8,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,8,0,4,0] (by decide +kernel))
      node_454
      (invalid_excluded a [2,7,6,8,0,4,2] (by decide +kernel))
      node_455
      (invalid_excluded a [2,7,6,8,0,4,4] (by decide +kernel))
      node_456
      (invalid_excluded a [2,7,6,8,0,4,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,0,4,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,0,4,8] (by decide +kernel)))

theorem node_450 : Excluded a [2,7,6,8,0] :=
  branch_excluded a [2,7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,8,0,0] (by decide +kernel))
      node_451
      (invalid_excluded a [2,7,6,8,0,2] (by decide +kernel))
      node_452
      node_453
      (invalid_excluded a [2,7,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,0,8] (by decide +kernel)))

theorem node_458 : Excluded a [2,7,6,8,1,0] :=
  predecessor_excluded a [2,7,6,8,1,0] 2 0 4 5 (by decide) (by decide +kernel)

theorem node_459 : Excluded a [2,7,6,8,1,3] :=
  source_excluded a [2,7,6,8,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_461 : Excluded a [2,7,6,8,1,4,0] :=
  source_excluded a [2,7,6,8,1,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_462 : Excluded a [2,7,6,8,1,4,3] :=
  source_excluded a [2,7,6,8,1,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_463 : Excluded a [2,7,6,8,1,4,5] :=
  predecessor_excluded a [2,7,6,8,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_460 : Excluded a [2,7,6,8,1,4] :=
  branch_excluded a [2,7,6,8,1,4] (by decide)
    (fin9_cases _
      node_461
      (invalid_excluded a [2,7,6,8,1,4,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,1,4,2] (by decide +kernel))
      node_462
      (invalid_excluded a [2,7,6,8,1,4,4] (by decide +kernel))
      node_463
      (invalid_excluded a [2,7,6,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,1,4,8] (by decide +kernel)))

theorem node_457 : Excluded a [2,7,6,8,1] :=
  branch_excluded a [2,7,6,8,1] (by decide)
    (fin9_cases _
      node_458
      (invalid_excluded a [2,7,6,8,1,1] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,1,2] (by decide +kernel))
      node_459
      node_460
      (invalid_excluded a [2,7,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,1,8] (by decide +kernel)))

theorem node_466 : Excluded a [2,7,6,8,3,0,1] :=
  source_excluded a [2,7,6,8,3,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_467 : Excluded a [2,7,6,8,3,0,4] :=
  predecessor_excluded a [2,7,6,8,3,0,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_469 : Excluded a [2,7,6,8,3,0,5,1] :=
  predecessor_excluded a [2,7,6,8,3,0,5,1] 2 1 1 7 (by decide) (by decide +kernel)

theorem node_470 : Excluded a [2,7,6,8,3,0,5,4] :=
  source_excluded a [2,7,6,8,3,0,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_468 : Excluded a [2,7,6,8,3,0,5] :=
  branch_excluded a [2,7,6,8,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,8,3,0,5,0] (by decide +kernel))
      node_469
      (invalid_excluded a [2,7,6,8,3,0,5,2] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,3,0,5,3] (by decide +kernel))
      node_470
      (invalid_excluded a [2,7,6,8,3,0,5,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,3,0,5,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,3,0,5,8] (by decide +kernel)))

theorem node_465 : Excluded a [2,7,6,8,3,0] :=
  branch_excluded a [2,7,6,8,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,6,8,3,0,0] (by decide +kernel))
      node_466
      (invalid_excluded a [2,7,6,8,3,0,2] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,3,0,3] (by decide +kernel))
      node_467
      node_468
      (invalid_excluded a [2,7,6,8,3,0,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,3,0,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,3,0,8] (by decide +kernel)))

theorem node_471 : Excluded a [2,7,6,8,3,1] :=
  predecessor_excluded a [2,7,6,8,3,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_472 : Excluded a [2,7,6,8,3,4] :=
  predecessor_excluded a [2,7,6,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_464 : Excluded a [2,7,6,8,3] :=
  branch_excluded a [2,7,6,8,3] (by decide)
    (fin9_cases _
      node_465
      node_471
      (invalid_excluded a [2,7,6,8,3,2] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,3,3] (by decide +kernel))
      node_472
      (invalid_excluded a [2,7,6,8,3,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,3,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,3,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,3,8] (by decide +kernel)))

theorem node_449 : Excluded a [2,7,6,8] :=
  branch_excluded a [2,7,6,8] (by decide)
    (fin9_cases _
      node_450
      node_457
      (invalid_excluded a [2,7,6,8,2] (by decide +kernel))
      node_464
      (invalid_excluded a [2,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [2,7,6,8,8] (by decide +kernel)))

theorem node_405 : Excluded a [2,7,6] :=
  branch_excluded a [2,7,6] (by decide)
    (fin9_cases _
      node_406
      node_422
      (invalid_excluded a [2,7,6,2] (by decide +kernel))
      (invalid_excluded a [2,7,6,3] (by decide +kernel))
      (invalid_excluded a [2,7,6,4] (by decide +kernel))
      node_448
      (invalid_excluded a [2,7,6,6] (by decide +kernel))
      (invalid_excluded a [2,7,6,7] (by decide +kernel))
      node_449)

theorem node_475 : Excluded a [2,7,8,0,1] :=
  predecessor_excluded a [2,7,8,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_477 : Excluded a [2,7,8,0,3,1] :=
  predecessor_excluded a [2,7,8,0,3,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_478 : Excluded a [2,7,8,0,3,4] :=
  predecessor_excluded a [2,7,8,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_476 : Excluded a [2,7,8,0,3] :=
  branch_excluded a [2,7,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,0,3,0] (by decide +kernel))
      node_477
      (invalid_excluded a [2,7,8,0,3,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,0,3,3] (by decide +kernel))
      node_478
      (invalid_excluded a [2,7,8,0,3,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,0,3,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,0,3,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,0,3,8] (by decide +kernel)))

theorem node_479 : Excluded a [2,7,8,0,6] :=
  source_excluded a [2,7,8,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_474 : Excluded a [2,7,8,0] :=
  branch_excluded a [2,7,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,0,0] (by decide +kernel))
      node_475
      (invalid_excluded a [2,7,8,0,2] (by decide +kernel))
      node_476
      (invalid_excluded a [2,7,8,0,4] (by decide +kernel))
      (invalid_excluded a [2,7,8,0,5] (by decide +kernel))
      node_479
      (invalid_excluded a [2,7,8,0,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,0,8] (by decide +kernel)))

theorem node_481 : Excluded a [2,7,8,1,0] :=
  predecessor_excluded a [2,7,8,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_485 : Excluded a [2,7,8,1,3,0,4,5] :=
  predecessor_excluded a [2,7,8,1,3,0,4,5] 0 5 6 7 (by decide) (by decide +kernel)

def b_487 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 7
  | 2 => 8
  | 3 => 1
  | 4 => 3
  | 5 => 0
  | 6 => 4
  | 7 => 6
  | 8 => 5
  | _ => 0

def cert_487 : LosingRegion (edgeOf a b_487) 0 :=
  losingMask a b_487 0 1286514411582720882770944
    (by decide +kernel) (by decide +kernel)

theorem node_487 : Excluded a [2,7,8,1,3,0,4,6,5] :=
  losing_excluded a [2,7,8,1,3,0,4,6,5] (by decide) b_487 (by decide +kernel) 2 0 3 cert_487 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_487 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1286514411582720882770944 2 3; decide +kernel)

theorem node_486 : Excluded a [2,7,8,1,3,0,4,6] :=
  branch_excluded a [2,7,8,1,3,0,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,1,3,0,4,6,0] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,4,6,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,4,6,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,4,6,3] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,4,6,4] (by decide +kernel))
      node_487
      (invalid_excluded a [2,7,8,1,3,0,4,6,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,4,6,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,4,6,8] (by decide +kernel)))

theorem node_484 : Excluded a [2,7,8,1,3,0,4] :=
  branch_excluded a [2,7,8,1,3,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,1,3,0,4,0] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,4,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,4,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,4,3] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,4,4] (by decide +kernel))
      node_485
      node_486
      (invalid_excluded a [2,7,8,1,3,0,4,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,4,8] (by decide +kernel)))

def b_490 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 7
  | 2 => 8
  | 3 => 1
  | 4 => 3
  | 5 => 0
  | 6 => 5
  | 7 => 4
  | 8 => 6
  | _ => 0

def cert_490 : LosingRegion (edgeOf a b_490) 0 :=
  losingMask a b_490 0 1928128919839298431222784
    (by decide +kernel) (by decide +kernel)

theorem node_490 : Excluded a [2,7,8,1,3,0,5,4,6] :=
  losing_excluded a [2,7,8,1,3,0,5,4,6] (by decide) b_490 (by decide +kernel) 2 0 3 cert_490 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_490 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1928128919839298431222784 2 3; decide +kernel)

theorem node_489 : Excluded a [2,7,8,1,3,0,5,4] :=
  branch_excluded a [2,7,8,1,3,0,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,1,3,0,5,4,0] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,5,4,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,5,4,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,5,4,3] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,5,4,4] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,5,4,5] (by decide +kernel))
      node_490
      (invalid_excluded a [2,7,8,1,3,0,5,4,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,5,4,8] (by decide +kernel)))

theorem node_491 : Excluded a [2,7,8,1,3,0,5,6] :=
  predecessor_excluded a [2,7,8,1,3,0,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_488 : Excluded a [2,7,8,1,3,0,5] :=
  branch_excluded a [2,7,8,1,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,1,3,0,5,0] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,5,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,5,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,5,3] (by decide +kernel))
      node_489
      (invalid_excluded a [2,7,8,1,3,0,5,5] (by decide +kernel))
      node_491
      (invalid_excluded a [2,7,8,1,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,5,8] (by decide +kernel)))

theorem node_483 : Excluded a [2,7,8,1,3,0] :=
  branch_excluded a [2,7,8,1,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,1,3,0,0] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,3] (by decide +kernel))
      node_484
      node_488
      (invalid_excluded a [2,7,8,1,3,0,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,0,8] (by decide +kernel)))

theorem node_492 : Excluded a [2,7,8,1,3,4] :=
  predecessor_excluded a [2,7,8,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_482 : Excluded a [2,7,8,1,3] :=
  branch_excluded a [2,7,8,1,3] (by decide)
    (fin9_cases _
      node_483
      (invalid_excluded a [2,7,8,1,3,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,3] (by decide +kernel))
      node_492
      (invalid_excluded a [2,7,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,3,8] (by decide +kernel)))

theorem node_493 : Excluded a [2,7,8,1,6] :=
  source_excluded a [2,7,8,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_480 : Excluded a [2,7,8,1] :=
  branch_excluded a [2,7,8,1] (by decide)
    (fin9_cases _
      node_481
      (invalid_excluded a [2,7,8,1,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,2] (by decide +kernel))
      node_482
      (invalid_excluded a [2,7,8,1,4] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,5] (by decide +kernel))
      node_493
      (invalid_excluded a [2,7,8,1,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,1,8] (by decide +kernel)))

theorem node_494 : Excluded a [2,7,8,5] :=
  source_excluded a [2,7,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_497 : Excluded a [2,7,8,6,0,1] :=
  predecessor_excluded a [2,7,8,6,0,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_498 : Excluded a [2,7,8,6,0,3] :=
  source_excluded a [2,7,8,6,0,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_499 : Excluded a [2,7,8,6,0,4] :=
  source_excluded a [2,7,8,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_496 : Excluded a [2,7,8,6,0] :=
  branch_excluded a [2,7,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,7,8,6,0,0] (by decide +kernel))
      node_497
      (invalid_excluded a [2,7,8,6,0,2] (by decide +kernel))
      node_498
      node_499
      (invalid_excluded a [2,7,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,0,8] (by decide +kernel)))

theorem node_501 : Excluded a [2,7,8,6,1,0] :=
  predecessor_excluded a [2,7,8,6,1,0] 2 0 4 5 (by decide) (by decide +kernel)

theorem node_502 : Excluded a [2,7,8,6,1,3] :=
  source_excluded a [2,7,8,6,1,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_503 : Excluded a [2,7,8,6,1,4] :=
  source_excluded a [2,7,8,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_500 : Excluded a [2,7,8,6,1] :=
  branch_excluded a [2,7,8,6,1] (by decide)
    (fin9_cases _
      node_501
      (invalid_excluded a [2,7,8,6,1,1] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,1,2] (by decide +kernel))
      node_502
      node_503
      (invalid_excluded a [2,7,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,1,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,1,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,1,8] (by decide +kernel)))

theorem node_504 : Excluded a [2,7,8,6,3] :=
  predecessor_excluded a [2,7,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_495 : Excluded a [2,7,8,6] :=
  branch_excluded a [2,7,8,6] (by decide)
    (fin9_cases _
      node_496
      node_500
      (invalid_excluded a [2,7,8,6,2] (by decide +kernel))
      node_504
      (invalid_excluded a [2,7,8,6,4] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,5] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,6] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,6,8] (by decide +kernel)))

theorem node_473 : Excluded a [2,7,8] :=
  branch_excluded a [2,7,8] (by decide)
    (fin9_cases _
      node_474
      node_480
      (invalid_excluded a [2,7,8,2] (by decide +kernel))
      (invalid_excluded a [2,7,8,3] (by decide +kernel))
      (invalid_excluded a [2,7,8,4] (by decide +kernel))
      node_494
      node_495
      (invalid_excluded a [2,7,8,7] (by decide +kernel))
      (invalid_excluded a [2,7,8,8] (by decide +kernel)))

theorem node_367 : Excluded a [2,7] :=
  branch_excluded a [2,7] (by decide)
    (fin9_cases _
      node_368
      node_369
      (invalid_excluded a [2,7,2] (by decide +kernel))
      (invalid_excluded a [2,7,3] (by decide +kernel))
      node_370
      node_371
      node_405
      (invalid_excluded a [2,7,7] (by decide +kernel))
      node_473)

theorem node_505 : Excluded a [2,8] :=
  predecessor_excluded a [2,8] 3 2 1 0 (by decide) (by decide +kernel)

theorem node_2 : Excluded a [2] :=
  branch_excluded a [2] (by decide)
    (fin9_cases _
      (invalid_excluded a [2,0] (by decide +kernel))
      (invalid_excluded a [2,1] (by decide +kernel))
      (invalid_excluded a [2,2] (by decide +kernel))
      node_3
      node_4
      node_103
      node_219
      node_367
      node_505)

theorem node_507 : Excluded a [3,2] :=
  predecessor_excluded a [3,2] 4 3 1 0 (by decide) (by decide +kernel)

theorem node_508 : Excluded a [3,4] :=
  predecessor_excluded a [3,4] 2 4 0 1 (by decide) (by decide +kernel)

theorem node_510 : Excluded a [3,5,0] :=
  source_excluded a [3,5,0] 2 1 0 (by decide) (by decide +kernel)

theorem node_511 : Excluded a [3,5,1] :=
  source_excluded a [3,5,1] 0 2 2 (by decide) (by decide +kernel)

theorem node_512 : Excluded a [3,5,4] :=
  source_excluded a [3,5,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_514 : Excluded a [3,5,6,0] :=
  predecessor_excluded a [3,5,6,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_515 : Excluded a [3,5,6,1] :=
  source_excluded a [3,5,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_517 : Excluded a [3,5,6,2,0] :=
  source_excluded a [3,5,6,2,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_518 : Excluded a [3,5,6,2,1] :=
  source_excluded a [3,5,6,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_520 : Excluded a [3,5,6,2,7,0] :=
  source_excluded a [3,5,6,2,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_521 : Excluded a [3,5,6,2,7,1] :=
  predecessor_excluded a [3,5,6,2,7,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_522 : Excluded a [3,5,6,2,7,4] :=
  predecessor_excluded a [3,5,6,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_523 : Excluded a [3,5,6,2,7,8] :=
  predecessor_excluded a [3,5,6,2,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_519 : Excluded a [3,5,6,2,7] :=
  branch_excluded a [3,5,6,2,7] (by decide)
    (fin9_cases _
      node_520
      node_521
      (invalid_excluded a [3,5,6,2,7,2] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,7,3] (by decide +kernel))
      node_522
      (invalid_excluded a [3,5,6,2,7,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,7,6] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,7,7] (by decide +kernel))
      node_523)

theorem node_525 : Excluded a [3,5,6,2,8,0] :=
  source_excluded a [3,5,6,2,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_526 : Excluded a [3,5,6,2,8,1] :=
  predecessor_excluded a [3,5,6,2,8,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_529 : Excluded a [3,5,6,2,8,4,0,1] :=
  predecessor_excluded a [3,5,6,2,8,4,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_528 : Excluded a [3,5,6,2,8,4,0] :=
  branch_excluded a [3,5,6,2,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,6,2,8,4,0,0] (by decide +kernel))
      node_529
      (invalid_excluded a [3,5,6,2,8,4,0,2] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,0,8] (by decide +kernel)))

theorem node_531 : Excluded a [3,5,6,2,8,4,1,0] :=
  predecessor_excluded a [3,5,6,2,8,4,1,0] 2 0 6 7 (by decide) (by decide +kernel)

theorem node_530 : Excluded a [3,5,6,2,8,4,1] :=
  branch_excluded a [3,5,6,2,8,4,1] (by decide)
    (fin9_cases _
      node_531
      (invalid_excluded a [3,5,6,2,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,1,2] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,1,3] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,1,8] (by decide +kernel)))

theorem node_527 : Excluded a [3,5,6,2,8,4] :=
  branch_excluded a [3,5,6,2,8,4] (by decide)
    (fin9_cases _
      node_528
      node_530
      (invalid_excluded a [3,5,6,2,8,4,2] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,3] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,4,8] (by decide +kernel)))

theorem node_532 : Excluded a [3,5,6,2,8,7] :=
  source_excluded a [3,5,6,2,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_524 : Excluded a [3,5,6,2,8] :=
  branch_excluded a [3,5,6,2,8] (by decide)
    (fin9_cases _
      node_525
      node_526
      (invalid_excluded a [3,5,6,2,8,2] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,3] (by decide +kernel))
      node_527
      (invalid_excluded a [3,5,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,8,6] (by decide +kernel))
      node_532
      (invalid_excluded a [3,5,6,2,8,8] (by decide +kernel)))

theorem node_516 : Excluded a [3,5,6,2] :=
  branch_excluded a [3,5,6,2] (by decide)
    (fin9_cases _
      node_517
      node_518
      (invalid_excluded a [3,5,6,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,3] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,4] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,2,6] (by decide +kernel))
      node_519
      node_524)

theorem node_533 : Excluded a [3,5,6,7] :=
  predecessor_excluded a [3,5,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_535 : Excluded a [3,5,6,8,0] :=
  source_excluded a [3,5,6,8,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_536 : Excluded a [3,5,6,8,1] :=
  source_excluded a [3,5,6,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_537 : Excluded a [3,5,6,8,2] :=
  predecessor_excluded a [3,5,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_539 : Excluded a [3,5,6,8,7,0] :=
  source_excluded a [3,5,6,8,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_540 : Excluded a [3,5,6,8,7,1] :=
  predecessor_excluded a [3,5,6,8,7,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_541 : Excluded a [3,5,6,8,7,2] :=
  source_excluded a [3,5,6,8,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_542 : Excluded a [3,5,6,8,7,4] :=
  predecessor_excluded a [3,5,6,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_538 : Excluded a [3,5,6,8,7] :=
  branch_excluded a [3,5,6,8,7] (by decide)
    (fin9_cases _
      node_539
      node_540
      node_541
      (invalid_excluded a [3,5,6,8,7,3] (by decide +kernel))
      node_542
      (invalid_excluded a [3,5,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,7,8] (by decide +kernel)))

theorem node_534 : Excluded a [3,5,6,8] :=
  branch_excluded a [3,5,6,8] (by decide)
    (fin9_cases _
      node_535
      node_536
      node_537
      (invalid_excluded a [3,5,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,4] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,8,6] (by decide +kernel))
      node_538
      (invalid_excluded a [3,5,6,8,8] (by decide +kernel)))

theorem node_513 : Excluded a [3,5,6] :=
  branch_excluded a [3,5,6] (by decide)
    (fin9_cases _
      node_514
      node_515
      node_516
      (invalid_excluded a [3,5,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,6,6] (by decide +kernel))
      node_533
      node_534)

theorem node_544 : Excluded a [3,5,7,0] :=
  predecessor_excluded a [3,5,7,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_545 : Excluded a [3,5,7,1] :=
  source_excluded a [3,5,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_547 : Excluded a [3,5,7,2,0] :=
  source_excluded a [3,5,7,2,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_548 : Excluded a [3,5,7,2,1] :=
  source_excluded a [3,5,7,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_549 : Excluded a [3,5,7,2,6] :=
  source_excluded a [3,5,7,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_551 : Excluded a [3,5,7,2,8,0] :=
  source_excluded a [3,5,7,2,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_552 : Excluded a [3,5,7,2,8,1] :=
  predecessor_excluded a [3,5,7,2,8,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_555 : Excluded a [3,5,7,2,8,4,0,1] :=
  predecessor_excluded a [3,5,7,2,8,4,0,1] 2 1 6 7 (by decide) (by decide +kernel)

def b_557 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 7
  | 3 => 2
  | 4 => 8
  | 5 => 4
  | 6 => 0
  | 7 => 6
  | 8 => 1
  | _ => 0

def cert_557 : LosingRegion (edgeOf a b_557) 0 :=
  losingMask a b_557 0 1210107572048077872169984
    (by decide +kernel) (by decide +kernel)

theorem node_557 : Excluded a [3,5,7,2,8,4,0,6,1] :=
  losing_excluded a [3,5,7,2,8,4,0,6,1] (by decide) b_557 (by decide +kernel) 2 0 6 cert_557 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_557 2 0 ∧ 6 ≠ 2 ∧ maskRegion 1210107572048077872169984 2 6; decide +kernel)

theorem node_556 : Excluded a [3,5,7,2,8,4,0,6] :=
  branch_excluded a [3,5,7,2,8,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,2,8,4,0,6,0] (by decide +kernel))
      node_557
      (invalid_excluded a [3,5,7,2,8,4,0,6,2] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,0,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,0,6,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,0,6,8] (by decide +kernel)))

theorem node_554 : Excluded a [3,5,7,2,8,4,0] :=
  branch_excluded a [3,5,7,2,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,2,8,4,0,0] (by decide +kernel))
      node_555
      (invalid_excluded a [3,5,7,2,8,4,0,2] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,0,5] (by decide +kernel))
      node_556
      (invalid_excluded a [3,5,7,2,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,0,8] (by decide +kernel)))

theorem node_559 : Excluded a [3,5,7,2,8,4,1,0] :=
  predecessor_excluded a [3,5,7,2,8,4,1,0] 2 0 6 7 (by decide) (by decide +kernel)

theorem node_561 : Excluded a [3,5,7,2,8,4,1,6,0] :=
  predecessor_excluded a [3,5,7,2,8,4,1,6,0] 1 3 8 0 (by decide) (by decide +kernel)

theorem node_560 : Excluded a [3,5,7,2,8,4,1,6] :=
  branch_excluded a [3,5,7,2,8,4,1,6] (by decide)
    (fin9_cases _
      node_561
      (invalid_excluded a [3,5,7,2,8,4,1,6,1] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,1,6,2] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,1,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,1,6,8] (by decide +kernel)))

theorem node_558 : Excluded a [3,5,7,2,8,4,1] :=
  branch_excluded a [3,5,7,2,8,4,1] (by decide)
    (fin9_cases _
      node_559
      (invalid_excluded a [3,5,7,2,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,1,2] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,1,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,1,5] (by decide +kernel))
      node_560
      (invalid_excluded a [3,5,7,2,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,1,8] (by decide +kernel)))

theorem node_553 : Excluded a [3,5,7,2,8,4] :=
  branch_excluded a [3,5,7,2,8,4] (by decide)
    (fin9_cases _
      node_554
      node_558
      (invalid_excluded a [3,5,7,2,8,4,2] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,4,8] (by decide +kernel)))

theorem node_550 : Excluded a [3,5,7,2,8] :=
  branch_excluded a [3,5,7,2,8] (by decide)
    (fin9_cases _
      node_551
      node_552
      (invalid_excluded a [3,5,7,2,8,2] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,3] (by decide +kernel))
      node_553
      (invalid_excluded a [3,5,7,2,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,8,8] (by decide +kernel)))

theorem node_546 : Excluded a [3,5,7,2] :=
  branch_excluded a [3,5,7,2] (by decide)
    (fin9_cases _
      node_547
      node_548
      (invalid_excluded a [3,5,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,2,5] (by decide +kernel))
      node_549
      (invalid_excluded a [3,5,7,2,7] (by decide +kernel))
      node_550)

theorem node_563 : Excluded a [3,5,7,6,0] :=
  source_excluded a [3,5,7,6,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_564 : Excluded a [3,5,7,6,1] :=
  source_excluded a [3,5,7,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_566 : Excluded a [3,5,7,6,2,0] :=
  source_excluded a [3,5,7,6,2,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_567 : Excluded a [3,5,7,6,2,1] :=
  predecessor_excluded a [3,5,7,6,2,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_568 : Excluded a [3,5,7,6,2,4] :=
  source_excluded a [3,5,7,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_571 : Excluded a [3,5,7,6,2,8,0,1] :=
  predecessor_excluded a [3,5,7,6,2,8,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_572 : Excluded a [3,5,7,6,2,8,0,4] :=
  predecessor_excluded a [3,5,7,6,2,8,0,4] 0 2 7 4 (by decide) (by decide +kernel)

theorem node_570 : Excluded a [3,5,7,6,2,8,0] :=
  branch_excluded a [3,5,7,6,2,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,7,6,2,8,0,0] (by decide +kernel))
      node_571
      (invalid_excluded a [3,5,7,6,2,8,0,2] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,2,8,0,3] (by decide +kernel))
      node_572
      (invalid_excluded a [3,5,7,6,2,8,0,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,2,8,0,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,2,8,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,2,8,0,8] (by decide +kernel)))

theorem node_574 : Excluded a [3,5,7,6,2,8,1,0] :=
  predecessor_excluded a [3,5,7,6,2,8,1,0] 2 0 6 7 (by decide) (by decide +kernel)

theorem node_575 : Excluded a [3,5,7,6,2,8,1,4] :=
  predecessor_excluded a [3,5,7,6,2,8,1,4] 0 2 7 4 (by decide) (by decide +kernel)

theorem node_573 : Excluded a [3,5,7,6,2,8,1] :=
  branch_excluded a [3,5,7,6,2,8,1] (by decide)
    (fin9_cases _
      node_574
      (invalid_excluded a [3,5,7,6,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,2,8,1,2] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,2,8,1,3] (by decide +kernel))
      node_575
      (invalid_excluded a [3,5,7,6,2,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,2,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,2,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,2,8,1,8] (by decide +kernel)))

theorem node_576 : Excluded a [3,5,7,6,2,8,4] :=
  source_excluded a [3,5,7,6,2,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_569 : Excluded a [3,5,7,6,2,8] :=
  branch_excluded a [3,5,7,6,2,8] (by decide)
    (fin9_cases _
      node_570
      node_573
      (invalid_excluded a [3,5,7,6,2,8,2] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,2,8,3] (by decide +kernel))
      node_576
      (invalid_excluded a [3,5,7,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,2,8,8] (by decide +kernel)))

theorem node_565 : Excluded a [3,5,7,6,2] :=
  branch_excluded a [3,5,7,6,2] (by decide)
    (fin9_cases _
      node_566
      node_567
      (invalid_excluded a [3,5,7,6,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,2,3] (by decide +kernel))
      node_568
      (invalid_excluded a [3,5,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,2,7] (by decide +kernel))
      node_569)

theorem node_578 : Excluded a [3,5,7,6,8,0] :=
  source_excluded a [3,5,7,6,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_579 : Excluded a [3,5,7,6,8,1] :=
  predecessor_excluded a [3,5,7,6,8,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_580 : Excluded a [3,5,7,6,8,2] :=
  predecessor_excluded a [3,5,7,6,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_581 : Excluded a [3,5,7,6,8,4] :=
  source_excluded a [3,5,7,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_577 : Excluded a [3,5,7,6,8] :=
  branch_excluded a [3,5,7,6,8] (by decide)
    (fin9_cases _
      node_578
      node_579
      node_580
      (invalid_excluded a [3,5,7,6,8,3] (by decide +kernel))
      node_581
      (invalid_excluded a [3,5,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,8,8] (by decide +kernel)))

theorem node_562 : Excluded a [3,5,7,6] :=
  branch_excluded a [3,5,7,6] (by decide)
    (fin9_cases _
      node_563
      node_564
      node_565
      (invalid_excluded a [3,5,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,7,6,7] (by decide +kernel))
      node_577)

theorem node_582 : Excluded a [3,5,7,8] :=
  predecessor_excluded a [3,5,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_543 : Excluded a [3,5,7] :=
  branch_excluded a [3,5,7] (by decide)
    (fin9_cases _
      node_544
      node_545
      node_546
      (invalid_excluded a [3,5,7,3] (by decide +kernel))
      (invalid_excluded a [3,5,7,4] (by decide +kernel))
      (invalid_excluded a [3,5,7,5] (by decide +kernel))
      node_562
      (invalid_excluded a [3,5,7,7] (by decide +kernel))
      node_582)

theorem node_584 : Excluded a [3,5,8,0] :=
  predecessor_excluded a [3,5,8,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_585 : Excluded a [3,5,8,1] :=
  source_excluded a [3,5,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_586 : Excluded a [3,5,8,2] :=
  predecessor_excluded a [3,5,8,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_588 : Excluded a [3,5,8,6,0] :=
  source_excluded a [3,5,8,6,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_589 : Excluded a [3,5,8,6,1] :=
  source_excluded a [3,5,8,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_591 : Excluded a [3,5,8,6,2,0] :=
  source_excluded a [3,5,8,6,2,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_592 : Excluded a [3,5,8,6,2,1] :=
  predecessor_excluded a [3,5,8,6,2,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_593 : Excluded a [3,5,8,6,2,4] :=
  source_excluded a [3,5,8,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_594 : Excluded a [3,5,8,6,2,7] :=
  source_excluded a [3,5,8,6,2,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_590 : Excluded a [3,5,8,6,2] :=
  branch_excluded a [3,5,8,6,2] (by decide)
    (fin9_cases _
      node_591
      node_592
      (invalid_excluded a [3,5,8,6,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,2,3] (by decide +kernel))
      node_593
      (invalid_excluded a [3,5,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,2,6] (by decide +kernel))
      node_594
      (invalid_excluded a [3,5,8,6,2,8] (by decide +kernel)))

theorem node_595 : Excluded a [3,5,8,6,7] :=
  predecessor_excluded a [3,5,8,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_587 : Excluded a [3,5,8,6] :=
  branch_excluded a [3,5,8,6] (by decide)
    (fin9_cases _
      node_588
      node_589
      node_590
      (invalid_excluded a [3,5,8,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,6,6] (by decide +kernel))
      node_595
      (invalid_excluded a [3,5,8,6,8] (by decide +kernel)))

theorem node_597 : Excluded a [3,5,8,7,0] :=
  source_excluded a [3,5,8,7,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_598 : Excluded a [3,5,8,7,1] :=
  source_excluded a [3,5,8,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_600 : Excluded a [3,5,8,7,2,0] :=
  source_excluded a [3,5,8,7,2,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_601 : Excluded a [3,5,8,7,2,1] :=
  predecessor_excluded a [3,5,8,7,2,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_604 : Excluded a [3,5,8,7,2,4,0,1] :=
  predecessor_excluded a [3,5,8,7,2,4,0,1] 2 1 6 7 (by decide) (by decide +kernel)

def b_606 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 5
  | 2 => 8
  | 3 => 7
  | 4 => 2
  | 5 => 4
  | 6 => 0
  | 7 => 6
  | 8 => 1
  | _ => 0

def cert_606 : LosingRegion (edgeOf a b_606) 0 :=
  losingMask a b_606 0 1224864967314329241912320
    (by decide +kernel) (by decide +kernel)

theorem node_606 : Excluded a [3,5,8,7,2,4,0,6,1] :=
  losing_excluded a [3,5,8,7,2,4,0,6,1] (by decide) b_606 (by decide +kernel) 2 0 0 cert_606 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_606 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1224864967314329241912320 2 0; decide +kernel)

theorem node_605 : Excluded a [3,5,8,7,2,4,0,6] :=
  branch_excluded a [3,5,8,7,2,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,7,2,4,0,6,0] (by decide +kernel))
      node_606
      (invalid_excluded a [3,5,8,7,2,4,0,6,2] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,0,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,0,6,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,0,6,8] (by decide +kernel)))

theorem node_603 : Excluded a [3,5,8,7,2,4,0] :=
  branch_excluded a [3,5,8,7,2,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,5,8,7,2,4,0,0] (by decide +kernel))
      node_604
      (invalid_excluded a [3,5,8,7,2,4,0,2] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,0,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,0,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,0,5] (by decide +kernel))
      node_605
      (invalid_excluded a [3,5,8,7,2,4,0,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,0,8] (by decide +kernel)))

theorem node_608 : Excluded a [3,5,8,7,2,4,1,0] :=
  predecessor_excluded a [3,5,8,7,2,4,1,0] 2 0 6 7 (by decide) (by decide +kernel)

theorem node_610 : Excluded a [3,5,8,7,2,4,1,6,0] :=
  predecessor_excluded a [3,5,8,7,2,4,1,6,0] 1 3 8 0 (by decide) (by decide +kernel)

theorem node_609 : Excluded a [3,5,8,7,2,4,1,6] :=
  branch_excluded a [3,5,8,7,2,4,1,6] (by decide)
    (fin9_cases _
      node_610
      (invalid_excluded a [3,5,8,7,2,4,1,6,1] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,1,6,2] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,1,6,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,1,6,8] (by decide +kernel)))

theorem node_607 : Excluded a [3,5,8,7,2,4,1] :=
  branch_excluded a [3,5,8,7,2,4,1] (by decide)
    (fin9_cases _
      node_608
      (invalid_excluded a [3,5,8,7,2,4,1,1] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,1,2] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,1,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,1,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,1,5] (by decide +kernel))
      node_609
      (invalid_excluded a [3,5,8,7,2,4,1,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,1,8] (by decide +kernel)))

theorem node_602 : Excluded a [3,5,8,7,2,4] :=
  branch_excluded a [3,5,8,7,2,4] (by decide)
    (fin9_cases _
      node_603
      node_607
      (invalid_excluded a [3,5,8,7,2,4,2] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,4,8] (by decide +kernel)))

theorem node_599 : Excluded a [3,5,8,7,2] :=
  branch_excluded a [3,5,8,7,2] (by decide)
    (fin9_cases _
      node_600
      node_601
      (invalid_excluded a [3,5,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,3] (by decide +kernel))
      node_602
      (invalid_excluded a [3,5,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,2,8] (by decide +kernel)))

theorem node_611 : Excluded a [3,5,8,7,6] :=
  source_excluded a [3,5,8,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_596 : Excluded a [3,5,8,7] :=
  branch_excluded a [3,5,8,7] (by decide)
    (fin9_cases _
      node_597
      node_598
      node_599
      (invalid_excluded a [3,5,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,5] (by decide +kernel))
      node_611
      (invalid_excluded a [3,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,5,8,7,8] (by decide +kernel)))

theorem node_583 : Excluded a [3,5,8] :=
  branch_excluded a [3,5,8] (by decide)
    (fin9_cases _
      node_584
      node_585
      node_586
      (invalid_excluded a [3,5,8,3] (by decide +kernel))
      (invalid_excluded a [3,5,8,4] (by decide +kernel))
      (invalid_excluded a [3,5,8,5] (by decide +kernel))
      node_587
      node_596
      (invalid_excluded a [3,5,8,8] (by decide +kernel)))

theorem node_509 : Excluded a [3,5] :=
  branch_excluded a [3,5] (by decide)
    (fin9_cases _
      node_510
      node_511
      (invalid_excluded a [3,5,2] (by decide +kernel))
      (invalid_excluded a [3,5,3] (by decide +kernel))
      node_512
      (invalid_excluded a [3,5,5] (by decide +kernel))
      node_513
      node_543
      node_583)

theorem node_613 : Excluded a [3,6,0] :=
  source_excluded a [3,6,0] 2 1 0 (by decide) (by decide +kernel)

theorem node_614 : Excluded a [3,6,1] :=
  source_excluded a [3,6,1] 0 2 2 (by decide) (by decide +kernel)

theorem node_615 : Excluded a [3,6,4] :=
  source_excluded a [3,6,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_617 : Excluded a [3,6,5,0] :=
  predecessor_excluded a [3,6,5,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_618 : Excluded a [3,6,5,1] :=
  source_excluded a [3,6,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_619 : Excluded a [3,6,5,2] :=
  predecessor_excluded a [3,6,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_622 : Excluded a [3,6,5,7,0,1] :=
  source_excluded a [3,6,5,7,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_624 : Excluded a [3,6,5,7,0,2,1] :=
  predecessor_excluded a [3,6,5,7,0,2,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_625 : Excluded a [3,6,5,7,0,2,4] :=
  source_excluded a [3,6,5,7,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_626 : Excluded a [3,6,5,7,0,2,8] :=
  source_excluded a [3,6,5,7,0,2,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_623 : Excluded a [3,6,5,7,0,2] :=
  branch_excluded a [3,6,5,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,7,0,2,0] (by decide +kernel))
      node_624
      (invalid_excluded a [3,6,5,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,2,3] (by decide +kernel))
      node_625
      (invalid_excluded a [3,6,5,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,2,7] (by decide +kernel))
      node_626)

theorem node_627 : Excluded a [3,6,5,7,0,4] :=
  predecessor_excluded a [3,6,5,7,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_629 : Excluded a [3,6,5,7,0,8,1] :=
  predecessor_excluded a [3,6,5,7,0,8,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_630 : Excluded a [3,6,5,7,0,8,2] :=
  predecessor_excluded a [3,6,5,7,0,8,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_631 : Excluded a [3,6,5,7,0,8,4] :=
  source_excluded a [3,6,5,7,0,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_628 : Excluded a [3,6,5,7,0,8] :=
  branch_excluded a [3,6,5,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,7,0,8,0] (by decide +kernel))
      node_629
      node_630
      (invalid_excluded a [3,6,5,7,0,8,3] (by decide +kernel))
      node_631
      (invalid_excluded a [3,6,5,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,8,8] (by decide +kernel)))

theorem node_621 : Excluded a [3,6,5,7,0] :=
  branch_excluded a [3,6,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,7,0,0] (by decide +kernel))
      node_622
      node_623
      (invalid_excluded a [3,6,5,7,0,3] (by decide +kernel))
      node_627
      (invalid_excluded a [3,6,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,0,7] (by decide +kernel))
      node_628)

theorem node_632 : Excluded a [3,6,5,7,1] :=
  predecessor_excluded a [3,6,5,7,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_633 : Excluded a [3,6,5,7,2] :=
  source_excluded a [3,6,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_634 : Excluded a [3,6,5,7,8] :=
  predecessor_excluded a [3,6,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_620 : Excluded a [3,6,5,7] :=
  branch_excluded a [3,6,5,7] (by decide)
    (fin9_cases _
      node_621
      node_632
      node_633
      (invalid_excluded a [3,6,5,7,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,7,7] (by decide +kernel))
      node_634)

theorem node_637 : Excluded a [3,6,5,8,0,1] :=
  source_excluded a [3,6,5,8,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_639 : Excluded a [3,6,5,8,0,2,1] :=
  predecessor_excluded a [3,6,5,8,0,2,1] 2 1 1 6 (by decide) (by decide +kernel)

def b_642 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 6
  | 2 => 5
  | 3 => 8
  | 4 => 0
  | 5 => 2
  | 6 => 4
  | 7 => 1
  | 8 => 7
  | _ => 0

def cert_642 : LosingRegion (edgeOf a b_642) 0 :=
  losingMask a b_642 0 2206554854682437799904256
    (by decide +kernel) (by decide +kernel)

theorem node_642 : Excluded a [3,6,5,8,0,2,4,1,7] :=
  losing_excluded a [3,6,5,8,0,2,4,1,7] (by decide) b_642 (by decide +kernel) 2 0 0 cert_642 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_642 2 0 ∧ 0 ≠ 2 ∧ maskRegion 2206554854682437799904256 2 0; decide +kernel)

theorem node_641 : Excluded a [3,6,5,8,0,2,4,1] :=
  branch_excluded a [3,6,5,8,0,2,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,8,0,2,4,1,0] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,2,4,1,1] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,2,4,1,2] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,2,4,1,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,2,4,1,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,2,4,1,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,2,4,1,6] (by decide +kernel))
      node_642
      (invalid_excluded a [3,6,5,8,0,2,4,1,8] (by decide +kernel)))

theorem node_640 : Excluded a [3,6,5,8,0,2,4] :=
  branch_excluded a [3,6,5,8,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,8,0,2,4,0] (by decide +kernel))
      node_641
      (invalid_excluded a [3,6,5,8,0,2,4,2] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,2,4,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,2,4,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,2,4,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,2,4,8] (by decide +kernel)))

theorem node_638 : Excluded a [3,6,5,8,0,2] :=
  branch_excluded a [3,6,5,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,8,0,2,0] (by decide +kernel))
      node_639
      (invalid_excluded a [3,6,5,8,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,2,3] (by decide +kernel))
      node_640
      (invalid_excluded a [3,6,5,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,2,8] (by decide +kernel)))

theorem node_643 : Excluded a [3,6,5,8,0,4] :=
  predecessor_excluded a [3,6,5,8,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_644 : Excluded a [3,6,5,8,0,7] :=
  source_excluded a [3,6,5,8,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_636 : Excluded a [3,6,5,8,0] :=
  branch_excluded a [3,6,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,5,8,0,0] (by decide +kernel))
      node_637
      node_638
      (invalid_excluded a [3,6,5,8,0,3] (by decide +kernel))
      node_643
      (invalid_excluded a [3,6,5,8,0,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,0,6] (by decide +kernel))
      node_644
      (invalid_excluded a [3,6,5,8,0,8] (by decide +kernel)))

theorem node_645 : Excluded a [3,6,5,8,1] :=
  predecessor_excluded a [3,6,5,8,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_646 : Excluded a [3,6,5,8,2] :=
  source_excluded a [3,6,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_648 : Excluded a [3,6,5,8,7,0] :=
  source_excluded a [3,6,5,8,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_649 : Excluded a [3,6,5,8,7,1] :=
  source_excluded a [3,6,5,8,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_651 : Excluded a [3,6,5,8,7,2,0] :=
  source_excluded a [3,6,5,8,7,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_652 : Excluded a [3,6,5,8,7,2,1] :=
  predecessor_excluded a [3,6,5,8,7,2,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_653 : Excluded a [3,6,5,8,7,2,4] :=
  source_excluded a [3,6,5,8,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_650 : Excluded a [3,6,5,8,7,2] :=
  branch_excluded a [3,6,5,8,7,2] (by decide)
    (fin9_cases _
      node_651
      node_652
      (invalid_excluded a [3,6,5,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,2,3] (by decide +kernel))
      node_653
      (invalid_excluded a [3,6,5,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,2,8] (by decide +kernel)))

theorem node_654 : Excluded a [3,6,5,8,7,4] :=
  predecessor_excluded a [3,6,5,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_647 : Excluded a [3,6,5,8,7] :=
  branch_excluded a [3,6,5,8,7] (by decide)
    (fin9_cases _
      node_648
      node_649
      node_650
      (invalid_excluded a [3,6,5,8,7,3] (by decide +kernel))
      node_654
      (invalid_excluded a [3,6,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,7,8] (by decide +kernel)))

theorem node_635 : Excluded a [3,6,5,8] :=
  branch_excluded a [3,6,5,8] (by decide)
    (fin9_cases _
      node_636
      node_645
      node_646
      (invalid_excluded a [3,6,5,8,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,8,6] (by decide +kernel))
      node_647
      (invalid_excluded a [3,6,5,8,8] (by decide +kernel)))

theorem node_616 : Excluded a [3,6,5] :=
  branch_excluded a [3,6,5] (by decide)
    (fin9_cases _
      node_617
      node_618
      node_619
      (invalid_excluded a [3,6,5,3] (by decide +kernel))
      (invalid_excluded a [3,6,5,4] (by decide +kernel))
      (invalid_excluded a [3,6,5,5] (by decide +kernel))
      (invalid_excluded a [3,6,5,6] (by decide +kernel))
      node_620
      node_635)

theorem node_656 : Excluded a [3,6,7,0] :=
  predecessor_excluded a [3,6,7,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_657 : Excluded a [3,6,7,1] :=
  source_excluded a [3,6,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_660 : Excluded a [3,6,7,2,0,1] :=
  source_excluded a [3,6,7,2,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_662 : Excluded a [3,6,7,2,0,4,1] :=
  predecessor_excluded a [3,6,7,2,0,4,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_663 : Excluded a [3,6,7,2,0,4,5] :=
  predecessor_excluded a [3,6,7,2,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_664 : Excluded a [3,6,7,2,0,4,8] :=
  source_excluded a [3,6,7,2,0,4,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_661 : Excluded a [3,6,7,2,0,4] :=
  branch_excluded a [3,6,7,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,7,2,0,4,0] (by decide +kernel))
      node_662
      (invalid_excluded a [3,6,7,2,0,4,2] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,4,4] (by decide +kernel))
      node_663
      (invalid_excluded a [3,6,7,2,0,4,6] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,4,7] (by decide +kernel))
      node_664)

theorem node_666 : Excluded a [3,6,7,2,0,8,1] :=
  predecessor_excluded a [3,6,7,2,0,8,1] 2 1 1 6 (by decide) (by decide +kernel)

def b_669 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 6
  | 2 => 7
  | 3 => 2
  | 4 => 0
  | 5 => 8
  | 6 => 4
  | 7 => 1
  | 8 => 5
  | _ => 0

def cert_669 : LosingRegion (edgeOf a b_669) 0 :=
  losingMask a b_669 0 2414338979928702178821120
    (by decide +kernel) (by decide +kernel)

theorem node_669 : Excluded a [3,6,7,2,0,8,4,1,5] :=
  losing_excluded a [3,6,7,2,0,8,4,1,5] (by decide) b_669 (by decide +kernel) 2 0 0 cert_669 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_669 2 0 ∧ 0 ≠ 2 ∧ maskRegion 2414338979928702178821120 2 0; decide +kernel)

theorem node_668 : Excluded a [3,6,7,2,0,8,4,1] :=
  branch_excluded a [3,6,7,2,0,8,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,7,2,0,8,4,1,0] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,8,4,1,2] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,8,4,1,3] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,8,4,1,4] (by decide +kernel))
      node_669
      (invalid_excluded a [3,6,7,2,0,8,4,1,6] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,8,4,1,8] (by decide +kernel)))

theorem node_670 : Excluded a [3,6,7,2,0,8,4,5] :=
  source_excluded a [3,6,7,2,0,8,4,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_667 : Excluded a [3,6,7,2,0,8,4] :=
  branch_excluded a [3,6,7,2,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,7,2,0,8,4,0] (by decide +kernel))
      node_668
      (invalid_excluded a [3,6,7,2,0,8,4,2] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,8,4,3] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,8,4,4] (by decide +kernel))
      node_670
      (invalid_excluded a [3,6,7,2,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,8,4,8] (by decide +kernel)))

theorem node_671 : Excluded a [3,6,7,2,0,8,5] :=
  predecessor_excluded a [3,6,7,2,0,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_665 : Excluded a [3,6,7,2,0,8] :=
  branch_excluded a [3,6,7,2,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,7,2,0,8,0] (by decide +kernel))
      node_666
      (invalid_excluded a [3,6,7,2,0,8,2] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,8,3] (by decide +kernel))
      node_667
      node_671
      (invalid_excluded a [3,6,7,2,0,8,6] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,8,7] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,8,8] (by decide +kernel)))

theorem node_659 : Excluded a [3,6,7,2,0] :=
  branch_excluded a [3,6,7,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,7,2,0,0] (by decide +kernel))
      node_660
      (invalid_excluded a [3,6,7,2,0,2] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,3] (by decide +kernel))
      node_661
      (invalid_excluded a [3,6,7,2,0,5] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,6] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,0,7] (by decide +kernel))
      node_665)

theorem node_672 : Excluded a [3,6,7,2,1] :=
  predecessor_excluded a [3,6,7,2,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_674 : Excluded a [3,6,7,2,8,0] :=
  source_excluded a [3,6,7,2,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_675 : Excluded a [3,6,7,2,8,1] :=
  source_excluded a [3,6,7,2,8,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_677 : Excluded a [3,6,7,2,8,4,0] :=
  source_excluded a [3,6,7,2,8,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_678 : Excluded a [3,6,7,2,8,4,1] :=
  predecessor_excluded a [3,6,7,2,8,4,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_679 : Excluded a [3,6,7,2,8,4,5] :=
  predecessor_excluded a [3,6,7,2,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_676 : Excluded a [3,6,7,2,8,4] :=
  branch_excluded a [3,6,7,2,8,4] (by decide)
    (fin9_cases _
      node_677
      node_678
      (invalid_excluded a [3,6,7,2,8,4,2] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,8,4,3] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,8,4,4] (by decide +kernel))
      node_679
      (invalid_excluded a [3,6,7,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,8,4,8] (by decide +kernel)))

theorem node_673 : Excluded a [3,6,7,2,8] :=
  branch_excluded a [3,6,7,2,8] (by decide)
    (fin9_cases _
      node_674
      node_675
      (invalid_excluded a [3,6,7,2,8,2] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,8,3] (by decide +kernel))
      node_676
      (invalid_excluded a [3,6,7,2,8,5] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,8,6] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,8,7] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,8,8] (by decide +kernel)))

theorem node_658 : Excluded a [3,6,7,2] :=
  branch_excluded a [3,6,7,2] (by decide)
    (fin9_cases _
      node_659
      node_672
      (invalid_excluded a [3,6,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,3] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,4] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,5] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,6] (by decide +kernel))
      (invalid_excluded a [3,6,7,2,7] (by decide +kernel))
      node_673)

theorem node_680 : Excluded a [3,6,7,5] :=
  source_excluded a [3,6,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_681 : Excluded a [3,6,7,8] :=
  predecessor_excluded a [3,6,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_655 : Excluded a [3,6,7] :=
  branch_excluded a [3,6,7] (by decide)
    (fin9_cases _
      node_656
      node_657
      node_658
      (invalid_excluded a [3,6,7,3] (by decide +kernel))
      (invalid_excluded a [3,6,7,4] (by decide +kernel))
      node_680
      (invalid_excluded a [3,6,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,7,7] (by decide +kernel))
      node_681)

theorem node_683 : Excluded a [3,6,8,0] :=
  predecessor_excluded a [3,6,8,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_684 : Excluded a [3,6,8,1] :=
  source_excluded a [3,6,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_685 : Excluded a [3,6,8,2] :=
  predecessor_excluded a [3,6,8,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_686 : Excluded a [3,6,8,5] :=
  source_excluded a [3,6,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_689 : Excluded a [3,6,8,7,0,1] :=
  source_excluded a [3,6,8,7,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_691 : Excluded a [3,6,8,7,0,2,1] :=
  predecessor_excluded a [3,6,8,7,0,2,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_692 : Excluded a [3,6,8,7,0,2,4] :=
  source_excluded a [3,6,8,7,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_695 : Excluded a [3,6,8,7,0,2,5,1,4] :=
  predecessor_excluded a [3,6,8,7,0,2,5,1,4] 0 4 2 8 (by decide) (by decide +kernel)

theorem node_694 : Excluded a [3,6,8,7,0,2,5,1] :=
  branch_excluded a [3,6,8,7,0,2,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,7,0,2,5,1,0] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,2,5,1,1] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,2,5,1,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,2,5,1,3] (by decide +kernel))
      node_695
      (invalid_excluded a [3,6,8,7,0,2,5,1,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,2,5,1,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,2,5,1,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,2,5,1,8] (by decide +kernel)))

theorem node_696 : Excluded a [3,6,8,7,0,2,5,4] :=
  source_excluded a [3,6,8,7,0,2,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_693 : Excluded a [3,6,8,7,0,2,5] :=
  branch_excluded a [3,6,8,7,0,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,7,0,2,5,0] (by decide +kernel))
      node_694
      (invalid_excluded a [3,6,8,7,0,2,5,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,2,5,3] (by decide +kernel))
      node_696
      (invalid_excluded a [3,6,8,7,0,2,5,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,2,5,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,2,5,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,2,5,8] (by decide +kernel)))

theorem node_690 : Excluded a [3,6,8,7,0,2] :=
  branch_excluded a [3,6,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,7,0,2,0] (by decide +kernel))
      node_691
      (invalid_excluded a [3,6,8,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,2,3] (by decide +kernel))
      node_692
      node_693
      (invalid_excluded a [3,6,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,2,8] (by decide +kernel)))

theorem node_698 : Excluded a [3,6,8,7,0,4,1] :=
  predecessor_excluded a [3,6,8,7,0,4,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_699 : Excluded a [3,6,8,7,0,4,2] :=
  predecessor_excluded a [3,6,8,7,0,4,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_700 : Excluded a [3,6,8,7,0,4,5] :=
  predecessor_excluded a [3,6,8,7,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_697 : Excluded a [3,6,8,7,0,4] :=
  branch_excluded a [3,6,8,7,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,7,0,4,0] (by decide +kernel))
      node_698
      node_699
      (invalid_excluded a [3,6,8,7,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,4,4] (by decide +kernel))
      node_700
      (invalid_excluded a [3,6,8,7,0,4,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,4,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,4,8] (by decide +kernel)))

theorem node_688 : Excluded a [3,6,8,7,0] :=
  branch_excluded a [3,6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,6,8,7,0,0] (by decide +kernel))
      node_689
      node_690
      (invalid_excluded a [3,6,8,7,0,3] (by decide +kernel))
      node_697
      (invalid_excluded a [3,6,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,0,8] (by decide +kernel)))

theorem node_701 : Excluded a [3,6,8,7,1] :=
  predecessor_excluded a [3,6,8,7,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_703 : Excluded a [3,6,8,7,2,0] :=
  source_excluded a [3,6,8,7,2,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_704 : Excluded a [3,6,8,7,2,1] :=
  source_excluded a [3,6,8,7,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_706 : Excluded a [3,6,8,7,2,4,0] :=
  source_excluded a [3,6,8,7,2,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_707 : Excluded a [3,6,8,7,2,4,1] :=
  predecessor_excluded a [3,6,8,7,2,4,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_708 : Excluded a [3,6,8,7,2,4,5] :=
  predecessor_excluded a [3,6,8,7,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_705 : Excluded a [3,6,8,7,2,4] :=
  branch_excluded a [3,6,8,7,2,4] (by decide)
    (fin9_cases _
      node_706
      node_707
      (invalid_excluded a [3,6,8,7,2,4,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,4] (by decide +kernel))
      node_708
      (invalid_excluded a [3,6,8,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,4,8] (by decide +kernel)))

theorem node_702 : Excluded a [3,6,8,7,2] :=
  branch_excluded a [3,6,8,7,2] (by decide)
    (fin9_cases _
      node_703
      node_704
      (invalid_excluded a [3,6,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,3] (by decide +kernel))
      node_705
      (invalid_excluded a [3,6,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,2,8] (by decide +kernel)))

theorem node_687 : Excluded a [3,6,8,7] :=
  branch_excluded a [3,6,8,7] (by decide)
    (fin9_cases _
      node_688
      node_701
      node_702
      (invalid_excluded a [3,6,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,6,8,7,8] (by decide +kernel)))

theorem node_682 : Excluded a [3,6,8] :=
  branch_excluded a [3,6,8] (by decide)
    (fin9_cases _
      node_683
      node_684
      node_685
      (invalid_excluded a [3,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,6,8,4] (by decide +kernel))
      node_686
      (invalid_excluded a [3,6,8,6] (by decide +kernel))
      node_687
      (invalid_excluded a [3,6,8,8] (by decide +kernel)))

theorem node_612 : Excluded a [3,6] :=
  branch_excluded a [3,6] (by decide)
    (fin9_cases _
      node_613
      node_614
      (invalid_excluded a [3,6,2] (by decide +kernel))
      (invalid_excluded a [3,6,3] (by decide +kernel))
      node_615
      node_616
      (invalid_excluded a [3,6,6] (by decide +kernel))
      node_655
      node_682)

theorem node_710 : Excluded a [3,7,0] :=
  source_excluded a [3,7,0] 2 1 0 (by decide) (by decide +kernel)

theorem node_711 : Excluded a [3,7,1] :=
  source_excluded a [3,7,1] 0 2 2 (by decide) (by decide +kernel)

theorem node_712 : Excluded a [3,7,4] :=
  source_excluded a [3,7,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_714 : Excluded a [3,7,5,0] :=
  predecessor_excluded a [3,7,5,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_715 : Excluded a [3,7,5,1] :=
  source_excluded a [3,7,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_716 : Excluded a [3,7,5,2] :=
  predecessor_excluded a [3,7,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_717 : Excluded a [3,7,5,6] :=
  predecessor_excluded a [3,7,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_720 : Excluded a [3,7,5,8,0,1] :=
  predecessor_excluded a [3,7,5,8,0,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_722 : Excluded a [3,7,5,8,0,2,1] :=
  source_excluded a [3,7,5,8,0,2,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_724 : Excluded a [3,7,5,8,0,2,4,1] :=
  predecessor_excluded a [3,7,5,8,0,2,4,1] 2 1 1 7 (by decide) (by decide +kernel)

def b_726 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 7
  | 2 => 5
  | 3 => 8
  | 4 => 0
  | 5 => 2
  | 6 => 4
  | 7 => 6
  | 8 => 1
  | _ => 0

def cert_726 : LosingRegion (edgeOf a b_726) 0 :=
  losingMask a b_726 0 1224505689154694621168640
    (by decide +kernel) (by decide +kernel)

theorem node_726 : Excluded a [3,7,5,8,0,2,4,6,1] :=
  losing_excluded a [3,7,5,8,0,2,4,6,1] (by decide) b_726 (by decide +kernel) 2 0 0 cert_726 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_726 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1224505689154694621168640 2 0; decide +kernel)

theorem node_725 : Excluded a [3,7,5,8,0,2,4,6] :=
  branch_excluded a [3,7,5,8,0,2,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,8,0,2,4,6,0] (by decide +kernel))
      node_726
      (invalid_excluded a [3,7,5,8,0,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,2,4,6,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,2,4,6,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,2,4,6,8] (by decide +kernel)))

theorem node_723 : Excluded a [3,7,5,8,0,2,4] :=
  branch_excluded a [3,7,5,8,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,8,0,2,4,0] (by decide +kernel))
      node_724
      (invalid_excluded a [3,7,5,8,0,2,4,2] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,2,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,2,4,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,2,4,5] (by decide +kernel))
      node_725
      (invalid_excluded a [3,7,5,8,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,2,4,8] (by decide +kernel)))

theorem node_721 : Excluded a [3,7,5,8,0,2] :=
  branch_excluded a [3,7,5,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,8,0,2,0] (by decide +kernel))
      node_722
      (invalid_excluded a [3,7,5,8,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,2,3] (by decide +kernel))
      node_723
      (invalid_excluded a [3,7,5,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,2,8] (by decide +kernel)))

theorem node_727 : Excluded a [3,7,5,8,0,4] :=
  predecessor_excluded a [3,7,5,8,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_719 : Excluded a [3,7,5,8,0] :=
  branch_excluded a [3,7,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,5,8,0,0] (by decide +kernel))
      node_720
      node_721
      (invalid_excluded a [3,7,5,8,0,3] (by decide +kernel))
      node_727
      (invalid_excluded a [3,7,5,8,0,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,0,8] (by decide +kernel)))

theorem node_729 : Excluded a [3,7,5,8,1,0] :=
  predecessor_excluded a [3,7,5,8,1,0] 2 0 4 5 (by decide) (by decide +kernel)

theorem node_731 : Excluded a [3,7,5,8,1,2,0] :=
  source_excluded a [3,7,5,8,1,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_733 : Excluded a [3,7,5,8,1,2,4,0] :=
  source_excluded a [3,7,5,8,1,2,4,0] 1 2 7 (by decide) (by decide +kernel)

theorem node_735 : Excluded a [3,7,5,8,1,2,4,6,0] :=
  predecessor_excluded a [3,7,5,8,1,2,4,6,0] 1 3 8 0 (by decide) (by decide +kernel)

theorem node_734 : Excluded a [3,7,5,8,1,2,4,6] :=
  branch_excluded a [3,7,5,8,1,2,4,6] (by decide)
    (fin9_cases _
      node_735
      (invalid_excluded a [3,7,5,8,1,2,4,6,1] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,6,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,6,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,6,8] (by decide +kernel)))

theorem node_732 : Excluded a [3,7,5,8,1,2,4] :=
  branch_excluded a [3,7,5,8,1,2,4] (by decide)
    (fin9_cases _
      node_733
      (invalid_excluded a [3,7,5,8,1,2,4,1] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,2] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,5] (by decide +kernel))
      node_734
      (invalid_excluded a [3,7,5,8,1,2,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,4,8] (by decide +kernel)))

theorem node_730 : Excluded a [3,7,5,8,1,2] :=
  branch_excluded a [3,7,5,8,1,2] (by decide)
    (fin9_cases _
      node_731
      (invalid_excluded a [3,7,5,8,1,2,1] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,3] (by decide +kernel))
      node_732
      (invalid_excluded a [3,7,5,8,1,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,2,8] (by decide +kernel)))

theorem node_736 : Excluded a [3,7,5,8,1,4] :=
  predecessor_excluded a [3,7,5,8,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_728 : Excluded a [3,7,5,8,1] :=
  branch_excluded a [3,7,5,8,1] (by decide)
    (fin9_cases _
      node_729
      (invalid_excluded a [3,7,5,8,1,1] (by decide +kernel))
      node_730
      (invalid_excluded a [3,7,5,8,1,3] (by decide +kernel))
      node_736
      (invalid_excluded a [3,7,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,1,8] (by decide +kernel)))

theorem node_737 : Excluded a [3,7,5,8,2] :=
  source_excluded a [3,7,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_738 : Excluded a [3,7,5,8,6] :=
  source_excluded a [3,7,5,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_718 : Excluded a [3,7,5,8] :=
  branch_excluded a [3,7,5,8] (by decide)
    (fin9_cases _
      node_719
      node_728
      node_737
      (invalid_excluded a [3,7,5,8,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,5] (by decide +kernel))
      node_738
      (invalid_excluded a [3,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,5,8,8] (by decide +kernel)))

theorem node_713 : Excluded a [3,7,5] :=
  branch_excluded a [3,7,5] (by decide)
    (fin9_cases _
      node_714
      node_715
      node_716
      (invalid_excluded a [3,7,5,3] (by decide +kernel))
      (invalid_excluded a [3,7,5,4] (by decide +kernel))
      (invalid_excluded a [3,7,5,5] (by decide +kernel))
      node_717
      (invalid_excluded a [3,7,5,7] (by decide +kernel))
      node_718)

theorem node_740 : Excluded a [3,7,6,0] :=
  predecessor_excluded a [3,7,6,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_741 : Excluded a [3,7,6,1] :=
  source_excluded a [3,7,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_744 : Excluded a [3,7,6,2,0,1] :=
  predecessor_excluded a [3,7,6,2,0,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_746 : Excluded a [3,7,6,2,0,4,1] :=
  source_excluded a [3,7,6,2,0,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_747 : Excluded a [3,7,6,2,0,4,5] :=
  predecessor_excluded a [3,7,6,2,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_748 : Excluded a [3,7,6,2,0,4,8] :=
  source_excluded a [3,7,6,2,0,4,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_745 : Excluded a [3,7,6,2,0,4] :=
  branch_excluded a [3,7,6,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,2,0,4,0] (by decide +kernel))
      node_746
      (invalid_excluded a [3,7,6,2,0,4,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,0,4,4] (by decide +kernel))
      node_747
      (invalid_excluded a [3,7,6,2,0,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,0,4,7] (by decide +kernel))
      node_748)

theorem node_750 : Excluded a [3,7,6,2,0,8,1] :=
  source_excluded a [3,7,6,2,0,8,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_751 : Excluded a [3,7,6,2,0,8,4] :=
  predecessor_excluded a [3,7,6,2,0,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_752 : Excluded a [3,7,6,2,0,8,5] :=
  predecessor_excluded a [3,7,6,2,0,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_749 : Excluded a [3,7,6,2,0,8] :=
  branch_excluded a [3,7,6,2,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,2,0,8,0] (by decide +kernel))
      node_750
      (invalid_excluded a [3,7,6,2,0,8,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,0,8,3] (by decide +kernel))
      node_751
      node_752
      (invalid_excluded a [3,7,6,2,0,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,0,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,0,8,8] (by decide +kernel)))

theorem node_743 : Excluded a [3,7,6,2,0] :=
  branch_excluded a [3,7,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,2,0,0] (by decide +kernel))
      node_744
      (invalid_excluded a [3,7,6,2,0,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,0,3] (by decide +kernel))
      node_745
      (invalid_excluded a [3,7,6,2,0,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,0,7] (by decide +kernel))
      node_749)

theorem node_754 : Excluded a [3,7,6,2,1,0] :=
  predecessor_excluded a [3,7,6,2,1,0] 2 0 4 5 (by decide) (by decide +kernel)

theorem node_756 : Excluded a [3,7,6,2,1,4,0] :=
  source_excluded a [3,7,6,2,1,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_757 : Excluded a [3,7,6,2,1,4,5] :=
  predecessor_excluded a [3,7,6,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_758 : Excluded a [3,7,6,2,1,4,8] :=
  source_excluded a [3,7,6,2,1,4,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_755 : Excluded a [3,7,6,2,1,4] :=
  branch_excluded a [3,7,6,2,1,4] (by decide)
    (fin9_cases _
      node_756
      (invalid_excluded a [3,7,6,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,1,4,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,1,4,4] (by decide +kernel))
      node_757
      (invalid_excluded a [3,7,6,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,1,4,7] (by decide +kernel))
      node_758)

theorem node_760 : Excluded a [3,7,6,2,1,8,0] :=
  source_excluded a [3,7,6,2,1,8,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_761 : Excluded a [3,7,6,2,1,8,4] :=
  predecessor_excluded a [3,7,6,2,1,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_762 : Excluded a [3,7,6,2,1,8,5] :=
  predecessor_excluded a [3,7,6,2,1,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_759 : Excluded a [3,7,6,2,1,8] :=
  branch_excluded a [3,7,6,2,1,8] (by decide)
    (fin9_cases _
      node_760
      (invalid_excluded a [3,7,6,2,1,8,1] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,1,8,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,1,8,3] (by decide +kernel))
      node_761
      node_762
      (invalid_excluded a [3,7,6,2,1,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,1,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,1,8,8] (by decide +kernel)))

theorem node_753 : Excluded a [3,7,6,2,1] :=
  branch_excluded a [3,7,6,2,1] (by decide)
    (fin9_cases _
      node_754
      (invalid_excluded a [3,7,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,1,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,1,3] (by decide +kernel))
      node_755
      (invalid_excluded a [3,7,6,2,1,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,1,7] (by decide +kernel))
      node_759)

theorem node_765 : Excluded a [3,7,6,2,8,0,1] :=
  source_excluded a [3,7,6,2,8,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_766 : Excluded a [3,7,6,2,8,0,4] :=
  predecessor_excluded a [3,7,6,2,8,0,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_768 : Excluded a [3,7,6,2,8,0,5,1] :=
  predecessor_excluded a [3,7,6,2,8,0,5,1] 2 1 1 7 (by decide) (by decide +kernel)

theorem node_769 : Excluded a [3,7,6,2,8,0,5,4] :=
  source_excluded a [3,7,6,2,8,0,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_767 : Excluded a [3,7,6,2,8,0,5] :=
  branch_excluded a [3,7,6,2,8,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,2,8,0,5,0] (by decide +kernel))
      node_768
      (invalid_excluded a [3,7,6,2,8,0,5,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,8,0,5,3] (by decide +kernel))
      node_769
      (invalid_excluded a [3,7,6,2,8,0,5,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,8,0,5,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,8,0,5,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,8,0,5,8] (by decide +kernel)))

theorem node_764 : Excluded a [3,7,6,2,8,0] :=
  branch_excluded a [3,7,6,2,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,2,8,0,0] (by decide +kernel))
      node_765
      (invalid_excluded a [3,7,6,2,8,0,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,8,0,3] (by decide +kernel))
      node_766
      node_767
      (invalid_excluded a [3,7,6,2,8,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,8,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,8,0,8] (by decide +kernel)))

theorem node_770 : Excluded a [3,7,6,2,8,1] :=
  predecessor_excluded a [3,7,6,2,8,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_772 : Excluded a [3,7,6,2,8,4,0] :=
  source_excluded a [3,7,6,2,8,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_773 : Excluded a [3,7,6,2,8,4,1] :=
  source_excluded a [3,7,6,2,8,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_774 : Excluded a [3,7,6,2,8,4,5] :=
  predecessor_excluded a [3,7,6,2,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_771 : Excluded a [3,7,6,2,8,4] :=
  branch_excluded a [3,7,6,2,8,4] (by decide)
    (fin9_cases _
      node_772
      node_773
      (invalid_excluded a [3,7,6,2,8,4,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,8,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,8,4,4] (by decide +kernel))
      node_774
      (invalid_excluded a [3,7,6,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,8,4,8] (by decide +kernel)))

theorem node_763 : Excluded a [3,7,6,2,8] :=
  branch_excluded a [3,7,6,2,8] (by decide)
    (fin9_cases _
      node_764
      node_770
      (invalid_excluded a [3,7,6,2,8,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,8,3] (by decide +kernel))
      node_771
      (invalid_excluded a [3,7,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,8,8] (by decide +kernel)))

theorem node_742 : Excluded a [3,7,6,2] :=
  branch_excluded a [3,7,6,2] (by decide)
    (fin9_cases _
      node_743
      node_753
      (invalid_excluded a [3,7,6,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,2,7] (by decide +kernel))
      node_763)

theorem node_775 : Excluded a [3,7,6,5] :=
  source_excluded a [3,7,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_778 : Excluded a [3,7,6,8,0,1] :=
  predecessor_excluded a [3,7,6,8,0,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_779 : Excluded a [3,7,6,8,0,2] :=
  source_excluded a [3,7,6,8,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_781 : Excluded a [3,7,6,8,0,4,1] :=
  source_excluded a [3,7,6,8,0,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_783 : Excluded a [3,7,6,8,0,4,2,1] :=
  predecessor_excluded a [3,7,6,8,0,4,2,1] 2 1 1 7 (by decide) (by decide +kernel)

def b_785 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 7
  | 2 => 6
  | 3 => 8
  | 4 => 0
  | 5 => 4
  | 6 => 2
  | 7 => 5
  | 8 => 1
  | _ => 0

def cert_785 : LosingRegion (edgeOf a b_785) 0 :=
  losingMask a b_785 0 1224508690627924394771456
    (by decide +kernel) (by decide +kernel)

theorem node_785 : Excluded a [3,7,6,8,0,4,2,5,1] :=
  losing_excluded a [3,7,6,8,0,4,2,5,1] (by decide) b_785 (by decide +kernel) 2 0 0 cert_785 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_785 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1224508690627924394771456 2 0; decide +kernel)

theorem node_784 : Excluded a [3,7,6,8,0,4,2,5] :=
  branch_excluded a [3,7,6,8,0,4,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,8,0,4,2,5,0] (by decide +kernel))
      node_785
      (invalid_excluded a [3,7,6,8,0,4,2,5,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,4,2,5,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,4,2,5,4] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,4,2,5,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,4,2,5,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,4,2,5,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,4,2,5,8] (by decide +kernel)))

theorem node_782 : Excluded a [3,7,6,8,0,4,2] :=
  branch_excluded a [3,7,6,8,0,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,8,0,4,2,0] (by decide +kernel))
      node_783
      (invalid_excluded a [3,7,6,8,0,4,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,4,2,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,4,2,4] (by decide +kernel))
      node_784
      (invalid_excluded a [3,7,6,8,0,4,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,4,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,4,2,8] (by decide +kernel)))

theorem node_786 : Excluded a [3,7,6,8,0,4,5] :=
  predecessor_excluded a [3,7,6,8,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_780 : Excluded a [3,7,6,8,0,4] :=
  branch_excluded a [3,7,6,8,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,8,0,4,0] (by decide +kernel))
      node_781
      node_782
      (invalid_excluded a [3,7,6,8,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,4,4] (by decide +kernel))
      node_786
      (invalid_excluded a [3,7,6,8,0,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,4,8] (by decide +kernel)))

theorem node_777 : Excluded a [3,7,6,8,0] :=
  branch_excluded a [3,7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,6,8,0,0] (by decide +kernel))
      node_778
      node_779
      (invalid_excluded a [3,7,6,8,0,3] (by decide +kernel))
      node_780
      (invalid_excluded a [3,7,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,0,8] (by decide +kernel)))

theorem node_788 : Excluded a [3,7,6,8,1,0] :=
  predecessor_excluded a [3,7,6,8,1,0] 2 0 4 5 (by decide) (by decide +kernel)

theorem node_789 : Excluded a [3,7,6,8,1,2] :=
  source_excluded a [3,7,6,8,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_791 : Excluded a [3,7,6,8,1,4,0] :=
  source_excluded a [3,7,6,8,1,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_793 : Excluded a [3,7,6,8,1,4,2,0] :=
  source_excluded a [3,7,6,8,1,4,2,0] 1 2 7 (by decide) (by decide +kernel)

theorem node_795 : Excluded a [3,7,6,8,1,4,2,5,0] :=
  predecessor_excluded a [3,7,6,8,1,4,2,5,0] 1 3 8 0 (by decide) (by decide +kernel)

theorem node_794 : Excluded a [3,7,6,8,1,4,2,5] :=
  branch_excluded a [3,7,6,8,1,4,2,5] (by decide)
    (fin9_cases _
      node_795
      (invalid_excluded a [3,7,6,8,1,4,2,5,1] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,2,5,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,2,5,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,2,5,4] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,2,5,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,2,5,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,2,5,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,2,5,8] (by decide +kernel)))

theorem node_792 : Excluded a [3,7,6,8,1,4,2] :=
  branch_excluded a [3,7,6,8,1,4,2] (by decide)
    (fin9_cases _
      node_793
      (invalid_excluded a [3,7,6,8,1,4,2,1] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,2,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,2,4] (by decide +kernel))
      node_794
      (invalid_excluded a [3,7,6,8,1,4,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,2,8] (by decide +kernel)))

theorem node_796 : Excluded a [3,7,6,8,1,4,5] :=
  predecessor_excluded a [3,7,6,8,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_790 : Excluded a [3,7,6,8,1,4] :=
  branch_excluded a [3,7,6,8,1,4] (by decide)
    (fin9_cases _
      node_791
      (invalid_excluded a [3,7,6,8,1,4,1] (by decide +kernel))
      node_792
      (invalid_excluded a [3,7,6,8,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,4] (by decide +kernel))
      node_796
      (invalid_excluded a [3,7,6,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,4,8] (by decide +kernel)))

theorem node_787 : Excluded a [3,7,6,8,1] :=
  branch_excluded a [3,7,6,8,1] (by decide)
    (fin9_cases _
      node_788
      (invalid_excluded a [3,7,6,8,1,1] (by decide +kernel))
      node_789
      (invalid_excluded a [3,7,6,8,1,3] (by decide +kernel))
      node_790
      (invalid_excluded a [3,7,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,1,8] (by decide +kernel)))

theorem node_797 : Excluded a [3,7,6,8,2] :=
  predecessor_excluded a [3,7,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_776 : Excluded a [3,7,6,8] :=
  branch_excluded a [3,7,6,8] (by decide)
    (fin9_cases _
      node_777
      node_787
      node_797
      (invalid_excluded a [3,7,6,8,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,6,8,8] (by decide +kernel)))

theorem node_739 : Excluded a [3,7,6] :=
  branch_excluded a [3,7,6] (by decide)
    (fin9_cases _
      node_740
      node_741
      node_742
      (invalid_excluded a [3,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,6,4] (by decide +kernel))
      node_775
      (invalid_excluded a [3,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,6,7] (by decide +kernel))
      node_776)

theorem node_799 : Excluded a [3,7,8,0] :=
  predecessor_excluded a [3,7,8,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_800 : Excluded a [3,7,8,1] :=
  source_excluded a [3,7,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_801 : Excluded a [3,7,8,2] :=
  predecessor_excluded a [3,7,8,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_802 : Excluded a [3,7,8,5] :=
  source_excluded a [3,7,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_805 : Excluded a [3,7,8,6,0,1] :=
  predecessor_excluded a [3,7,8,6,0,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_807 : Excluded a [3,7,8,6,0,2,1] :=
  source_excluded a [3,7,8,6,0,2,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_808 : Excluded a [3,7,8,6,0,2,4] :=
  source_excluded a [3,7,8,6,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_809 : Excluded a [3,7,8,6,0,2,5] :=
  predecessor_excluded a [3,7,8,6,0,2,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_806 : Excluded a [3,7,8,6,0,2] :=
  branch_excluded a [3,7,8,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,8,6,0,2,0] (by decide +kernel))
      node_807
      (invalid_excluded a [3,7,8,6,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,0,2,3] (by decide +kernel))
      node_808
      node_809
      (invalid_excluded a [3,7,8,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,0,2,8] (by decide +kernel)))

theorem node_810 : Excluded a [3,7,8,6,0,4] :=
  source_excluded a [3,7,8,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_804 : Excluded a [3,7,8,6,0] :=
  branch_excluded a [3,7,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,8,6,0,0] (by decide +kernel))
      node_805
      node_806
      (invalid_excluded a [3,7,8,6,0,3] (by decide +kernel))
      node_810
      (invalid_excluded a [3,7,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,0,8] (by decide +kernel)))

theorem node_812 : Excluded a [3,7,8,6,1,0] :=
  predecessor_excluded a [3,7,8,6,1,0] 2 0 4 5 (by decide) (by decide +kernel)

theorem node_814 : Excluded a [3,7,8,6,1,2,0] :=
  source_excluded a [3,7,8,6,1,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_815 : Excluded a [3,7,8,6,1,2,4] :=
  source_excluded a [3,7,8,6,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_816 : Excluded a [3,7,8,6,1,2,5] :=
  predecessor_excluded a [3,7,8,6,1,2,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_813 : Excluded a [3,7,8,6,1,2] :=
  branch_excluded a [3,7,8,6,1,2] (by decide)
    (fin9_cases _
      node_814
      (invalid_excluded a [3,7,8,6,1,2,1] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,3] (by decide +kernel))
      node_815
      node_816
      (invalid_excluded a [3,7,8,6,1,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,2,8] (by decide +kernel)))

theorem node_817 : Excluded a [3,7,8,6,1,4] :=
  source_excluded a [3,7,8,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_811 : Excluded a [3,7,8,6,1] :=
  branch_excluded a [3,7,8,6,1] (by decide)
    (fin9_cases _
      node_812
      (invalid_excluded a [3,7,8,6,1,1] (by decide +kernel))
      node_813
      (invalid_excluded a [3,7,8,6,1,3] (by decide +kernel))
      node_817
      (invalid_excluded a [3,7,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,1,8] (by decide +kernel)))

theorem node_820 : Excluded a [3,7,8,6,2,0,1] :=
  source_excluded a [3,7,8,6,2,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_821 : Excluded a [3,7,8,6,2,0,4] :=
  source_excluded a [3,7,8,6,2,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_822 : Excluded a [3,7,8,6,2,0,5] :=
  predecessor_excluded a [3,7,8,6,2,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_819 : Excluded a [3,7,8,6,2,0] :=
  branch_excluded a [3,7,8,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,7,8,6,2,0,0] (by decide +kernel))
      node_820
      (invalid_excluded a [3,7,8,6,2,0,2] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,2,0,3] (by decide +kernel))
      node_821
      node_822
      (invalid_excluded a [3,7,8,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,2,0,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,2,0,8] (by decide +kernel)))

theorem node_823 : Excluded a [3,7,8,6,2,1] :=
  predecessor_excluded a [3,7,8,6,2,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_824 : Excluded a [3,7,8,6,2,4] :=
  source_excluded a [3,7,8,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_818 : Excluded a [3,7,8,6,2] :=
  branch_excluded a [3,7,8,6,2] (by decide)
    (fin9_cases _
      node_819
      node_823
      (invalid_excluded a [3,7,8,6,2,2] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,2,3] (by decide +kernel))
      node_824
      (invalid_excluded a [3,7,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,2,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,2,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,2,8] (by decide +kernel)))

theorem node_803 : Excluded a [3,7,8,6] :=
  branch_excluded a [3,7,8,6] (by decide)
    (fin9_cases _
      node_804
      node_811
      node_818
      (invalid_excluded a [3,7,8,6,3] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,4] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,5] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,6] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,6,8] (by decide +kernel)))

theorem node_798 : Excluded a [3,7,8] :=
  branch_excluded a [3,7,8] (by decide)
    (fin9_cases _
      node_799
      node_800
      node_801
      (invalid_excluded a [3,7,8,3] (by decide +kernel))
      (invalid_excluded a [3,7,8,4] (by decide +kernel))
      node_802
      node_803
      (invalid_excluded a [3,7,8,7] (by decide +kernel))
      (invalid_excluded a [3,7,8,8] (by decide +kernel)))

theorem node_709 : Excluded a [3,7] :=
  branch_excluded a [3,7] (by decide)
    (fin9_cases _
      node_710
      node_711
      (invalid_excluded a [3,7,2] (by decide +kernel))
      (invalid_excluded a [3,7,3] (by decide +kernel))
      node_712
      node_713
      node_739
      (invalid_excluded a [3,7,7] (by decide +kernel))
      node_798)

theorem node_826 : Excluded a [3,8,0] :=
  source_excluded a [3,8,0] 2 1 0 (by decide) (by decide +kernel)

theorem node_827 : Excluded a [3,8,1] :=
  source_excluded a [3,8,1] 0 2 2 (by decide) (by decide +kernel)

theorem node_828 : Excluded a [3,8,4] :=
  source_excluded a [3,8,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_830 : Excluded a [3,8,5,0] :=
  predecessor_excluded a [3,8,5,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_831 : Excluded a [3,8,5,1] :=
  source_excluded a [3,8,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_832 : Excluded a [3,8,5,2] :=
  predecessor_excluded a [3,8,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_833 : Excluded a [3,8,5,6] :=
  predecessor_excluded a [3,8,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_836 : Excluded a [3,8,5,7,0,1] :=
  predecessor_excluded a [3,8,5,7,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_838 : Excluded a [3,8,5,7,0,2,1] :=
  predecessor_excluded a [3,8,5,7,0,2,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_839 : Excluded a [3,8,5,7,0,2,4] :=
  source_excluded a [3,8,5,7,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_837 : Excluded a [3,8,5,7,0,2] :=
  branch_excluded a [3,8,5,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,0,2,0] (by decide +kernel))
      node_838
      (invalid_excluded a [3,8,5,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,0,2,3] (by decide +kernel))
      node_839
      (invalid_excluded a [3,8,5,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,0,2,8] (by decide +kernel)))

theorem node_840 : Excluded a [3,8,5,7,0,4] :=
  predecessor_excluded a [3,8,5,7,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_835 : Excluded a [3,8,5,7,0] :=
  branch_excluded a [3,8,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,0,0] (by decide +kernel))
      node_836
      node_837
      (invalid_excluded a [3,8,5,7,0,3] (by decide +kernel))
      node_840
      (invalid_excluded a [3,8,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,0,8] (by decide +kernel)))

theorem node_842 : Excluded a [3,8,5,7,1,0] :=
  predecessor_excluded a [3,8,5,7,1,0] 2 0 4 5 (by decide) (by decide +kernel)

theorem node_845 : Excluded a [3,8,5,7,1,2,0,4] :=
  source_excluded a [3,8,5,7,1,2,0,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_847 : Excluded a [3,8,5,7,1,2,0,6,4] :=
  predecessor_excluded a [3,8,5,7,1,2,0,6,4] 0 5 8 2 (by decide) (by decide +kernel)

theorem node_846 : Excluded a [3,8,5,7,1,2,0,6] :=
  branch_excluded a [3,8,5,7,1,2,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,1,2,0,6,0] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,6,1] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,6,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,6,3] (by decide +kernel))
      node_847
      (invalid_excluded a [3,8,5,7,1,2,0,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,6,8] (by decide +kernel)))

theorem node_844 : Excluded a [3,8,5,7,1,2,0] :=
  branch_excluded a [3,8,5,7,1,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,5,7,1,2,0,0] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,1] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,3] (by decide +kernel))
      node_845
      (invalid_excluded a [3,8,5,7,1,2,0,5] (by decide +kernel))
      node_846
      (invalid_excluded a [3,8,5,7,1,2,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,0,8] (by decide +kernel)))

theorem node_848 : Excluded a [3,8,5,7,1,2,4] :=
  source_excluded a [3,8,5,7,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_843 : Excluded a [3,8,5,7,1,2] :=
  branch_excluded a [3,8,5,7,1,2] (by decide)
    (fin9_cases _
      node_844
      (invalid_excluded a [3,8,5,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,3] (by decide +kernel))
      node_848
      (invalid_excluded a [3,8,5,7,1,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,2,8] (by decide +kernel)))

theorem node_849 : Excluded a [3,8,5,7,1,4] :=
  predecessor_excluded a [3,8,5,7,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_841 : Excluded a [3,8,5,7,1] :=
  branch_excluded a [3,8,5,7,1] (by decide)
    (fin9_cases _
      node_842
      (invalid_excluded a [3,8,5,7,1,1] (by decide +kernel))
      node_843
      (invalid_excluded a [3,8,5,7,1,3] (by decide +kernel))
      node_849
      (invalid_excluded a [3,8,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,1,8] (by decide +kernel)))

theorem node_850 : Excluded a [3,8,5,7,2] :=
  source_excluded a [3,8,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_851 : Excluded a [3,8,5,7,6] :=
  source_excluded a [3,8,5,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_834 : Excluded a [3,8,5,7] :=
  branch_excluded a [3,8,5,7] (by decide)
    (fin9_cases _
      node_835
      node_841
      node_850
      (invalid_excluded a [3,8,5,7,3] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,4] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,5] (by decide +kernel))
      node_851
      (invalid_excluded a [3,8,5,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,5,7,8] (by decide +kernel)))

theorem node_829 : Excluded a [3,8,5] :=
  branch_excluded a [3,8,5] (by decide)
    (fin9_cases _
      node_830
      node_831
      node_832
      (invalid_excluded a [3,8,5,3] (by decide +kernel))
      (invalid_excluded a [3,8,5,4] (by decide +kernel))
      (invalid_excluded a [3,8,5,5] (by decide +kernel))
      node_833
      node_834
      (invalid_excluded a [3,8,5,8] (by decide +kernel)))

theorem node_853 : Excluded a [3,8,6,0] :=
  predecessor_excluded a [3,8,6,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_854 : Excluded a [3,8,6,1] :=
  source_excluded a [3,8,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_857 : Excluded a [3,8,6,2,0,1] :=
  predecessor_excluded a [3,8,6,2,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_859 : Excluded a [3,8,6,2,0,4,1] :=
  predecessor_excluded a [3,8,6,2,0,4,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_860 : Excluded a [3,8,6,2,0,4,5] :=
  predecessor_excluded a [3,8,6,2,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_858 : Excluded a [3,8,6,2,0,4] :=
  branch_excluded a [3,8,6,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,2,0,4,0] (by decide +kernel))
      node_859
      (invalid_excluded a [3,8,6,2,0,4,2] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,0,4,4] (by decide +kernel))
      node_860
      (invalid_excluded a [3,8,6,2,0,4,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,0,4,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,0,4,8] (by decide +kernel)))

theorem node_861 : Excluded a [3,8,6,2,0,7] :=
  source_excluded a [3,8,6,2,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_856 : Excluded a [3,8,6,2,0] :=
  branch_excluded a [3,8,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,2,0,0] (by decide +kernel))
      node_857
      (invalid_excluded a [3,8,6,2,0,2] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,0,3] (by decide +kernel))
      node_858
      (invalid_excluded a [3,8,6,2,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,0,6] (by decide +kernel))
      node_861
      (invalid_excluded a [3,8,6,2,0,8] (by decide +kernel)))

theorem node_863 : Excluded a [3,8,6,2,1,0] :=
  predecessor_excluded a [3,8,6,2,1,0] 2 0 4 5 (by decide) (by decide +kernel)

def b_867 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 8
  | 2 => 6
  | 3 => 2
  | 4 => 1
  | 5 => 4
  | 6 => 0
  | 7 => 5
  | 8 => 7
  | _ => 0

def cert_867 : LosingRegion (edgeOf a b_867) 0 :=
  losingMask a b_867 0 2079465719989641885516800
    (by decide +kernel) (by decide +kernel)

theorem node_867 : Excluded a [3,8,6,2,1,4,0,5,7] :=
  losing_excluded a [3,8,6,2,1,4,0,5,7] (by decide) b_867 (by decide +kernel) 2 0 5 cert_867 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_867 2 0 ∧ 5 ≠ 2 ∧ maskRegion 2079465719989641885516800 2 5; decide +kernel)

theorem node_866 : Excluded a [3,8,6,2,1,4,0,5] :=
  branch_excluded a [3,8,6,2,1,4,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,2,1,4,0,5,0] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,0,5,1] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,0,5,2] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,0,5,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,0,5,4] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,0,5,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,0,5,6] (by decide +kernel))
      node_867
      (invalid_excluded a [3,8,6,2,1,4,0,5,8] (by decide +kernel)))

theorem node_865 : Excluded a [3,8,6,2,1,4,0] :=
  branch_excluded a [3,8,6,2,1,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,2,1,4,0,0] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,0,1] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,0,2] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,0,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,0,4] (by decide +kernel))
      node_866
      (invalid_excluded a [3,8,6,2,1,4,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,0,8] (by decide +kernel)))

theorem node_868 : Excluded a [3,8,6,2,1,4,5] :=
  predecessor_excluded a [3,8,6,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_864 : Excluded a [3,8,6,2,1,4] :=
  branch_excluded a [3,8,6,2,1,4] (by decide)
    (fin9_cases _
      node_865
      (invalid_excluded a [3,8,6,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,2] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,4] (by decide +kernel))
      node_868
      (invalid_excluded a [3,8,6,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,4,8] (by decide +kernel)))

theorem node_869 : Excluded a [3,8,6,2,1,7] :=
  source_excluded a [3,8,6,2,1,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_862 : Excluded a [3,8,6,2,1] :=
  branch_excluded a [3,8,6,2,1] (by decide)
    (fin9_cases _
      node_863
      (invalid_excluded a [3,8,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,2] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,3] (by decide +kernel))
      node_864
      (invalid_excluded a [3,8,6,2,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,1,6] (by decide +kernel))
      node_869
      (invalid_excluded a [3,8,6,2,1,8] (by decide +kernel)))

theorem node_872 : Excluded a [3,8,6,2,7,0,1] :=
  predecessor_excluded a [3,8,6,2,7,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_873 : Excluded a [3,8,6,2,7,0,4] :=
  source_excluded a [3,8,6,2,7,0,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_874 : Excluded a [3,8,6,2,7,0,5] :=
  source_excluded a [3,8,6,2,7,0,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_871 : Excluded a [3,8,6,2,7,0] :=
  branch_excluded a [3,8,6,2,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,6,2,7,0,0] (by decide +kernel))
      node_872
      (invalid_excluded a [3,8,6,2,7,0,2] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,7,0,3] (by decide +kernel))
      node_873
      node_874
      (invalid_excluded a [3,8,6,2,7,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,7,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,7,0,8] (by decide +kernel)))

theorem node_876 : Excluded a [3,8,6,2,7,1,0] :=
  predecessor_excluded a [3,8,6,2,7,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_877 : Excluded a [3,8,6,2,7,1,4] :=
  source_excluded a [3,8,6,2,7,1,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_878 : Excluded a [3,8,6,2,7,1,5] :=
  source_excluded a [3,8,6,2,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_875 : Excluded a [3,8,6,2,7,1] :=
  branch_excluded a [3,8,6,2,7,1] (by decide)
    (fin9_cases _
      node_876
      (invalid_excluded a [3,8,6,2,7,1,1] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,7,1,2] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,7,1,3] (by decide +kernel))
      node_877
      node_878
      (invalid_excluded a [3,8,6,2,7,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,7,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,7,1,8] (by decide +kernel)))

theorem node_879 : Excluded a [3,8,6,2,7,4] :=
  predecessor_excluded a [3,8,6,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_870 : Excluded a [3,8,6,2,7] :=
  branch_excluded a [3,8,6,2,7] (by decide)
    (fin9_cases _
      node_871
      node_875
      (invalid_excluded a [3,8,6,2,7,2] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,7,3] (by decide +kernel))
      node_879
      (invalid_excluded a [3,8,6,2,7,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,7,6] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,7,8] (by decide +kernel)))

theorem node_855 : Excluded a [3,8,6,2] :=
  branch_excluded a [3,8,6,2] (by decide)
    (fin9_cases _
      node_856
      node_862
      (invalid_excluded a [3,8,6,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,4] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,6,2,6] (by decide +kernel))
      node_870
      (invalid_excluded a [3,8,6,2,8] (by decide +kernel)))

theorem node_880 : Excluded a [3,8,6,5] :=
  source_excluded a [3,8,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_881 : Excluded a [3,8,6,7] :=
  predecessor_excluded a [3,8,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_852 : Excluded a [3,8,6] :=
  branch_excluded a [3,8,6] (by decide)
    (fin9_cases _
      node_853
      node_854
      node_855
      (invalid_excluded a [3,8,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,6,4] (by decide +kernel))
      node_880
      (invalid_excluded a [3,8,6,6] (by decide +kernel))
      node_881
      (invalid_excluded a [3,8,6,8] (by decide +kernel)))

theorem node_883 : Excluded a [3,8,7,0] :=
  predecessor_excluded a [3,8,7,0] 2 0 0 3 (by decide) (by decide +kernel)

theorem node_884 : Excluded a [3,8,7,1] :=
  source_excluded a [3,8,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_887 : Excluded a [3,8,7,2,0,1] :=
  predecessor_excluded a [3,8,7,2,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_889 : Excluded a [3,8,7,2,0,4,1] :=
  predecessor_excluded a [3,8,7,2,0,4,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_890 : Excluded a [3,8,7,2,0,4,5] :=
  predecessor_excluded a [3,8,7,2,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_888 : Excluded a [3,8,7,2,0,4] :=
  branch_excluded a [3,8,7,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,2,0,4,0] (by decide +kernel))
      node_889
      (invalid_excluded a [3,8,7,2,0,4,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,0,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,0,4,4] (by decide +kernel))
      node_890
      (invalid_excluded a [3,8,7,2,0,4,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,0,4,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,0,4,8] (by decide +kernel)))

theorem node_886 : Excluded a [3,8,7,2,0] :=
  branch_excluded a [3,8,7,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,2,0,0] (by decide +kernel))
      node_887
      (invalid_excluded a [3,8,7,2,0,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,0,3] (by decide +kernel))
      node_888
      (invalid_excluded a [3,8,7,2,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,0,8] (by decide +kernel)))

theorem node_892 : Excluded a [3,8,7,2,1,0] :=
  predecessor_excluded a [3,8,7,2,1,0] 2 0 4 5 (by decide) (by decide +kernel)

theorem node_896 : Excluded a [3,8,7,2,1,4,0,5,6] :=
  predecessor_excluded a [3,8,7,2,1,4,0,5,6] 0 7 8 2 (by decide) (by decide +kernel)

theorem node_895 : Excluded a [3,8,7,2,1,4,0,5] :=
  branch_excluded a [3,8,7,2,1,4,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,2,1,4,0,5,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,5,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,5,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,5,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,5,4] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,5,5] (by decide +kernel))
      node_896
      (invalid_excluded a [3,8,7,2,1,4,0,5,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,5,8] (by decide +kernel)))

def b_898 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 8
  | 2 => 7
  | 3 => 2
  | 4 => 1
  | 5 => 4
  | 6 => 0
  | 7 => 6
  | 8 => 5
  | _ => 0

def cert_898 : LosingRegion (edgeOf a b_898) 0 :=
  losingMask a b_898 0 1437076304366780531344384
    (by decide +kernel) (by decide +kernel)

theorem node_898 : Excluded a [3,8,7,2,1,4,0,6,5] :=
  losing_excluded a [3,8,7,2,1,4,0,6,5] (by decide) b_898 (by decide +kernel) 2 0 4 cert_898 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_898 2 0 ∧ 4 ≠ 2 ∧ maskRegion 1437076304366780531344384 2 4; decide +kernel)

theorem node_897 : Excluded a [3,8,7,2,1,4,0,6] :=
  branch_excluded a [3,8,7,2,1,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,2,1,4,0,6,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,6,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,6,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,6,4] (by decide +kernel))
      node_898
      (invalid_excluded a [3,8,7,2,1,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,6,8] (by decide +kernel)))

theorem node_894 : Excluded a [3,8,7,2,1,4,0] :=
  branch_excluded a [3,8,7,2,1,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,2,1,4,0,0] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,4] (by decide +kernel))
      node_895
      node_897
      (invalid_excluded a [3,8,7,2,1,4,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,0,8] (by decide +kernel)))

theorem node_899 : Excluded a [3,8,7,2,1,4,5] :=
  predecessor_excluded a [3,8,7,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_893 : Excluded a [3,8,7,2,1,4] :=
  branch_excluded a [3,8,7,2,1,4] (by decide)
    (fin9_cases _
      node_894
      (invalid_excluded a [3,8,7,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,4] (by decide +kernel))
      node_899
      (invalid_excluded a [3,8,7,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,4,8] (by decide +kernel)))

theorem node_891 : Excluded a [3,8,7,2,1] :=
  branch_excluded a [3,8,7,2,1] (by decide)
    (fin9_cases _
      node_892
      (invalid_excluded a [3,8,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,3] (by decide +kernel))
      node_893
      (invalid_excluded a [3,8,7,2,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,1,8] (by decide +kernel)))

theorem node_900 : Excluded a [3,8,7,2,6] :=
  source_excluded a [3,8,7,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_885 : Excluded a [3,8,7,2] :=
  branch_excluded a [3,8,7,2] (by decide)
    (fin9_cases _
      node_886
      node_891
      (invalid_excluded a [3,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,5] (by decide +kernel))
      node_900
      (invalid_excluded a [3,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,2,8] (by decide +kernel)))

theorem node_901 : Excluded a [3,8,7,5] :=
  source_excluded a [3,8,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_904 : Excluded a [3,8,7,6,0,1] :=
  predecessor_excluded a [3,8,7,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_905 : Excluded a [3,8,7,6,0,2] :=
  predecessor_excluded a [3,8,7,6,0,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_906 : Excluded a [3,8,7,6,0,4] :=
  source_excluded a [3,8,7,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_903 : Excluded a [3,8,7,6,0] :=
  branch_excluded a [3,8,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,6,0,0] (by decide +kernel))
      node_904
      node_905
      (invalid_excluded a [3,8,7,6,0,3] (by decide +kernel))
      node_906
      (invalid_excluded a [3,8,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,0,8] (by decide +kernel)))

theorem node_908 : Excluded a [3,8,7,6,1,0] :=
  predecessor_excluded a [3,8,7,6,1,0] 2 0 4 5 (by decide) (by decide +kernel)

theorem node_909 : Excluded a [3,8,7,6,1,2] :=
  predecessor_excluded a [3,8,7,6,1,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_910 : Excluded a [3,8,7,6,1,4] :=
  source_excluded a [3,8,7,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_907 : Excluded a [3,8,7,6,1] :=
  branch_excluded a [3,8,7,6,1] (by decide)
    (fin9_cases _
      node_908
      (invalid_excluded a [3,8,7,6,1,1] (by decide +kernel))
      node_909
      (invalid_excluded a [3,8,7,6,1,3] (by decide +kernel))
      node_910
      (invalid_excluded a [3,8,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,1,8] (by decide +kernel)))

theorem node_913 : Excluded a [3,8,7,6,2,0,1] :=
  predecessor_excluded a [3,8,7,6,2,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_914 : Excluded a [3,8,7,6,2,0,4] :=
  source_excluded a [3,8,7,6,2,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_915 : Excluded a [3,8,7,6,2,0,5] :=
  predecessor_excluded a [3,8,7,6,2,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_912 : Excluded a [3,8,7,6,2,0] :=
  branch_excluded a [3,8,7,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,8,7,6,2,0,0] (by decide +kernel))
      node_913
      (invalid_excluded a [3,8,7,6,2,0,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,0,3] (by decide +kernel))
      node_914
      node_915
      (invalid_excluded a [3,8,7,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,0,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,0,8] (by decide +kernel)))

theorem node_917 : Excluded a [3,8,7,6,2,1,0] :=
  predecessor_excluded a [3,8,7,6,2,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_918 : Excluded a [3,8,7,6,2,1,4] :=
  source_excluded a [3,8,7,6,2,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_919 : Excluded a [3,8,7,6,2,1,5] :=
  predecessor_excluded a [3,8,7,6,2,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_916 : Excluded a [3,8,7,6,2,1] :=
  branch_excluded a [3,8,7,6,2,1] (by decide)
    (fin9_cases _
      node_917
      (invalid_excluded a [3,8,7,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,3] (by decide +kernel))
      node_918
      node_919
      (invalid_excluded a [3,8,7,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,1,8] (by decide +kernel)))

theorem node_920 : Excluded a [3,8,7,6,2,4] :=
  source_excluded a [3,8,7,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_911 : Excluded a [3,8,7,6,2] :=
  branch_excluded a [3,8,7,6,2] (by decide)
    (fin9_cases _
      node_912
      node_916
      (invalid_excluded a [3,8,7,6,2,2] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,3] (by decide +kernel))
      node_920
      (invalid_excluded a [3,8,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,2,8] (by decide +kernel)))

theorem node_902 : Excluded a [3,8,7,6] :=
  branch_excluded a [3,8,7,6] (by decide)
    (fin9_cases _
      node_903
      node_907
      node_911
      (invalid_excluded a [3,8,7,6,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,6,8] (by decide +kernel)))

theorem node_882 : Excluded a [3,8,7] :=
  branch_excluded a [3,8,7] (by decide)
    (fin9_cases _
      node_883
      node_884
      node_885
      (invalid_excluded a [3,8,7,3] (by decide +kernel))
      (invalid_excluded a [3,8,7,4] (by decide +kernel))
      node_901
      node_902
      (invalid_excluded a [3,8,7,7] (by decide +kernel))
      (invalid_excluded a [3,8,7,8] (by decide +kernel)))

theorem node_825 : Excluded a [3,8] :=
  branch_excluded a [3,8] (by decide)
    (fin9_cases _
      node_826
      node_827
      (invalid_excluded a [3,8,2] (by decide +kernel))
      (invalid_excluded a [3,8,3] (by decide +kernel))
      node_828
      node_829
      node_852
      node_882
      (invalid_excluded a [3,8,8] (by decide +kernel)))

theorem node_506 : Excluded a [3] :=
  branch_excluded a [3] (by decide)
    (fin9_cases _
      (invalid_excluded a [3,0] (by decide +kernel))
      (invalid_excluded a [3,1] (by decide +kernel))
      node_507
      (invalid_excluded a [3,3] (by decide +kernel))
      node_508
      node_509
      node_612
      node_709
      node_825)

theorem node_923 : Excluded a [4,2,0] :=
  source_excluded a [4,2,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_924 : Excluded a [4,2,1] :=
  predecessor_excluded a [4,2,1] 3 1 1 2 (by decide) (by decide +kernel)

theorem node_926 : Excluded a [4,2,5,0] :=
  source_excluded a [4,2,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_927 : Excluded a [4,2,5,1] :=
  source_excluded a [4,2,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_928 : Excluded a [4,2,5,6] :=
  predecessor_excluded a [4,2,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_930 : Excluded a [4,2,5,7,0] :=
  predecessor_excluded a [4,2,5,7,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_931 : Excluded a [4,2,5,7,1] :=
  source_excluded a [4,2,5,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_932 : Excluded a [4,2,5,7,3] :=
  source_excluded a [4,2,5,7,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_933 : Excluded a [4,2,5,7,6] :=
  source_excluded a [4,2,5,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_934 : Excluded a [4,2,5,7,8] :=
  predecessor_excluded a [4,2,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_929 : Excluded a [4,2,5,7] :=
  branch_excluded a [4,2,5,7] (by decide)
    (fin9_cases _
      node_930
      node_931
      (invalid_excluded a [4,2,5,7,2] (by decide +kernel))
      node_932
      (invalid_excluded a [4,2,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,2,5,7,5] (by decide +kernel))
      node_933
      (invalid_excluded a [4,2,5,7,7] (by decide +kernel))
      node_934)

theorem node_936 : Excluded a [4,2,5,8,0] :=
  predecessor_excluded a [4,2,5,8,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_937 : Excluded a [4,2,5,8,1] :=
  source_excluded a [4,2,5,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_938 : Excluded a [4,2,5,8,3] :=
  source_excluded a [4,2,5,8,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_939 : Excluded a [4,2,5,8,6] :=
  source_excluded a [4,2,5,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_942 : Excluded a [4,2,5,8,7,0,1] :=
  predecessor_excluded a [4,2,5,8,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_943 : Excluded a [4,2,5,8,7,0,3] :=
  predecessor_excluded a [4,2,5,8,7,0,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_941 : Excluded a [4,2,5,8,7,0] :=
  branch_excluded a [4,2,5,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,2,5,8,7,0,0] (by decide +kernel))
      node_942
      (invalid_excluded a [4,2,5,8,7,0,2] (by decide +kernel))
      node_943
      (invalid_excluded a [4,2,5,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [4,2,5,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [4,2,5,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,2,5,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,2,5,8,7,0,8] (by decide +kernel)))

theorem node_945 : Excluded a [4,2,5,8,7,1,0] :=
  predecessor_excluded a [4,2,5,8,7,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_946 : Excluded a [4,2,5,8,7,1,3] :=
  predecessor_excluded a [4,2,5,8,7,1,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_944 : Excluded a [4,2,5,8,7,1] :=
  branch_excluded a [4,2,5,8,7,1] (by decide)
    (fin9_cases _
      node_945
      (invalid_excluded a [4,2,5,8,7,1,1] (by decide +kernel))
      (invalid_excluded a [4,2,5,8,7,1,2] (by decide +kernel))
      node_946
      (invalid_excluded a [4,2,5,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [4,2,5,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [4,2,5,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [4,2,5,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [4,2,5,8,7,1,8] (by decide +kernel)))

theorem node_947 : Excluded a [4,2,5,8,7,3] :=
  source_excluded a [4,2,5,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_940 : Excluded a [4,2,5,8,7] :=
  branch_excluded a [4,2,5,8,7] (by decide)
    (fin9_cases _
      node_941
      node_944
      (invalid_excluded a [4,2,5,8,7,2] (by decide +kernel))
      node_947
      (invalid_excluded a [4,2,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,2,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,2,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,2,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,2,5,8,7,8] (by decide +kernel)))

theorem node_935 : Excluded a [4,2,5,8] :=
  branch_excluded a [4,2,5,8] (by decide)
    (fin9_cases _
      node_936
      node_937
      (invalid_excluded a [4,2,5,8,2] (by decide +kernel))
      node_938
      (invalid_excluded a [4,2,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,2,5,8,5] (by decide +kernel))
      node_939
      node_940
      (invalid_excluded a [4,2,5,8,8] (by decide +kernel)))

theorem node_925 : Excluded a [4,2,5] :=
  branch_excluded a [4,2,5] (by decide)
    (fin9_cases _
      node_926
      node_927
      (invalid_excluded a [4,2,5,2] (by decide +kernel))
      (invalid_excluded a [4,2,5,3] (by decide +kernel))
      (invalid_excluded a [4,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,2,5,5] (by decide +kernel))
      node_928
      node_929
      node_935)

theorem node_949 : Excluded a [4,2,6,0] :=
  source_excluded a [4,2,6,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_950 : Excluded a [4,2,6,1] :=
  source_excluded a [4,2,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_951 : Excluded a [4,2,6,5] :=
  source_excluded a [4,2,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_952 : Excluded a [4,2,6,7] :=
  predecessor_excluded a [4,2,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_954 : Excluded a [4,2,6,8,0] :=
  predecessor_excluded a [4,2,6,8,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_955 : Excluded a [4,2,6,8,1] :=
  source_excluded a [4,2,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_958 : Excluded a [4,2,6,8,3,0,1] :=
  predecessor_excluded a [4,2,6,8,3,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_960 : Excluded a [4,2,6,8,3,0,5,1] :=
  predecessor_excluded a [4,2,6,8,3,0,5,1] 0 2 7 1 (by decide) (by decide +kernel)

theorem node_959 : Excluded a [4,2,6,8,3,0,5] :=
  branch_excluded a [4,2,6,8,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,2,6,8,3,0,5,0] (by decide +kernel))
      node_960
      (invalid_excluded a [4,2,6,8,3,0,5,2] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,0,5,5] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,0,5,6] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,0,5,8] (by decide +kernel)))

theorem node_957 : Excluded a [4,2,6,8,3,0] :=
  branch_excluded a [4,2,6,8,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,2,6,8,3,0,0] (by decide +kernel))
      node_958
      (invalid_excluded a [4,2,6,8,3,0,2] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,0,4] (by decide +kernel))
      node_959
      (invalid_excluded a [4,2,6,8,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,0,8] (by decide +kernel)))

theorem node_962 : Excluded a [4,2,6,8,3,1,0] :=
  predecessor_excluded a [4,2,6,8,3,1,0] 2 0 5 6 (by decide) (by decide +kernel)

def b_965 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 2
  | 2 => 6
  | 3 => 8
  | 4 => 3
  | 5 => 1
  | 6 => 5
  | 7 => 0
  | 8 => 7
  | _ => 0

def cert_965 : LosingRegion (edgeOf a b_965) 0 :=
  losingMask a b_965 0 1512339020194119496500224
    (by decide +kernel) (by decide +kernel)

theorem node_965 : Excluded a [4,2,6,8,3,1,5,0,7] :=
  losing_excluded a [4,2,6,8,3,1,5,0,7] (by decide) b_965 (by decide +kernel) 2 0 5 cert_965 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_965 2 0 ∧ 5 ≠ 2 ∧ maskRegion 1512339020194119496500224 2 5; decide +kernel)

theorem node_964 : Excluded a [4,2,6,8,3,1,5,0] :=
  branch_excluded a [4,2,6,8,3,1,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,2,6,8,3,1,5,0,0] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,5,0,1] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,5,0,2] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,5,0,3] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,5,0,4] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,5,0,5] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,5,0,6] (by decide +kernel))
      node_965
      (invalid_excluded a [4,2,6,8,3,1,5,0,8] (by decide +kernel)))

theorem node_963 : Excluded a [4,2,6,8,3,1,5] :=
  branch_excluded a [4,2,6,8,3,1,5] (by decide)
    (fin9_cases _
      node_964
      (invalid_excluded a [4,2,6,8,3,1,5,1] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,5,2] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,5,3] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,5,4] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,5,5] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,5,6] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,5,8] (by decide +kernel)))

theorem node_961 : Excluded a [4,2,6,8,3,1] :=
  branch_excluded a [4,2,6,8,3,1] (by decide)
    (fin9_cases _
      node_962
      (invalid_excluded a [4,2,6,8,3,1,1] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,2] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,3] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,4] (by decide +kernel))
      node_963
      (invalid_excluded a [4,2,6,8,3,1,6] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,7] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,1,8] (by decide +kernel)))

theorem node_966 : Excluded a [4,2,6,8,3,7] :=
  source_excluded a [4,2,6,8,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_956 : Excluded a [4,2,6,8,3] :=
  branch_excluded a [4,2,6,8,3] (by decide)
    (fin9_cases _
      node_957
      node_961
      (invalid_excluded a [4,2,6,8,3,2] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,4] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,5] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,3,6] (by decide +kernel))
      node_966
      (invalid_excluded a [4,2,6,8,3,8] (by decide +kernel)))

theorem node_969 : Excluded a [4,2,6,8,7,0,1] :=
  predecessor_excluded a [4,2,6,8,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_970 : Excluded a [4,2,6,8,7,0,3] :=
  source_excluded a [4,2,6,8,7,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_971 : Excluded a [4,2,6,8,7,0,5] :=
  source_excluded a [4,2,6,8,7,0,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_968 : Excluded a [4,2,6,8,7,0] :=
  branch_excluded a [4,2,6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,2,6,8,7,0,0] (by decide +kernel))
      node_969
      (invalid_excluded a [4,2,6,8,7,0,2] (by decide +kernel))
      node_970
      (invalid_excluded a [4,2,6,8,7,0,4] (by decide +kernel))
      node_971
      (invalid_excluded a [4,2,6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,7,0,8] (by decide +kernel)))

theorem node_973 : Excluded a [4,2,6,8,7,1,0] :=
  predecessor_excluded a [4,2,6,8,7,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_974 : Excluded a [4,2,6,8,7,1,3] :=
  source_excluded a [4,2,6,8,7,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_975 : Excluded a [4,2,6,8,7,1,5] :=
  source_excluded a [4,2,6,8,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_972 : Excluded a [4,2,6,8,7,1] :=
  branch_excluded a [4,2,6,8,7,1] (by decide)
    (fin9_cases _
      node_973
      (invalid_excluded a [4,2,6,8,7,1,1] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,7,1,2] (by decide +kernel))
      node_974
      (invalid_excluded a [4,2,6,8,7,1,4] (by decide +kernel))
      node_975
      (invalid_excluded a [4,2,6,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,7,1,8] (by decide +kernel)))

theorem node_976 : Excluded a [4,2,6,8,7,3] :=
  source_excluded a [4,2,6,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_967 : Excluded a [4,2,6,8,7] :=
  branch_excluded a [4,2,6,8,7] (by decide)
    (fin9_cases _
      node_968
      node_972
      (invalid_excluded a [4,2,6,8,7,2] (by decide +kernel))
      node_976
      (invalid_excluded a [4,2,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,7,8] (by decide +kernel)))

theorem node_953 : Excluded a [4,2,6,8] :=
  branch_excluded a [4,2,6,8] (by decide)
    (fin9_cases _
      node_954
      node_955
      (invalid_excluded a [4,2,6,8,2] (by decide +kernel))
      node_956
      (invalid_excluded a [4,2,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,2,6,8,6] (by decide +kernel))
      node_967
      (invalid_excluded a [4,2,6,8,8] (by decide +kernel)))

theorem node_948 : Excluded a [4,2,6] :=
  branch_excluded a [4,2,6] (by decide)
    (fin9_cases _
      node_949
      node_950
      (invalid_excluded a [4,2,6,2] (by decide +kernel))
      (invalid_excluded a [4,2,6,3] (by decide +kernel))
      (invalid_excluded a [4,2,6,4] (by decide +kernel))
      node_951
      (invalid_excluded a [4,2,6,6] (by decide +kernel))
      node_952
      node_953)

theorem node_978 : Excluded a [4,2,7,0] :=
  source_excluded a [4,2,7,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_979 : Excluded a [4,2,7,1] :=
  source_excluded a [4,2,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_980 : Excluded a [4,2,7,5] :=
  source_excluded a [4,2,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_982 : Excluded a [4,2,7,6,0] :=
  predecessor_excluded a [4,2,7,6,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_983 : Excluded a [4,2,7,6,1] :=
  source_excluded a [4,2,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_984 : Excluded a [4,2,7,6,3] :=
  predecessor_excluded a [4,2,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_987 : Excluded a [4,2,7,6,8,0,1] :=
  predecessor_excluded a [4,2,7,6,8,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_988 : Excluded a [4,2,7,6,8,0,3] :=
  source_excluded a [4,2,7,6,8,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_989 : Excluded a [4,2,7,6,8,0,5] :=
  predecessor_excluded a [4,2,7,6,8,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_986 : Excluded a [4,2,7,6,8,0] :=
  branch_excluded a [4,2,7,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,2,7,6,8,0,0] (by decide +kernel))
      node_987
      (invalid_excluded a [4,2,7,6,8,0,2] (by decide +kernel))
      node_988
      (invalid_excluded a [4,2,7,6,8,0,4] (by decide +kernel))
      node_989
      (invalid_excluded a [4,2,7,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [4,2,7,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [4,2,7,6,8,0,8] (by decide +kernel)))

theorem node_991 : Excluded a [4,2,7,6,8,1,0] :=
  predecessor_excluded a [4,2,7,6,8,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_992 : Excluded a [4,2,7,6,8,1,3] :=
  source_excluded a [4,2,7,6,8,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_993 : Excluded a [4,2,7,6,8,1,5] :=
  predecessor_excluded a [4,2,7,6,8,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_990 : Excluded a [4,2,7,6,8,1] :=
  branch_excluded a [4,2,7,6,8,1] (by decide)
    (fin9_cases _
      node_991
      (invalid_excluded a [4,2,7,6,8,1,1] (by decide +kernel))
      (invalid_excluded a [4,2,7,6,8,1,2] (by decide +kernel))
      node_992
      (invalid_excluded a [4,2,7,6,8,1,4] (by decide +kernel))
      node_993
      (invalid_excluded a [4,2,7,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [4,2,7,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [4,2,7,6,8,1,8] (by decide +kernel)))

theorem node_994 : Excluded a [4,2,7,6,8,3] :=
  source_excluded a [4,2,7,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_985 : Excluded a [4,2,7,6,8] :=
  branch_excluded a [4,2,7,6,8] (by decide)
    (fin9_cases _
      node_986
      node_990
      (invalid_excluded a [4,2,7,6,8,2] (by decide +kernel))
      node_994
      (invalid_excluded a [4,2,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,2,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,2,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,2,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,2,7,6,8,8] (by decide +kernel)))

theorem node_981 : Excluded a [4,2,7,6] :=
  branch_excluded a [4,2,7,6] (by decide)
    (fin9_cases _
      node_982
      node_983
      (invalid_excluded a [4,2,7,6,2] (by decide +kernel))
      node_984
      (invalid_excluded a [4,2,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,2,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,2,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,2,7,6,7] (by decide +kernel))
      node_985)

theorem node_995 : Excluded a [4,2,7,8] :=
  predecessor_excluded a [4,2,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_977 : Excluded a [4,2,7] :=
  branch_excluded a [4,2,7] (by decide)
    (fin9_cases _
      node_978
      node_979
      (invalid_excluded a [4,2,7,2] (by decide +kernel))
      (invalid_excluded a [4,2,7,3] (by decide +kernel))
      (invalid_excluded a [4,2,7,4] (by decide +kernel))
      node_980
      node_981
      (invalid_excluded a [4,2,7,7] (by decide +kernel))
      node_995)

theorem node_997 : Excluded a [4,2,8,0] :=
  source_excluded a [4,2,8,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_998 : Excluded a [4,2,8,1] :=
  source_excluded a [4,2,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_999 : Excluded a [4,2,8,5] :=
  source_excluded a [4,2,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1001 : Excluded a [4,2,8,6,0] :=
  predecessor_excluded a [4,2,8,6,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1002 : Excluded a [4,2,8,6,1] :=
  source_excluded a [4,2,8,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1003 : Excluded a [4,2,8,6,3] :=
  predecessor_excluded a [4,2,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1004 : Excluded a [4,2,8,6,7] :=
  predecessor_excluded a [4,2,8,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_1000 : Excluded a [4,2,8,6] :=
  branch_excluded a [4,2,8,6] (by decide)
    (fin9_cases _
      node_1001
      node_1002
      (invalid_excluded a [4,2,8,6,2] (by decide +kernel))
      node_1003
      (invalid_excluded a [4,2,8,6,4] (by decide +kernel))
      (invalid_excluded a [4,2,8,6,5] (by decide +kernel))
      (invalid_excluded a [4,2,8,6,6] (by decide +kernel))
      node_1004
      (invalid_excluded a [4,2,8,6,8] (by decide +kernel)))

theorem node_1006 : Excluded a [4,2,8,7,0] :=
  predecessor_excluded a [4,2,8,7,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1007 : Excluded a [4,2,8,7,1] :=
  source_excluded a [4,2,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1010 : Excluded a [4,2,8,7,3,0,1] :=
  predecessor_excluded a [4,2,8,7,3,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_1012 : Excluded a [4,2,8,7,3,0,5,1] :=
  predecessor_excluded a [4,2,8,7,3,0,5,1] 0 2 7 1 (by decide) (by decide +kernel)

theorem node_1013 : Excluded a [4,2,8,7,3,0,5,6] :=
  predecessor_excluded a [4,2,8,7,3,0,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_1011 : Excluded a [4,2,8,7,3,0,5] :=
  branch_excluded a [4,2,8,7,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,2,8,7,3,0,5,0] (by decide +kernel))
      node_1012
      (invalid_excluded a [4,2,8,7,3,0,5,2] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,0,5,5] (by decide +kernel))
      node_1013
      (invalid_excluded a [4,2,8,7,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,0,5,8] (by decide +kernel)))

theorem node_1009 : Excluded a [4,2,8,7,3,0] :=
  branch_excluded a [4,2,8,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,2,8,7,3,0,0] (by decide +kernel))
      node_1010
      (invalid_excluded a [4,2,8,7,3,0,2] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,0,4] (by decide +kernel))
      node_1011
      (invalid_excluded a [4,2,8,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,0,8] (by decide +kernel)))

theorem node_1015 : Excluded a [4,2,8,7,3,1,0] :=
  predecessor_excluded a [4,2,8,7,3,1,0] 2 0 5 6 (by decide) (by decide +kernel)

def b_1018 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 2
  | 2 => 8
  | 3 => 7
  | 4 => 3
  | 5 => 1
  | 6 => 5
  | 7 => 0
  | 8 => 6
  | _ => 0

def cert_1018 : LosingRegion (edgeOf a b_1018) 0 :=
  losingMask a b_1018 0 1663454747645943382803456
    (by decide +kernel) (by decide +kernel)

theorem node_1018 : Excluded a [4,2,8,7,3,1,5,0,6] :=
  losing_excluded a [4,2,8,7,3,1,5,0,6] (by decide) b_1018 (by decide +kernel) 2 0 4 cert_1018 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1018 2 0 ∧ 4 ≠ 2 ∧ maskRegion 1663454747645943382803456 2 4; decide +kernel)

theorem node_1017 : Excluded a [4,2,8,7,3,1,5,0] :=
  branch_excluded a [4,2,8,7,3,1,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,2,8,7,3,1,5,0,0] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,1,5,0,1] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,1,5,0,2] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,1,5,0,3] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,1,5,0,4] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,1,5,0,5] (by decide +kernel))
      node_1018
      (invalid_excluded a [4,2,8,7,3,1,5,0,7] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,1,5,0,8] (by decide +kernel)))

theorem node_1019 : Excluded a [4,2,8,7,3,1,5,6] :=
  predecessor_excluded a [4,2,8,7,3,1,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_1016 : Excluded a [4,2,8,7,3,1,5] :=
  branch_excluded a [4,2,8,7,3,1,5] (by decide)
    (fin9_cases _
      node_1017
      (invalid_excluded a [4,2,8,7,3,1,5,1] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,1,5,2] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,1,5,3] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,1,5,4] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,1,5,5] (by decide +kernel))
      node_1019
      (invalid_excluded a [4,2,8,7,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,1,5,8] (by decide +kernel)))

theorem node_1014 : Excluded a [4,2,8,7,3,1] :=
  branch_excluded a [4,2,8,7,3,1] (by decide)
    (fin9_cases _
      node_1015
      (invalid_excluded a [4,2,8,7,3,1,1] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,1,2] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,1,3] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,1,4] (by decide +kernel))
      node_1016
      (invalid_excluded a [4,2,8,7,3,1,6] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,1,8] (by decide +kernel)))

theorem node_1008 : Excluded a [4,2,8,7,3] :=
  branch_excluded a [4,2,8,7,3] (by decide)
    (fin9_cases _
      node_1009
      node_1014
      (invalid_excluded a [4,2,8,7,3,2] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,4] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,3,8] (by decide +kernel)))

theorem node_1020 : Excluded a [4,2,8,7,6] :=
  source_excluded a [4,2,8,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1005 : Excluded a [4,2,8,7] :=
  branch_excluded a [4,2,8,7] (by decide)
    (fin9_cases _
      node_1006
      node_1007
      (invalid_excluded a [4,2,8,7,2] (by decide +kernel))
      node_1008
      (invalid_excluded a [4,2,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,5] (by decide +kernel))
      node_1020
      (invalid_excluded a [4,2,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,2,8,7,8] (by decide +kernel)))

theorem node_996 : Excluded a [4,2,8] :=
  branch_excluded a [4,2,8] (by decide)
    (fin9_cases _
      node_997
      node_998
      (invalid_excluded a [4,2,8,2] (by decide +kernel))
      (invalid_excluded a [4,2,8,3] (by decide +kernel))
      (invalid_excluded a [4,2,8,4] (by decide +kernel))
      node_999
      node_1000
      node_1005
      (invalid_excluded a [4,2,8,8] (by decide +kernel)))

theorem node_922 : Excluded a [4,2] :=
  branch_excluded a [4,2] (by decide)
    (fin9_cases _
      node_923
      node_924
      (invalid_excluded a [4,2,2] (by decide +kernel))
      (invalid_excluded a [4,2,3] (by decide +kernel))
      (invalid_excluded a [4,2,4] (by decide +kernel))
      node_925
      node_948
      node_977
      node_996)

theorem node_1021 : Excluded a [4,3] :=
  predecessor_excluded a [4,3] 2 4 1 0 (by decide) (by decide +kernel)

theorem node_1022 : Excluded a [4,5] :=
  predecessor_excluded a [4,5] 2 5 0 1 (by decide) (by decide +kernel)

theorem node_1024 : Excluded a [4,6,0] :=
  predecessor_excluded a [4,6,0] 1 4 2 0 (by decide) (by decide +kernel)

theorem node_1026 : Excluded a [4,6,1,0] :=
  source_excluded a [4,6,1,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1028 : Excluded a [4,6,1,2,0] :=
  predecessor_excluded a [4,6,1,2,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1029 : Excluded a [4,6,1,2,3] :=
  predecessor_excluded a [4,6,1,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1031 : Excluded a [4,6,1,2,7,0] :=
  source_excluded a [4,6,1,2,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_1033 : Excluded a [4,6,1,2,7,3,0] :=
  source_excluded a [4,6,1,2,7,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1034 : Excluded a [4,6,1,2,7,3,5] :=
  source_excluded a [4,6,1,2,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1035 : Excluded a [4,6,1,2,7,3,8] :=
  source_excluded a [4,6,1,2,7,3,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_1032 : Excluded a [4,6,1,2,7,3] :=
  branch_excluded a [4,6,1,2,7,3] (by decide)
    (fin9_cases _
      node_1033
      (invalid_excluded a [4,6,1,2,7,3,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,7,3,4] (by decide +kernel))
      node_1034
      (invalid_excluded a [4,6,1,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,7,3,7] (by decide +kernel))
      node_1035)

theorem node_1036 : Excluded a [4,6,1,2,7,8] :=
  predecessor_excluded a [4,6,1,2,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_1030 : Excluded a [4,6,1,2,7] :=
  branch_excluded a [4,6,1,2,7] (by decide)
    (fin9_cases _
      node_1031
      (invalid_excluded a [4,6,1,2,7,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,7,2] (by decide +kernel))
      node_1032
      (invalid_excluded a [4,6,1,2,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,7,7] (by decide +kernel))
      node_1036)

theorem node_1038 : Excluded a [4,6,1,2,8,0] :=
  source_excluded a [4,6,1,2,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_1040 : Excluded a [4,6,1,2,8,3,0] :=
  source_excluded a [4,6,1,2,8,3,0] 1 2 6 (by decide) (by decide +kernel)

def b_1043 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 6
  | 2 => 1
  | 3 => 2
  | 4 => 8
  | 5 => 3
  | 6 => 5
  | 7 => 0
  | 8 => 7
  | _ => 0

def cert_1043 : LosingRegion (edgeOf a b_1043) 0 :=
  losingMask a b_1043 0 1814577409046949576573952
    (by decide +kernel) (by decide +kernel)

theorem node_1043 : Excluded a [4,6,1,2,8,3,5,0,7] :=
  losing_excluded a [4,6,1,2,8,3,5,0,7] (by decide) b_1043 (by decide +kernel) 2 0 0 cert_1043 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1043 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1814577409046949576573952 2 0; decide +kernel)

theorem node_1042 : Excluded a [4,6,1,2,8,3,5,0] :=
  branch_excluded a [4,6,1,2,8,3,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,2,8,3,5,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,5,0,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,5,0,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,5,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,5,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,5,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,5,0,6] (by decide +kernel))
      node_1043
      (invalid_excluded a [4,6,1,2,8,3,5,0,8] (by decide +kernel)))

theorem node_1041 : Excluded a [4,6,1,2,8,3,5] :=
  branch_excluded a [4,6,1,2,8,3,5] (by decide)
    (fin9_cases _
      node_1042
      (invalid_excluded a [4,6,1,2,8,3,5,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,5,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,5,8] (by decide +kernel)))

theorem node_1039 : Excluded a [4,6,1,2,8,3] :=
  branch_excluded a [4,6,1,2,8,3] (by decide)
    (fin9_cases _
      node_1040
      (invalid_excluded a [4,6,1,2,8,3,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,4] (by decide +kernel))
      node_1041
      (invalid_excluded a [4,6,1,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,3,8] (by decide +kernel)))

theorem node_1044 : Excluded a [4,6,1,2,8,7] :=
  source_excluded a [4,6,1,2,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1037 : Excluded a [4,6,1,2,8] :=
  branch_excluded a [4,6,1,2,8] (by decide)
    (fin9_cases _
      node_1038
      (invalid_excluded a [4,6,1,2,8,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,2] (by decide +kernel))
      node_1039
      (invalid_excluded a [4,6,1,2,8,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,8,6] (by decide +kernel))
      node_1044
      (invalid_excluded a [4,6,1,2,8,8] (by decide +kernel)))

theorem node_1027 : Excluded a [4,6,1,2] :=
  branch_excluded a [4,6,1,2] (by decide)
    (fin9_cases _
      node_1028
      (invalid_excluded a [4,6,1,2,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,2] (by decide +kernel))
      node_1029
      (invalid_excluded a [4,6,1,2,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,2,6] (by decide +kernel))
      node_1030
      node_1037)

theorem node_1045 : Excluded a [4,6,1,5] :=
  source_excluded a [4,6,1,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1047 : Excluded a [4,6,1,7,0] :=
  predecessor_excluded a [4,6,1,7,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1049 : Excluded a [4,6,1,7,2,0] :=
  source_excluded a [4,6,1,7,2,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_1050 : Excluded a [4,6,1,7,2,3] :=
  predecessor_excluded a [4,6,1,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1052 : Excluded a [4,6,1,7,2,8,0] :=
  source_excluded a [4,6,1,7,2,8,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1053 : Excluded a [4,6,1,7,2,8,3] :=
  source_excluded a [4,6,1,7,2,8,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1054 : Excluded a [4,6,1,7,2,8,5] :=
  predecessor_excluded a [4,6,1,7,2,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_1051 : Excluded a [4,6,1,7,2,8] :=
  branch_excluded a [4,6,1,7,2,8] (by decide)
    (fin9_cases _
      node_1052
      (invalid_excluded a [4,6,1,7,2,8,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,2,8,2] (by decide +kernel))
      node_1053
      (invalid_excluded a [4,6,1,7,2,8,4] (by decide +kernel))
      node_1054
      (invalid_excluded a [4,6,1,7,2,8,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,2,8,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,2,8,8] (by decide +kernel)))

theorem node_1048 : Excluded a [4,6,1,7,2] :=
  branch_excluded a [4,6,1,7,2] (by decide)
    (fin9_cases _
      node_1049
      (invalid_excluded a [4,6,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,2,2] (by decide +kernel))
      node_1050
      (invalid_excluded a [4,6,1,7,2,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,2,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,2,7] (by decide +kernel))
      node_1051)

theorem node_1056 : Excluded a [4,6,1,7,3,0] :=
  source_excluded a [4,6,1,7,3,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_1058 : Excluded a [4,6,1,7,3,2,0] :=
  source_excluded a [4,6,1,7,3,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1060 : Excluded a [4,6,1,7,3,2,5,0] :=
  branch_excluded a [4,6,1,7,3,2,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,7,3,2,5,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,5,0,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,5,0,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,5,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,5,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,5,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,5,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,5,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,5,0,8] (by decide +kernel)))

theorem node_1059 : Excluded a [4,6,1,7,3,2,5] :=
  branch_excluded a [4,6,1,7,3,2,5] (by decide)
    (fin9_cases _
      node_1060
      (invalid_excluded a [4,6,1,7,3,2,5,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,5,8] (by decide +kernel)))

theorem node_1061 : Excluded a [4,6,1,7,3,2,8] :=
  source_excluded a [4,6,1,7,3,2,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_1057 : Excluded a [4,6,1,7,3,2] :=
  branch_excluded a [4,6,1,7,3,2] (by decide)
    (fin9_cases _
      node_1058
      (invalid_excluded a [4,6,1,7,3,2,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,4] (by decide +kernel))
      node_1059
      (invalid_excluded a [4,6,1,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,2,7] (by decide +kernel))
      node_1061)

theorem node_1063 : Excluded a [4,6,1,7,3,8,0] :=
  source_excluded a [4,6,1,7,3,8,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1064 : Excluded a [4,6,1,7,3,8,2] :=
  predecessor_excluded a [4,6,1,7,3,8,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_1065 : Excluded a [4,6,1,7,3,8,5] :=
  predecessor_excluded a [4,6,1,7,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_1062 : Excluded a [4,6,1,7,3,8] :=
  branch_excluded a [4,6,1,7,3,8] (by decide)
    (fin9_cases _
      node_1063
      (invalid_excluded a [4,6,1,7,3,8,1] (by decide +kernel))
      node_1064
      (invalid_excluded a [4,6,1,7,3,8,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,8,4] (by decide +kernel))
      node_1065
      (invalid_excluded a [4,6,1,7,3,8,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,8,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,8,8] (by decide +kernel)))

theorem node_1055 : Excluded a [4,6,1,7,3] :=
  branch_excluded a [4,6,1,7,3] (by decide)
    (fin9_cases _
      node_1056
      (invalid_excluded a [4,6,1,7,3,1] (by decide +kernel))
      node_1057
      (invalid_excluded a [4,6,1,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,3,7] (by decide +kernel))
      node_1062)

theorem node_1066 : Excluded a [4,6,1,7,8] :=
  predecessor_excluded a [4,6,1,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_1046 : Excluded a [4,6,1,7] :=
  branch_excluded a [4,6,1,7] (by decide)
    (fin9_cases _
      node_1047
      (invalid_excluded a [4,6,1,7,1] (by decide +kernel))
      node_1048
      node_1055
      (invalid_excluded a [4,6,1,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,7,7] (by decide +kernel))
      node_1066)

theorem node_1068 : Excluded a [4,6,1,8,0] :=
  predecessor_excluded a [4,6,1,8,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1069 : Excluded a [4,6,1,8,2] :=
  predecessor_excluded a [4,6,1,8,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1071 : Excluded a [4,6,1,8,3,0] :=
  source_excluded a [4,6,1,8,3,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_1073 : Excluded a [4,6,1,8,3,2,0] :=
  source_excluded a [4,6,1,8,3,2,0] 1 2 6 (by decide) (by decide +kernel)

def b_1076 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 6
  | 2 => 1
  | 3 => 8
  | 4 => 3
  | 5 => 2
  | 6 => 5
  | 7 => 0
  | 8 => 7
  | _ => 0

def cert_1076 : LosingRegion (edgeOf a b_1076) 0 :=
  losingMask a b_1076 0 1210114491851466202940416
    (by decide +kernel) (by decide +kernel)

theorem node_1076 : Excluded a [4,6,1,8,3,2,5,0,7] :=
  losing_excluded a [4,6,1,8,3,2,5,0,7] (by decide) b_1076 (by decide +kernel) 3 0 7 cert_1076 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_1076 3 0 ∧ 7 ≠ 3 ∧ maskRegion 1210114491851466202940416 3 7; decide +kernel)

theorem node_1075 : Excluded a [4,6,1,8,3,2,5,0] :=
  branch_excluded a [4,6,1,8,3,2,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,8,3,2,5,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,5,0,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,5,0,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,5,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,5,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,5,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,5,0,6] (by decide +kernel))
      node_1076
      (invalid_excluded a [4,6,1,8,3,2,5,0,8] (by decide +kernel)))

theorem node_1074 : Excluded a [4,6,1,8,3,2,5] :=
  branch_excluded a [4,6,1,8,3,2,5] (by decide)
    (fin9_cases _
      node_1075
      (invalid_excluded a [4,6,1,8,3,2,5,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,5,8] (by decide +kernel)))

theorem node_1072 : Excluded a [4,6,1,8,3,2] :=
  branch_excluded a [4,6,1,8,3,2] (by decide)
    (fin9_cases _
      node_1073
      (invalid_excluded a [4,6,1,8,3,2,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,4] (by decide +kernel))
      node_1074
      (invalid_excluded a [4,6,1,8,3,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,2,8] (by decide +kernel)))

theorem node_1077 : Excluded a [4,6,1,8,3,7] :=
  source_excluded a [4,6,1,8,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1070 : Excluded a [4,6,1,8,3] :=
  branch_excluded a [4,6,1,8,3] (by decide)
    (fin9_cases _
      node_1071
      (invalid_excluded a [4,6,1,8,3,1] (by decide +kernel))
      node_1072
      (invalid_excluded a [4,6,1,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,3,6] (by decide +kernel))
      node_1077
      (invalid_excluded a [4,6,1,8,3,8] (by decide +kernel)))

theorem node_1079 : Excluded a [4,6,1,8,7,0] :=
  source_excluded a [4,6,1,8,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_1081 : Excluded a [4,6,1,8,7,2,0] :=
  source_excluded a [4,6,1,8,7,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1082 : Excluded a [4,6,1,8,7,2,3] :=
  predecessor_excluded a [4,6,1,8,7,2,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_1083 : Excluded a [4,6,1,8,7,2,5] :=
  source_excluded a [4,6,1,8,7,2,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1080 : Excluded a [4,6,1,8,7,2] :=
  branch_excluded a [4,6,1,8,7,2] (by decide)
    (fin9_cases _
      node_1081
      (invalid_excluded a [4,6,1,8,7,2,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,2] (by decide +kernel))
      node_1082
      (invalid_excluded a [4,6,1,8,7,2,4] (by decide +kernel))
      node_1083
      (invalid_excluded a [4,6,1,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,2,8] (by decide +kernel)))

theorem node_1085 : Excluded a [4,6,1,8,7,3,0] :=
  source_excluded a [4,6,1,8,7,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1088 : Excluded a [4,6,1,8,7,3,2,0,5] :=
  predecessor_excluded a [4,6,1,8,7,3,2,0,5] 0 3 8 5 (by decide) (by decide +kernel)

theorem node_1087 : Excluded a [4,6,1,8,7,3,2,0] :=
  branch_excluded a [4,6,1,8,7,3,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,1,8,7,3,2,0,0] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,2,0,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,2,0,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,2,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,2,0,4] (by decide +kernel))
      node_1088
      (invalid_excluded a [4,6,1,8,7,3,2,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,2,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,2,0,8] (by decide +kernel)))

theorem node_1089 : Excluded a [4,6,1,8,7,3,2,5] :=
  source_excluded a [4,6,1,8,7,3,2,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_1086 : Excluded a [4,6,1,8,7,3,2] :=
  branch_excluded a [4,6,1,8,7,3,2] (by decide)
    (fin9_cases _
      node_1087
      (invalid_excluded a [4,6,1,8,7,3,2,1] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,2,4] (by decide +kernel))
      node_1089
      (invalid_excluded a [4,6,1,8,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,2,8] (by decide +kernel)))

theorem node_1090 : Excluded a [4,6,1,8,7,3,5] :=
  source_excluded a [4,6,1,8,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1084 : Excluded a [4,6,1,8,7,3] :=
  branch_excluded a [4,6,1,8,7,3] (by decide)
    (fin9_cases _
      node_1085
      (invalid_excluded a [4,6,1,8,7,3,1] (by decide +kernel))
      node_1086
      (invalid_excluded a [4,6,1,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,4] (by decide +kernel))
      node_1090
      (invalid_excluded a [4,6,1,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,3,8] (by decide +kernel)))

theorem node_1078 : Excluded a [4,6,1,8,7] :=
  branch_excluded a [4,6,1,8,7] (by decide)
    (fin9_cases _
      node_1079
      (invalid_excluded a [4,6,1,8,7,1] (by decide +kernel))
      node_1080
      node_1084
      (invalid_excluded a [4,6,1,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,7,8] (by decide +kernel)))

theorem node_1067 : Excluded a [4,6,1,8] :=
  branch_excluded a [4,6,1,8] (by decide)
    (fin9_cases _
      node_1068
      (invalid_excluded a [4,6,1,8,1] (by decide +kernel))
      node_1069
      node_1070
      (invalid_excluded a [4,6,1,8,4] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [4,6,1,8,6] (by decide +kernel))
      node_1078
      (invalid_excluded a [4,6,1,8,8] (by decide +kernel)))

theorem node_1025 : Excluded a [4,6,1] :=
  branch_excluded a [4,6,1] (by decide)
    (fin9_cases _
      node_1026
      (invalid_excluded a [4,6,1,1] (by decide +kernel))
      node_1027
      (invalid_excluded a [4,6,1,3] (by decide +kernel))
      (invalid_excluded a [4,6,1,4] (by decide +kernel))
      node_1045
      (invalid_excluded a [4,6,1,6] (by decide +kernel))
      node_1046
      node_1067)

theorem node_1092 : Excluded a [4,6,5,0] :=
  source_excluded a [4,6,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1093 : Excluded a [4,6,5,1] :=
  source_excluded a [4,6,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1094 : Excluded a [4,6,5,2] :=
  predecessor_excluded a [4,6,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_1096 : Excluded a [4,6,5,7,0] :=
  predecessor_excluded a [4,6,5,7,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1097 : Excluded a [4,6,5,7,1] :=
  source_excluded a [4,6,5,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1098 : Excluded a [4,6,5,7,2] :=
  source_excluded a [4,6,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1099 : Excluded a [4,6,5,7,3] :=
  source_excluded a [4,6,5,7,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_1100 : Excluded a [4,6,5,7,8] :=
  predecessor_excluded a [4,6,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_1095 : Excluded a [4,6,5,7] :=
  branch_excluded a [4,6,5,7] (by decide)
    (fin9_cases _
      node_1096
      node_1097
      node_1098
      node_1099
      (invalid_excluded a [4,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,7,7] (by decide +kernel))
      node_1100)

theorem node_1102 : Excluded a [4,6,5,8,0] :=
  predecessor_excluded a [4,6,5,8,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1103 : Excluded a [4,6,5,8,1] :=
  source_excluded a [4,6,5,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1104 : Excluded a [4,6,5,8,2] :=
  source_excluded a [4,6,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1105 : Excluded a [4,6,5,8,3] :=
  source_excluded a [4,6,5,8,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_1107 : Excluded a [4,6,5,8,7,0] :=
  source_excluded a [4,6,5,8,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_1108 : Excluded a [4,6,5,8,7,1] :=
  source_excluded a [4,6,5,8,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_1110 : Excluded a [4,6,5,8,7,2,0] :=
  source_excluded a [4,6,5,8,7,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1111 : Excluded a [4,6,5,8,7,2,1] :=
  predecessor_excluded a [4,6,5,8,7,2,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_1112 : Excluded a [4,6,5,8,7,2,3] :=
  predecessor_excluded a [4,6,5,8,7,2,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_1109 : Excluded a [4,6,5,8,7,2] :=
  branch_excluded a [4,6,5,8,7,2] (by decide)
    (fin9_cases _
      node_1110
      node_1111
      (invalid_excluded a [4,6,5,8,7,2,2] (by decide +kernel))
      node_1112
      (invalid_excluded a [4,6,5,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,2,8] (by decide +kernel)))

theorem node_1113 : Excluded a [4,6,5,8,7,3] :=
  source_excluded a [4,6,5,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1106 : Excluded a [4,6,5,8,7] :=
  branch_excluded a [4,6,5,8,7] (by decide)
    (fin9_cases _
      node_1107
      node_1108
      node_1109
      node_1113
      (invalid_excluded a [4,6,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,7,8] (by decide +kernel)))

theorem node_1101 : Excluded a [4,6,5,8] :=
  branch_excluded a [4,6,5,8] (by decide)
    (fin9_cases _
      node_1102
      node_1103
      node_1104
      node_1105
      (invalid_excluded a [4,6,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,8,6] (by decide +kernel))
      node_1106
      (invalid_excluded a [4,6,5,8,8] (by decide +kernel)))

theorem node_1091 : Excluded a [4,6,5] :=
  branch_excluded a [4,6,5] (by decide)
    (fin9_cases _
      node_1092
      node_1093
      node_1094
      (invalid_excluded a [4,6,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,5,6] (by decide +kernel))
      node_1095
      node_1101)

theorem node_1115 : Excluded a [4,6,7,0] :=
  source_excluded a [4,6,7,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1116 : Excluded a [4,6,7,1] :=
  source_excluded a [4,6,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1118 : Excluded a [4,6,7,2,0] :=
  predecessor_excluded a [4,6,7,2,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1119 : Excluded a [4,6,7,2,1] :=
  source_excluded a [4,6,7,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1120 : Excluded a [4,6,7,2,3] :=
  predecessor_excluded a [4,6,7,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1122 : Excluded a [4,6,7,2,8,0] :=
  source_excluded a [4,6,7,2,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_1123 : Excluded a [4,6,7,2,8,1] :=
  source_excluded a [4,6,7,2,8,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_1125 : Excluded a [4,6,7,2,8,3,0] :=
  source_excluded a [4,6,7,2,8,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1126 : Excluded a [4,6,7,2,8,3,1] :=
  predecessor_excluded a [4,6,7,2,8,3,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_1129 : Excluded a [4,6,7,2,8,3,5,0,1] :=
  predecessor_excluded a [4,6,7,2,8,3,5,0,1] 2 1 7 8 (by decide) (by decide +kernel)

theorem node_1128 : Excluded a [4,6,7,2,8,3,5,0] :=
  branch_excluded a [4,6,7,2,8,3,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,7,2,8,3,5,0,0] (by decide +kernel))
      node_1129
      (invalid_excluded a [4,6,7,2,8,3,5,0,2] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,0,8] (by decide +kernel)))

theorem node_1131 : Excluded a [4,6,7,2,8,3,5,1,0] :=
  predecessor_excluded a [4,6,7,2,8,3,5,1,0] 2 0 7 8 (by decide) (by decide +kernel)

theorem node_1130 : Excluded a [4,6,7,2,8,3,5,1] :=
  branch_excluded a [4,6,7,2,8,3,5,1] (by decide)
    (fin9_cases _
      node_1131
      (invalid_excluded a [4,6,7,2,8,3,5,1,1] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,1,2] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,1,3] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,1,4] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,1,5] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,1,6] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,1,7] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,1,8] (by decide +kernel)))

theorem node_1127 : Excluded a [4,6,7,2,8,3,5] :=
  branch_excluded a [4,6,7,2,8,3,5] (by decide)
    (fin9_cases _
      node_1128
      node_1130
      (invalid_excluded a [4,6,7,2,8,3,5,2] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,5,8] (by decide +kernel)))

theorem node_1124 : Excluded a [4,6,7,2,8,3] :=
  branch_excluded a [4,6,7,2,8,3] (by decide)
    (fin9_cases _
      node_1125
      node_1126
      (invalid_excluded a [4,6,7,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,4] (by decide +kernel))
      node_1127
      (invalid_excluded a [4,6,7,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,3,8] (by decide +kernel)))

theorem node_1121 : Excluded a [4,6,7,2,8] :=
  branch_excluded a [4,6,7,2,8] (by decide)
    (fin9_cases _
      node_1122
      node_1123
      (invalid_excluded a [4,6,7,2,8,2] (by decide +kernel))
      node_1124
      (invalid_excluded a [4,6,7,2,8,4] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,5] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,6] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,7] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,8,8] (by decide +kernel)))

theorem node_1117 : Excluded a [4,6,7,2] :=
  branch_excluded a [4,6,7,2] (by decide)
    (fin9_cases _
      node_1118
      node_1119
      (invalid_excluded a [4,6,7,2,2] (by decide +kernel))
      node_1120
      (invalid_excluded a [4,6,7,2,4] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,5] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,7,2,7] (by decide +kernel))
      node_1121)

theorem node_1132 : Excluded a [4,6,7,5] :=
  source_excluded a [4,6,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1133 : Excluded a [4,6,7,8] :=
  predecessor_excluded a [4,6,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_1114 : Excluded a [4,6,7] :=
  branch_excluded a [4,6,7] (by decide)
    (fin9_cases _
      node_1115
      node_1116
      node_1117
      (invalid_excluded a [4,6,7,3] (by decide +kernel))
      (invalid_excluded a [4,6,7,4] (by decide +kernel))
      node_1132
      (invalid_excluded a [4,6,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,7,7] (by decide +kernel))
      node_1133)

theorem node_1135 : Excluded a [4,6,8,0] :=
  source_excluded a [4,6,8,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1136 : Excluded a [4,6,8,1] :=
  source_excluded a [4,6,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1137 : Excluded a [4,6,8,2] :=
  predecessor_excluded a [4,6,8,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_1138 : Excluded a [4,6,8,5] :=
  source_excluded a [4,6,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1140 : Excluded a [4,6,8,7,0] :=
  predecessor_excluded a [4,6,8,7,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1141 : Excluded a [4,6,8,7,1] :=
  source_excluded a [4,6,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1143 : Excluded a [4,6,8,7,2,0] :=
  source_excluded a [4,6,8,7,2,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_1144 : Excluded a [4,6,8,7,2,1] :=
  source_excluded a [4,6,8,7,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_1145 : Excluded a [4,6,8,7,2,3] :=
  predecessor_excluded a [4,6,8,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1142 : Excluded a [4,6,8,7,2] :=
  branch_excluded a [4,6,8,7,2] (by decide)
    (fin9_cases _
      node_1143
      node_1144
      (invalid_excluded a [4,6,8,7,2,2] (by decide +kernel))
      node_1145
      (invalid_excluded a [4,6,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,2,8] (by decide +kernel)))

theorem node_1147 : Excluded a [4,6,8,7,3,0] :=
  source_excluded a [4,6,8,7,3,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_1148 : Excluded a [4,6,8,7,3,1] :=
  source_excluded a [4,6,8,7,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_1150 : Excluded a [4,6,8,7,3,2,0] :=
  source_excluded a [4,6,8,7,3,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1151 : Excluded a [4,6,8,7,3,2,1] :=
  predecessor_excluded a [4,6,8,7,3,2,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_1154 : Excluded a [4,6,8,7,3,2,5,0,1] :=
  predecessor_excluded a [4,6,8,7,3,2,5,0,1] 2 1 7 8 (by decide) (by decide +kernel)

theorem node_1153 : Excluded a [4,6,8,7,3,2,5,0] :=
  branch_excluded a [4,6,8,7,3,2,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,6,8,7,3,2,5,0,0] (by decide +kernel))
      node_1154
      (invalid_excluded a [4,6,8,7,3,2,5,0,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,0,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,0,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,0,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,0,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,0,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,0,8] (by decide +kernel)))

theorem node_1156 : Excluded a [4,6,8,7,3,2,5,1,0] :=
  predecessor_excluded a [4,6,8,7,3,2,5,1,0] 2 0 7 8 (by decide) (by decide +kernel)

theorem node_1155 : Excluded a [4,6,8,7,3,2,5,1] :=
  branch_excluded a [4,6,8,7,3,2,5,1] (by decide)
    (fin9_cases _
      node_1156
      (invalid_excluded a [4,6,8,7,3,2,5,1,1] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,1,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,1,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,1,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,1,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,1,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,1,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,1,8] (by decide +kernel)))

theorem node_1152 : Excluded a [4,6,8,7,3,2,5] :=
  branch_excluded a [4,6,8,7,3,2,5] (by decide)
    (fin9_cases _
      node_1153
      node_1155
      (invalid_excluded a [4,6,8,7,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,5,8] (by decide +kernel)))

theorem node_1149 : Excluded a [4,6,8,7,3,2] :=
  branch_excluded a [4,6,8,7,3,2] (by decide)
    (fin9_cases _
      node_1150
      node_1151
      (invalid_excluded a [4,6,8,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,4] (by decide +kernel))
      node_1152
      (invalid_excluded a [4,6,8,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,2,8] (by decide +kernel)))

theorem node_1146 : Excluded a [4,6,8,7,3] :=
  branch_excluded a [4,6,8,7,3] (by decide)
    (fin9_cases _
      node_1147
      node_1148
      node_1149
      (invalid_excluded a [4,6,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,3,8] (by decide +kernel)))

theorem node_1139 : Excluded a [4,6,8,7] :=
  branch_excluded a [4,6,8,7] (by decide)
    (fin9_cases _
      node_1140
      node_1141
      node_1142
      node_1146
      (invalid_excluded a [4,6,8,7,4] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,6,8,7,8] (by decide +kernel)))

theorem node_1134 : Excluded a [4,6,8] :=
  branch_excluded a [4,6,8] (by decide)
    (fin9_cases _
      node_1135
      node_1136
      node_1137
      (invalid_excluded a [4,6,8,3] (by decide +kernel))
      (invalid_excluded a [4,6,8,4] (by decide +kernel))
      node_1138
      (invalid_excluded a [4,6,8,6] (by decide +kernel))
      node_1139
      (invalid_excluded a [4,6,8,8] (by decide +kernel)))

theorem node_1023 : Excluded a [4,6] :=
  branch_excluded a [4,6] (by decide)
    (fin9_cases _
      node_1024
      node_1025
      (invalid_excluded a [4,6,2] (by decide +kernel))
      (invalid_excluded a [4,6,3] (by decide +kernel))
      (invalid_excluded a [4,6,4] (by decide +kernel))
      node_1091
      (invalid_excluded a [4,6,6] (by decide +kernel))
      node_1114
      node_1134)

theorem node_1158 : Excluded a [4,7,0] :=
  predecessor_excluded a [4,7,0] 1 4 2 0 (by decide) (by decide +kernel)

theorem node_1160 : Excluded a [4,7,1,0] :=
  source_excluded a [4,7,1,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1162 : Excluded a [4,7,1,2,0] :=
  predecessor_excluded a [4,7,1,2,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1163 : Excluded a [4,7,1,2,3] :=
  predecessor_excluded a [4,7,1,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1164 : Excluded a [4,7,1,2,6] :=
  source_excluded a [4,7,1,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1168 : Excluded a [4,7,1,2,8,0,3,5] :=
  source_excluded a [4,7,1,2,8,0,3,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_1170 : Excluded a [4,7,1,2,8,0,3,6,5] :=
  source_excluded a [4,7,1,2,8,0,3,6,5] 4 0 8 (by decide) (by decide +kernel)

theorem node_1169 : Excluded a [4,7,1,2,8,0,3,6] :=
  branch_excluded a [4,7,1,2,8,0,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,2,8,0,3,6,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,3,6,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,3,6,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,3,6,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,3,6,4] (by decide +kernel))
      node_1170
      (invalid_excluded a [4,7,1,2,8,0,3,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,3,6,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,3,6,8] (by decide +kernel)))

theorem node_1167 : Excluded a [4,7,1,2,8,0,3] :=
  branch_excluded a [4,7,1,2,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,2,8,0,3,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,3,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,3,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,3,4] (by decide +kernel))
      node_1168
      node_1169
      (invalid_excluded a [4,7,1,2,8,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,3,8] (by decide +kernel)))

theorem node_1172 : Excluded a [4,7,1,2,8,0,5,3] :=
  predecessor_excluded a [4,7,1,2,8,0,5,3] 0 2 7 3 (by decide) (by decide +kernel)

theorem node_1173 : Excluded a [4,7,1,2,8,0,5,6] :=
  predecessor_excluded a [4,7,1,2,8,0,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_1171 : Excluded a [4,7,1,2,8,0,5] :=
  branch_excluded a [4,7,1,2,8,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,2,8,0,5,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,5,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,5,2] (by decide +kernel))
      node_1172
      (invalid_excluded a [4,7,1,2,8,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,5,5] (by decide +kernel))
      node_1173
      (invalid_excluded a [4,7,1,2,8,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,5,8] (by decide +kernel)))

theorem node_1166 : Excluded a [4,7,1,2,8,0] :=
  branch_excluded a [4,7,1,2,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,2,8,0,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,2] (by decide +kernel))
      node_1167
      (invalid_excluded a [4,7,1,2,8,0,4] (by decide +kernel))
      node_1171
      (invalid_excluded a [4,7,1,2,8,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,0,8] (by decide +kernel)))

theorem node_1175 : Excluded a [4,7,1,2,8,3,0] :=
  source_excluded a [4,7,1,2,8,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1177 : Excluded a [4,7,1,2,8,3,5,0] :=
  source_excluded a [4,7,1,2,8,3,5,0] 1 2 7 (by decide) (by decide +kernel)

theorem node_1178 : Excluded a [4,7,1,2,8,3,5,6] :=
  predecessor_excluded a [4,7,1,2,8,3,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_1176 : Excluded a [4,7,1,2,8,3,5] :=
  branch_excluded a [4,7,1,2,8,3,5] (by decide)
    (fin9_cases _
      node_1177
      (invalid_excluded a [4,7,1,2,8,3,5,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,3,5,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,3,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,3,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,3,5,5] (by decide +kernel))
      node_1178
      (invalid_excluded a [4,7,1,2,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,3,5,8] (by decide +kernel)))

theorem node_1174 : Excluded a [4,7,1,2,8,3] :=
  branch_excluded a [4,7,1,2,8,3] (by decide)
    (fin9_cases _
      node_1175
      (invalid_excluded a [4,7,1,2,8,3,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,3,4] (by decide +kernel))
      node_1176
      (invalid_excluded a [4,7,1,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,3,8] (by decide +kernel)))

theorem node_1165 : Excluded a [4,7,1,2,8] :=
  branch_excluded a [4,7,1,2,8] (by decide)
    (fin9_cases _
      node_1166
      (invalid_excluded a [4,7,1,2,8,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,2] (by decide +kernel))
      node_1174
      (invalid_excluded a [4,7,1,2,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,8,8] (by decide +kernel)))

theorem node_1161 : Excluded a [4,7,1,2] :=
  branch_excluded a [4,7,1,2] (by decide)
    (fin9_cases _
      node_1162
      (invalid_excluded a [4,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,2] (by decide +kernel))
      node_1163
      (invalid_excluded a [4,7,1,2,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,2,5] (by decide +kernel))
      node_1164
      (invalid_excluded a [4,7,1,2,7] (by decide +kernel))
      node_1165)

theorem node_1179 : Excluded a [4,7,1,5] :=
  source_excluded a [4,7,1,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1181 : Excluded a [4,7,1,6,0] :=
  predecessor_excluded a [4,7,1,6,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1185 : Excluded a [4,7,1,6,2,0,3,5] :=
  branch_excluded a [4,7,1,6,2,0,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,2,0,3,5,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,3,5,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,3,5,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,3,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,3,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,3,5,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,3,5,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,3,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,3,5,8] (by decide +kernel)))

theorem node_1184 : Excluded a [4,7,1,6,2,0,3] :=
  branch_excluded a [4,7,1,6,2,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,2,0,3,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,3,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,3,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,3,4] (by decide +kernel))
      node_1185
      (invalid_excluded a [4,7,1,6,2,0,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,3,8] (by decide +kernel)))

theorem node_1186 : Excluded a [4,7,1,6,2,0,5] :=
  predecessor_excluded a [4,7,1,6,2,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_1187 : Excluded a [4,7,1,6,2,0,8] :=
  source_excluded a [4,7,1,6,2,0,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_1183 : Excluded a [4,7,1,6,2,0] :=
  branch_excluded a [4,7,1,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,2,0,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,2] (by decide +kernel))
      node_1184
      (invalid_excluded a [4,7,1,6,2,0,4] (by decide +kernel))
      node_1186
      (invalid_excluded a [4,7,1,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,0,7] (by decide +kernel))
      node_1187)

theorem node_1188 : Excluded a [4,7,1,6,2,3] :=
  source_excluded a [4,7,1,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1190 : Excluded a [4,7,1,6,2,8,0] :=
  source_excluded a [4,7,1,6,2,8,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1192 : Excluded a [4,7,1,6,2,8,3,0] :=
  source_excluded a [4,7,1,6,2,8,3,0] 1 2 7 (by decide) (by decide +kernel)

theorem node_1193 : Excluded a [4,7,1,6,2,8,3,5] :=
  source_excluded a [4,7,1,6,2,8,3,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_1191 : Excluded a [4,7,1,6,2,8,3] :=
  branch_excluded a [4,7,1,6,2,8,3] (by decide)
    (fin9_cases _
      node_1192
      (invalid_excluded a [4,7,1,6,2,8,3,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,8,3,4] (by decide +kernel))
      node_1193
      (invalid_excluded a [4,7,1,6,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,8,3,8] (by decide +kernel)))

theorem node_1194 : Excluded a [4,7,1,6,2,8,5] :=
  predecessor_excluded a [4,7,1,6,2,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_1189 : Excluded a [4,7,1,6,2,8] :=
  branch_excluded a [4,7,1,6,2,8] (by decide)
    (fin9_cases _
      node_1190
      (invalid_excluded a [4,7,1,6,2,8,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,8,2] (by decide +kernel))
      node_1191
      (invalid_excluded a [4,7,1,6,2,8,4] (by decide +kernel))
      node_1194
      (invalid_excluded a [4,7,1,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,8,8] (by decide +kernel)))

theorem node_1182 : Excluded a [4,7,1,6,2] :=
  branch_excluded a [4,7,1,6,2] (by decide)
    (fin9_cases _
      node_1183
      (invalid_excluded a [4,7,1,6,2,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,2] (by decide +kernel))
      node_1188
      (invalid_excluded a [4,7,1,6,2,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,2,7] (by decide +kernel))
      node_1189)

theorem node_1195 : Excluded a [4,7,1,6,3] :=
  predecessor_excluded a [4,7,1,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1199 : Excluded a [4,7,1,6,8,0,2,3] :=
  predecessor_excluded a [4,7,1,6,8,0,2,3] 0 3 6 7 (by decide) (by decide +kernel)

theorem node_1200 : Excluded a [4,7,1,6,8,0,2,5] :=
  source_excluded a [4,7,1,6,8,0,2,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_1198 : Excluded a [4,7,1,6,8,0,2] :=
  branch_excluded a [4,7,1,6,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,8,0,2,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,2,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,2,2] (by decide +kernel))
      node_1199
      (invalid_excluded a [4,7,1,6,8,0,2,4] (by decide +kernel))
      node_1200
      (invalid_excluded a [4,7,1,6,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,2,8] (by decide +kernel)))

theorem node_1202 : Excluded a [4,7,1,6,8,0,3,2] :=
  source_excluded a [4,7,1,6,8,0,3,2] 7 0 8 (by decide) (by decide +kernel)

theorem node_1203 : Excluded a [4,7,1,6,8,0,3,5] :=
  source_excluded a [4,7,1,6,8,0,3,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_1201 : Excluded a [4,7,1,6,8,0,3] :=
  branch_excluded a [4,7,1,6,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,8,0,3,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,3,1] (by decide +kernel))
      node_1202
      (invalid_excluded a [4,7,1,6,8,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,3,4] (by decide +kernel))
      node_1203
      (invalid_excluded a [4,7,1,6,8,0,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,3,8] (by decide +kernel)))

theorem node_1204 : Excluded a [4,7,1,6,8,0,5] :=
  predecessor_excluded a [4,7,1,6,8,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_1197 : Excluded a [4,7,1,6,8,0] :=
  branch_excluded a [4,7,1,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,6,8,0,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,1] (by decide +kernel))
      node_1198
      node_1201
      (invalid_excluded a [4,7,1,6,8,0,4] (by decide +kernel))
      node_1204
      (invalid_excluded a [4,7,1,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,0,8] (by decide +kernel)))

theorem node_1205 : Excluded a [4,7,1,6,8,2] :=
  predecessor_excluded a [4,7,1,6,8,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1206 : Excluded a [4,7,1,6,8,3] :=
  source_excluded a [4,7,1,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1196 : Excluded a [4,7,1,6,8] :=
  branch_excluded a [4,7,1,6,8] (by decide)
    (fin9_cases _
      node_1197
      (invalid_excluded a [4,7,1,6,8,1] (by decide +kernel))
      node_1205
      node_1206
      (invalid_excluded a [4,7,1,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,8,8] (by decide +kernel)))

theorem node_1180 : Excluded a [4,7,1,6] :=
  branch_excluded a [4,7,1,6] (by decide)
    (fin9_cases _
      node_1181
      (invalid_excluded a [4,7,1,6,1] (by decide +kernel))
      node_1182
      node_1195
      (invalid_excluded a [4,7,1,6,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,6,7] (by decide +kernel))
      node_1196)

theorem node_1208 : Excluded a [4,7,1,8,0] :=
  predecessor_excluded a [4,7,1,8,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1209 : Excluded a [4,7,1,8,2] :=
  predecessor_excluded a [4,7,1,8,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1214 : Excluded a [4,7,1,8,3,0,2,5,6] :=
  source_excluded a [4,7,1,8,3,0,2,5,6] 8 0 6 (by decide) (by decide +kernel)

theorem node_1213 : Excluded a [4,7,1,8,3,0,2,5] :=
  branch_excluded a [4,7,1,8,3,0,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,8,3,0,2,5,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,2,5,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,2,5,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,2,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,2,5,5] (by decide +kernel))
      node_1214
      (invalid_excluded a [4,7,1,8,3,0,2,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,2,5,8] (by decide +kernel)))

theorem node_1215 : Excluded a [4,7,1,8,3,0,2,6] :=
  predecessor_excluded a [4,7,1,8,3,0,2,6] 0 2 7 6 (by decide) (by decide +kernel)

theorem node_1212 : Excluded a [4,7,1,8,3,0,2] :=
  branch_excluded a [4,7,1,8,3,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,8,3,0,2,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,2,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,2,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,2,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,2,4] (by decide +kernel))
      node_1213
      node_1215
      (invalid_excluded a [4,7,1,8,3,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,2,8] (by decide +kernel)))

theorem node_1217 : Excluded a [4,7,1,8,3,0,5,2] :=
  source_excluded a [4,7,1,8,3,0,5,2] 7 0 8 (by decide) (by decide +kernel)

theorem node_1218 : Excluded a [4,7,1,8,3,0,5,6] :=
  predecessor_excluded a [4,7,1,8,3,0,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_1216 : Excluded a [4,7,1,8,3,0,5] :=
  branch_excluded a [4,7,1,8,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,8,3,0,5,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,5,1] (by decide +kernel))
      node_1217
      (invalid_excluded a [4,7,1,8,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,5,5] (by decide +kernel))
      node_1218
      (invalid_excluded a [4,7,1,8,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,5,8] (by decide +kernel)))

theorem node_1211 : Excluded a [4,7,1,8,3,0] :=
  branch_excluded a [4,7,1,8,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,1,8,3,0,0] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,1] (by decide +kernel))
      node_1212
      (invalid_excluded a [4,7,1,8,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,4] (by decide +kernel))
      node_1216
      (invalid_excluded a [4,7,1,8,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,0,8] (by decide +kernel)))

theorem node_1220 : Excluded a [4,7,1,8,3,2,0] :=
  source_excluded a [4,7,1,8,3,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1222 : Excluded a [4,7,1,8,3,2,5,0] :=
  source_excluded a [4,7,1,8,3,2,5,0] 1 2 7 (by decide) (by decide +kernel)

theorem node_1223 : Excluded a [4,7,1,8,3,2,5,6] :=
  predecessor_excluded a [4,7,1,8,3,2,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_1221 : Excluded a [4,7,1,8,3,2,5] :=
  branch_excluded a [4,7,1,8,3,2,5] (by decide)
    (fin9_cases _
      node_1222
      (invalid_excluded a [4,7,1,8,3,2,5,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,5,5] (by decide +kernel))
      node_1223
      (invalid_excluded a [4,7,1,8,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,5,8] (by decide +kernel)))

theorem node_1219 : Excluded a [4,7,1,8,3,2] :=
  branch_excluded a [4,7,1,8,3,2] (by decide)
    (fin9_cases _
      node_1220
      (invalid_excluded a [4,7,1,8,3,2,1] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,4] (by decide +kernel))
      node_1221
      (invalid_excluded a [4,7,1,8,3,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,2,8] (by decide +kernel)))

theorem node_1210 : Excluded a [4,7,1,8,3] :=
  branch_excluded a [4,7,1,8,3] (by decide)
    (fin9_cases _
      node_1211
      (invalid_excluded a [4,7,1,8,3,1] (by decide +kernel))
      node_1219
      (invalid_excluded a [4,7,1,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,5] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,3,8] (by decide +kernel)))

theorem node_1224 : Excluded a [4,7,1,8,6] :=
  source_excluded a [4,7,1,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1207 : Excluded a [4,7,1,8] :=
  branch_excluded a [4,7,1,8] (by decide)
    (fin9_cases _
      node_1208
      (invalid_excluded a [4,7,1,8,1] (by decide +kernel))
      node_1209
      node_1210
      (invalid_excluded a [4,7,1,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,5] (by decide +kernel))
      node_1224
      (invalid_excluded a [4,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,1,8,8] (by decide +kernel)))

theorem node_1159 : Excluded a [4,7,1] :=
  branch_excluded a [4,7,1] (by decide)
    (fin9_cases _
      node_1160
      (invalid_excluded a [4,7,1,1] (by decide +kernel))
      node_1161
      (invalid_excluded a [4,7,1,3] (by decide +kernel))
      (invalid_excluded a [4,7,1,4] (by decide +kernel))
      node_1179
      node_1180
      (invalid_excluded a [4,7,1,7] (by decide +kernel))
      node_1207)

theorem node_1226 : Excluded a [4,7,5,0] :=
  source_excluded a [4,7,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1227 : Excluded a [4,7,5,1] :=
  source_excluded a [4,7,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1228 : Excluded a [4,7,5,2] :=
  predecessor_excluded a [4,7,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_1229 : Excluded a [4,7,5,6] :=
  predecessor_excluded a [4,7,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_1231 : Excluded a [4,7,5,8,0] :=
  predecessor_excluded a [4,7,5,8,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1232 : Excluded a [4,7,5,8,1] :=
  source_excluded a [4,7,5,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1233 : Excluded a [4,7,5,8,2] :=
  source_excluded a [4,7,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1234 : Excluded a [4,7,5,8,3] :=
  source_excluded a [4,7,5,8,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_1235 : Excluded a [4,7,5,8,6] :=
  source_excluded a [4,7,5,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1230 : Excluded a [4,7,5,8] :=
  branch_excluded a [4,7,5,8] (by decide)
    (fin9_cases _
      node_1231
      node_1232
      node_1233
      node_1234
      (invalid_excluded a [4,7,5,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,5] (by decide +kernel))
      node_1235
      (invalid_excluded a [4,7,5,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,5,8,8] (by decide +kernel)))

theorem node_1225 : Excluded a [4,7,5] :=
  branch_excluded a [4,7,5] (by decide)
    (fin9_cases _
      node_1226
      node_1227
      node_1228
      (invalid_excluded a [4,7,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,5,5] (by decide +kernel))
      node_1229
      (invalid_excluded a [4,7,5,7] (by decide +kernel))
      node_1230)

theorem node_1237 : Excluded a [4,7,6,0] :=
  source_excluded a [4,7,6,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1238 : Excluded a [4,7,6,1] :=
  source_excluded a [4,7,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1240 : Excluded a [4,7,6,2,0] :=
  predecessor_excluded a [4,7,6,2,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1241 : Excluded a [4,7,6,2,1] :=
  source_excluded a [4,7,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1242 : Excluded a [4,7,6,2,3] :=
  predecessor_excluded a [4,7,6,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1245 : Excluded a [4,7,6,2,8,0,1] :=
  source_excluded a [4,7,6,2,8,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1246 : Excluded a [4,7,6,2,8,0,3] :=
  source_excluded a [4,7,6,2,8,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1248 : Excluded a [4,7,6,2,8,0,5,1] :=
  predecessor_excluded a [4,7,6,2,8,0,5,1] 2 1 1 7 (by decide) (by decide +kernel)

theorem node_1249 : Excluded a [4,7,6,2,8,0,5,3] :=
  predecessor_excluded a [4,7,6,2,8,0,5,3] 0 2 7 3 (by decide) (by decide +kernel)

theorem node_1247 : Excluded a [4,7,6,2,8,0,5] :=
  branch_excluded a [4,7,6,2,8,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,2,8,0,5,0] (by decide +kernel))
      node_1248
      (invalid_excluded a [4,7,6,2,8,0,5,2] (by decide +kernel))
      node_1249
      (invalid_excluded a [4,7,6,2,8,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,0,5,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,0,5,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,0,5,8] (by decide +kernel)))

theorem node_1244 : Excluded a [4,7,6,2,8,0] :=
  branch_excluded a [4,7,6,2,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,2,8,0,0] (by decide +kernel))
      node_1245
      (invalid_excluded a [4,7,6,2,8,0,2] (by decide +kernel))
      node_1246
      (invalid_excluded a [4,7,6,2,8,0,4] (by decide +kernel))
      node_1247
      (invalid_excluded a [4,7,6,2,8,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,0,8] (by decide +kernel)))

theorem node_1250 : Excluded a [4,7,6,2,8,1] :=
  predecessor_excluded a [4,7,6,2,8,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_1251 : Excluded a [4,7,6,2,8,3] :=
  source_excluded a [4,7,6,2,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1243 : Excluded a [4,7,6,2,8] :=
  branch_excluded a [4,7,6,2,8] (by decide)
    (fin9_cases _
      node_1244
      node_1250
      (invalid_excluded a [4,7,6,2,8,2] (by decide +kernel))
      node_1251
      (invalid_excluded a [4,7,6,2,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,8,8] (by decide +kernel)))

theorem node_1239 : Excluded a [4,7,6,2] :=
  branch_excluded a [4,7,6,2] (by decide)
    (fin9_cases _
      node_1240
      node_1241
      (invalid_excluded a [4,7,6,2,2] (by decide +kernel))
      node_1242
      (invalid_excluded a [4,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,2,7] (by decide +kernel))
      node_1243)

theorem node_1252 : Excluded a [4,7,6,5] :=
  source_excluded a [4,7,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1254 : Excluded a [4,7,6,8,0] :=
  predecessor_excluded a [4,7,6,8,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1255 : Excluded a [4,7,6,8,1] :=
  source_excluded a [4,7,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1256 : Excluded a [4,7,6,8,2] :=
  predecessor_excluded a [4,7,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_1259 : Excluded a [4,7,6,8,3,0,1] :=
  source_excluded a [4,7,6,8,3,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1261 : Excluded a [4,7,6,8,3,0,2,1] :=
  predecessor_excluded a [4,7,6,8,3,0,2,1] 2 1 1 7 (by decide) (by decide +kernel)

def b_1263 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 7
  | 2 => 6
  | 3 => 8
  | 4 => 3
  | 5 => 0
  | 6 => 2
  | 7 => 5
  | 8 => 1
  | _ => 0

def cert_1263 : LosingRegion (edgeOf a b_1263) 0 :=
  losingMask a b_1263 0 1224573019211591789052928
    (by decide +kernel) (by decide +kernel)

theorem node_1263 : Excluded a [4,7,6,8,3,0,2,5,1] :=
  losing_excluded a [4,7,6,8,3,0,2,5,1] (by decide) b_1263 (by decide +kernel) 2 0 0 cert_1263 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1263 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1224573019211591789052928 2 0; decide +kernel)

theorem node_1262 : Excluded a [4,7,6,8,3,0,2,5] :=
  branch_excluded a [4,7,6,8,3,0,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,8,3,0,2,5,0] (by decide +kernel))
      node_1263
      (invalid_excluded a [4,7,6,8,3,0,2,5,2] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,2,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,2,5,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,2,5,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,2,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,2,5,8] (by decide +kernel)))

theorem node_1260 : Excluded a [4,7,6,8,3,0,2] :=
  branch_excluded a [4,7,6,8,3,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,8,3,0,2,0] (by decide +kernel))
      node_1261
      (invalid_excluded a [4,7,6,8,3,0,2,2] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,2,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,2,4] (by decide +kernel))
      node_1262
      (invalid_excluded a [4,7,6,8,3,0,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,2,8] (by decide +kernel)))

theorem node_1265 : Excluded a [4,7,6,8,3,0,5,1] :=
  predecessor_excluded a [4,7,6,8,3,0,5,1] 2 1 1 7 (by decide) (by decide +kernel)

theorem node_1266 : Excluded a [4,7,6,8,3,0,5,2] :=
  source_excluded a [4,7,6,8,3,0,5,2] 7 0 8 (by decide) (by decide +kernel)

theorem node_1264 : Excluded a [4,7,6,8,3,0,5] :=
  branch_excluded a [4,7,6,8,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,8,3,0,5,0] (by decide +kernel))
      node_1265
      node_1266
      (invalid_excluded a [4,7,6,8,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,5,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,5,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,5,8] (by decide +kernel)))

theorem node_1258 : Excluded a [4,7,6,8,3,0] :=
  branch_excluded a [4,7,6,8,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,6,8,3,0,0] (by decide +kernel))
      node_1259
      node_1260
      (invalid_excluded a [4,7,6,8,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,4] (by decide +kernel))
      node_1264
      (invalid_excluded a [4,7,6,8,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,0,8] (by decide +kernel)))

theorem node_1267 : Excluded a [4,7,6,8,3,1] :=
  predecessor_excluded a [4,7,6,8,3,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_1268 : Excluded a [4,7,6,8,3,2] :=
  source_excluded a [4,7,6,8,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1257 : Excluded a [4,7,6,8,3] :=
  branch_excluded a [4,7,6,8,3] (by decide)
    (fin9_cases _
      node_1258
      node_1267
      node_1268
      (invalid_excluded a [4,7,6,8,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,3,8] (by decide +kernel)))

theorem node_1253 : Excluded a [4,7,6,8] :=
  branch_excluded a [4,7,6,8] (by decide)
    (fin9_cases _
      node_1254
      node_1255
      node_1256
      node_1257
      (invalid_excluded a [4,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,6,8,8] (by decide +kernel)))

theorem node_1236 : Excluded a [4,7,6] :=
  branch_excluded a [4,7,6] (by decide)
    (fin9_cases _
      node_1237
      node_1238
      node_1239
      (invalid_excluded a [4,7,6,3] (by decide +kernel))
      (invalid_excluded a [4,7,6,4] (by decide +kernel))
      node_1252
      (invalid_excluded a [4,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,6,7] (by decide +kernel))
      node_1253)

theorem node_1270 : Excluded a [4,7,8,0] :=
  source_excluded a [4,7,8,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1271 : Excluded a [4,7,8,1] :=
  source_excluded a [4,7,8,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1272 : Excluded a [4,7,8,2] :=
  predecessor_excluded a [4,7,8,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_1273 : Excluded a [4,7,8,5] :=
  source_excluded a [4,7,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1275 : Excluded a [4,7,8,6,0] :=
  predecessor_excluded a [4,7,8,6,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1276 : Excluded a [4,7,8,6,1] :=
  source_excluded a [4,7,8,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1279 : Excluded a [4,7,8,6,2,0,1] :=
  source_excluded a [4,7,8,6,2,0,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1281 : Excluded a [4,7,8,6,2,0,3,1] :=
  predecessor_excluded a [4,7,8,6,2,0,3,1] 2 1 1 7 (by decide) (by decide +kernel)

def b_1283 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 7
  | 2 => 8
  | 3 => 6
  | 4 => 2
  | 5 => 0
  | 6 => 3
  | 7 => 5
  | 8 => 1
  | _ => 0

def cert_1283 : LosingRegion (edgeOf a b_1283) 0 :=
  losingMask a b_1283 0 1224573019211602503402496
    (by decide +kernel) (by decide +kernel)

theorem node_1283 : Excluded a [4,7,8,6,2,0,3,5,1] :=
  losing_excluded a [4,7,8,6,2,0,3,5,1] (by decide) b_1283 (by decide +kernel) 2 0 0 cert_1283 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1283 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1224573019211602503402496 2 0; decide +kernel)

theorem node_1282 : Excluded a [4,7,8,6,2,0,3,5] :=
  branch_excluded a [4,7,8,6,2,0,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,8,6,2,0,3,5,0] (by decide +kernel))
      node_1283
      (invalid_excluded a [4,7,8,6,2,0,3,5,2] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,2,0,3,5,3] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,2,0,3,5,4] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,2,0,3,5,5] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,2,0,3,5,6] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,2,0,3,5,7] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,2,0,3,5,8] (by decide +kernel)))

theorem node_1280 : Excluded a [4,7,8,6,2,0,3] :=
  branch_excluded a [4,7,8,6,2,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,8,6,2,0,3,0] (by decide +kernel))
      node_1281
      (invalid_excluded a [4,7,8,6,2,0,3,2] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,2,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,2,0,3,4] (by decide +kernel))
      node_1282
      (invalid_excluded a [4,7,8,6,2,0,3,6] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,2,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,2,0,3,8] (by decide +kernel)))

theorem node_1284 : Excluded a [4,7,8,6,2,0,5] :=
  predecessor_excluded a [4,7,8,6,2,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_1278 : Excluded a [4,7,8,6,2,0] :=
  branch_excluded a [4,7,8,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,7,8,6,2,0,0] (by decide +kernel))
      node_1279
      (invalid_excluded a [4,7,8,6,2,0,2] (by decide +kernel))
      node_1280
      (invalid_excluded a [4,7,8,6,2,0,4] (by decide +kernel))
      node_1284
      (invalid_excluded a [4,7,8,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,2,0,7] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,2,0,8] (by decide +kernel)))

theorem node_1285 : Excluded a [4,7,8,6,2,1] :=
  predecessor_excluded a [4,7,8,6,2,1] 0 7 5 1 (by decide) (by decide +kernel)

theorem node_1286 : Excluded a [4,7,8,6,2,3] :=
  source_excluded a [4,7,8,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1277 : Excluded a [4,7,8,6,2] :=
  branch_excluded a [4,7,8,6,2] (by decide)
    (fin9_cases _
      node_1278
      node_1285
      (invalid_excluded a [4,7,8,6,2,2] (by decide +kernel))
      node_1286
      (invalid_excluded a [4,7,8,6,2,4] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,2,6] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,2,7] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,2,8] (by decide +kernel)))

theorem node_1287 : Excluded a [4,7,8,6,3] :=
  predecessor_excluded a [4,7,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1274 : Excluded a [4,7,8,6] :=
  branch_excluded a [4,7,8,6] (by decide)
    (fin9_cases _
      node_1275
      node_1276
      node_1277
      node_1287
      (invalid_excluded a [4,7,8,6,4] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,5] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,6] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,7] (by decide +kernel))
      (invalid_excluded a [4,7,8,6,8] (by decide +kernel)))

theorem node_1269 : Excluded a [4,7,8] :=
  branch_excluded a [4,7,8] (by decide)
    (fin9_cases _
      node_1270
      node_1271
      node_1272
      (invalid_excluded a [4,7,8,3] (by decide +kernel))
      (invalid_excluded a [4,7,8,4] (by decide +kernel))
      node_1273
      node_1274
      (invalid_excluded a [4,7,8,7] (by decide +kernel))
      (invalid_excluded a [4,7,8,8] (by decide +kernel)))

theorem node_1157 : Excluded a [4,7] :=
  branch_excluded a [4,7] (by decide)
    (fin9_cases _
      node_1158
      node_1159
      (invalid_excluded a [4,7,2] (by decide +kernel))
      (invalid_excluded a [4,7,3] (by decide +kernel))
      (invalid_excluded a [4,7,4] (by decide +kernel))
      node_1225
      node_1236
      (invalid_excluded a [4,7,7] (by decide +kernel))
      node_1269)

theorem node_1289 : Excluded a [4,8,0] :=
  predecessor_excluded a [4,8,0] 1 4 2 0 (by decide) (by decide +kernel)

theorem node_1291 : Excluded a [4,8,1,0] :=
  source_excluded a [4,8,1,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1293 : Excluded a [4,8,1,2,0] :=
  predecessor_excluded a [4,8,1,2,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1294 : Excluded a [4,8,1,2,3] :=
  predecessor_excluded a [4,8,1,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1295 : Excluded a [4,8,1,2,6] :=
  source_excluded a [4,8,1,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1299 : Excluded a [4,8,1,2,7,0,3,5] :=
  source_excluded a [4,8,1,2,7,0,3,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_1300 : Excluded a [4,8,1,2,7,0,3,6] :=
  predecessor_excluded a [4,8,1,2,7,0,3,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_1298 : Excluded a [4,8,1,2,7,0,3] :=
  branch_excluded a [4,8,1,2,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,2,7,0,3,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,0,3,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,0,3,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,0,3,4] (by decide +kernel))
      node_1299
      node_1300
      (invalid_excluded a [4,8,1,2,7,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,0,3,8] (by decide +kernel)))

theorem node_1301 : Excluded a [4,8,1,2,7,0,5] :=
  source_excluded a [4,8,1,2,7,0,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1297 : Excluded a [4,8,1,2,7,0] :=
  branch_excluded a [4,8,1,2,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,2,7,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,0,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,0,2] (by decide +kernel))
      node_1298
      (invalid_excluded a [4,8,1,2,7,0,4] (by decide +kernel))
      node_1301
      (invalid_excluded a [4,8,1,2,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,0,8] (by decide +kernel)))

theorem node_1304 : Excluded a [4,8,1,2,7,3,0,5] :=
  source_excluded a [4,8,1,2,7,3,0,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_1305 : Excluded a [4,8,1,2,7,3,0,6] :=
  predecessor_excluded a [4,8,1,2,7,3,0,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_1303 : Excluded a [4,8,1,2,7,3,0] :=
  branch_excluded a [4,8,1,2,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,2,7,3,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,3,0,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,3,0,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,3,0,4] (by decide +kernel))
      node_1304
      node_1305
      (invalid_excluded a [4,8,1,2,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,3,0,8] (by decide +kernel)))

theorem node_1306 : Excluded a [4,8,1,2,7,3,5] :=
  source_excluded a [4,8,1,2,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1302 : Excluded a [4,8,1,2,7,3] :=
  branch_excluded a [4,8,1,2,7,3] (by decide)
    (fin9_cases _
      node_1303
      (invalid_excluded a [4,8,1,2,7,3,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,3,4] (by decide +kernel))
      node_1306
      (invalid_excluded a [4,8,1,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,3,8] (by decide +kernel)))

theorem node_1296 : Excluded a [4,8,1,2,7] :=
  branch_excluded a [4,8,1,2,7] (by decide)
    (fin9_cases _
      node_1297
      (invalid_excluded a [4,8,1,2,7,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,2] (by decide +kernel))
      node_1302
      (invalid_excluded a [4,8,1,2,7,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,7,8] (by decide +kernel)))

theorem node_1292 : Excluded a [4,8,1,2] :=
  branch_excluded a [4,8,1,2] (by decide)
    (fin9_cases _
      node_1293
      (invalid_excluded a [4,8,1,2,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,2] (by decide +kernel))
      node_1294
      (invalid_excluded a [4,8,1,2,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,2,5] (by decide +kernel))
      node_1295
      node_1296
      (invalid_excluded a [4,8,1,2,8] (by decide +kernel)))

theorem node_1307 : Excluded a [4,8,1,5] :=
  source_excluded a [4,8,1,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1309 : Excluded a [4,8,1,6,0] :=
  predecessor_excluded a [4,8,1,6,0] 2 0 0 4 (by decide) (by decide +kernel)

def b_1314 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 8
  | 2 => 1
  | 3 => 6
  | 4 => 2
  | 5 => 0
  | 6 => 3
  | 7 => 5
  | 8 => 7
  | _ => 0

def cert_1314 : LosingRegion (edgeOf a b_1314) 0 :=
  losingMask a b_1314 0 1441954189154198792963072
    (by decide +kernel) (by decide +kernel)

theorem node_1314 : Excluded a [4,8,1,6,2,0,3,5,7] :=
  losing_excluded a [4,8,1,6,2,0,3,5,7] (by decide) b_1314 (by decide +kernel) 2 0 0 cert_1314 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1314 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1441954189154198792963072 2 0; decide +kernel)

theorem node_1313 : Excluded a [4,8,1,6,2,0,3,5] :=
  branch_excluded a [4,8,1,6,2,0,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,6,2,0,3,5,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,0,3,5,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,0,3,5,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,0,3,5,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,0,3,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,0,3,5,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,0,3,5,6] (by decide +kernel))
      node_1314
      (invalid_excluded a [4,8,1,6,2,0,3,5,8] (by decide +kernel)))

theorem node_1312 : Excluded a [4,8,1,6,2,0,3] :=
  branch_excluded a [4,8,1,6,2,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,6,2,0,3,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,0,3,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,0,3,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,0,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,0,3,4] (by decide +kernel))
      node_1313
      (invalid_excluded a [4,8,1,6,2,0,3,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,0,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,0,3,8] (by decide +kernel)))

theorem node_1315 : Excluded a [4,8,1,6,2,0,5] :=
  predecessor_excluded a [4,8,1,6,2,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_1311 : Excluded a [4,8,1,6,2,0] :=
  branch_excluded a [4,8,1,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,6,2,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,0,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,0,2] (by decide +kernel))
      node_1312
      (invalid_excluded a [4,8,1,6,2,0,4] (by decide +kernel))
      node_1315
      (invalid_excluded a [4,8,1,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,0,8] (by decide +kernel)))

theorem node_1316 : Excluded a [4,8,1,6,2,3] :=
  source_excluded a [4,8,1,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1317 : Excluded a [4,8,1,6,2,7] :=
  source_excluded a [4,8,1,6,2,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1310 : Excluded a [4,8,1,6,2] :=
  branch_excluded a [4,8,1,6,2] (by decide)
    (fin9_cases _
      node_1311
      (invalid_excluded a [4,8,1,6,2,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,2] (by decide +kernel))
      node_1316
      (invalid_excluded a [4,8,1,6,2,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,2,6] (by decide +kernel))
      node_1317
      (invalid_excluded a [4,8,1,6,2,8] (by decide +kernel)))

theorem node_1318 : Excluded a [4,8,1,6,3] :=
  predecessor_excluded a [4,8,1,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1319 : Excluded a [4,8,1,6,7] :=
  predecessor_excluded a [4,8,1,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_1308 : Excluded a [4,8,1,6] :=
  branch_excluded a [4,8,1,6] (by decide)
    (fin9_cases _
      node_1309
      (invalid_excluded a [4,8,1,6,1] (by decide +kernel))
      node_1310
      node_1318
      (invalid_excluded a [4,8,1,6,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,6,6] (by decide +kernel))
      node_1319
      (invalid_excluded a [4,8,1,6,8] (by decide +kernel)))

theorem node_1321 : Excluded a [4,8,1,7,0] :=
  predecessor_excluded a [4,8,1,7,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1324 : Excluded a [4,8,1,7,2,0,3] :=
  source_excluded a [4,8,1,7,2,0,3] 6 0 3 (by decide) (by decide +kernel)

def b_1327 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 8
  | 2 => 1
  | 3 => 7
  | 4 => 2
  | 5 => 0
  | 6 => 5
  | 7 => 3
  | 8 => 6
  | _ => 0

def cert_1327 : LosingRegion (edgeOf a b_1327) 0 :=
  losingMask a b_1327 0 1445000045639774907401216
    (by decide +kernel) (by decide +kernel)

theorem node_1327 : Excluded a [4,8,1,7,2,0,5,3,6] :=
  losing_excluded a [4,8,1,7,2,0,5,3,6] (by decide) b_1327 (by decide +kernel) 2 0 0 cert_1327 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1327 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1445000045639774907401216 2 0; decide +kernel)

theorem node_1326 : Excluded a [4,8,1,7,2,0,5,3] :=
  branch_excluded a [4,8,1,7,2,0,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,2,0,5,3,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,0,5,3,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,0,5,3,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,0,5,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,0,5,3,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,0,5,3,5] (by decide +kernel))
      node_1327
      (invalid_excluded a [4,8,1,7,2,0,5,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,0,5,3,8] (by decide +kernel)))

theorem node_1328 : Excluded a [4,8,1,7,2,0,5,6] :=
  predecessor_excluded a [4,8,1,7,2,0,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_1325 : Excluded a [4,8,1,7,2,0,5] :=
  branch_excluded a [4,8,1,7,2,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,2,0,5,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,0,5,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,0,5,2] (by decide +kernel))
      node_1326
      (invalid_excluded a [4,8,1,7,2,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,0,5,5] (by decide +kernel))
      node_1328
      (invalid_excluded a [4,8,1,7,2,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,0,5,8] (by decide +kernel)))

theorem node_1323 : Excluded a [4,8,1,7,2,0] :=
  branch_excluded a [4,8,1,7,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,2,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,0,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,0,2] (by decide +kernel))
      node_1324
      (invalid_excluded a [4,8,1,7,2,0,4] (by decide +kernel))
      node_1325
      (invalid_excluded a [4,8,1,7,2,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,0,8] (by decide +kernel)))

theorem node_1329 : Excluded a [4,8,1,7,2,3] :=
  predecessor_excluded a [4,8,1,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1322 : Excluded a [4,8,1,7,2] :=
  branch_excluded a [4,8,1,7,2] (by decide)
    (fin9_cases _
      node_1323
      (invalid_excluded a [4,8,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,2] (by decide +kernel))
      node_1329
      (invalid_excluded a [4,8,1,7,2,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,2,8] (by decide +kernel)))

theorem node_1333 : Excluded a [4,8,1,7,3,0,2,5] :=
  predecessor_excluded a [4,8,1,7,3,0,2,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_1334 : Excluded a [4,8,1,7,3,0,2,6] :=
  predecessor_excluded a [4,8,1,7,3,0,2,6] 0 2 7 6 (by decide) (by decide +kernel)

theorem node_1332 : Excluded a [4,8,1,7,3,0,2] :=
  branch_excluded a [4,8,1,7,3,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,3,0,2,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,2,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,2,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,2,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,2,4] (by decide +kernel))
      node_1333
      node_1334
      (invalid_excluded a [4,8,1,7,3,0,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,2,8] (by decide +kernel)))

theorem node_1336 : Excluded a [4,8,1,7,3,0,5,2] :=
  source_excluded a [4,8,1,7,3,0,5,2] 7 0 8 (by decide) (by decide +kernel)

theorem node_1337 : Excluded a [4,8,1,7,3,0,5,6] :=
  predecessor_excluded a [4,8,1,7,3,0,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_1335 : Excluded a [4,8,1,7,3,0,5] :=
  branch_excluded a [4,8,1,7,3,0,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,3,0,5,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,5,1] (by decide +kernel))
      node_1336
      (invalid_excluded a [4,8,1,7,3,0,5,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,5,5] (by decide +kernel))
      node_1337
      (invalid_excluded a [4,8,1,7,3,0,5,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,5,8] (by decide +kernel)))

theorem node_1331 : Excluded a [4,8,1,7,3,0] :=
  branch_excluded a [4,8,1,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,3,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,1] (by decide +kernel))
      node_1332
      (invalid_excluded a [4,8,1,7,3,0,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,4] (by decide +kernel))
      node_1335
      (invalid_excluded a [4,8,1,7,3,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,0,8] (by decide +kernel)))

theorem node_1340 : Excluded a [4,8,1,7,3,2,0,5] :=
  predecessor_excluded a [4,8,1,7,3,2,0,5] 0 2 7 5 (by decide) (by decide +kernel)

theorem node_1342 : Excluded a [4,8,1,7,3,2,0,6,5] :=
  source_excluded a [4,8,1,7,3,2,0,6,5] 8 0 5 (by decide) (by decide +kernel)

theorem node_1341 : Excluded a [4,8,1,7,3,2,0,6] :=
  branch_excluded a [4,8,1,7,3,2,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,3,2,0,6,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,0,6,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,0,6,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,0,6,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,0,6,4] (by decide +kernel))
      node_1342
      (invalid_excluded a [4,8,1,7,3,2,0,6,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,0,6,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,0,6,8] (by decide +kernel)))

theorem node_1339 : Excluded a [4,8,1,7,3,2,0] :=
  branch_excluded a [4,8,1,7,3,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,1,7,3,2,0,0] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,0,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,0,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,0,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,0,4] (by decide +kernel))
      node_1340
      node_1341
      (invalid_excluded a [4,8,1,7,3,2,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,0,8] (by decide +kernel)))

theorem node_1344 : Excluded a [4,8,1,7,3,2,5,0] :=
  source_excluded a [4,8,1,7,3,2,5,0] 1 2 7 (by decide) (by decide +kernel)

theorem node_1345 : Excluded a [4,8,1,7,3,2,5,6] :=
  predecessor_excluded a [4,8,1,7,3,2,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_1343 : Excluded a [4,8,1,7,3,2,5] :=
  branch_excluded a [4,8,1,7,3,2,5] (by decide)
    (fin9_cases _
      node_1344
      (invalid_excluded a [4,8,1,7,3,2,5,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,5,5] (by decide +kernel))
      node_1345
      (invalid_excluded a [4,8,1,7,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,5,8] (by decide +kernel)))

theorem node_1338 : Excluded a [4,8,1,7,3,2] :=
  branch_excluded a [4,8,1,7,3,2] (by decide)
    (fin9_cases _
      node_1339
      (invalid_excluded a [4,8,1,7,3,2,1] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,4] (by decide +kernel))
      node_1343
      (invalid_excluded a [4,8,1,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,2,8] (by decide +kernel)))

theorem node_1330 : Excluded a [4,8,1,7,3] :=
  branch_excluded a [4,8,1,7,3] (by decide)
    (fin9_cases _
      node_1331
      (invalid_excluded a [4,8,1,7,3,1] (by decide +kernel))
      node_1338
      (invalid_excluded a [4,8,1,7,3,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,3,8] (by decide +kernel)))

theorem node_1346 : Excluded a [4,8,1,7,6] :=
  source_excluded a [4,8,1,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1320 : Excluded a [4,8,1,7] :=
  branch_excluded a [4,8,1,7] (by decide)
    (fin9_cases _
      node_1321
      (invalid_excluded a [4,8,1,7,1] (by decide +kernel))
      node_1322
      node_1330
      (invalid_excluded a [4,8,1,7,4] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,5] (by decide +kernel))
      node_1346
      (invalid_excluded a [4,8,1,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,1,7,8] (by decide +kernel)))

theorem node_1290 : Excluded a [4,8,1] :=
  branch_excluded a [4,8,1] (by decide)
    (fin9_cases _
      node_1291
      (invalid_excluded a [4,8,1,1] (by decide +kernel))
      node_1292
      (invalid_excluded a [4,8,1,3] (by decide +kernel))
      (invalid_excluded a [4,8,1,4] (by decide +kernel))
      node_1307
      node_1308
      node_1320
      (invalid_excluded a [4,8,1,8] (by decide +kernel)))

theorem node_1348 : Excluded a [4,8,5,0] :=
  source_excluded a [4,8,5,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1349 : Excluded a [4,8,5,1] :=
  source_excluded a [4,8,5,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1350 : Excluded a [4,8,5,2] :=
  predecessor_excluded a [4,8,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_1351 : Excluded a [4,8,5,6] :=
  predecessor_excluded a [4,8,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_1353 : Excluded a [4,8,5,7,0] :=
  predecessor_excluded a [4,8,5,7,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1354 : Excluded a [4,8,5,7,1] :=
  source_excluded a [4,8,5,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1355 : Excluded a [4,8,5,7,2] :=
  source_excluded a [4,8,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_1356 : Excluded a [4,8,5,7,3] :=
  source_excluded a [4,8,5,7,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_1357 : Excluded a [4,8,5,7,6] :=
  source_excluded a [4,8,5,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1352 : Excluded a [4,8,5,7] :=
  branch_excluded a [4,8,5,7] (by decide)
    (fin9_cases _
      node_1353
      node_1354
      node_1355
      node_1356
      (invalid_excluded a [4,8,5,7,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,5] (by decide +kernel))
      node_1357
      (invalid_excluded a [4,8,5,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,5,7,8] (by decide +kernel)))

theorem node_1347 : Excluded a [4,8,5] :=
  branch_excluded a [4,8,5] (by decide)
    (fin9_cases _
      node_1348
      node_1349
      node_1350
      (invalid_excluded a [4,8,5,3] (by decide +kernel))
      (invalid_excluded a [4,8,5,4] (by decide +kernel))
      (invalid_excluded a [4,8,5,5] (by decide +kernel))
      node_1351
      node_1352
      (invalid_excluded a [4,8,5,8] (by decide +kernel)))

theorem node_1359 : Excluded a [4,8,6,0] :=
  source_excluded a [4,8,6,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1360 : Excluded a [4,8,6,1] :=
  source_excluded a [4,8,6,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1362 : Excluded a [4,8,6,2,0] :=
  predecessor_excluded a [4,8,6,2,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1363 : Excluded a [4,8,6,2,1] :=
  source_excluded a [4,8,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1364 : Excluded a [4,8,6,2,3] :=
  predecessor_excluded a [4,8,6,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1367 : Excluded a [4,8,6,2,7,0,1] :=
  predecessor_excluded a [4,8,6,2,7,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_1368 : Excluded a [4,8,6,2,7,0,3] :=
  source_excluded a [4,8,6,2,7,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1369 : Excluded a [4,8,6,2,7,0,5] :=
  source_excluded a [4,8,6,2,7,0,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1366 : Excluded a [4,8,6,2,7,0] :=
  branch_excluded a [4,8,6,2,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,6,2,7,0,0] (by decide +kernel))
      node_1367
      (invalid_excluded a [4,8,6,2,7,0,2] (by decide +kernel))
      node_1368
      (invalid_excluded a [4,8,6,2,7,0,4] (by decide +kernel))
      node_1369
      (invalid_excluded a [4,8,6,2,7,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,0,8] (by decide +kernel)))

theorem node_1371 : Excluded a [4,8,6,2,7,1,0] :=
  predecessor_excluded a [4,8,6,2,7,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_1372 : Excluded a [4,8,6,2,7,1,3] :=
  source_excluded a [4,8,6,2,7,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1373 : Excluded a [4,8,6,2,7,1,5] :=
  source_excluded a [4,8,6,2,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_1370 : Excluded a [4,8,6,2,7,1] :=
  branch_excluded a [4,8,6,2,7,1] (by decide)
    (fin9_cases _
      node_1371
      (invalid_excluded a [4,8,6,2,7,1,1] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,2] (by decide +kernel))
      node_1372
      (invalid_excluded a [4,8,6,2,7,1,4] (by decide +kernel))
      node_1373
      (invalid_excluded a [4,8,6,2,7,1,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,1,8] (by decide +kernel)))

theorem node_1374 : Excluded a [4,8,6,2,7,3] :=
  source_excluded a [4,8,6,2,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1365 : Excluded a [4,8,6,2,7] :=
  branch_excluded a [4,8,6,2,7] (by decide)
    (fin9_cases _
      node_1366
      node_1370
      (invalid_excluded a [4,8,6,2,7,2] (by decide +kernel))
      node_1374
      (invalid_excluded a [4,8,6,2,7,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,6] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,7,8] (by decide +kernel)))

theorem node_1361 : Excluded a [4,8,6,2] :=
  branch_excluded a [4,8,6,2] (by decide)
    (fin9_cases _
      node_1362
      node_1363
      (invalid_excluded a [4,8,6,2,2] (by decide +kernel))
      node_1364
      (invalid_excluded a [4,8,6,2,4] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [4,8,6,2,6] (by decide +kernel))
      node_1365
      (invalid_excluded a [4,8,6,2,8] (by decide +kernel)))

theorem node_1375 : Excluded a [4,8,6,5] :=
  source_excluded a [4,8,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1376 : Excluded a [4,8,6,7] :=
  predecessor_excluded a [4,8,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_1358 : Excluded a [4,8,6] :=
  branch_excluded a [4,8,6] (by decide)
    (fin9_cases _
      node_1359
      node_1360
      node_1361
      (invalid_excluded a [4,8,6,3] (by decide +kernel))
      (invalid_excluded a [4,8,6,4] (by decide +kernel))
      node_1375
      (invalid_excluded a [4,8,6,6] (by decide +kernel))
      node_1376
      (invalid_excluded a [4,8,6,8] (by decide +kernel)))

theorem node_1378 : Excluded a [4,8,7,0] :=
  source_excluded a [4,8,7,0] 3 1 0 (by decide) (by decide +kernel)

theorem node_1379 : Excluded a [4,8,7,1] :=
  source_excluded a [4,8,7,1] 0 2 3 (by decide) (by decide +kernel)

theorem node_1381 : Excluded a [4,8,7,2,0] :=
  predecessor_excluded a [4,8,7,2,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1382 : Excluded a [4,8,7,2,1] :=
  source_excluded a [4,8,7,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1383 : Excluded a [4,8,7,2,3] :=
  predecessor_excluded a [4,8,7,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1384 : Excluded a [4,8,7,2,6] :=
  source_excluded a [4,8,7,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1380 : Excluded a [4,8,7,2] :=
  branch_excluded a [4,8,7,2] (by decide)
    (fin9_cases _
      node_1381
      node_1382
      (invalid_excluded a [4,8,7,2,2] (by decide +kernel))
      node_1383
      (invalid_excluded a [4,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,5] (by decide +kernel))
      node_1384
      (invalid_excluded a [4,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,2,8] (by decide +kernel)))

theorem node_1385 : Excluded a [4,8,7,5] :=
  source_excluded a [4,8,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_1387 : Excluded a [4,8,7,6,0] :=
  predecessor_excluded a [4,8,7,6,0] 2 0 0 4 (by decide) (by decide +kernel)

theorem node_1388 : Excluded a [4,8,7,6,1] :=
  source_excluded a [4,8,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1391 : Excluded a [4,8,7,6,2,0,1] :=
  predecessor_excluded a [4,8,7,6,2,0,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_1392 : Excluded a [4,8,7,6,2,0,3] :=
  source_excluded a [4,8,7,6,2,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1393 : Excluded a [4,8,7,6,2,0,5] :=
  predecessor_excluded a [4,8,7,6,2,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_1390 : Excluded a [4,8,7,6,2,0] :=
  branch_excluded a [4,8,7,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,8,7,6,2,0,0] (by decide +kernel))
      node_1391
      (invalid_excluded a [4,8,7,6,2,0,2] (by decide +kernel))
      node_1392
      (invalid_excluded a [4,8,7,6,2,0,4] (by decide +kernel))
      node_1393
      (invalid_excluded a [4,8,7,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,2,0,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,2,0,8] (by decide +kernel)))

theorem node_1395 : Excluded a [4,8,7,6,2,1,0] :=
  predecessor_excluded a [4,8,7,6,2,1,0] 2 0 5 6 (by decide) (by decide +kernel)

theorem node_1396 : Excluded a [4,8,7,6,2,1,3] :=
  source_excluded a [4,8,7,6,2,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1397 : Excluded a [4,8,7,6,2,1,5] :=
  predecessor_excluded a [4,8,7,6,2,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_1394 : Excluded a [4,8,7,6,2,1] :=
  branch_excluded a [4,8,7,6,2,1] (by decide)
    (fin9_cases _
      node_1395
      (invalid_excluded a [4,8,7,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,2,1,2] (by decide +kernel))
      node_1396
      (invalid_excluded a [4,8,7,6,2,1,4] (by decide +kernel))
      node_1397
      (invalid_excluded a [4,8,7,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,2,1,8] (by decide +kernel)))

theorem node_1398 : Excluded a [4,8,7,6,2,3] :=
  source_excluded a [4,8,7,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1389 : Excluded a [4,8,7,6,2] :=
  branch_excluded a [4,8,7,6,2] (by decide)
    (fin9_cases _
      node_1390
      node_1394
      (invalid_excluded a [4,8,7,6,2,2] (by decide +kernel))
      node_1398
      (invalid_excluded a [4,8,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,2,8] (by decide +kernel)))

theorem node_1399 : Excluded a [4,8,7,6,3] :=
  predecessor_excluded a [4,8,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1386 : Excluded a [4,8,7,6] :=
  branch_excluded a [4,8,7,6] (by decide)
    (fin9_cases _
      node_1387
      node_1388
      node_1389
      node_1399
      (invalid_excluded a [4,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,6,8] (by decide +kernel)))

theorem node_1377 : Excluded a [4,8,7] :=
  branch_excluded a [4,8,7] (by decide)
    (fin9_cases _
      node_1378
      node_1379
      node_1380
      (invalid_excluded a [4,8,7,3] (by decide +kernel))
      (invalid_excluded a [4,8,7,4] (by decide +kernel))
      node_1385
      node_1386
      (invalid_excluded a [4,8,7,7] (by decide +kernel))
      (invalid_excluded a [4,8,7,8] (by decide +kernel)))

theorem node_1288 : Excluded a [4,8] :=
  branch_excluded a [4,8] (by decide)
    (fin9_cases _
      node_1289
      node_1290
      (invalid_excluded a [4,8,2] (by decide +kernel))
      (invalid_excluded a [4,8,3] (by decide +kernel))
      (invalid_excluded a [4,8,4] (by decide +kernel))
      node_1347
      node_1358
      node_1377
      (invalid_excluded a [4,8,8] (by decide +kernel)))

theorem node_921 : Excluded a [4] :=
  branch_excluded a [4] (by decide)
    (fin9_cases _
      (invalid_excluded a [4,0] (by decide +kernel))
      (invalid_excluded a [4,1] (by decide +kernel))
      node_922
      node_1021
      (invalid_excluded a [4,4] (by decide +kernel))
      node_1022
      node_1023
      node_1157
      node_1288)

theorem node_1402 : Excluded a [5,2,0] :=
  source_excluded a [5,2,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_1403 : Excluded a [5,2,1] :=
  predecessor_excluded a [5,2,1] 3 1 1 2 (by decide) (by decide +kernel)

theorem node_1404 : Excluded a [5,2,4] :=
  source_excluded a [5,2,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_1406 : Excluded a [5,2,6,0] :=
  predecessor_excluded a [5,2,6,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1408 : Excluded a [5,2,6,1,0] :=
  source_excluded a [5,2,6,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1410 : Excluded a [5,2,6,1,3,0] :=
  predecessor_excluded a [5,2,6,1,3,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1411 : Excluded a [5,2,6,1,3,4] :=
  predecessor_excluded a [5,2,6,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1412 : Excluded a [5,2,6,1,3,7] :=
  source_excluded a [5,2,6,1,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1416 : Excluded a [5,2,6,1,3,8,0,4,7] :=
  predecessor_excluded a [5,2,6,1,3,8,0,4,7] 0 7 5 8 (by decide) (by decide +kernel)

theorem node_1415 : Excluded a [5,2,6,1,3,8,0,4] :=
  branch_excluded a [5,2,6,1,3,8,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,6,1,3,8,0,4,0] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,0,4,1] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,0,4,2] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,0,4,3] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,0,4,4] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,0,4,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,0,4,6] (by decide +kernel))
      node_1416
      (invalid_excluded a [5,2,6,1,3,8,0,4,8] (by decide +kernel)))

theorem node_1414 : Excluded a [5,2,6,1,3,8,0] :=
  branch_excluded a [5,2,6,1,3,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,6,1,3,8,0,0] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,0,1] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,0,2] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,0,3] (by decide +kernel))
      node_1415
      (invalid_excluded a [5,2,6,1,3,8,0,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,0,6] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,0,7] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,0,8] (by decide +kernel)))

theorem node_1417 : Excluded a [5,2,6,1,3,8,4] :=
  predecessor_excluded a [5,2,6,1,3,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_1413 : Excluded a [5,2,6,1,3,8] :=
  branch_excluded a [5,2,6,1,3,8] (by decide)
    (fin9_cases _
      node_1414
      (invalid_excluded a [5,2,6,1,3,8,1] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,2] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,3] (by decide +kernel))
      node_1417
      (invalid_excluded a [5,2,6,1,3,8,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,6] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,7] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,8,8] (by decide +kernel)))

theorem node_1409 : Excluded a [5,2,6,1,3] :=
  branch_excluded a [5,2,6,1,3] (by decide)
    (fin9_cases _
      node_1410
      (invalid_excluded a [5,2,6,1,3,1] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,2] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,3] (by decide +kernel))
      node_1411
      (invalid_excluded a [5,2,6,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,3,6] (by decide +kernel))
      node_1412
      node_1413)

theorem node_1419 : Excluded a [5,2,6,1,7,0] :=
  predecessor_excluded a [5,2,6,1,7,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1420 : Excluded a [5,2,6,1,7,3] :=
  source_excluded a [5,2,6,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1421 : Excluded a [5,2,6,1,7,4] :=
  predecessor_excluded a [5,2,6,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1422 : Excluded a [5,2,6,1,7,8] :=
  predecessor_excluded a [5,2,6,1,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_1418 : Excluded a [5,2,6,1,7] :=
  branch_excluded a [5,2,6,1,7] (by decide)
    (fin9_cases _
      node_1419
      (invalid_excluded a [5,2,6,1,7,1] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,7,2] (by decide +kernel))
      node_1420
      node_1421
      (invalid_excluded a [5,2,6,1,7,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,7,6] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,7,7] (by decide +kernel))
      node_1422)

theorem node_1424 : Excluded a [5,2,6,1,8,0] :=
  predecessor_excluded a [5,2,6,1,8,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1425 : Excluded a [5,2,6,1,8,3] :=
  source_excluded a [5,2,6,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1429 : Excluded a [5,2,6,1,8,4,0,3,7] :=
  predecessor_excluded a [5,2,6,1,8,4,0,3,7] 0 3 8 7 (by decide) (by decide +kernel)

theorem node_1428 : Excluded a [5,2,6,1,8,4,0,3] :=
  branch_excluded a [5,2,6,1,8,4,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,6,1,8,4,0,3,0] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,0,3,1] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,0,3,2] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,0,3,3] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,0,3,4] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,0,3,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,0,3,6] (by decide +kernel))
      node_1429
      (invalid_excluded a [5,2,6,1,8,4,0,3,8] (by decide +kernel)))

theorem node_1427 : Excluded a [5,2,6,1,8,4,0] :=
  branch_excluded a [5,2,6,1,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,6,1,8,4,0,0] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,0,1] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,0,2] (by decide +kernel))
      node_1428
      (invalid_excluded a [5,2,6,1,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,0,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,0,6] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,0,8] (by decide +kernel)))

theorem node_1430 : Excluded a [5,2,6,1,8,4,3] :=
  source_excluded a [5,2,6,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1426 : Excluded a [5,2,6,1,8,4] :=
  branch_excluded a [5,2,6,1,8,4] (by decide)
    (fin9_cases _
      node_1427
      (invalid_excluded a [5,2,6,1,8,4,1] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,2] (by decide +kernel))
      node_1430
      (invalid_excluded a [5,2,6,1,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,4,8] (by decide +kernel)))

theorem node_1431 : Excluded a [5,2,6,1,8,7] :=
  source_excluded a [5,2,6,1,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1423 : Excluded a [5,2,6,1,8] :=
  branch_excluded a [5,2,6,1,8] (by decide)
    (fin9_cases _
      node_1424
      (invalid_excluded a [5,2,6,1,8,1] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,2] (by decide +kernel))
      node_1425
      node_1426
      (invalid_excluded a [5,2,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,8,6] (by decide +kernel))
      node_1431
      (invalid_excluded a [5,2,6,1,8,8] (by decide +kernel)))

theorem node_1407 : Excluded a [5,2,6,1] :=
  branch_excluded a [5,2,6,1] (by decide)
    (fin9_cases _
      node_1408
      (invalid_excluded a [5,2,6,1,1] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,2] (by decide +kernel))
      node_1409
      (invalid_excluded a [5,2,6,1,4] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,1,6] (by decide +kernel))
      node_1418
      node_1423)

theorem node_1432 : Excluded a [5,2,6,7] :=
  predecessor_excluded a [5,2,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_1434 : Excluded a [5,2,6,8,0] :=
  source_excluded a [5,2,6,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1435 : Excluded a [5,2,6,8,1] :=
  source_excluded a [5,2,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1437 : Excluded a [5,2,6,8,3,0] :=
  predecessor_excluded a [5,2,6,8,3,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1438 : Excluded a [5,2,6,8,3,1] :=
  source_excluded a [5,2,6,8,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1439 : Excluded a [5,2,6,8,3,4] :=
  predecessor_excluded a [5,2,6,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1440 : Excluded a [5,2,6,8,3,7] :=
  source_excluded a [5,2,6,8,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1436 : Excluded a [5,2,6,8,3] :=
  branch_excluded a [5,2,6,8,3] (by decide)
    (fin9_cases _
      node_1437
      node_1438
      (invalid_excluded a [5,2,6,8,3,2] (by decide +kernel))
      (invalid_excluded a [5,2,6,8,3,3] (by decide +kernel))
      node_1439
      (invalid_excluded a [5,2,6,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,8,3,6] (by decide +kernel))
      node_1440
      (invalid_excluded a [5,2,6,8,3,8] (by decide +kernel)))

theorem node_1442 : Excluded a [5,2,6,8,7,0] :=
  predecessor_excluded a [5,2,6,8,7,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1443 : Excluded a [5,2,6,8,7,1] :=
  source_excluded a [5,2,6,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1444 : Excluded a [5,2,6,8,7,3] :=
  source_excluded a [5,2,6,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1445 : Excluded a [5,2,6,8,7,4] :=
  predecessor_excluded a [5,2,6,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1441 : Excluded a [5,2,6,8,7] :=
  branch_excluded a [5,2,6,8,7] (by decide)
    (fin9_cases _
      node_1442
      node_1443
      (invalid_excluded a [5,2,6,8,7,2] (by decide +kernel))
      node_1444
      node_1445
      (invalid_excluded a [5,2,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,2,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,2,6,8,7,8] (by decide +kernel)))

theorem node_1433 : Excluded a [5,2,6,8] :=
  branch_excluded a [5,2,6,8] (by decide)
    (fin9_cases _
      node_1434
      node_1435
      (invalid_excluded a [5,2,6,8,2] (by decide +kernel))
      node_1436
      (invalid_excluded a [5,2,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,2,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,8,6] (by decide +kernel))
      node_1441
      (invalid_excluded a [5,2,6,8,8] (by decide +kernel)))

theorem node_1405 : Excluded a [5,2,6] :=
  branch_excluded a [5,2,6] (by decide)
    (fin9_cases _
      node_1406
      node_1407
      (invalid_excluded a [5,2,6,2] (by decide +kernel))
      (invalid_excluded a [5,2,6,3] (by decide +kernel))
      (invalid_excluded a [5,2,6,4] (by decide +kernel))
      (invalid_excluded a [5,2,6,5] (by decide +kernel))
      (invalid_excluded a [5,2,6,6] (by decide +kernel))
      node_1432
      node_1433)

theorem node_1447 : Excluded a [5,2,7,0] :=
  predecessor_excluded a [5,2,7,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1449 : Excluded a [5,2,7,1,0] :=
  source_excluded a [5,2,7,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1451 : Excluded a [5,2,7,1,3,0] :=
  predecessor_excluded a [5,2,7,1,3,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1452 : Excluded a [5,2,7,1,3,4] :=
  predecessor_excluded a [5,2,7,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1455 : Excluded a [5,2,7,1,3,8,0,4] :=
  predecessor_excluded a [5,2,7,1,3,8,0,4] 0 4 2 7 (by decide) (by decide +kernel)

theorem node_1456 : Excluded a [5,2,7,1,3,8,0,6] :=
  source_excluded a [5,2,7,1,3,8,0,6] 5 0 7 (by decide) (by decide +kernel)

theorem node_1454 : Excluded a [5,2,7,1,3,8,0] :=
  branch_excluded a [5,2,7,1,3,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,7,1,3,8,0,0] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,0,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,0,2] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,0,3] (by decide +kernel))
      node_1455
      (invalid_excluded a [5,2,7,1,3,8,0,5] (by decide +kernel))
      node_1456
      (invalid_excluded a [5,2,7,1,3,8,0,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,0,8] (by decide +kernel)))

theorem node_1459 : Excluded a [5,2,7,1,3,8,4,0,6] :=
  source_excluded a [5,2,7,1,3,8,4,0,6] 5 0 8 (by decide) (by decide +kernel)

theorem node_1458 : Excluded a [5,2,7,1,3,8,4,0] :=
  branch_excluded a [5,2,7,1,3,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,7,1,3,8,4,0,0] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,4,0,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,4,0,2] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,4,0,3] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,4,0,5] (by decide +kernel))
      node_1459
      (invalid_excluded a [5,2,7,1,3,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,4,0,8] (by decide +kernel)))

theorem node_1460 : Excluded a [5,2,7,1,3,8,4,6] :=
  source_excluded a [5,2,7,1,3,8,4,6] 5 0 7 (by decide) (by decide +kernel)

theorem node_1457 : Excluded a [5,2,7,1,3,8,4] :=
  branch_excluded a [5,2,7,1,3,8,4] (by decide)
    (fin9_cases _
      node_1458
      (invalid_excluded a [5,2,7,1,3,8,4,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,4,2] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,4,5] (by decide +kernel))
      node_1460
      (invalid_excluded a [5,2,7,1,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,4,8] (by decide +kernel)))

theorem node_1453 : Excluded a [5,2,7,1,3,8] :=
  branch_excluded a [5,2,7,1,3,8] (by decide)
    (fin9_cases _
      node_1454
      (invalid_excluded a [5,2,7,1,3,8,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,2] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,3] (by decide +kernel))
      node_1457
      (invalid_excluded a [5,2,7,1,3,8,5] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,6] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,8,8] (by decide +kernel)))

theorem node_1450 : Excluded a [5,2,7,1,3] :=
  branch_excluded a [5,2,7,1,3] (by decide)
    (fin9_cases _
      node_1451
      (invalid_excluded a [5,2,7,1,3,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,2] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,3] (by decide +kernel))
      node_1452
      (invalid_excluded a [5,2,7,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,6] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,3,7] (by decide +kernel))
      node_1453)

theorem node_1461 : Excluded a [5,2,7,1,6] :=
  source_excluded a [5,2,7,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1463 : Excluded a [5,2,7,1,8,0] :=
  predecessor_excluded a [5,2,7,1,8,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1466 : Excluded a [5,2,7,1,8,3,0,4] :=
  source_excluded a [5,2,7,1,8,3,0,4] 7 0 4 (by decide) (by decide +kernel)

def b_1468 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 2
  | 2 => 7
  | 3 => 1
  | 4 => 8
  | 5 => 3
  | 6 => 0
  | 7 => 6
  | 8 => 4
  | _ => 0

def cert_1468 : LosingRegion (edgeOf a b_1468) 0 :=
  losingMask a b_1468 0 2377417532535454236410880
    (by decide +kernel) (by decide +kernel)

theorem node_1468 : Excluded a [5,2,7,1,8,3,0,6,4] :=
  losing_excluded a [5,2,7,1,8,3,0,6,4] (by decide) b_1468 (by decide +kernel) 2 0 0 cert_1468 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1468 2 0 ∧ 0 ≠ 2 ∧ maskRegion 2377417532535454236410880 2 0; decide +kernel)

theorem node_1467 : Excluded a [5,2,7,1,8,3,0,6] :=
  branch_excluded a [5,2,7,1,8,3,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,7,1,8,3,0,6,0] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,3,0,6,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,3,0,6,2] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,3,0,6,3] (by decide +kernel))
      node_1468
      (invalid_excluded a [5,2,7,1,8,3,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,3,0,6,6] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,3,0,6,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,3,0,6,8] (by decide +kernel)))

theorem node_1465 : Excluded a [5,2,7,1,8,3,0] :=
  branch_excluded a [5,2,7,1,8,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,7,1,8,3,0,0] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,3,0,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,3,0,2] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,3,0,3] (by decide +kernel))
      node_1466
      (invalid_excluded a [5,2,7,1,8,3,0,5] (by decide +kernel))
      node_1467
      (invalid_excluded a [5,2,7,1,8,3,0,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,3,0,8] (by decide +kernel)))

theorem node_1469 : Excluded a [5,2,7,1,8,3,4] :=
  predecessor_excluded a [5,2,7,1,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_1464 : Excluded a [5,2,7,1,8,3] :=
  branch_excluded a [5,2,7,1,8,3] (by decide)
    (fin9_cases _
      node_1465
      (invalid_excluded a [5,2,7,1,8,3,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,3,2] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,3,3] (by decide +kernel))
      node_1469
      (invalid_excluded a [5,2,7,1,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,3,8] (by decide +kernel)))

theorem node_1472 : Excluded a [5,2,7,1,8,4,0,3] :=
  source_excluded a [5,2,7,1,8,4,0,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_1474 : Excluded a [5,2,7,1,8,4,0,6,3] :=
  source_excluded a [5,2,7,1,8,4,0,6,3] 8 0 2 (by decide) (by decide +kernel)

theorem node_1473 : Excluded a [5,2,7,1,8,4,0,6] :=
  branch_excluded a [5,2,7,1,8,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,7,1,8,4,0,6,0] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,4,0,6,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,4,0,6,2] (by decide +kernel))
      node_1474
      (invalid_excluded a [5,2,7,1,8,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,4,0,6,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,4,0,6,8] (by decide +kernel)))

theorem node_1471 : Excluded a [5,2,7,1,8,4,0] :=
  branch_excluded a [5,2,7,1,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,7,1,8,4,0,0] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,4,0,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,4,0,2] (by decide +kernel))
      node_1472
      (invalid_excluded a [5,2,7,1,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,4,0,5] (by decide +kernel))
      node_1473
      (invalid_excluded a [5,2,7,1,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,4,0,8] (by decide +kernel)))

theorem node_1475 : Excluded a [5,2,7,1,8,4,3] :=
  source_excluded a [5,2,7,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1470 : Excluded a [5,2,7,1,8,4] :=
  branch_excluded a [5,2,7,1,8,4] (by decide)
    (fin9_cases _
      node_1471
      (invalid_excluded a [5,2,7,1,8,4,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,4,2] (by decide +kernel))
      node_1475
      (invalid_excluded a [5,2,7,1,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,4,8] (by decide +kernel)))

theorem node_1462 : Excluded a [5,2,7,1,8] :=
  branch_excluded a [5,2,7,1,8] (by decide)
    (fin9_cases _
      node_1463
      (invalid_excluded a [5,2,7,1,8,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,2] (by decide +kernel))
      node_1464
      node_1470
      (invalid_excluded a [5,2,7,1,8,5] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,8,8] (by decide +kernel)))

theorem node_1448 : Excluded a [5,2,7,1] :=
  branch_excluded a [5,2,7,1] (by decide)
    (fin9_cases _
      node_1449
      (invalid_excluded a [5,2,7,1,1] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,2] (by decide +kernel))
      node_1450
      (invalid_excluded a [5,2,7,1,4] (by decide +kernel))
      (invalid_excluded a [5,2,7,1,5] (by decide +kernel))
      node_1461
      (invalid_excluded a [5,2,7,1,7] (by decide +kernel))
      node_1462)

theorem node_1477 : Excluded a [5,2,7,6,0] :=
  source_excluded a [5,2,7,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1478 : Excluded a [5,2,7,6,1] :=
  source_excluded a [5,2,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1479 : Excluded a [5,2,7,6,3] :=
  predecessor_excluded a [5,2,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1481 : Excluded a [5,2,7,6,8,0] :=
  predecessor_excluded a [5,2,7,6,8,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1482 : Excluded a [5,2,7,6,8,1] :=
  source_excluded a [5,2,7,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1483 : Excluded a [5,2,7,6,8,3] :=
  source_excluded a [5,2,7,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1484 : Excluded a [5,2,7,6,8,4] :=
  source_excluded a [5,2,7,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1480 : Excluded a [5,2,7,6,8] :=
  branch_excluded a [5,2,7,6,8] (by decide)
    (fin9_cases _
      node_1481
      node_1482
      (invalid_excluded a [5,2,7,6,8,2] (by decide +kernel))
      node_1483
      node_1484
      (invalid_excluded a [5,2,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,2,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,2,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,2,7,6,8,8] (by decide +kernel)))

theorem node_1476 : Excluded a [5,2,7,6] :=
  branch_excluded a [5,2,7,6] (by decide)
    (fin9_cases _
      node_1477
      node_1478
      (invalid_excluded a [5,2,7,6,2] (by decide +kernel))
      node_1479
      (invalid_excluded a [5,2,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,2,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,2,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,2,7,6,7] (by decide +kernel))
      node_1480)

theorem node_1485 : Excluded a [5,2,7,8] :=
  predecessor_excluded a [5,2,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_1446 : Excluded a [5,2,7] :=
  branch_excluded a [5,2,7] (by decide)
    (fin9_cases _
      node_1447
      node_1448
      (invalid_excluded a [5,2,7,2] (by decide +kernel))
      (invalid_excluded a [5,2,7,3] (by decide +kernel))
      (invalid_excluded a [5,2,7,4] (by decide +kernel))
      (invalid_excluded a [5,2,7,5] (by decide +kernel))
      node_1476
      (invalid_excluded a [5,2,7,7] (by decide +kernel))
      node_1485)

theorem node_1487 : Excluded a [5,2,8,0] :=
  predecessor_excluded a [5,2,8,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1489 : Excluded a [5,2,8,1,0] :=
  source_excluded a [5,2,8,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1491 : Excluded a [5,2,8,1,3,0] :=
  predecessor_excluded a [5,2,8,1,3,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1492 : Excluded a [5,2,8,1,3,4] :=
  predecessor_excluded a [5,2,8,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1493 : Excluded a [5,2,8,1,3,7] :=
  source_excluded a [5,2,8,1,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1490 : Excluded a [5,2,8,1,3] :=
  branch_excluded a [5,2,8,1,3] (by decide)
    (fin9_cases _
      node_1491
      (invalid_excluded a [5,2,8,1,3,1] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,3,2] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,3,3] (by decide +kernel))
      node_1492
      (invalid_excluded a [5,2,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,3,6] (by decide +kernel))
      node_1493
      (invalid_excluded a [5,2,8,1,3,8] (by decide +kernel)))

theorem node_1494 : Excluded a [5,2,8,1,6] :=
  source_excluded a [5,2,8,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1496 : Excluded a [5,2,8,1,7,0] :=
  predecessor_excluded a [5,2,8,1,7,0] 2 0 0 5 (by decide) (by decide +kernel)

def b_1500 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 2
  | 2 => 8
  | 3 => 1
  | 4 => 7
  | 5 => 3
  | 6 => 0
  | 7 => 4
  | 8 => 6
  | _ => 0

def cert_1500 : LosingRegion (edgeOf a b_1500) 0 :=
  losingMask a b_1500 0 1666895067685142675063808
    (by decide +kernel) (by decide +kernel)

theorem node_1500 : Excluded a [5,2,8,1,7,3,0,4,6] :=
  losing_excluded a [5,2,8,1,7,3,0,4,6] (by decide) b_1500 (by decide +kernel) 2 0 0 cert_1500 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1500 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1666895067685142675063808 2 0; decide +kernel)

theorem node_1499 : Excluded a [5,2,8,1,7,3,0,4] :=
  branch_excluded a [5,2,8,1,7,3,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,8,1,7,3,0,4,0] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,3,0,4,1] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,3,0,4,2] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,3,0,4,3] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,3,0,4,4] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,3,0,4,5] (by decide +kernel))
      node_1500
      (invalid_excluded a [5,2,8,1,7,3,0,4,7] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,3,0,4,8] (by decide +kernel)))

theorem node_1501 : Excluded a [5,2,8,1,7,3,0,6] :=
  predecessor_excluded a [5,2,8,1,7,3,0,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_1498 : Excluded a [5,2,8,1,7,3,0] :=
  branch_excluded a [5,2,8,1,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,2,8,1,7,3,0,0] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,3,0,1] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,3,0,2] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,3,0,3] (by decide +kernel))
      node_1499
      (invalid_excluded a [5,2,8,1,7,3,0,5] (by decide +kernel))
      node_1501
      (invalid_excluded a [5,2,8,1,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,3,0,8] (by decide +kernel)))

theorem node_1502 : Excluded a [5,2,8,1,7,3,4] :=
  source_excluded a [5,2,8,1,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1497 : Excluded a [5,2,8,1,7,3] :=
  branch_excluded a [5,2,8,1,7,3] (by decide)
    (fin9_cases _
      node_1498
      (invalid_excluded a [5,2,8,1,7,3,1] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,3,2] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,3,3] (by decide +kernel))
      node_1502
      (invalid_excluded a [5,2,8,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,3,8] (by decide +kernel)))

theorem node_1503 : Excluded a [5,2,8,1,7,4] :=
  predecessor_excluded a [5,2,8,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1495 : Excluded a [5,2,8,1,7] :=
  branch_excluded a [5,2,8,1,7] (by decide)
    (fin9_cases _
      node_1496
      (invalid_excluded a [5,2,8,1,7,1] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,2] (by decide +kernel))
      node_1497
      node_1503
      (invalid_excluded a [5,2,8,1,7,5] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,6] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,7] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,7,8] (by decide +kernel)))

theorem node_1488 : Excluded a [5,2,8,1] :=
  branch_excluded a [5,2,8,1] (by decide)
    (fin9_cases _
      node_1489
      (invalid_excluded a [5,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,2] (by decide +kernel))
      node_1490
      (invalid_excluded a [5,2,8,1,4] (by decide +kernel))
      (invalid_excluded a [5,2,8,1,5] (by decide +kernel))
      node_1494
      node_1495
      (invalid_excluded a [5,2,8,1,8] (by decide +kernel)))

theorem node_1505 : Excluded a [5,2,8,6,0] :=
  source_excluded a [5,2,8,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1506 : Excluded a [5,2,8,6,1] :=
  source_excluded a [5,2,8,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1507 : Excluded a [5,2,8,6,3] :=
  predecessor_excluded a [5,2,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1508 : Excluded a [5,2,8,6,7] :=
  predecessor_excluded a [5,2,8,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_1504 : Excluded a [5,2,8,6] :=
  branch_excluded a [5,2,8,6] (by decide)
    (fin9_cases _
      node_1505
      node_1506
      (invalid_excluded a [5,2,8,6,2] (by decide +kernel))
      node_1507
      (invalid_excluded a [5,2,8,6,4] (by decide +kernel))
      (invalid_excluded a [5,2,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,2,8,6,6] (by decide +kernel))
      node_1508
      (invalid_excluded a [5,2,8,6,8] (by decide +kernel)))

theorem node_1510 : Excluded a [5,2,8,7,0] :=
  source_excluded a [5,2,8,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1511 : Excluded a [5,2,8,7,1] :=
  source_excluded a [5,2,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1513 : Excluded a [5,2,8,7,3,0] :=
  predecessor_excluded a [5,2,8,7,3,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1514 : Excluded a [5,2,8,7,3,1] :=
  source_excluded a [5,2,8,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1515 : Excluded a [5,2,8,7,3,4] :=
  predecessor_excluded a [5,2,8,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1512 : Excluded a [5,2,8,7,3] :=
  branch_excluded a [5,2,8,7,3] (by decide)
    (fin9_cases _
      node_1513
      node_1514
      (invalid_excluded a [5,2,8,7,3,2] (by decide +kernel))
      (invalid_excluded a [5,2,8,7,3,3] (by decide +kernel))
      node_1515
      (invalid_excluded a [5,2,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,2,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,2,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,2,8,7,3,8] (by decide +kernel)))

theorem node_1516 : Excluded a [5,2,8,7,6] :=
  source_excluded a [5,2,8,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1509 : Excluded a [5,2,8,7] :=
  branch_excluded a [5,2,8,7] (by decide)
    (fin9_cases _
      node_1510
      node_1511
      (invalid_excluded a [5,2,8,7,2] (by decide +kernel))
      node_1512
      (invalid_excluded a [5,2,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,2,8,7,5] (by decide +kernel))
      node_1516
      (invalid_excluded a [5,2,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,2,8,7,8] (by decide +kernel)))

theorem node_1486 : Excluded a [5,2,8] :=
  branch_excluded a [5,2,8] (by decide)
    (fin9_cases _
      node_1487
      node_1488
      (invalid_excluded a [5,2,8,2] (by decide +kernel))
      (invalid_excluded a [5,2,8,3] (by decide +kernel))
      (invalid_excluded a [5,2,8,4] (by decide +kernel))
      (invalid_excluded a [5,2,8,5] (by decide +kernel))
      node_1504
      node_1509
      (invalid_excluded a [5,2,8,8] (by decide +kernel)))

theorem node_1401 : Excluded a [5,2] :=
  branch_excluded a [5,2] (by decide)
    (fin9_cases _
      node_1402
      node_1403
      (invalid_excluded a [5,2,2] (by decide +kernel))
      (invalid_excluded a [5,2,3] (by decide +kernel))
      node_1404
      (invalid_excluded a [5,2,5] (by decide +kernel))
      node_1405
      node_1446
      node_1486)

theorem node_1518 : Excluded a [5,3,0] :=
  source_excluded a [5,3,0] 1 2 2 (by decide) (by decide +kernel)

theorem node_1519 : Excluded a [5,3,1] :=
  source_excluded a [5,3,1] 2 0 1 (by decide) (by decide +kernel)

theorem node_1520 : Excluded a [5,3,4] :=
  source_excluded a [5,3,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_1522 : Excluded a [5,3,6,0] :=
  source_excluded a [5,3,6,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_1523 : Excluded a [5,3,6,1] :=
  predecessor_excluded a [5,3,6,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_1525 : Excluded a [5,3,6,2,0] :=
  source_excluded a [5,3,6,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1526 : Excluded a [5,3,6,2,1] :=
  source_excluded a [5,3,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1528 : Excluded a [5,3,6,2,7,0] :=
  predecessor_excluded a [5,3,6,2,7,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1529 : Excluded a [5,3,6,2,7,1] :=
  source_excluded a [5,3,6,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1530 : Excluded a [5,3,6,2,7,4] :=
  predecessor_excluded a [5,3,6,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1531 : Excluded a [5,3,6,2,7,8] :=
  predecessor_excluded a [5,3,6,2,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_1527 : Excluded a [5,3,6,2,7] :=
  branch_excluded a [5,3,6,2,7] (by decide)
    (fin9_cases _
      node_1528
      node_1529
      (invalid_excluded a [5,3,6,2,7,2] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,7,3] (by decide +kernel))
      node_1530
      (invalid_excluded a [5,3,6,2,7,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,7,6] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,7,7] (by decide +kernel))
      node_1531)

theorem node_1533 : Excluded a [5,3,6,2,8,0] :=
  predecessor_excluded a [5,3,6,2,8,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1534 : Excluded a [5,3,6,2,8,1] :=
  source_excluded a [5,3,6,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1537 : Excluded a [5,3,6,2,8,4,0,1] :=
  predecessor_excluded a [5,3,6,2,8,4,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_1536 : Excluded a [5,3,6,2,8,4,0] :=
  branch_excluded a [5,3,6,2,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,6,2,8,4,0,0] (by decide +kernel))
      node_1537
      (invalid_excluded a [5,3,6,2,8,4,0,2] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,0,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,0,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,0,6] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,0,8] (by decide +kernel)))

theorem node_1539 : Excluded a [5,3,6,2,8,4,1,0] :=
  predecessor_excluded a [5,3,6,2,8,4,1,0] 2 0 6 7 (by decide) (by decide +kernel)

theorem node_1538 : Excluded a [5,3,6,2,8,4,1] :=
  branch_excluded a [5,3,6,2,8,4,1] (by decide)
    (fin9_cases _
      node_1539
      (invalid_excluded a [5,3,6,2,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,1,2] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,1,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,1,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,1,6] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,1,8] (by decide +kernel)))

theorem node_1535 : Excluded a [5,3,6,2,8,4] :=
  branch_excluded a [5,3,6,2,8,4] (by decide)
    (fin9_cases _
      node_1536
      node_1538
      (invalid_excluded a [5,3,6,2,8,4,2] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,4,8] (by decide +kernel)))

theorem node_1540 : Excluded a [5,3,6,2,8,7] :=
  source_excluded a [5,3,6,2,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1532 : Excluded a [5,3,6,2,8] :=
  branch_excluded a [5,3,6,2,8] (by decide)
    (fin9_cases _
      node_1533
      node_1534
      (invalid_excluded a [5,3,6,2,8,2] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,3] (by decide +kernel))
      node_1535
      (invalid_excluded a [5,3,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,8,6] (by decide +kernel))
      node_1540
      (invalid_excluded a [5,3,6,2,8,8] (by decide +kernel)))

theorem node_1524 : Excluded a [5,3,6,2] :=
  branch_excluded a [5,3,6,2] (by decide)
    (fin9_cases _
      node_1525
      node_1526
      (invalid_excluded a [5,3,6,2,2] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,2,6] (by decide +kernel))
      node_1527
      node_1532)

theorem node_1541 : Excluded a [5,3,6,7] :=
  predecessor_excluded a [5,3,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_1543 : Excluded a [5,3,6,8,0] :=
  source_excluded a [5,3,6,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1544 : Excluded a [5,3,6,8,1] :=
  source_excluded a [5,3,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1545 : Excluded a [5,3,6,8,2] :=
  predecessor_excluded a [5,3,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_1547 : Excluded a [5,3,6,8,7,0] :=
  predecessor_excluded a [5,3,6,8,7,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1548 : Excluded a [5,3,6,8,7,1] :=
  source_excluded a [5,3,6,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1549 : Excluded a [5,3,6,8,7,2] :=
  source_excluded a [5,3,6,8,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1550 : Excluded a [5,3,6,8,7,4] :=
  predecessor_excluded a [5,3,6,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1546 : Excluded a [5,3,6,8,7] :=
  branch_excluded a [5,3,6,8,7] (by decide)
    (fin9_cases _
      node_1547
      node_1548
      node_1549
      (invalid_excluded a [5,3,6,8,7,3] (by decide +kernel))
      node_1550
      (invalid_excluded a [5,3,6,8,7,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,7,6] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,7,8] (by decide +kernel)))

theorem node_1542 : Excluded a [5,3,6,8] :=
  branch_excluded a [5,3,6,8] (by decide)
    (fin9_cases _
      node_1543
      node_1544
      node_1545
      (invalid_excluded a [5,3,6,8,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,8,6] (by decide +kernel))
      node_1546
      (invalid_excluded a [5,3,6,8,8] (by decide +kernel)))

theorem node_1521 : Excluded a [5,3,6] :=
  branch_excluded a [5,3,6] (by decide)
    (fin9_cases _
      node_1522
      node_1523
      node_1524
      (invalid_excluded a [5,3,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,6,6] (by decide +kernel))
      node_1541
      node_1542)

theorem node_1552 : Excluded a [5,3,7,0] :=
  source_excluded a [5,3,7,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_1553 : Excluded a [5,3,7,1] :=
  predecessor_excluded a [5,3,7,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_1555 : Excluded a [5,3,7,2,0] :=
  source_excluded a [5,3,7,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1556 : Excluded a [5,3,7,2,1] :=
  source_excluded a [5,3,7,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1557 : Excluded a [5,3,7,2,6] :=
  source_excluded a [5,3,7,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1559 : Excluded a [5,3,7,2,8,0] :=
  predecessor_excluded a [5,3,7,2,8,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1560 : Excluded a [5,3,7,2,8,1] :=
  source_excluded a [5,3,7,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1563 : Excluded a [5,3,7,2,8,4,0,1] :=
  predecessor_excluded a [5,3,7,2,8,4,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_1565 : Excluded a [5,3,7,2,8,4,0,6,1] :=
  predecessor_excluded a [5,3,7,2,8,4,0,6,1] 0 3 8 1 (by decide) (by decide +kernel)

theorem node_1564 : Excluded a [5,3,7,2,8,4,0,6] :=
  branch_excluded a [5,3,7,2,8,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,7,2,8,4,0,6,0] (by decide +kernel))
      node_1565
      (invalid_excluded a [5,3,7,2,8,4,0,6,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,0,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,0,6,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,0,6,8] (by decide +kernel)))

theorem node_1562 : Excluded a [5,3,7,2,8,4,0] :=
  branch_excluded a [5,3,7,2,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,7,2,8,4,0,0] (by decide +kernel))
      node_1563
      (invalid_excluded a [5,3,7,2,8,4,0,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,0,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,0,5] (by decide +kernel))
      node_1564
      (invalid_excluded a [5,3,7,2,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,0,8] (by decide +kernel)))

theorem node_1567 : Excluded a [5,3,7,2,8,4,1,0] :=
  predecessor_excluded a [5,3,7,2,8,4,1,0] 2 0 6 7 (by decide) (by decide +kernel)

def b_1569 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 7
  | 3 => 2
  | 4 => 8
  | 5 => 4
  | 6 => 1
  | 7 => 6
  | 8 => 0
  | _ => 0

def cert_1569 : LosingRegion (edgeOf a b_1569) 0 :=
  losingMask a b_1569 0 1210107572048077872169984
    (by decide +kernel) (by decide +kernel)

theorem node_1569 : Excluded a [5,3,7,2,8,4,1,6,0] :=
  losing_excluded a [5,3,7,2,8,4,1,6,0] (by decide) b_1569 (by decide +kernel) 2 0 6 cert_1569 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1569 2 0 ∧ 6 ≠ 2 ∧ maskRegion 1210107572048077872169984 2 6; decide +kernel)

theorem node_1568 : Excluded a [5,3,7,2,8,4,1,6] :=
  branch_excluded a [5,3,7,2,8,4,1,6] (by decide)
    (fin9_cases _
      node_1569
      (invalid_excluded a [5,3,7,2,8,4,1,6,1] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,1,6,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,1,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,1,6,8] (by decide +kernel)))

theorem node_1566 : Excluded a [5,3,7,2,8,4,1] :=
  branch_excluded a [5,3,7,2,8,4,1] (by decide)
    (fin9_cases _
      node_1567
      (invalid_excluded a [5,3,7,2,8,4,1,1] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,1,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,1,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,1,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,1,5] (by decide +kernel))
      node_1568
      (invalid_excluded a [5,3,7,2,8,4,1,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,1,8] (by decide +kernel)))

theorem node_1561 : Excluded a [5,3,7,2,8,4] :=
  branch_excluded a [5,3,7,2,8,4] (by decide)
    (fin9_cases _
      node_1562
      node_1566
      (invalid_excluded a [5,3,7,2,8,4,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,4,8] (by decide +kernel)))

theorem node_1558 : Excluded a [5,3,7,2,8] :=
  branch_excluded a [5,3,7,2,8] (by decide)
    (fin9_cases _
      node_1559
      node_1560
      (invalid_excluded a [5,3,7,2,8,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,3] (by decide +kernel))
      node_1561
      (invalid_excluded a [5,3,7,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,8,8] (by decide +kernel)))

theorem node_1554 : Excluded a [5,3,7,2] :=
  branch_excluded a [5,3,7,2] (by decide)
    (fin9_cases _
      node_1555
      node_1556
      (invalid_excluded a [5,3,7,2,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,2,5] (by decide +kernel))
      node_1557
      (invalid_excluded a [5,3,7,2,7] (by decide +kernel))
      node_1558)

theorem node_1571 : Excluded a [5,3,7,6,0] :=
  source_excluded a [5,3,7,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1572 : Excluded a [5,3,7,6,1] :=
  source_excluded a [5,3,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1574 : Excluded a [5,3,7,6,2,0] :=
  predecessor_excluded a [5,3,7,6,2,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1575 : Excluded a [5,3,7,6,2,1] :=
  source_excluded a [5,3,7,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1576 : Excluded a [5,3,7,6,2,4] :=
  source_excluded a [5,3,7,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1579 : Excluded a [5,3,7,6,2,8,0,1] :=
  predecessor_excluded a [5,3,7,6,2,8,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_1580 : Excluded a [5,3,7,6,2,8,0,4] :=
  predecessor_excluded a [5,3,7,6,2,8,0,4] 0 2 7 4 (by decide) (by decide +kernel)

theorem node_1578 : Excluded a [5,3,7,6,2,8,0] :=
  branch_excluded a [5,3,7,6,2,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,7,6,2,8,0,0] (by decide +kernel))
      node_1579
      (invalid_excluded a [5,3,7,6,2,8,0,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,0,3] (by decide +kernel))
      node_1580
      (invalid_excluded a [5,3,7,6,2,8,0,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,0,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,0,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,0,8] (by decide +kernel)))

theorem node_1582 : Excluded a [5,3,7,6,2,8,1,0] :=
  predecessor_excluded a [5,3,7,6,2,8,1,0] 2 0 6 7 (by decide) (by decide +kernel)

theorem node_1583 : Excluded a [5,3,7,6,2,8,1,4] :=
  predecessor_excluded a [5,3,7,6,2,8,1,4] 0 2 7 4 (by decide) (by decide +kernel)

theorem node_1581 : Excluded a [5,3,7,6,2,8,1] :=
  branch_excluded a [5,3,7,6,2,8,1] (by decide)
    (fin9_cases _
      node_1582
      (invalid_excluded a [5,3,7,6,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,3] (by decide +kernel))
      node_1583
      (invalid_excluded a [5,3,7,6,2,8,1,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,1,8] (by decide +kernel)))

theorem node_1584 : Excluded a [5,3,7,6,2,8,4] :=
  source_excluded a [5,3,7,6,2,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1577 : Excluded a [5,3,7,6,2,8] :=
  branch_excluded a [5,3,7,6,2,8] (by decide)
    (fin9_cases _
      node_1578
      node_1581
      (invalid_excluded a [5,3,7,6,2,8,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,3] (by decide +kernel))
      node_1584
      (invalid_excluded a [5,3,7,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,8,8] (by decide +kernel)))

theorem node_1573 : Excluded a [5,3,7,6,2] :=
  branch_excluded a [5,3,7,6,2] (by decide)
    (fin9_cases _
      node_1574
      node_1575
      (invalid_excluded a [5,3,7,6,2,2] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,3] (by decide +kernel))
      node_1576
      (invalid_excluded a [5,3,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,2,7] (by decide +kernel))
      node_1577)

theorem node_1586 : Excluded a [5,3,7,6,8,0] :=
  predecessor_excluded a [5,3,7,6,8,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1587 : Excluded a [5,3,7,6,8,1] :=
  source_excluded a [5,3,7,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1588 : Excluded a [5,3,7,6,8,2] :=
  predecessor_excluded a [5,3,7,6,8,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1589 : Excluded a [5,3,7,6,8,4] :=
  source_excluded a [5,3,7,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1585 : Excluded a [5,3,7,6,8] :=
  branch_excluded a [5,3,7,6,8] (by decide)
    (fin9_cases _
      node_1586
      node_1587
      node_1588
      (invalid_excluded a [5,3,7,6,8,3] (by decide +kernel))
      node_1589
      (invalid_excluded a [5,3,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,8,8] (by decide +kernel)))

theorem node_1570 : Excluded a [5,3,7,6] :=
  branch_excluded a [5,3,7,6] (by decide)
    (fin9_cases _
      node_1571
      node_1572
      node_1573
      (invalid_excluded a [5,3,7,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,3,7,6,7] (by decide +kernel))
      node_1585)

theorem node_1590 : Excluded a [5,3,7,8] :=
  predecessor_excluded a [5,3,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_1551 : Excluded a [5,3,7] :=
  branch_excluded a [5,3,7] (by decide)
    (fin9_cases _
      node_1552
      node_1553
      node_1554
      (invalid_excluded a [5,3,7,3] (by decide +kernel))
      (invalid_excluded a [5,3,7,4] (by decide +kernel))
      (invalid_excluded a [5,3,7,5] (by decide +kernel))
      node_1570
      (invalid_excluded a [5,3,7,7] (by decide +kernel))
      node_1590)

theorem node_1592 : Excluded a [5,3,8,0] :=
  source_excluded a [5,3,8,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_1593 : Excluded a [5,3,8,1] :=
  predecessor_excluded a [5,3,8,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_1594 : Excluded a [5,3,8,2] :=
  predecessor_excluded a [5,3,8,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_1596 : Excluded a [5,3,8,6,0] :=
  source_excluded a [5,3,8,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1597 : Excluded a [5,3,8,6,1] :=
  source_excluded a [5,3,8,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1599 : Excluded a [5,3,8,6,2,0] :=
  predecessor_excluded a [5,3,8,6,2,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1600 : Excluded a [5,3,8,6,2,1] :=
  source_excluded a [5,3,8,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1601 : Excluded a [5,3,8,6,2,4] :=
  source_excluded a [5,3,8,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1602 : Excluded a [5,3,8,6,2,7] :=
  source_excluded a [5,3,8,6,2,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1598 : Excluded a [5,3,8,6,2] :=
  branch_excluded a [5,3,8,6,2] (by decide)
    (fin9_cases _
      node_1599
      node_1600
      (invalid_excluded a [5,3,8,6,2,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,2,3] (by decide +kernel))
      node_1601
      (invalid_excluded a [5,3,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,2,6] (by decide +kernel))
      node_1602
      (invalid_excluded a [5,3,8,6,2,8] (by decide +kernel)))

theorem node_1603 : Excluded a [5,3,8,6,7] :=
  predecessor_excluded a [5,3,8,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_1595 : Excluded a [5,3,8,6] :=
  branch_excluded a [5,3,8,6] (by decide)
    (fin9_cases _
      node_1596
      node_1597
      node_1598
      (invalid_excluded a [5,3,8,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,6,6] (by decide +kernel))
      node_1603
      (invalid_excluded a [5,3,8,6,8] (by decide +kernel)))

theorem node_1605 : Excluded a [5,3,8,7,0] :=
  source_excluded a [5,3,8,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1606 : Excluded a [5,3,8,7,1] :=
  source_excluded a [5,3,8,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1608 : Excluded a [5,3,8,7,2,0] :=
  predecessor_excluded a [5,3,8,7,2,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1609 : Excluded a [5,3,8,7,2,1] :=
  source_excluded a [5,3,8,7,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1612 : Excluded a [5,3,8,7,2,4,0,1] :=
  predecessor_excluded a [5,3,8,7,2,4,0,1] 2 1 6 7 (by decide) (by decide +kernel)

theorem node_1614 : Excluded a [5,3,8,7,2,4,0,6,1] :=
  predecessor_excluded a [5,3,8,7,2,4,0,6,1] 0 3 8 1 (by decide) (by decide +kernel)

theorem node_1613 : Excluded a [5,3,8,7,2,4,0,6] :=
  branch_excluded a [5,3,8,7,2,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,8,7,2,4,0,6,0] (by decide +kernel))
      node_1614
      (invalid_excluded a [5,3,8,7,2,4,0,6,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,6,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,6,8] (by decide +kernel)))

theorem node_1611 : Excluded a [5,3,8,7,2,4,0] :=
  branch_excluded a [5,3,8,7,2,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,3,8,7,2,4,0,0] (by decide +kernel))
      node_1612
      (invalid_excluded a [5,3,8,7,2,4,0,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,5] (by decide +kernel))
      node_1613
      (invalid_excluded a [5,3,8,7,2,4,0,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,0,8] (by decide +kernel)))

theorem node_1616 : Excluded a [5,3,8,7,2,4,1,0] :=
  predecessor_excluded a [5,3,8,7,2,4,1,0] 2 0 6 7 (by decide) (by decide +kernel)

def b_1618 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 8
  | 3 => 7
  | 4 => 2
  | 5 => 4
  | 6 => 1
  | 7 => 6
  | 8 => 0
  | _ => 0

def cert_1618 : LosingRegion (edgeOf a b_1618) 0 :=
  losingMask a b_1618 0 1210107572053020825879552
    (by decide +kernel) (by decide +kernel)

theorem node_1618 : Excluded a [5,3,8,7,2,4,1,6,0] :=
  losing_excluded a [5,3,8,7,2,4,1,6,0] (by decide) b_1618 (by decide +kernel) 2 0 7 cert_1618 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1618 2 0 ∧ 7 ≠ 2 ∧ maskRegion 1210107572053020825879552 2 7; decide +kernel)

theorem node_1617 : Excluded a [5,3,8,7,2,4,1,6] :=
  branch_excluded a [5,3,8,7,2,4,1,6] (by decide)
    (fin9_cases _
      node_1618
      (invalid_excluded a [5,3,8,7,2,4,1,6,1] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,6,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,6,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,6,8] (by decide +kernel)))

theorem node_1615 : Excluded a [5,3,8,7,2,4,1] :=
  branch_excluded a [5,3,8,7,2,4,1] (by decide)
    (fin9_cases _
      node_1616
      (invalid_excluded a [5,3,8,7,2,4,1,1] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,5] (by decide +kernel))
      node_1617
      (invalid_excluded a [5,3,8,7,2,4,1,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,1,8] (by decide +kernel)))

theorem node_1610 : Excluded a [5,3,8,7,2,4] :=
  branch_excluded a [5,3,8,7,2,4] (by decide)
    (fin9_cases _
      node_1611
      node_1615
      (invalid_excluded a [5,3,8,7,2,4,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,4,8] (by decide +kernel)))

theorem node_1607 : Excluded a [5,3,8,7,2] :=
  branch_excluded a [5,3,8,7,2] (by decide)
    (fin9_cases _
      node_1608
      node_1609
      (invalid_excluded a [5,3,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,3] (by decide +kernel))
      node_1610
      (invalid_excluded a [5,3,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,2,8] (by decide +kernel)))

theorem node_1619 : Excluded a [5,3,8,7,6] :=
  source_excluded a [5,3,8,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1604 : Excluded a [5,3,8,7] :=
  branch_excluded a [5,3,8,7] (by decide)
    (fin9_cases _
      node_1605
      node_1606
      node_1607
      (invalid_excluded a [5,3,8,7,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,5] (by decide +kernel))
      node_1619
      (invalid_excluded a [5,3,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,3,8,7,8] (by decide +kernel)))

theorem node_1591 : Excluded a [5,3,8] :=
  branch_excluded a [5,3,8] (by decide)
    (fin9_cases _
      node_1592
      node_1593
      node_1594
      (invalid_excluded a [5,3,8,3] (by decide +kernel))
      (invalid_excluded a [5,3,8,4] (by decide +kernel))
      (invalid_excluded a [5,3,8,5] (by decide +kernel))
      node_1595
      node_1604
      (invalid_excluded a [5,3,8,8] (by decide +kernel)))

theorem node_1517 : Excluded a [5,3] :=
  branch_excluded a [5,3] (by decide)
    (fin9_cases _
      node_1518
      node_1519
      (invalid_excluded a [5,3,2] (by decide +kernel))
      (invalid_excluded a [5,3,3] (by decide +kernel))
      node_1520
      (invalid_excluded a [5,3,5] (by decide +kernel))
      node_1521
      node_1551
      node_1591)

theorem node_1620 : Excluded a [5,4] :=
  predecessor_excluded a [5,4] 2 5 1 0 (by decide) (by decide +kernel)

theorem node_1621 : Excluded a [5,6] :=
  predecessor_excluded a [5,6] 2 6 0 1 (by decide) (by decide +kernel)

theorem node_1624 : Excluded a [5,7,0,1] :=
  predecessor_excluded a [5,7,0,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_1626 : Excluded a [5,7,0,2,1] :=
  source_excluded a [5,7,0,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1627 : Excluded a [5,7,0,2,3] :=
  predecessor_excluded a [5,7,0,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1628 : Excluded a [5,7,0,2,6] :=
  source_excluded a [5,7,0,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1630 : Excluded a [5,7,0,2,8,1] :=
  source_excluded a [5,7,0,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1632 : Excluded a [5,7,0,2,8,3,1] :=
  source_excluded a [5,7,0,2,8,3,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1633 : Excluded a [5,7,0,2,8,3,4] :=
  predecessor_excluded a [5,7,0,2,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_1631 : Excluded a [5,7,0,2,8,3] :=
  branch_excluded a [5,7,0,2,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,2,8,3,0] (by decide +kernel))
      node_1632
      (invalid_excluded a [5,7,0,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,3,3] (by decide +kernel))
      node_1633
      (invalid_excluded a [5,7,0,2,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,3,8] (by decide +kernel)))

theorem node_1635 : Excluded a [5,7,0,2,8,4,1] :=
  source_excluded a [5,7,0,2,8,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1637 : Excluded a [5,7,0,2,8,4,3,1] :=
  predecessor_excluded a [5,7,0,2,8,4,3,1] 2 1 1 7 (by decide) (by decide +kernel)

theorem node_1639 : Excluded a [5,7,0,2,8,4,3,6,1] :=
  predecessor_excluded a [5,7,0,2,8,4,3,6,1] 3 0 8 2 (by decide) (by decide +kernel)

theorem node_1638 : Excluded a [5,7,0,2,8,4,3,6] :=
  branch_excluded a [5,7,0,2,8,4,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,2,8,4,3,6,0] (by decide +kernel))
      node_1639
      (invalid_excluded a [5,7,0,2,8,4,3,6,2] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,6,8] (by decide +kernel)))

theorem node_1636 : Excluded a [5,7,0,2,8,4,3] :=
  branch_excluded a [5,7,0,2,8,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,2,8,4,3,0] (by decide +kernel))
      node_1637
      (invalid_excluded a [5,7,0,2,8,4,3,2] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,5] (by decide +kernel))
      node_1638
      (invalid_excluded a [5,7,0,2,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,3,8] (by decide +kernel)))

theorem node_1634 : Excluded a [5,7,0,2,8,4] :=
  branch_excluded a [5,7,0,2,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,2,8,4,0] (by decide +kernel))
      node_1635
      (invalid_excluded a [5,7,0,2,8,4,2] (by decide +kernel))
      node_1636
      (invalid_excluded a [5,7,0,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,4,8] (by decide +kernel)))

theorem node_1629 : Excluded a [5,7,0,2,8] :=
  branch_excluded a [5,7,0,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,2,8,0] (by decide +kernel))
      node_1630
      (invalid_excluded a [5,7,0,2,8,2] (by decide +kernel))
      node_1631
      node_1634
      (invalid_excluded a [5,7,0,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,8,8] (by decide +kernel)))

theorem node_1625 : Excluded a [5,7,0,2] :=
  branch_excluded a [5,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,2,0] (by decide +kernel))
      node_1626
      (invalid_excluded a [5,7,0,2,2] (by decide +kernel))
      node_1627
      (invalid_excluded a [5,7,0,2,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,2,5] (by decide +kernel))
      node_1628
      (invalid_excluded a [5,7,0,2,7] (by decide +kernel))
      node_1629)

theorem node_1641 : Excluded a [5,7,0,6,1] :=
  source_excluded a [5,7,0,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1643 : Excluded a [5,7,0,6,2,1] :=
  source_excluded a [5,7,0,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1644 : Excluded a [5,7,0,6,2,3] :=
  source_excluded a [5,7,0,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1645 : Excluded a [5,7,0,6,2,4] :=
  source_excluded a [5,7,0,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1647 : Excluded a [5,7,0,6,2,8,1] :=
  source_excluded a [5,7,0,6,2,8,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1649 : Excluded a [5,7,0,6,2,8,3,1] :=
  predecessor_excluded a [5,7,0,6,2,8,3,1] 2 1 1 7 (by decide) (by decide +kernel)

theorem node_1650 : Excluded a [5,7,0,6,2,8,3,4] :=
  predecessor_excluded a [5,7,0,6,2,8,3,4] 0 2 7 4 (by decide) (by decide +kernel)

theorem node_1648 : Excluded a [5,7,0,6,2,8,3] :=
  branch_excluded a [5,7,0,6,2,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,6,2,8,3,0] (by decide +kernel))
      node_1649
      (invalid_excluded a [5,7,0,6,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,3,3] (by decide +kernel))
      node_1650
      (invalid_excluded a [5,7,0,6,2,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,3,8] (by decide +kernel)))

theorem node_1651 : Excluded a [5,7,0,6,2,8,4] :=
  source_excluded a [5,7,0,6,2,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1646 : Excluded a [5,7,0,6,2,8] :=
  branch_excluded a [5,7,0,6,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,6,2,8,0] (by decide +kernel))
      node_1647
      (invalid_excluded a [5,7,0,6,2,8,2] (by decide +kernel))
      node_1648
      node_1651
      (invalid_excluded a [5,7,0,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,8,8] (by decide +kernel)))

theorem node_1642 : Excluded a [5,7,0,6,2] :=
  branch_excluded a [5,7,0,6,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,6,2,0] (by decide +kernel))
      node_1643
      (invalid_excluded a [5,7,0,6,2,2] (by decide +kernel))
      node_1644
      node_1645
      (invalid_excluded a [5,7,0,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,2,7] (by decide +kernel))
      node_1646)

theorem node_1652 : Excluded a [5,7,0,6,3] :=
  predecessor_excluded a [5,7,0,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1654 : Excluded a [5,7,0,6,8,1] :=
  source_excluded a [5,7,0,6,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1655 : Excluded a [5,7,0,6,8,2] :=
  predecessor_excluded a [5,7,0,6,8,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1656 : Excluded a [5,7,0,6,8,3] :=
  source_excluded a [5,7,0,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1657 : Excluded a [5,7,0,6,8,4] :=
  source_excluded a [5,7,0,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1653 : Excluded a [5,7,0,6,8] :=
  branch_excluded a [5,7,0,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,6,8,0] (by decide +kernel))
      node_1654
      node_1655
      node_1656
      node_1657
      (invalid_excluded a [5,7,0,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,8,8] (by decide +kernel)))

theorem node_1640 : Excluded a [5,7,0,6] :=
  branch_excluded a [5,7,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,6,0] (by decide +kernel))
      node_1641
      node_1642
      node_1652
      (invalid_excluded a [5,7,0,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,6,7] (by decide +kernel))
      node_1653)

theorem node_1659 : Excluded a [5,7,0,8,1] :=
  source_excluded a [5,7,0,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1660 : Excluded a [5,7,0,8,2] :=
  predecessor_excluded a [5,7,0,8,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1662 : Excluded a [5,7,0,8,3,1] :=
  source_excluded a [5,7,0,8,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1664 : Excluded a [5,7,0,8,3,2,1] :=
  source_excluded a [5,7,0,8,3,2,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1666 : Excluded a [5,7,0,8,3,2,4,1] :=
  predecessor_excluded a [5,7,0,8,3,2,4,1] 2 1 1 7 (by decide) (by decide +kernel)

theorem node_1668 : Excluded a [5,7,0,8,3,2,4,6,1] :=
  predecessor_excluded a [5,7,0,8,3,2,4,6,1] 3 0 8 2 (by decide) (by decide +kernel)

theorem node_1667 : Excluded a [5,7,0,8,3,2,4,6] :=
  branch_excluded a [5,7,0,8,3,2,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,8,3,2,4,6,0] (by decide +kernel))
      node_1668
      (invalid_excluded a [5,7,0,8,3,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,2,4,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,2,4,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,2,4,6,8] (by decide +kernel)))

theorem node_1665 : Excluded a [5,7,0,8,3,2,4] :=
  branch_excluded a [5,7,0,8,3,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,8,3,2,4,0] (by decide +kernel))
      node_1666
      (invalid_excluded a [5,7,0,8,3,2,4,2] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,2,4,3] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,2,4,5] (by decide +kernel))
      node_1667
      (invalid_excluded a [5,7,0,8,3,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,2,4,8] (by decide +kernel)))

theorem node_1663 : Excluded a [5,7,0,8,3,2] :=
  branch_excluded a [5,7,0,8,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,8,3,2,0] (by decide +kernel))
      node_1664
      (invalid_excluded a [5,7,0,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,2,3] (by decide +kernel))
      node_1665
      (invalid_excluded a [5,7,0,8,3,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,2,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,2,8] (by decide +kernel)))

theorem node_1669 : Excluded a [5,7,0,8,3,4] :=
  predecessor_excluded a [5,7,0,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1661 : Excluded a [5,7,0,8,3] :=
  branch_excluded a [5,7,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,8,3,0] (by decide +kernel))
      node_1662
      node_1663
      (invalid_excluded a [5,7,0,8,3,3] (by decide +kernel))
      node_1669
      (invalid_excluded a [5,7,0,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,3,8] (by decide +kernel)))

theorem node_1670 : Excluded a [5,7,0,8,6] :=
  source_excluded a [5,7,0,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1658 : Excluded a [5,7,0,8] :=
  branch_excluded a [5,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,8,0] (by decide +kernel))
      node_1659
      node_1660
      node_1661
      (invalid_excluded a [5,7,0,8,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,5] (by decide +kernel))
      node_1670
      (invalid_excluded a [5,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,0,8,8] (by decide +kernel)))

theorem node_1623 : Excluded a [5,7,0] :=
  branch_excluded a [5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,7,0,0] (by decide +kernel))
      node_1624
      node_1625
      (invalid_excluded a [5,7,0,3] (by decide +kernel))
      (invalid_excluded a [5,7,0,4] (by decide +kernel))
      (invalid_excluded a [5,7,0,5] (by decide +kernel))
      node_1640
      (invalid_excluded a [5,7,0,7] (by decide +kernel))
      node_1658)

theorem node_1672 : Excluded a [5,7,1,0] :=
  predecessor_excluded a [5,7,1,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1674 : Excluded a [5,7,1,2,0] :=
  source_excluded a [5,7,1,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1675 : Excluded a [5,7,1,2,3] :=
  predecessor_excluded a [5,7,1,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1676 : Excluded a [5,7,1,2,6] :=
  source_excluded a [5,7,1,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1678 : Excluded a [5,7,1,2,8,0] :=
  predecessor_excluded a [5,7,1,2,8,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1680 : Excluded a [5,7,1,2,8,3,0] :=
  source_excluded a [5,7,1,2,8,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1681 : Excluded a [5,7,1,2,8,3,4] :=
  predecessor_excluded a [5,7,1,2,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_1679 : Excluded a [5,7,1,2,8,3] :=
  branch_excluded a [5,7,1,2,8,3] (by decide)
    (fin9_cases _
      node_1680
      (invalid_excluded a [5,7,1,2,8,3,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,3,3] (by decide +kernel))
      node_1681
      (invalid_excluded a [5,7,1,2,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,3,8] (by decide +kernel)))

theorem node_1683 : Excluded a [5,7,1,2,8,4,0] :=
  source_excluded a [5,7,1,2,8,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1685 : Excluded a [5,7,1,2,8,4,3,0] :=
  source_excluded a [5,7,1,2,8,4,3,0] 1 2 7 (by decide) (by decide +kernel)

theorem node_1687 : Excluded a [5,7,1,2,8,4,3,6,0] :=
  predecessor_excluded a [5,7,1,2,8,4,3,6,0] 3 1 8 2 (by decide) (by decide +kernel)

theorem node_1686 : Excluded a [5,7,1,2,8,4,3,6] :=
  branch_excluded a [5,7,1,2,8,4,3,6] (by decide)
    (fin9_cases _
      node_1687
      (invalid_excluded a [5,7,1,2,8,4,3,6,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,3,6,2] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,3,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,3,6,8] (by decide +kernel)))

theorem node_1684 : Excluded a [5,7,1,2,8,4,3] :=
  branch_excluded a [5,7,1,2,8,4,3] (by decide)
    (fin9_cases _
      node_1685
      (invalid_excluded a [5,7,1,2,8,4,3,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,3,2] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,3,5] (by decide +kernel))
      node_1686
      (invalid_excluded a [5,7,1,2,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,3,8] (by decide +kernel)))

theorem node_1682 : Excluded a [5,7,1,2,8,4] :=
  branch_excluded a [5,7,1,2,8,4] (by decide)
    (fin9_cases _
      node_1683
      (invalid_excluded a [5,7,1,2,8,4,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,2] (by decide +kernel))
      node_1684
      (invalid_excluded a [5,7,1,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,4,8] (by decide +kernel)))

theorem node_1677 : Excluded a [5,7,1,2,8] :=
  branch_excluded a [5,7,1,2,8] (by decide)
    (fin9_cases _
      node_1678
      (invalid_excluded a [5,7,1,2,8,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,2] (by decide +kernel))
      node_1679
      node_1682
      (invalid_excluded a [5,7,1,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,8,8] (by decide +kernel)))

theorem node_1673 : Excluded a [5,7,1,2] :=
  branch_excluded a [5,7,1,2] (by decide)
    (fin9_cases _
      node_1674
      (invalid_excluded a [5,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,2] (by decide +kernel))
      node_1675
      (invalid_excluded a [5,7,1,2,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,2,5] (by decide +kernel))
      node_1676
      (invalid_excluded a [5,7,1,2,7] (by decide +kernel))
      node_1677)

theorem node_1689 : Excluded a [5,7,1,6,0] :=
  source_excluded a [5,7,1,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1691 : Excluded a [5,7,1,6,2,0] :=
  predecessor_excluded a [5,7,1,6,2,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1692 : Excluded a [5,7,1,6,2,3] :=
  source_excluded a [5,7,1,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1693 : Excluded a [5,7,1,6,2,4] :=
  source_excluded a [5,7,1,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1695 : Excluded a [5,7,1,6,2,8,0] :=
  source_excluded a [5,7,1,6,2,8,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1697 : Excluded a [5,7,1,6,2,8,3,0] :=
  source_excluded a [5,7,1,6,2,8,3,0] 1 2 7 (by decide) (by decide +kernel)

theorem node_1698 : Excluded a [5,7,1,6,2,8,3,4] :=
  predecessor_excluded a [5,7,1,6,2,8,3,4] 0 2 7 4 (by decide) (by decide +kernel)

theorem node_1696 : Excluded a [5,7,1,6,2,8,3] :=
  branch_excluded a [5,7,1,6,2,8,3] (by decide)
    (fin9_cases _
      node_1697
      (invalid_excluded a [5,7,1,6,2,8,3,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,3,3] (by decide +kernel))
      node_1698
      (invalid_excluded a [5,7,1,6,2,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,3,8] (by decide +kernel)))

theorem node_1699 : Excluded a [5,7,1,6,2,8,4] :=
  source_excluded a [5,7,1,6,2,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1694 : Excluded a [5,7,1,6,2,8] :=
  branch_excluded a [5,7,1,6,2,8] (by decide)
    (fin9_cases _
      node_1695
      (invalid_excluded a [5,7,1,6,2,8,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,2] (by decide +kernel))
      node_1696
      node_1699
      (invalid_excluded a [5,7,1,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,8,8] (by decide +kernel)))

theorem node_1690 : Excluded a [5,7,1,6,2] :=
  branch_excluded a [5,7,1,6,2] (by decide)
    (fin9_cases _
      node_1691
      (invalid_excluded a [5,7,1,6,2,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,2] (by decide +kernel))
      node_1692
      node_1693
      (invalid_excluded a [5,7,1,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,2,7] (by decide +kernel))
      node_1694)

theorem node_1700 : Excluded a [5,7,1,6,3] :=
  predecessor_excluded a [5,7,1,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1702 : Excluded a [5,7,1,6,8,0] :=
  predecessor_excluded a [5,7,1,6,8,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1703 : Excluded a [5,7,1,6,8,2] :=
  predecessor_excluded a [5,7,1,6,8,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_1704 : Excluded a [5,7,1,6,8,3] :=
  source_excluded a [5,7,1,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1705 : Excluded a [5,7,1,6,8,4] :=
  source_excluded a [5,7,1,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1701 : Excluded a [5,7,1,6,8] :=
  branch_excluded a [5,7,1,6,8] (by decide)
    (fin9_cases _
      node_1702
      (invalid_excluded a [5,7,1,6,8,1] (by decide +kernel))
      node_1703
      node_1704
      node_1705
      (invalid_excluded a [5,7,1,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,8,8] (by decide +kernel)))

theorem node_1688 : Excluded a [5,7,1,6] :=
  branch_excluded a [5,7,1,6] (by decide)
    (fin9_cases _
      node_1689
      (invalid_excluded a [5,7,1,6,1] (by decide +kernel))
      node_1690
      node_1700
      (invalid_excluded a [5,7,1,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,6,7] (by decide +kernel))
      node_1701)

theorem node_1707 : Excluded a [5,7,1,8,0] :=
  source_excluded a [5,7,1,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1708 : Excluded a [5,7,1,8,2] :=
  predecessor_excluded a [5,7,1,8,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_1710 : Excluded a [5,7,1,8,3,0] :=
  predecessor_excluded a [5,7,1,8,3,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1712 : Excluded a [5,7,1,8,3,2,0] :=
  source_excluded a [5,7,1,8,3,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1714 : Excluded a [5,7,1,8,3,2,4,0] :=
  source_excluded a [5,7,1,8,3,2,4,0] 1 2 7 (by decide) (by decide +kernel)

theorem node_1716 : Excluded a [5,7,1,8,3,2,4,6,0] :=
  predecessor_excluded a [5,7,1,8,3,2,4,6,0] 3 1 8 2 (by decide) (by decide +kernel)

theorem node_1715 : Excluded a [5,7,1,8,3,2,4,6] :=
  branch_excluded a [5,7,1,8,3,2,4,6] (by decide)
    (fin9_cases _
      node_1716
      (invalid_excluded a [5,7,1,8,3,2,4,6,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,4,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,4,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,4,6,8] (by decide +kernel)))

theorem node_1713 : Excluded a [5,7,1,8,3,2,4] :=
  branch_excluded a [5,7,1,8,3,2,4] (by decide)
    (fin9_cases _
      node_1714
      (invalid_excluded a [5,7,1,8,3,2,4,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,4,2] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,4,3] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,4,5] (by decide +kernel))
      node_1715
      (invalid_excluded a [5,7,1,8,3,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,4,8] (by decide +kernel)))

theorem node_1711 : Excluded a [5,7,1,8,3,2] :=
  branch_excluded a [5,7,1,8,3,2] (by decide)
    (fin9_cases _
      node_1712
      (invalid_excluded a [5,7,1,8,3,2,1] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,3] (by decide +kernel))
      node_1713
      (invalid_excluded a [5,7,1,8,3,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,2,8] (by decide +kernel)))

theorem node_1717 : Excluded a [5,7,1,8,3,4] :=
  predecessor_excluded a [5,7,1,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1709 : Excluded a [5,7,1,8,3] :=
  branch_excluded a [5,7,1,8,3] (by decide)
    (fin9_cases _
      node_1710
      (invalid_excluded a [5,7,1,8,3,1] (by decide +kernel))
      node_1711
      (invalid_excluded a [5,7,1,8,3,3] (by decide +kernel))
      node_1717
      (invalid_excluded a [5,7,1,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,3,8] (by decide +kernel)))

theorem node_1718 : Excluded a [5,7,1,8,6] :=
  source_excluded a [5,7,1,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1706 : Excluded a [5,7,1,8] :=
  branch_excluded a [5,7,1,8] (by decide)
    (fin9_cases _
      node_1707
      (invalid_excluded a [5,7,1,8,1] (by decide +kernel))
      node_1708
      node_1709
      (invalid_excluded a [5,7,1,8,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,5] (by decide +kernel))
      node_1718
      (invalid_excluded a [5,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,1,8,8] (by decide +kernel)))

theorem node_1671 : Excluded a [5,7,1] :=
  branch_excluded a [5,7,1] (by decide)
    (fin9_cases _
      node_1672
      (invalid_excluded a [5,7,1,1] (by decide +kernel))
      node_1673
      (invalid_excluded a [5,7,1,3] (by decide +kernel))
      (invalid_excluded a [5,7,1,4] (by decide +kernel))
      (invalid_excluded a [5,7,1,5] (by decide +kernel))
      node_1688
      (invalid_excluded a [5,7,1,7] (by decide +kernel))
      node_1706)

theorem node_1719 : Excluded a [5,7,4] :=
  source_excluded a [5,7,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_1721 : Excluded a [5,7,6,0] :=
  predecessor_excluded a [5,7,6,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1723 : Excluded a [5,7,6,1,0] :=
  source_excluded a [5,7,6,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1724 : Excluded a [5,7,6,1,2] :=
  predecessor_excluded a [5,7,6,1,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_1726 : Excluded a [5,7,6,1,3,0] :=
  predecessor_excluded a [5,7,6,1,3,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1727 : Excluded a [5,7,6,1,3,2] :=
  source_excluded a [5,7,6,1,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1728 : Excluded a [5,7,6,1,3,4] :=
  predecessor_excluded a [5,7,6,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1730 : Excluded a [5,7,6,1,3,8,0] :=
  source_excluded a [5,7,6,1,3,8,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1731 : Excluded a [5,7,6,1,3,8,2] :=
  predecessor_excluded a [5,7,6,1,3,8,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_1732 : Excluded a [5,7,6,1,3,8,4] :=
  predecessor_excluded a [5,7,6,1,3,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_1729 : Excluded a [5,7,6,1,3,8] :=
  branch_excluded a [5,7,6,1,3,8] (by decide)
    (fin9_cases _
      node_1730
      (invalid_excluded a [5,7,6,1,3,8,1] (by decide +kernel))
      node_1731
      (invalid_excluded a [5,7,6,1,3,8,3] (by decide +kernel))
      node_1732
      (invalid_excluded a [5,7,6,1,3,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,8,8] (by decide +kernel)))

theorem node_1725 : Excluded a [5,7,6,1,3] :=
  branch_excluded a [5,7,6,1,3] (by decide)
    (fin9_cases _
      node_1726
      (invalid_excluded a [5,7,6,1,3,1] (by decide +kernel))
      node_1727
      (invalid_excluded a [5,7,6,1,3,3] (by decide +kernel))
      node_1728
      (invalid_excluded a [5,7,6,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,3,7] (by decide +kernel))
      node_1729)

theorem node_1734 : Excluded a [5,7,6,1,8,0] :=
  predecessor_excluded a [5,7,6,1,8,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1735 : Excluded a [5,7,6,1,8,2] :=
  source_excluded a [5,7,6,1,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1736 : Excluded a [5,7,6,1,8,3] :=
  source_excluded a [5,7,6,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1738 : Excluded a [5,7,6,1,8,4,0] :=
  source_excluded a [5,7,6,1,8,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1740 : Excluded a [5,7,6,1,8,4,2,0] :=
  source_excluded a [5,7,6,1,8,4,2,0] 1 2 7 (by decide) (by decide +kernel)

theorem node_1741 : Excluded a [5,7,6,1,8,4,2,3] :=
  predecessor_excluded a [5,7,6,1,8,4,2,3] 0 3 6 7 (by decide) (by decide +kernel)

theorem node_1739 : Excluded a [5,7,6,1,8,4,2] :=
  branch_excluded a [5,7,6,1,8,4,2] (by decide)
    (fin9_cases _
      node_1740
      (invalid_excluded a [5,7,6,1,8,4,2,1] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,2,2] (by decide +kernel))
      node_1741
      (invalid_excluded a [5,7,6,1,8,4,2,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,2,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,2,8] (by decide +kernel)))

theorem node_1742 : Excluded a [5,7,6,1,8,4,3] :=
  source_excluded a [5,7,6,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1737 : Excluded a [5,7,6,1,8,4] :=
  branch_excluded a [5,7,6,1,8,4] (by decide)
    (fin9_cases _
      node_1738
      (invalid_excluded a [5,7,6,1,8,4,1] (by decide +kernel))
      node_1739
      node_1742
      (invalid_excluded a [5,7,6,1,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,4,8] (by decide +kernel)))

theorem node_1733 : Excluded a [5,7,6,1,8] :=
  branch_excluded a [5,7,6,1,8] (by decide)
    (fin9_cases _
      node_1734
      (invalid_excluded a [5,7,6,1,8,1] (by decide +kernel))
      node_1735
      node_1736
      node_1737
      (invalid_excluded a [5,7,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,8,8] (by decide +kernel)))

theorem node_1722 : Excluded a [5,7,6,1] :=
  branch_excluded a [5,7,6,1] (by decide)
    (fin9_cases _
      node_1723
      (invalid_excluded a [5,7,6,1,1] (by decide +kernel))
      node_1724
      node_1725
      (invalid_excluded a [5,7,6,1,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,1,7] (by decide +kernel))
      node_1733)

theorem node_1744 : Excluded a [5,7,6,2,0] :=
  source_excluded a [5,7,6,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1745 : Excluded a [5,7,6,2,1] :=
  source_excluded a [5,7,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1746 : Excluded a [5,7,6,2,3] :=
  predecessor_excluded a [5,7,6,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1748 : Excluded a [5,7,6,2,8,0] :=
  predecessor_excluded a [5,7,6,2,8,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1749 : Excluded a [5,7,6,2,8,1] :=
  source_excluded a [5,7,6,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1750 : Excluded a [5,7,6,2,8,3] :=
  source_excluded a [5,7,6,2,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1752 : Excluded a [5,7,6,2,8,4,0] :=
  source_excluded a [5,7,6,2,8,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1753 : Excluded a [5,7,6,2,8,4,1] :=
  source_excluded a [5,7,6,2,8,4,1] 6 0 1 (by decide) (by decide +kernel)

theorem node_1754 : Excluded a [5,7,6,2,8,4,3] :=
  source_excluded a [5,7,6,2,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1751 : Excluded a [5,7,6,2,8,4] :=
  branch_excluded a [5,7,6,2,8,4] (by decide)
    (fin9_cases _
      node_1752
      node_1753
      (invalid_excluded a [5,7,6,2,8,4,2] (by decide +kernel))
      node_1754
      (invalid_excluded a [5,7,6,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,4,8] (by decide +kernel)))

theorem node_1747 : Excluded a [5,7,6,2,8] :=
  branch_excluded a [5,7,6,2,8] (by decide)
    (fin9_cases _
      node_1748
      node_1749
      (invalid_excluded a [5,7,6,2,8,2] (by decide +kernel))
      node_1750
      node_1751
      (invalid_excluded a [5,7,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,8,8] (by decide +kernel)))

theorem node_1743 : Excluded a [5,7,6,2] :=
  branch_excluded a [5,7,6,2] (by decide)
    (fin9_cases _
      node_1744
      node_1745
      (invalid_excluded a [5,7,6,2,2] (by decide +kernel))
      node_1746
      (invalid_excluded a [5,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,2,7] (by decide +kernel))
      node_1747)

theorem node_1756 : Excluded a [5,7,6,8,0] :=
  source_excluded a [5,7,6,8,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1757 : Excluded a [5,7,6,8,1] :=
  source_excluded a [5,7,6,8,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1758 : Excluded a [5,7,6,8,2] :=
  predecessor_excluded a [5,7,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_1760 : Excluded a [5,7,6,8,3,0] :=
  predecessor_excluded a [5,7,6,8,3,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1761 : Excluded a [5,7,6,8,3,1] :=
  source_excluded a [5,7,6,8,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1762 : Excluded a [5,7,6,8,3,2] :=
  source_excluded a [5,7,6,8,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1763 : Excluded a [5,7,6,8,3,4] :=
  predecessor_excluded a [5,7,6,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1759 : Excluded a [5,7,6,8,3] :=
  branch_excluded a [5,7,6,8,3] (by decide)
    (fin9_cases _
      node_1760
      node_1761
      node_1762
      (invalid_excluded a [5,7,6,8,3,3] (by decide +kernel))
      node_1763
      (invalid_excluded a [5,7,6,8,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,3,8] (by decide +kernel)))

theorem node_1755 : Excluded a [5,7,6,8] :=
  branch_excluded a [5,7,6,8] (by decide)
    (fin9_cases _
      node_1756
      node_1757
      node_1758
      node_1759
      (invalid_excluded a [5,7,6,8,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,6,8,8] (by decide +kernel)))

theorem node_1720 : Excluded a [5,7,6] :=
  branch_excluded a [5,7,6] (by decide)
    (fin9_cases _
      node_1721
      node_1722
      node_1743
      (invalid_excluded a [5,7,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,6,7] (by decide +kernel))
      node_1755)

theorem node_1765 : Excluded a [5,7,8,0] :=
  predecessor_excluded a [5,7,8,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1767 : Excluded a [5,7,8,1,0] :=
  source_excluded a [5,7,8,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1769 : Excluded a [5,7,8,1,2,0] :=
  predecessor_excluded a [5,7,8,1,2,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1770 : Excluded a [5,7,8,1,2,3] :=
  predecessor_excluded a [5,7,8,1,2,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_1772 : Excluded a [5,7,8,1,2,4,0] :=
  source_excluded a [5,7,8,1,2,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1774 : Excluded a [5,7,8,1,2,4,3,0] :=
  source_excluded a [5,7,8,1,2,4,3,0] 1 2 7 (by decide) (by decide +kernel)

def b_1776 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 7
  | 2 => 8
  | 3 => 1
  | 4 => 2
  | 5 => 4
  | 6 => 3
  | 7 => 6
  | 8 => 0
  | _ => 0

def cert_1776 : LosingRegion (edgeOf a b_1776) 0 :=
  losingMask a b_1776 0 1212505728303381353595904
    (by decide +kernel) (by decide +kernel)

theorem node_1776 : Excluded a [5,7,8,1,2,4,3,6,0] :=
  losing_excluded a [5,7,8,1,2,4,3,6,0] (by decide) b_1776 (by decide +kernel) 4 0 2 cert_1776 (by change 4 ≠ 0 ∧ ¬ edgeOf a b_1776 4 0 ∧ 2 ≠ 4 ∧ maskRegion 1212505728303381353595904 4 2; decide +kernel)

theorem node_1775 : Excluded a [5,7,8,1,2,4,3,6] :=
  branch_excluded a [5,7,8,1,2,4,3,6] (by decide)
    (fin9_cases _
      node_1776
      (invalid_excluded a [5,7,8,1,2,4,3,6,1] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,3,6,2] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,3,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,3,6,8] (by decide +kernel)))

theorem node_1773 : Excluded a [5,7,8,1,2,4,3] :=
  branch_excluded a [5,7,8,1,2,4,3] (by decide)
    (fin9_cases _
      node_1774
      (invalid_excluded a [5,7,8,1,2,4,3,1] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,3,2] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,3,3] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,3,4] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,3,5] (by decide +kernel))
      node_1775
      (invalid_excluded a [5,7,8,1,2,4,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,3,8] (by decide +kernel)))

theorem node_1771 : Excluded a [5,7,8,1,2,4] :=
  branch_excluded a [5,7,8,1,2,4] (by decide)
    (fin9_cases _
      node_1772
      (invalid_excluded a [5,7,8,1,2,4,1] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,2] (by decide +kernel))
      node_1773
      (invalid_excluded a [5,7,8,1,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,4,8] (by decide +kernel)))

theorem node_1768 : Excluded a [5,7,8,1,2] :=
  branch_excluded a [5,7,8,1,2] (by decide)
    (fin9_cases _
      node_1769
      (invalid_excluded a [5,7,8,1,2,1] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,2] (by decide +kernel))
      node_1770
      node_1771
      (invalid_excluded a [5,7,8,1,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,2,8] (by decide +kernel)))

theorem node_1778 : Excluded a [5,7,8,1,3,0] :=
  predecessor_excluded a [5,7,8,1,3,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1780 : Excluded a [5,7,8,1,3,2,0] :=
  source_excluded a [5,7,8,1,3,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_1782 : Excluded a [5,7,8,1,3,2,4,0] :=
  source_excluded a [5,7,8,1,3,2,4,0] 1 2 7 (by decide) (by decide +kernel)

def b_1784 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 7
  | 2 => 8
  | 3 => 1
  | 4 => 3
  | 5 => 2
  | 6 => 4
  | 7 => 6
  | 8 => 0
  | _ => 0

def cert_1784 : LosingRegion (edgeOf a b_1784) 0 :=
  losingMask a b_1784 0 1212513257759214991836160
    (by decide +kernel) (by decide +kernel)

theorem node_1784 : Excluded a [5,7,8,1,3,2,4,6,0] :=
  losing_excluded a [5,7,8,1,3,2,4,6,0] (by decide) b_1784 (by decide +kernel) 2 0 8 cert_1784 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1784 2 0 ∧ 8 ≠ 2 ∧ maskRegion 1212513257759214991836160 2 8; decide +kernel)

theorem node_1783 : Excluded a [5,7,8,1,3,2,4,6] :=
  branch_excluded a [5,7,8,1,3,2,4,6] (by decide)
    (fin9_cases _
      node_1784
      (invalid_excluded a [5,7,8,1,3,2,4,6,1] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,4,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,4,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,4,6,8] (by decide +kernel)))

theorem node_1781 : Excluded a [5,7,8,1,3,2,4] :=
  branch_excluded a [5,7,8,1,3,2,4] (by decide)
    (fin9_cases _
      node_1782
      (invalid_excluded a [5,7,8,1,3,2,4,1] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,4,2] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,4,3] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,4,5] (by decide +kernel))
      node_1783
      (invalid_excluded a [5,7,8,1,3,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,4,8] (by decide +kernel)))

theorem node_1779 : Excluded a [5,7,8,1,3,2] :=
  branch_excluded a [5,7,8,1,3,2] (by decide)
    (fin9_cases _
      node_1780
      (invalid_excluded a [5,7,8,1,3,2,1] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,2] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,3] (by decide +kernel))
      node_1781
      (invalid_excluded a [5,7,8,1,3,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,2,8] (by decide +kernel)))

theorem node_1785 : Excluded a [5,7,8,1,3,4] :=
  predecessor_excluded a [5,7,8,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1777 : Excluded a [5,7,8,1,3] :=
  branch_excluded a [5,7,8,1,3] (by decide)
    (fin9_cases _
      node_1778
      (invalid_excluded a [5,7,8,1,3,1] (by decide +kernel))
      node_1779
      (invalid_excluded a [5,7,8,1,3,3] (by decide +kernel))
      node_1785
      (invalid_excluded a [5,7,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,3,8] (by decide +kernel)))

theorem node_1786 : Excluded a [5,7,8,1,6] :=
  source_excluded a [5,7,8,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1766 : Excluded a [5,7,8,1] :=
  branch_excluded a [5,7,8,1] (by decide)
    (fin9_cases _
      node_1767
      (invalid_excluded a [5,7,8,1,1] (by decide +kernel))
      node_1768
      node_1777
      (invalid_excluded a [5,7,8,1,4] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,5] (by decide +kernel))
      node_1786
      (invalid_excluded a [5,7,8,1,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,1,8] (by decide +kernel)))

theorem node_1787 : Excluded a [5,7,8,2] :=
  predecessor_excluded a [5,7,8,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_1789 : Excluded a [5,7,8,6,0] :=
  source_excluded a [5,7,8,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1790 : Excluded a [5,7,8,6,1] :=
  source_excluded a [5,7,8,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1792 : Excluded a [5,7,8,6,2,0] :=
  predecessor_excluded a [5,7,8,6,2,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1793 : Excluded a [5,7,8,6,2,1] :=
  source_excluded a [5,7,8,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1794 : Excluded a [5,7,8,6,2,3] :=
  source_excluded a [5,7,8,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1795 : Excluded a [5,7,8,6,2,4] :=
  source_excluded a [5,7,8,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1791 : Excluded a [5,7,8,6,2] :=
  branch_excluded a [5,7,8,6,2] (by decide)
    (fin9_cases _
      node_1792
      node_1793
      (invalid_excluded a [5,7,8,6,2,2] (by decide +kernel))
      node_1794
      node_1795
      (invalid_excluded a [5,7,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,2,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,2,8] (by decide +kernel)))

theorem node_1796 : Excluded a [5,7,8,6,3] :=
  predecessor_excluded a [5,7,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1788 : Excluded a [5,7,8,6] :=
  branch_excluded a [5,7,8,6] (by decide)
    (fin9_cases _
      node_1789
      node_1790
      node_1791
      node_1796
      (invalid_excluded a [5,7,8,6,4] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,6] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,6,8] (by decide +kernel)))

theorem node_1764 : Excluded a [5,7,8] :=
  branch_excluded a [5,7,8] (by decide)
    (fin9_cases _
      node_1765
      node_1766
      node_1787
      (invalid_excluded a [5,7,8,3] (by decide +kernel))
      (invalid_excluded a [5,7,8,4] (by decide +kernel))
      (invalid_excluded a [5,7,8,5] (by decide +kernel))
      node_1788
      (invalid_excluded a [5,7,8,7] (by decide +kernel))
      (invalid_excluded a [5,7,8,8] (by decide +kernel)))

theorem node_1622 : Excluded a [5,7] :=
  branch_excluded a [5,7] (by decide)
    (fin9_cases _
      node_1623
      node_1671
      (invalid_excluded a [5,7,2] (by decide +kernel))
      (invalid_excluded a [5,7,3] (by decide +kernel))
      node_1719
      (invalid_excluded a [5,7,5] (by decide +kernel))
      node_1720
      (invalid_excluded a [5,7,7] (by decide +kernel))
      node_1764)

theorem node_1799 : Excluded a [5,8,0,1] :=
  predecessor_excluded a [5,8,0,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_1801 : Excluded a [5,8,0,2,1] :=
  source_excluded a [5,8,0,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1802 : Excluded a [5,8,0,2,3] :=
  predecessor_excluded a [5,8,0,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1803 : Excluded a [5,8,0,2,6] :=
  source_excluded a [5,8,0,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1805 : Excluded a [5,8,0,2,7,1] :=
  source_excluded a [5,8,0,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1807 : Excluded a [5,8,0,2,7,3,1] :=
  predecessor_excluded a [5,8,0,2,7,3,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_1808 : Excluded a [5,8,0,2,7,3,4] :=
  source_excluded a [5,8,0,2,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1806 : Excluded a [5,8,0,2,7,3] :=
  branch_excluded a [5,8,0,2,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,0,2,7,3,0] (by decide +kernel))
      node_1807
      (invalid_excluded a [5,8,0,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [5,8,0,2,7,3,3] (by decide +kernel))
      node_1808
      (invalid_excluded a [5,8,0,2,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,0,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,8,0,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,8,0,2,7,3,8] (by decide +kernel)))

theorem node_1809 : Excluded a [5,8,0,2,7,4] :=
  predecessor_excluded a [5,8,0,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1804 : Excluded a [5,8,0,2,7] :=
  branch_excluded a [5,8,0,2,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,0,2,7,0] (by decide +kernel))
      node_1805
      (invalid_excluded a [5,8,0,2,7,2] (by decide +kernel))
      node_1806
      node_1809
      (invalid_excluded a [5,8,0,2,7,5] (by decide +kernel))
      (invalid_excluded a [5,8,0,2,7,6] (by decide +kernel))
      (invalid_excluded a [5,8,0,2,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,0,2,7,8] (by decide +kernel)))

theorem node_1800 : Excluded a [5,8,0,2] :=
  branch_excluded a [5,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,0,2,0] (by decide +kernel))
      node_1801
      (invalid_excluded a [5,8,0,2,2] (by decide +kernel))
      node_1802
      (invalid_excluded a [5,8,0,2,4] (by decide +kernel))
      (invalid_excluded a [5,8,0,2,5] (by decide +kernel))
      node_1803
      node_1804
      (invalid_excluded a [5,8,0,2,8] (by decide +kernel)))

theorem node_1811 : Excluded a [5,8,0,6,1] :=
  source_excluded a [5,8,0,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1813 : Excluded a [5,8,0,6,2,1] :=
  source_excluded a [5,8,0,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1814 : Excluded a [5,8,0,6,2,3] :=
  source_excluded a [5,8,0,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1815 : Excluded a [5,8,0,6,2,4] :=
  source_excluded a [5,8,0,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1816 : Excluded a [5,8,0,6,2,7] :=
  source_excluded a [5,8,0,6,2,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1812 : Excluded a [5,8,0,6,2] :=
  branch_excluded a [5,8,0,6,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,0,6,2,0] (by decide +kernel))
      node_1813
      (invalid_excluded a [5,8,0,6,2,2] (by decide +kernel))
      node_1814
      node_1815
      (invalid_excluded a [5,8,0,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,0,6,2,6] (by decide +kernel))
      node_1816
      (invalid_excluded a [5,8,0,6,2,8] (by decide +kernel)))

theorem node_1817 : Excluded a [5,8,0,6,3] :=
  predecessor_excluded a [5,8,0,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1818 : Excluded a [5,8,0,6,7] :=
  predecessor_excluded a [5,8,0,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_1810 : Excluded a [5,8,0,6] :=
  branch_excluded a [5,8,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,0,6,0] (by decide +kernel))
      node_1811
      node_1812
      node_1817
      (invalid_excluded a [5,8,0,6,4] (by decide +kernel))
      (invalid_excluded a [5,8,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,0,6,6] (by decide +kernel))
      node_1818
      (invalid_excluded a [5,8,0,6,8] (by decide +kernel)))

theorem node_1820 : Excluded a [5,8,0,7,1] :=
  source_excluded a [5,8,0,7,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1822 : Excluded a [5,8,0,7,2,1] :=
  source_excluded a [5,8,0,7,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1823 : Excluded a [5,8,0,7,2,3] :=
  predecessor_excluded a [5,8,0,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_1825 : Excluded a [5,8,0,7,2,4,1] :=
  predecessor_excluded a [5,8,0,7,2,4,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_1826 : Excluded a [5,8,0,7,2,4,3] :=
  source_excluded a [5,8,0,7,2,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1824 : Excluded a [5,8,0,7,2,4] :=
  branch_excluded a [5,8,0,7,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,0,7,2,4,0] (by decide +kernel))
      node_1825
      (invalid_excluded a [5,8,0,7,2,4,2] (by decide +kernel))
      node_1826
      (invalid_excluded a [5,8,0,7,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,8,0,7,2,4,5] (by decide +kernel))
      (invalid_excluded a [5,8,0,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [5,8,0,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,8,0,7,2,4,8] (by decide +kernel)))

theorem node_1821 : Excluded a [5,8,0,7,2] :=
  branch_excluded a [5,8,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,0,7,2,0] (by decide +kernel))
      node_1822
      (invalid_excluded a [5,8,0,7,2,2] (by decide +kernel))
      node_1823
      node_1824
      (invalid_excluded a [5,8,0,7,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [5,8,0,7,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,0,7,2,8] (by decide +kernel)))

theorem node_1828 : Excluded a [5,8,0,7,3,1] :=
  source_excluded a [5,8,0,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1830 : Excluded a [5,8,0,7,3,2,1] :=
  predecessor_excluded a [5,8,0,7,3,2,1] 0 8 6 1 (by decide) (by decide +kernel)

theorem node_1831 : Excluded a [5,8,0,7,3,2,4] :=
  source_excluded a [5,8,0,7,3,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1829 : Excluded a [5,8,0,7,3,2] :=
  branch_excluded a [5,8,0,7,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,0,7,3,2,0] (by decide +kernel))
      node_1830
      (invalid_excluded a [5,8,0,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [5,8,0,7,3,2,3] (by decide +kernel))
      node_1831
      (invalid_excluded a [5,8,0,7,3,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,0,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [5,8,0,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,0,7,3,2,8] (by decide +kernel)))

theorem node_1832 : Excluded a [5,8,0,7,3,4] :=
  predecessor_excluded a [5,8,0,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1827 : Excluded a [5,8,0,7,3] :=
  branch_excluded a [5,8,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,0,7,3,0] (by decide +kernel))
      node_1828
      node_1829
      (invalid_excluded a [5,8,0,7,3,3] (by decide +kernel))
      node_1832
      (invalid_excluded a [5,8,0,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,8,0,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,8,0,7,3,8] (by decide +kernel)))

theorem node_1833 : Excluded a [5,8,0,7,6] :=
  source_excluded a [5,8,0,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1819 : Excluded a [5,8,0,7] :=
  branch_excluded a [5,8,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,0,7,0] (by decide +kernel))
      node_1820
      node_1821
      node_1827
      (invalid_excluded a [5,8,0,7,4] (by decide +kernel))
      (invalid_excluded a [5,8,0,7,5] (by decide +kernel))
      node_1833
      (invalid_excluded a [5,8,0,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,0,7,8] (by decide +kernel)))

theorem node_1798 : Excluded a [5,8,0] :=
  branch_excluded a [5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,0,0] (by decide +kernel))
      node_1799
      node_1800
      (invalid_excluded a [5,8,0,3] (by decide +kernel))
      (invalid_excluded a [5,8,0,4] (by decide +kernel))
      (invalid_excluded a [5,8,0,5] (by decide +kernel))
      node_1810
      node_1819
      (invalid_excluded a [5,8,0,8] (by decide +kernel)))

theorem node_1835 : Excluded a [5,8,1,0] :=
  predecessor_excluded a [5,8,1,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1837 : Excluded a [5,8,1,2,0] :=
  source_excluded a [5,8,1,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1838 : Excluded a [5,8,1,2,3] :=
  predecessor_excluded a [5,8,1,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1839 : Excluded a [5,8,1,2,6] :=
  source_excluded a [5,8,1,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1841 : Excluded a [5,8,1,2,7,0] :=
  predecessor_excluded a [5,8,1,2,7,0] 2 0 0 5 (by decide) (by decide +kernel)

def b_1845 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 8
  | 2 => 1
  | 3 => 2
  | 4 => 7
  | 5 => 3
  | 6 => 0
  | 7 => 4
  | 8 => 6
  | _ => 0

def cert_1845 : LosingRegion (edgeOf a b_1845) 0 :=
  losingMask a b_1845 0 1515604105180790036104192
    (by decide +kernel) (by decide +kernel)

theorem node_1845 : Excluded a [5,8,1,2,7,3,0,4,6] :=
  losing_excluded a [5,8,1,2,7,3,0,4,6] (by decide) b_1845 (by decide +kernel) 2 0 0 cert_1845 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1845 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1515604105180790036104192 2 0; decide +kernel)

theorem node_1844 : Excluded a [5,8,1,2,7,3,0,4] :=
  branch_excluded a [5,8,1,2,7,3,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,1,2,7,3,0,4,0] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,3,0,4,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,3,0,4,2] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,3,0,4,3] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,3,0,4,4] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,3,0,4,5] (by decide +kernel))
      node_1845
      (invalid_excluded a [5,8,1,2,7,3,0,4,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,3,0,4,8] (by decide +kernel)))

theorem node_1846 : Excluded a [5,8,1,2,7,3,0,6] :=
  predecessor_excluded a [5,8,1,2,7,3,0,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_1843 : Excluded a [5,8,1,2,7,3,0] :=
  branch_excluded a [5,8,1,2,7,3,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,1,2,7,3,0,0] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,3,0,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,3,0,2] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,3,0,3] (by decide +kernel))
      node_1844
      (invalid_excluded a [5,8,1,2,7,3,0,5] (by decide +kernel))
      node_1846
      (invalid_excluded a [5,8,1,2,7,3,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,3,0,8] (by decide +kernel)))

theorem node_1847 : Excluded a [5,8,1,2,7,3,4] :=
  source_excluded a [5,8,1,2,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_1842 : Excluded a [5,8,1,2,7,3] :=
  branch_excluded a [5,8,1,2,7,3] (by decide)
    (fin9_cases _
      node_1843
      (invalid_excluded a [5,8,1,2,7,3,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,3,3] (by decide +kernel))
      node_1847
      (invalid_excluded a [5,8,1,2,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,3,8] (by decide +kernel)))

theorem node_1848 : Excluded a [5,8,1,2,7,4] :=
  predecessor_excluded a [5,8,1,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1840 : Excluded a [5,8,1,2,7] :=
  branch_excluded a [5,8,1,2,7] (by decide)
    (fin9_cases _
      node_1841
      (invalid_excluded a [5,8,1,2,7,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,2] (by decide +kernel))
      node_1842
      node_1848
      (invalid_excluded a [5,8,1,2,7,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,6] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,7,8] (by decide +kernel)))

theorem node_1836 : Excluded a [5,8,1,2] :=
  branch_excluded a [5,8,1,2] (by decide)
    (fin9_cases _
      node_1837
      (invalid_excluded a [5,8,1,2,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,2] (by decide +kernel))
      node_1838
      (invalid_excluded a [5,8,1,2,4] (by decide +kernel))
      (invalid_excluded a [5,8,1,2,5] (by decide +kernel))
      node_1839
      node_1840
      (invalid_excluded a [5,8,1,2,8] (by decide +kernel)))

theorem node_1850 : Excluded a [5,8,1,6,0] :=
  source_excluded a [5,8,1,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1852 : Excluded a [5,8,1,6,2,0] :=
  predecessor_excluded a [5,8,1,6,2,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1853 : Excluded a [5,8,1,6,2,3] :=
  source_excluded a [5,8,1,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1854 : Excluded a [5,8,1,6,2,4] :=
  source_excluded a [5,8,1,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1855 : Excluded a [5,8,1,6,2,7] :=
  source_excluded a [5,8,1,6,2,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1851 : Excluded a [5,8,1,6,2] :=
  branch_excluded a [5,8,1,6,2] (by decide)
    (fin9_cases _
      node_1852
      (invalid_excluded a [5,8,1,6,2,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,2,2] (by decide +kernel))
      node_1853
      node_1854
      (invalid_excluded a [5,8,1,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,2,6] (by decide +kernel))
      node_1855
      (invalid_excluded a [5,8,1,6,2,8] (by decide +kernel)))

theorem node_1856 : Excluded a [5,8,1,6,3] :=
  predecessor_excluded a [5,8,1,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1857 : Excluded a [5,8,1,6,7] :=
  predecessor_excluded a [5,8,1,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_1849 : Excluded a [5,8,1,6] :=
  branch_excluded a [5,8,1,6] (by decide)
    (fin9_cases _
      node_1850
      (invalid_excluded a [5,8,1,6,1] (by decide +kernel))
      node_1851
      node_1856
      (invalid_excluded a [5,8,1,6,4] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,6,6] (by decide +kernel))
      node_1857
      (invalid_excluded a [5,8,1,6,8] (by decide +kernel)))

theorem node_1859 : Excluded a [5,8,1,7,0] :=
  source_excluded a [5,8,1,7,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1861 : Excluded a [5,8,1,7,2,0] :=
  predecessor_excluded a [5,8,1,7,2,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1862 : Excluded a [5,8,1,7,2,3] :=
  predecessor_excluded a [5,8,1,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

def b_1866 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 8
  | 2 => 1
  | 3 => 7
  | 4 => 2
  | 5 => 4
  | 6 => 0
  | 7 => 3
  | 8 => 6
  | _ => 0

def cert_1866 : LosingRegion (edgeOf a b_1866) 0 :=
  losingMask a b_1866 0 1515604105169818542146560
    (by decide +kernel) (by decide +kernel)

theorem node_1866 : Excluded a [5,8,1,7,2,4,0,3,6] :=
  losing_excluded a [5,8,1,7,2,4,0,3,6] (by decide) b_1866 (by decide +kernel) 2 0 0 cert_1866 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_1866 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1515604105169818542146560 2 0; decide +kernel)

theorem node_1865 : Excluded a [5,8,1,7,2,4,0,3] :=
  branch_excluded a [5,8,1,7,2,4,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,1,7,2,4,0,3,0] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,3,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,3,2] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,3,3] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,3,4] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,3,5] (by decide +kernel))
      node_1866
      (invalid_excluded a [5,8,1,7,2,4,0,3,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,3,8] (by decide +kernel)))

theorem node_1868 : Excluded a [5,8,1,7,2,4,0,6,3] :=
  source_excluded a [5,8,1,7,2,4,0,6,3] 8 0 2 (by decide) (by decide +kernel)

theorem node_1867 : Excluded a [5,8,1,7,2,4,0,6] :=
  branch_excluded a [5,8,1,7,2,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,1,7,2,4,0,6,0] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,6,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,6,2] (by decide +kernel))
      node_1868
      (invalid_excluded a [5,8,1,7,2,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,6,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,6,8] (by decide +kernel)))

theorem node_1864 : Excluded a [5,8,1,7,2,4,0] :=
  branch_excluded a [5,8,1,7,2,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,1,7,2,4,0,0] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,2] (by decide +kernel))
      node_1865
      (invalid_excluded a [5,8,1,7,2,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,5] (by decide +kernel))
      node_1867
      (invalid_excluded a [5,8,1,7,2,4,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,0,8] (by decide +kernel)))

theorem node_1869 : Excluded a [5,8,1,7,2,4,3] :=
  source_excluded a [5,8,1,7,2,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1863 : Excluded a [5,8,1,7,2,4] :=
  branch_excluded a [5,8,1,7,2,4] (by decide)
    (fin9_cases _
      node_1864
      (invalid_excluded a [5,8,1,7,2,4,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,2] (by decide +kernel))
      node_1869
      (invalid_excluded a [5,8,1,7,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,4,8] (by decide +kernel)))

theorem node_1860 : Excluded a [5,8,1,7,2] :=
  branch_excluded a [5,8,1,7,2] (by decide)
    (fin9_cases _
      node_1861
      (invalid_excluded a [5,8,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,2] (by decide +kernel))
      node_1862
      node_1863
      (invalid_excluded a [5,8,1,7,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,2,8] (by decide +kernel)))

theorem node_1871 : Excluded a [5,8,1,7,3,0] :=
  predecessor_excluded a [5,8,1,7,3,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1874 : Excluded a [5,8,1,7,3,2,0,4] :=
  source_excluded a [5,8,1,7,3,2,0,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_1876 : Excluded a [5,8,1,7,3,2,0,6,4] :=
  predecessor_excluded a [5,8,1,7,3,2,0,6,4] 0 3 8 4 (by decide) (by decide +kernel)

theorem node_1875 : Excluded a [5,8,1,7,3,2,0,6] :=
  branch_excluded a [5,8,1,7,3,2,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,1,7,3,2,0,6,0] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,2,0,6,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,2,0,6,2] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,2,0,6,3] (by decide +kernel))
      node_1876
      (invalid_excluded a [5,8,1,7,3,2,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,2,0,6,6] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,2,0,6,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,2,0,6,8] (by decide +kernel)))

theorem node_1873 : Excluded a [5,8,1,7,3,2,0] :=
  branch_excluded a [5,8,1,7,3,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,1,7,3,2,0,0] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,2,0,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,2,0,2] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,2,0,3] (by decide +kernel))
      node_1874
      (invalid_excluded a [5,8,1,7,3,2,0,5] (by decide +kernel))
      node_1875
      (invalid_excluded a [5,8,1,7,3,2,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,2,0,8] (by decide +kernel)))

theorem node_1877 : Excluded a [5,8,1,7,3,2,4] :=
  source_excluded a [5,8,1,7,3,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1872 : Excluded a [5,8,1,7,3,2] :=
  branch_excluded a [5,8,1,7,3,2] (by decide)
    (fin9_cases _
      node_1873
      (invalid_excluded a [5,8,1,7,3,2,1] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,2,3] (by decide +kernel))
      node_1877
      (invalid_excluded a [5,8,1,7,3,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,2,8] (by decide +kernel)))

theorem node_1878 : Excluded a [5,8,1,7,3,4] :=
  predecessor_excluded a [5,8,1,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1870 : Excluded a [5,8,1,7,3] :=
  branch_excluded a [5,8,1,7,3] (by decide)
    (fin9_cases _
      node_1871
      (invalid_excluded a [5,8,1,7,3,1] (by decide +kernel))
      node_1872
      (invalid_excluded a [5,8,1,7,3,3] (by decide +kernel))
      node_1878
      (invalid_excluded a [5,8,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,3,8] (by decide +kernel)))

theorem node_1879 : Excluded a [5,8,1,7,6] :=
  source_excluded a [5,8,1,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1858 : Excluded a [5,8,1,7] :=
  branch_excluded a [5,8,1,7] (by decide)
    (fin9_cases _
      node_1859
      (invalid_excluded a [5,8,1,7,1] (by decide +kernel))
      node_1860
      node_1870
      (invalid_excluded a [5,8,1,7,4] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,5] (by decide +kernel))
      node_1879
      (invalid_excluded a [5,8,1,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,1,7,8] (by decide +kernel)))

theorem node_1834 : Excluded a [5,8,1] :=
  branch_excluded a [5,8,1] (by decide)
    (fin9_cases _
      node_1835
      (invalid_excluded a [5,8,1,1] (by decide +kernel))
      node_1836
      (invalid_excluded a [5,8,1,3] (by decide +kernel))
      (invalid_excluded a [5,8,1,4] (by decide +kernel))
      (invalid_excluded a [5,8,1,5] (by decide +kernel))
      node_1849
      node_1858
      (invalid_excluded a [5,8,1,8] (by decide +kernel)))

theorem node_1880 : Excluded a [5,8,4] :=
  source_excluded a [5,8,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_1882 : Excluded a [5,8,6,0] :=
  predecessor_excluded a [5,8,6,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1884 : Excluded a [5,8,6,1,0] :=
  source_excluded a [5,8,6,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1885 : Excluded a [5,8,6,1,2] :=
  predecessor_excluded a [5,8,6,1,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_1887 : Excluded a [5,8,6,1,3,0] :=
  predecessor_excluded a [5,8,6,1,3,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1888 : Excluded a [5,8,6,1,3,2] :=
  source_excluded a [5,8,6,1,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1889 : Excluded a [5,8,6,1,3,4] :=
  predecessor_excluded a [5,8,6,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1890 : Excluded a [5,8,6,1,3,7] :=
  source_excluded a [5,8,6,1,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1886 : Excluded a [5,8,6,1,3] :=
  branch_excluded a [5,8,6,1,3] (by decide)
    (fin9_cases _
      node_1887
      (invalid_excluded a [5,8,6,1,3,1] (by decide +kernel))
      node_1888
      (invalid_excluded a [5,8,6,1,3,3] (by decide +kernel))
      node_1889
      (invalid_excluded a [5,8,6,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,3,6] (by decide +kernel))
      node_1890
      (invalid_excluded a [5,8,6,1,3,8] (by decide +kernel)))

theorem node_1892 : Excluded a [5,8,6,1,7,0] :=
  predecessor_excluded a [5,8,6,1,7,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1893 : Excluded a [5,8,6,1,7,2] :=
  source_excluded a [5,8,6,1,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_1894 : Excluded a [5,8,6,1,7,3] :=
  source_excluded a [5,8,6,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1895 : Excluded a [5,8,6,1,7,4] :=
  predecessor_excluded a [5,8,6,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1891 : Excluded a [5,8,6,1,7] :=
  branch_excluded a [5,8,6,1,7] (by decide)
    (fin9_cases _
      node_1892
      (invalid_excluded a [5,8,6,1,7,1] (by decide +kernel))
      node_1893
      node_1894
      node_1895
      (invalid_excluded a [5,8,6,1,7,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,7,8] (by decide +kernel)))

theorem node_1883 : Excluded a [5,8,6,1] :=
  branch_excluded a [5,8,6,1] (by decide)
    (fin9_cases _
      node_1884
      (invalid_excluded a [5,8,6,1,1] (by decide +kernel))
      node_1885
      node_1886
      (invalid_excluded a [5,8,6,1,4] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,1,6] (by decide +kernel))
      node_1891
      (invalid_excluded a [5,8,6,1,8] (by decide +kernel)))

theorem node_1897 : Excluded a [5,8,6,2,0] :=
  source_excluded a [5,8,6,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1898 : Excluded a [5,8,6,2,1] :=
  source_excluded a [5,8,6,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1899 : Excluded a [5,8,6,2,3] :=
  predecessor_excluded a [5,8,6,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1901 : Excluded a [5,8,6,2,7,0] :=
  predecessor_excluded a [5,8,6,2,7,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1902 : Excluded a [5,8,6,2,7,1] :=
  source_excluded a [5,8,6,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1903 : Excluded a [5,8,6,2,7,3] :=
  source_excluded a [5,8,6,2,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1904 : Excluded a [5,8,6,2,7,4] :=
  predecessor_excluded a [5,8,6,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1900 : Excluded a [5,8,6,2,7] :=
  branch_excluded a [5,8,6,2,7] (by decide)
    (fin9_cases _
      node_1901
      node_1902
      (invalid_excluded a [5,8,6,2,7,2] (by decide +kernel))
      node_1903
      node_1904
      (invalid_excluded a [5,8,6,2,7,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,7,6] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,7,8] (by decide +kernel)))

theorem node_1896 : Excluded a [5,8,6,2] :=
  branch_excluded a [5,8,6,2] (by decide)
    (fin9_cases _
      node_1897
      node_1898
      (invalid_excluded a [5,8,6,2,2] (by decide +kernel))
      node_1899
      (invalid_excluded a [5,8,6,2,4] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,2,6] (by decide +kernel))
      node_1900
      (invalid_excluded a [5,8,6,2,8] (by decide +kernel)))

theorem node_1905 : Excluded a [5,8,6,7] :=
  predecessor_excluded a [5,8,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_1881 : Excluded a [5,8,6] :=
  branch_excluded a [5,8,6] (by decide)
    (fin9_cases _
      node_1882
      node_1883
      node_1896
      (invalid_excluded a [5,8,6,3] (by decide +kernel))
      (invalid_excluded a [5,8,6,4] (by decide +kernel))
      (invalid_excluded a [5,8,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,6,6] (by decide +kernel))
      node_1905
      (invalid_excluded a [5,8,6,8] (by decide +kernel)))

theorem node_1907 : Excluded a [5,8,7,0] :=
  predecessor_excluded a [5,8,7,0] 1 5 3 0 (by decide) (by decide +kernel)

theorem node_1909 : Excluded a [5,8,7,1,0] :=
  source_excluded a [5,8,7,1,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1911 : Excluded a [5,8,7,1,2,0] :=
  predecessor_excluded a [5,8,7,1,2,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1912 : Excluded a [5,8,7,1,2,3] :=
  predecessor_excluded a [5,8,7,1,2,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_1915 : Excluded a [5,8,7,1,2,4,0,3] :=
  source_excluded a [5,8,7,1,2,4,0,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_1917 : Excluded a [5,8,7,1,2,4,0,6,3] :=
  source_excluded a [5,8,7,1,2,4,0,6,3] 8 0 2 (by decide) (by decide +kernel)

theorem node_1916 : Excluded a [5,8,7,1,2,4,0,6] :=
  branch_excluded a [5,8,7,1,2,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,7,1,2,4,0,6,0] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,4,0,6,1] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,4,0,6,2] (by decide +kernel))
      node_1917
      (invalid_excluded a [5,8,7,1,2,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,4,0,6,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,4,0,6,8] (by decide +kernel)))

theorem node_1914 : Excluded a [5,8,7,1,2,4,0] :=
  branch_excluded a [5,8,7,1,2,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,8,7,1,2,4,0,0] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,4,0,1] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,4,0,2] (by decide +kernel))
      node_1915
      (invalid_excluded a [5,8,7,1,2,4,0,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,4,0,5] (by decide +kernel))
      node_1916
      (invalid_excluded a [5,8,7,1,2,4,0,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,4,0,8] (by decide +kernel)))

theorem node_1918 : Excluded a [5,8,7,1,2,4,3] :=
  source_excluded a [5,8,7,1,2,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_1913 : Excluded a [5,8,7,1,2,4] :=
  branch_excluded a [5,8,7,1,2,4] (by decide)
    (fin9_cases _
      node_1914
      (invalid_excluded a [5,8,7,1,2,4,1] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,4,2] (by decide +kernel))
      node_1918
      (invalid_excluded a [5,8,7,1,2,4,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,4,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,4,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,4,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,4,8] (by decide +kernel)))

theorem node_1910 : Excluded a [5,8,7,1,2] :=
  branch_excluded a [5,8,7,1,2] (by decide)
    (fin9_cases _
      node_1911
      (invalid_excluded a [5,8,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,2] (by decide +kernel))
      node_1912
      node_1913
      (invalid_excluded a [5,8,7,1,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,2,8] (by decide +kernel)))

theorem node_1920 : Excluded a [5,8,7,1,3,0] :=
  predecessor_excluded a [5,8,7,1,3,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1921 : Excluded a [5,8,7,1,3,2] :=
  predecessor_excluded a [5,8,7,1,3,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_1922 : Excluded a [5,8,7,1,3,4] :=
  predecessor_excluded a [5,8,7,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_1919 : Excluded a [5,8,7,1,3] :=
  branch_excluded a [5,8,7,1,3] (by decide)
    (fin9_cases _
      node_1920
      (invalid_excluded a [5,8,7,1,3,1] (by decide +kernel))
      node_1921
      (invalid_excluded a [5,8,7,1,3,3] (by decide +kernel))
      node_1922
      (invalid_excluded a [5,8,7,1,3,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,3,8] (by decide +kernel)))

theorem node_1923 : Excluded a [5,8,7,1,6] :=
  source_excluded a [5,8,7,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1908 : Excluded a [5,8,7,1] :=
  branch_excluded a [5,8,7,1] (by decide)
    (fin9_cases _
      node_1909
      (invalid_excluded a [5,8,7,1,1] (by decide +kernel))
      node_1910
      node_1919
      (invalid_excluded a [5,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,5] (by decide +kernel))
      node_1923
      (invalid_excluded a [5,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,1,8] (by decide +kernel)))

theorem node_1925 : Excluded a [5,8,7,2,0] :=
  source_excluded a [5,8,7,2,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1926 : Excluded a [5,8,7,2,1] :=
  source_excluded a [5,8,7,2,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1927 : Excluded a [5,8,7,2,3] :=
  predecessor_excluded a [5,8,7,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_1928 : Excluded a [5,8,7,2,6] :=
  source_excluded a [5,8,7,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_1924 : Excluded a [5,8,7,2] :=
  branch_excluded a [5,8,7,2] (by decide)
    (fin9_cases _
      node_1925
      node_1926
      (invalid_excluded a [5,8,7,2,2] (by decide +kernel))
      node_1927
      (invalid_excluded a [5,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,5] (by decide +kernel))
      node_1928
      (invalid_excluded a [5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,2,8] (by decide +kernel)))

theorem node_1930 : Excluded a [5,8,7,6,0] :=
  source_excluded a [5,8,7,6,0] 4 1 0 (by decide) (by decide +kernel)

theorem node_1931 : Excluded a [5,8,7,6,1] :=
  source_excluded a [5,8,7,6,1] 0 2 4 (by decide) (by decide +kernel)

theorem node_1933 : Excluded a [5,8,7,6,2,0] :=
  predecessor_excluded a [5,8,7,6,2,0] 2 0 0 5 (by decide) (by decide +kernel)

theorem node_1934 : Excluded a [5,8,7,6,2,1] :=
  source_excluded a [5,8,7,6,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1935 : Excluded a [5,8,7,6,2,3] :=
  source_excluded a [5,8,7,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_1936 : Excluded a [5,8,7,6,2,4] :=
  source_excluded a [5,8,7,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_1932 : Excluded a [5,8,7,6,2] :=
  branch_excluded a [5,8,7,6,2] (by decide)
    (fin9_cases _
      node_1933
      node_1934
      (invalid_excluded a [5,8,7,6,2,2] (by decide +kernel))
      node_1935
      node_1936
      (invalid_excluded a [5,8,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,2,8] (by decide +kernel)))

theorem node_1937 : Excluded a [5,8,7,6,3] :=
  predecessor_excluded a [5,8,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_1929 : Excluded a [5,8,7,6] :=
  branch_excluded a [5,8,7,6] (by decide)
    (fin9_cases _
      node_1930
      node_1931
      node_1932
      node_1937
      (invalid_excluded a [5,8,7,6,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,5] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,6] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,6,8] (by decide +kernel)))

theorem node_1906 : Excluded a [5,8,7] :=
  branch_excluded a [5,8,7] (by decide)
    (fin9_cases _
      node_1907
      node_1908
      node_1924
      (invalid_excluded a [5,8,7,3] (by decide +kernel))
      (invalid_excluded a [5,8,7,4] (by decide +kernel))
      (invalid_excluded a [5,8,7,5] (by decide +kernel))
      node_1929
      (invalid_excluded a [5,8,7,7] (by decide +kernel))
      (invalid_excluded a [5,8,7,8] (by decide +kernel)))

theorem node_1797 : Excluded a [5,8] :=
  branch_excluded a [5,8] (by decide)
    (fin9_cases _
      node_1798
      node_1834
      (invalid_excluded a [5,8,2] (by decide +kernel))
      (invalid_excluded a [5,8,3] (by decide +kernel))
      node_1880
      (invalid_excluded a [5,8,5] (by decide +kernel))
      node_1881
      node_1906
      (invalid_excluded a [5,8,8] (by decide +kernel)))

theorem node_1400 : Excluded a [5] :=
  branch_excluded a [5] (by decide)
    (fin9_cases _
      (invalid_excluded a [5,0] (by decide +kernel))
      (invalid_excluded a [5,1] (by decide +kernel))
      node_1401
      node_1517
      node_1620
      (invalid_excluded a [5,5] (by decide +kernel))
      node_1621
      node_1622
      node_1797)

theorem node_1940 : Excluded a [6,2,0] :=
  source_excluded a [6,2,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_1941 : Excluded a [6,2,1] :=
  predecessor_excluded a [6,2,1] 3 1 1 2 (by decide) (by decide +kernel)

theorem node_1942 : Excluded a [6,2,4] :=
  source_excluded a [6,2,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_1945 : Excluded a [6,2,5,0,1] :=
  predecessor_excluded a [6,2,5,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1946 : Excluded a [6,2,5,0,3] :=
  source_excluded a [6,2,5,0,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_1948 : Excluded a [6,2,5,0,7,1] :=
  source_excluded a [6,2,5,0,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1949 : Excluded a [6,2,5,0,7,3] :=
  source_excluded a [6,2,5,0,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1950 : Excluded a [6,2,5,0,7,4] :=
  predecessor_excluded a [6,2,5,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1951 : Excluded a [6,2,5,0,7,8] :=
  predecessor_excluded a [6,2,5,0,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_1947 : Excluded a [6,2,5,0,7] :=
  branch_excluded a [6,2,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,5,0,7,0] (by decide +kernel))
      node_1948
      (invalid_excluded a [6,2,5,0,7,2] (by decide +kernel))
      node_1949
      node_1950
      (invalid_excluded a [6,2,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,7,7] (by decide +kernel))
      node_1951)

theorem node_1953 : Excluded a [6,2,5,0,8,1] :=
  source_excluded a [6,2,5,0,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1954 : Excluded a [6,2,5,0,8,3] :=
  source_excluded a [6,2,5,0,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1955 : Excluded a [6,2,5,0,8,4] :=
  predecessor_excluded a [6,2,5,0,8,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_1956 : Excluded a [6,2,5,0,8,7] :=
  source_excluded a [6,2,5,0,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1952 : Excluded a [6,2,5,0,8] :=
  branch_excluded a [6,2,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,5,0,8,0] (by decide +kernel))
      node_1953
      (invalid_excluded a [6,2,5,0,8,2] (by decide +kernel))
      node_1954
      node_1955
      (invalid_excluded a [6,2,5,0,8,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,8,6] (by decide +kernel))
      node_1956
      (invalid_excluded a [6,2,5,0,8,8] (by decide +kernel)))

theorem node_1944 : Excluded a [6,2,5,0] :=
  branch_excluded a [6,2,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,5,0,0] (by decide +kernel))
      node_1945
      (invalid_excluded a [6,2,5,0,2] (by decide +kernel))
      node_1946
      (invalid_excluded a [6,2,5,0,4] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,0,6] (by decide +kernel))
      node_1947
      node_1952)

theorem node_1958 : Excluded a [6,2,5,1,0] :=
  predecessor_excluded a [6,2,5,1,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1959 : Excluded a [6,2,5,1,3] :=
  source_excluded a [6,2,5,1,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_1961 : Excluded a [6,2,5,1,7,0] :=
  source_excluded a [6,2,5,1,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1962 : Excluded a [6,2,5,1,7,3] :=
  source_excluded a [6,2,5,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1963 : Excluded a [6,2,5,1,7,4] :=
  predecessor_excluded a [6,2,5,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1964 : Excluded a [6,2,5,1,7,8] :=
  predecessor_excluded a [6,2,5,1,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_1960 : Excluded a [6,2,5,1,7] :=
  branch_excluded a [6,2,5,1,7] (by decide)
    (fin9_cases _
      node_1961
      (invalid_excluded a [6,2,5,1,7,1] (by decide +kernel))
      (invalid_excluded a [6,2,5,1,7,2] (by decide +kernel))
      node_1962
      node_1963
      (invalid_excluded a [6,2,5,1,7,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,2,5,1,7,7] (by decide +kernel))
      node_1964)

theorem node_1966 : Excluded a [6,2,5,1,8,0] :=
  source_excluded a [6,2,5,1,8,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1967 : Excluded a [6,2,5,1,8,3] :=
  source_excluded a [6,2,5,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1968 : Excluded a [6,2,5,1,8,4] :=
  predecessor_excluded a [6,2,5,1,8,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_1969 : Excluded a [6,2,5,1,8,7] :=
  source_excluded a [6,2,5,1,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1965 : Excluded a [6,2,5,1,8] :=
  branch_excluded a [6,2,5,1,8] (by decide)
    (fin9_cases _
      node_1966
      (invalid_excluded a [6,2,5,1,8,1] (by decide +kernel))
      (invalid_excluded a [6,2,5,1,8,2] (by decide +kernel))
      node_1967
      node_1968
      (invalid_excluded a [6,2,5,1,8,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,1,8,6] (by decide +kernel))
      node_1969
      (invalid_excluded a [6,2,5,1,8,8] (by decide +kernel)))

theorem node_1957 : Excluded a [6,2,5,1] :=
  branch_excluded a [6,2,5,1] (by decide)
    (fin9_cases _
      node_1958
      (invalid_excluded a [6,2,5,1,1] (by decide +kernel))
      (invalid_excluded a [6,2,5,1,2] (by decide +kernel))
      node_1959
      (invalid_excluded a [6,2,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,2,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,1,6] (by decide +kernel))
      node_1960
      node_1965)

theorem node_1971 : Excluded a [6,2,5,7,0] :=
  predecessor_excluded a [6,2,5,7,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1973 : Excluded a [6,2,5,7,1,0] :=
  source_excluded a [6,2,5,7,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1974 : Excluded a [6,2,5,7,1,3] :=
  source_excluded a [6,2,5,7,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1975 : Excluded a [6,2,5,7,1,4] :=
  predecessor_excluded a [6,2,5,7,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_1977 : Excluded a [6,2,5,7,1,8,0] :=
  predecessor_excluded a [6,2,5,7,1,8,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_1978 : Excluded a [6,2,5,7,1,8,3] :=
  source_excluded a [6,2,5,7,1,8,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_1979 : Excluded a [6,2,5,7,1,8,4] :=
  source_excluded a [6,2,5,7,1,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_1976 : Excluded a [6,2,5,7,1,8] :=
  branch_excluded a [6,2,5,7,1,8] (by decide)
    (fin9_cases _
      node_1977
      (invalid_excluded a [6,2,5,7,1,8,1] (by decide +kernel))
      (invalid_excluded a [6,2,5,7,1,8,2] (by decide +kernel))
      node_1978
      node_1979
      (invalid_excluded a [6,2,5,7,1,8,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [6,2,5,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [6,2,5,7,1,8,8] (by decide +kernel)))

theorem node_1972 : Excluded a [6,2,5,7,1] :=
  branch_excluded a [6,2,5,7,1] (by decide)
    (fin9_cases _
      node_1973
      (invalid_excluded a [6,2,5,7,1,1] (by decide +kernel))
      (invalid_excluded a [6,2,5,7,1,2] (by decide +kernel))
      node_1974
      node_1975
      (invalid_excluded a [6,2,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,2,5,7,1,7] (by decide +kernel))
      node_1976)

theorem node_1980 : Excluded a [6,2,5,7,3] :=
  source_excluded a [6,2,5,7,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_1981 : Excluded a [6,2,5,7,8] :=
  predecessor_excluded a [6,2,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_1970 : Excluded a [6,2,5,7] :=
  branch_excluded a [6,2,5,7] (by decide)
    (fin9_cases _
      node_1971
      node_1972
      (invalid_excluded a [6,2,5,7,2] (by decide +kernel))
      node_1980
      (invalid_excluded a [6,2,5,7,4] (by decide +kernel))
      (invalid_excluded a [6,2,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,2,5,7,7] (by decide +kernel))
      node_1981)

theorem node_1983 : Excluded a [6,2,5,8,0] :=
  predecessor_excluded a [6,2,5,8,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_1985 : Excluded a [6,2,5,8,1,0] :=
  source_excluded a [6,2,5,8,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1986 : Excluded a [6,2,5,8,1,3] :=
  source_excluded a [6,2,5,8,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1987 : Excluded a [6,2,5,8,1,4] :=
  predecessor_excluded a [6,2,5,8,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_1988 : Excluded a [6,2,5,8,1,7] :=
  source_excluded a [6,2,5,8,1,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_1984 : Excluded a [6,2,5,8,1] :=
  branch_excluded a [6,2,5,8,1] (by decide)
    (fin9_cases _
      node_1985
      (invalid_excluded a [6,2,5,8,1,1] (by decide +kernel))
      (invalid_excluded a [6,2,5,8,1,2] (by decide +kernel))
      node_1986
      node_1987
      (invalid_excluded a [6,2,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,8,1,6] (by decide +kernel))
      node_1988
      (invalid_excluded a [6,2,5,8,1,8] (by decide +kernel)))

theorem node_1989 : Excluded a [6,2,5,8,3] :=
  source_excluded a [6,2,5,8,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_1991 : Excluded a [6,2,5,8,7,0] :=
  source_excluded a [6,2,5,8,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_1992 : Excluded a [6,2,5,8,7,1] :=
  source_excluded a [6,2,5,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_1993 : Excluded a [6,2,5,8,7,3] :=
  source_excluded a [6,2,5,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_1994 : Excluded a [6,2,5,8,7,4] :=
  predecessor_excluded a [6,2,5,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_1990 : Excluded a [6,2,5,8,7] :=
  branch_excluded a [6,2,5,8,7] (by decide)
    (fin9_cases _
      node_1991
      node_1992
      (invalid_excluded a [6,2,5,8,7,2] (by decide +kernel))
      node_1993
      node_1994
      (invalid_excluded a [6,2,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,2,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,2,5,8,7,8] (by decide +kernel)))

theorem node_1982 : Excluded a [6,2,5,8] :=
  branch_excluded a [6,2,5,8] (by decide)
    (fin9_cases _
      node_1983
      node_1984
      (invalid_excluded a [6,2,5,8,2] (by decide +kernel))
      node_1989
      (invalid_excluded a [6,2,5,8,4] (by decide +kernel))
      (invalid_excluded a [6,2,5,8,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,8,6] (by decide +kernel))
      node_1990
      (invalid_excluded a [6,2,5,8,8] (by decide +kernel)))

theorem node_1943 : Excluded a [6,2,5] :=
  branch_excluded a [6,2,5] (by decide)
    (fin9_cases _
      node_1944
      node_1957
      (invalid_excluded a [6,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,2,5,3] (by decide +kernel))
      (invalid_excluded a [6,2,5,4] (by decide +kernel))
      (invalid_excluded a [6,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,2,5,6] (by decide +kernel))
      node_1970
      node_1982)

theorem node_1997 : Excluded a [6,2,7,0,1] :=
  predecessor_excluded a [6,2,7,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_1999 : Excluded a [6,2,7,0,3,1] :=
  source_excluded a [6,2,7,0,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2000 : Excluded a [6,2,7,0,3,4] :=
  predecessor_excluded a [6,2,7,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2002 : Excluded a [6,2,7,0,3,8,1] :=
  source_excluded a [6,2,7,0,3,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2004 : Excluded a [6,2,7,0,3,8,4,1] :=
  predecessor_excluded a [6,2,7,0,3,8,4,1] 0 2 7 1 (by decide) (by decide +kernel)

theorem node_2005 : Excluded a [6,2,7,0,3,8,4,5] :=
  source_excluded a [6,2,7,0,3,8,4,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_2003 : Excluded a [6,2,7,0,3,8,4] :=
  branch_excluded a [6,2,7,0,3,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,3,8,4,0] (by decide +kernel))
      node_2004
      (invalid_excluded a [6,2,7,0,3,8,4,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,3,8,4,4] (by decide +kernel))
      node_2005
      (invalid_excluded a [6,2,7,0,3,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,3,8,4,8] (by decide +kernel)))

theorem node_2006 : Excluded a [6,2,7,0,3,8,5] :=
  predecessor_excluded a [6,2,7,0,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_2001 : Excluded a [6,2,7,0,3,8] :=
  branch_excluded a [6,2,7,0,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,3,8,0] (by decide +kernel))
      node_2002
      (invalid_excluded a [6,2,7,0,3,8,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,3,8,3] (by decide +kernel))
      node_2003
      node_2006
      (invalid_excluded a [6,2,7,0,3,8,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,3,8,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,3,8,8] (by decide +kernel)))

theorem node_1998 : Excluded a [6,2,7,0,3] :=
  branch_excluded a [6,2,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,3,0] (by decide +kernel))
      node_1999
      (invalid_excluded a [6,2,7,0,3,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,3,3] (by decide +kernel))
      node_2000
      (invalid_excluded a [6,2,7,0,3,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,3,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,3,7] (by decide +kernel))
      node_2001)

theorem node_2008 : Excluded a [6,2,7,0,8,1] :=
  source_excluded a [6,2,7,0,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2010 : Excluded a [6,2,7,0,8,3,1] :=
  source_excluded a [6,2,7,0,8,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2011 : Excluded a [6,2,7,0,8,3,4] :=
  predecessor_excluded a [6,2,7,0,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_2013 : Excluded a [6,2,7,0,8,3,5,1] :=
  predecessor_excluded a [6,2,7,0,8,3,5,1] 0 2 7 1 (by decide) (by decide +kernel)

theorem node_2014 : Excluded a [6,2,7,0,8,3,5,4] :=
  source_excluded a [6,2,7,0,8,3,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_2012 : Excluded a [6,2,7,0,8,3,5] :=
  branch_excluded a [6,2,7,0,8,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,8,3,5,0] (by decide +kernel))
      node_2013
      (invalid_excluded a [6,2,7,0,8,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,5,3] (by decide +kernel))
      node_2014
      (invalid_excluded a [6,2,7,0,8,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,5,8] (by decide +kernel)))

theorem node_2009 : Excluded a [6,2,7,0,8,3] :=
  branch_excluded a [6,2,7,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,8,3,0] (by decide +kernel))
      node_2010
      (invalid_excluded a [6,2,7,0,8,3,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,3] (by decide +kernel))
      node_2011
      node_2012
      (invalid_excluded a [6,2,7,0,8,3,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,3,8] (by decide +kernel)))

theorem node_2016 : Excluded a [6,2,7,0,8,4,1] :=
  source_excluded a [6,2,7,0,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2017 : Excluded a [6,2,7,0,8,4,3] :=
  source_excluded a [6,2,7,0,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2018 : Excluded a [6,2,7,0,8,4,5] :=
  predecessor_excluded a [6,2,7,0,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2015 : Excluded a [6,2,7,0,8,4] :=
  branch_excluded a [6,2,7,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,8,4,0] (by decide +kernel))
      node_2016
      (invalid_excluded a [6,2,7,0,8,4,2] (by decide +kernel))
      node_2017
      (invalid_excluded a [6,2,7,0,8,4,4] (by decide +kernel))
      node_2018
      (invalid_excluded a [6,2,7,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,4,8] (by decide +kernel)))

theorem node_2007 : Excluded a [6,2,7,0,8] :=
  branch_excluded a [6,2,7,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,8,0] (by decide +kernel))
      node_2008
      (invalid_excluded a [6,2,7,0,8,2] (by decide +kernel))
      node_2009
      node_2015
      (invalid_excluded a [6,2,7,0,8,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,8,8] (by decide +kernel)))

theorem node_1996 : Excluded a [6,2,7,0] :=
  branch_excluded a [6,2,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,0,0] (by decide +kernel))
      node_1997
      (invalid_excluded a [6,2,7,0,2] (by decide +kernel))
      node_1998
      (invalid_excluded a [6,2,7,0,4] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,0,7] (by decide +kernel))
      node_2007)

theorem node_2020 : Excluded a [6,2,7,1,0] :=
  predecessor_excluded a [6,2,7,1,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_2022 : Excluded a [6,2,7,1,3,0] :=
  source_excluded a [6,2,7,1,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2023 : Excluded a [6,2,7,1,3,4] :=
  predecessor_excluded a [6,2,7,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2025 : Excluded a [6,2,7,1,3,8,0] :=
  predecessor_excluded a [6,2,7,1,3,8,0] 2 0 0 6 (by decide) (by decide +kernel)

def b_2028 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 2
  | 2 => 7
  | 3 => 1
  | 4 => 3
  | 5 => 8
  | 6 => 4
  | 7 => 0
  | 8 => 5
  | _ => 0

def cert_2028 : LosingRegion (edgeOf a b_2028) 0 :=
  losingMask a b_2028 0 2145138522811361311851520
    (by decide +kernel) (by decide +kernel)

theorem node_2028 : Excluded a [6,2,7,1,3,8,4,0,5] :=
  losing_excluded a [6,2,7,1,3,8,4,0,5] (by decide) b_2028 (by decide +kernel) 2 0 7 cert_2028 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2028 2 0 ∧ 7 ≠ 2 ∧ maskRegion 2145138522811361311851520 2 7; decide +kernel)

theorem node_2027 : Excluded a [6,2,7,1,3,8,4,0] :=
  branch_excluded a [6,2,7,1,3,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,1,3,8,4,0,0] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,8,4,0,1] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,8,4,0,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,8,4,0,3] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,8,4,0,4] (by decide +kernel))
      node_2028
      (invalid_excluded a [6,2,7,1,3,8,4,0,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,8,4,0,8] (by decide +kernel)))

theorem node_2029 : Excluded a [6,2,7,1,3,8,4,5] :=
  source_excluded a [6,2,7,1,3,8,4,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_2026 : Excluded a [6,2,7,1,3,8,4] :=
  branch_excluded a [6,2,7,1,3,8,4] (by decide)
    (fin9_cases _
      node_2027
      (invalid_excluded a [6,2,7,1,3,8,4,1] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,8,4,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,8,4,3] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,8,4,4] (by decide +kernel))
      node_2029
      (invalid_excluded a [6,2,7,1,3,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,8,4,8] (by decide +kernel)))

theorem node_2030 : Excluded a [6,2,7,1,3,8,5] :=
  predecessor_excluded a [6,2,7,1,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_2024 : Excluded a [6,2,7,1,3,8] :=
  branch_excluded a [6,2,7,1,3,8] (by decide)
    (fin9_cases _
      node_2025
      (invalid_excluded a [6,2,7,1,3,8,1] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,8,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,8,3] (by decide +kernel))
      node_2026
      node_2030
      (invalid_excluded a [6,2,7,1,3,8,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,8,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,8,8] (by decide +kernel)))

theorem node_2021 : Excluded a [6,2,7,1,3] :=
  branch_excluded a [6,2,7,1,3] (by decide)
    (fin9_cases _
      node_2022
      (invalid_excluded a [6,2,7,1,3,1] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,3] (by decide +kernel))
      node_2023
      (invalid_excluded a [6,2,7,1,3,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,3,7] (by decide +kernel))
      node_2024)

theorem node_2032 : Excluded a [6,2,7,1,8,0] :=
  source_excluded a [6,2,7,1,8,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2034 : Excluded a [6,2,7,1,8,3,0] :=
  predecessor_excluded a [6,2,7,1,8,3,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2035 : Excluded a [6,2,7,1,8,3,4] :=
  predecessor_excluded a [6,2,7,1,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

def b_2038 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 2
  | 2 => 7
  | 3 => 1
  | 4 => 8
  | 5 => 3
  | 6 => 5
  | 7 => 0
  | 8 => 4
  | _ => 0

def cert_2038 : LosingRegion (edgeOf a b_2038) 0 :=
  losingMask a b_2038 0 2145138511576551499236352
    (by decide +kernel) (by decide +kernel)

theorem node_2038 : Excluded a [6,2,7,1,8,3,5,0,4] :=
  losing_excluded a [6,2,7,1,8,3,5,0,4] (by decide) b_2038 (by decide +kernel) 2 0 7 cert_2038 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2038 2 0 ∧ 7 ≠ 2 ∧ maskRegion 2145138511576551499236352 2 7; decide +kernel)

theorem node_2037 : Excluded a [6,2,7,1,8,3,5,0] :=
  branch_excluded a [6,2,7,1,8,3,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,7,1,8,3,5,0,0] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,3,5,0,1] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,3,5,0,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,3,5,0,3] (by decide +kernel))
      node_2038
      (invalid_excluded a [6,2,7,1,8,3,5,0,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,3,5,0,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,3,5,0,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,3,5,0,8] (by decide +kernel)))

theorem node_2039 : Excluded a [6,2,7,1,8,3,5,4] :=
  source_excluded a [6,2,7,1,8,3,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_2036 : Excluded a [6,2,7,1,8,3,5] :=
  branch_excluded a [6,2,7,1,8,3,5] (by decide)
    (fin9_cases _
      node_2037
      (invalid_excluded a [6,2,7,1,8,3,5,1] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,3,5,3] (by decide +kernel))
      node_2039
      (invalid_excluded a [6,2,7,1,8,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,3,5,8] (by decide +kernel)))

theorem node_2033 : Excluded a [6,2,7,1,8,3] :=
  branch_excluded a [6,2,7,1,8,3] (by decide)
    (fin9_cases _
      node_2034
      (invalid_excluded a [6,2,7,1,8,3,1] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,3,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,3,3] (by decide +kernel))
      node_2035
      node_2036
      (invalid_excluded a [6,2,7,1,8,3,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,3,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,3,8] (by decide +kernel)))

theorem node_2041 : Excluded a [6,2,7,1,8,4,0] :=
  predecessor_excluded a [6,2,7,1,8,4,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2042 : Excluded a [6,2,7,1,8,4,3] :=
  source_excluded a [6,2,7,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2043 : Excluded a [6,2,7,1,8,4,5] :=
  predecessor_excluded a [6,2,7,1,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2040 : Excluded a [6,2,7,1,8,4] :=
  branch_excluded a [6,2,7,1,8,4] (by decide)
    (fin9_cases _
      node_2041
      (invalid_excluded a [6,2,7,1,8,4,1] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,4,2] (by decide +kernel))
      node_2042
      (invalid_excluded a [6,2,7,1,8,4,4] (by decide +kernel))
      node_2043
      (invalid_excluded a [6,2,7,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,4,8] (by decide +kernel)))

theorem node_2031 : Excluded a [6,2,7,1,8] :=
  branch_excluded a [6,2,7,1,8] (by decide)
    (fin9_cases _
      node_2032
      (invalid_excluded a [6,2,7,1,8,1] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,2] (by decide +kernel))
      node_2033
      node_2040
      (invalid_excluded a [6,2,7,1,8,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,8,8] (by decide +kernel)))

theorem node_2019 : Excluded a [6,2,7,1] :=
  branch_excluded a [6,2,7,1] (by decide)
    (fin9_cases _
      node_2020
      (invalid_excluded a [6,2,7,1,1] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,2] (by decide +kernel))
      node_2021
      (invalid_excluded a [6,2,7,1,4] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,1,7] (by decide +kernel))
      node_2031)

theorem node_2044 : Excluded a [6,2,7,5] :=
  source_excluded a [6,2,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2045 : Excluded a [6,2,7,8] :=
  predecessor_excluded a [6,2,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_1995 : Excluded a [6,2,7] :=
  branch_excluded a [6,2,7] (by decide)
    (fin9_cases _
      node_1996
      node_2019
      (invalid_excluded a [6,2,7,2] (by decide +kernel))
      (invalid_excluded a [6,2,7,3] (by decide +kernel))
      (invalid_excluded a [6,2,7,4] (by decide +kernel))
      node_2044
      (invalid_excluded a [6,2,7,6] (by decide +kernel))
      (invalid_excluded a [6,2,7,7] (by decide +kernel))
      node_2045)

theorem node_2048 : Excluded a [6,2,8,0,1] :=
  predecessor_excluded a [6,2,8,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2050 : Excluded a [6,2,8,0,3,1] :=
  source_excluded a [6,2,8,0,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2051 : Excluded a [6,2,8,0,3,4] :=
  predecessor_excluded a [6,2,8,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2052 : Excluded a [6,2,8,0,3,7] :=
  source_excluded a [6,2,8,0,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2049 : Excluded a [6,2,8,0,3] :=
  branch_excluded a [6,2,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,8,0,3,0] (by decide +kernel))
      node_2050
      (invalid_excluded a [6,2,8,0,3,2] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,3,3] (by decide +kernel))
      node_2051
      (invalid_excluded a [6,2,8,0,3,5] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,3,6] (by decide +kernel))
      node_2052
      (invalid_excluded a [6,2,8,0,3,8] (by decide +kernel)))

theorem node_2054 : Excluded a [6,2,8,0,7,1] :=
  source_excluded a [6,2,8,0,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2056 : Excluded a [6,2,8,0,7,3,1] :=
  source_excluded a [6,2,8,0,7,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2057 : Excluded a [6,2,8,0,7,3,4] :=
  source_excluded a [6,2,8,0,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2058 : Excluded a [6,2,8,0,7,3,5] :=
  source_excluded a [6,2,8,0,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_2055 : Excluded a [6,2,8,0,7,3] :=
  branch_excluded a [6,2,8,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,8,0,7,3,0] (by decide +kernel))
      node_2056
      (invalid_excluded a [6,2,8,0,7,3,2] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,7,3,3] (by decide +kernel))
      node_2057
      node_2058
      (invalid_excluded a [6,2,8,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,7,3,8] (by decide +kernel)))

theorem node_2059 : Excluded a [6,2,8,0,7,4] :=
  predecessor_excluded a [6,2,8,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2053 : Excluded a [6,2,8,0,7] :=
  branch_excluded a [6,2,8,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,8,0,7,0] (by decide +kernel))
      node_2054
      (invalid_excluded a [6,2,8,0,7,2] (by decide +kernel))
      node_2055
      node_2059
      (invalid_excluded a [6,2,8,0,7,5] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,7,7] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,7,8] (by decide +kernel)))

theorem node_2047 : Excluded a [6,2,8,0] :=
  branch_excluded a [6,2,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,2,8,0,0] (by decide +kernel))
      node_2048
      (invalid_excluded a [6,2,8,0,2] (by decide +kernel))
      node_2049
      (invalid_excluded a [6,2,8,0,4] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,5] (by decide +kernel))
      (invalid_excluded a [6,2,8,0,6] (by decide +kernel))
      node_2053
      (invalid_excluded a [6,2,8,0,8] (by decide +kernel)))

theorem node_2061 : Excluded a [6,2,8,1,0] :=
  predecessor_excluded a [6,2,8,1,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_2063 : Excluded a [6,2,8,1,3,0] :=
  source_excluded a [6,2,8,1,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2064 : Excluded a [6,2,8,1,3,4] :=
  predecessor_excluded a [6,2,8,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2065 : Excluded a [6,2,8,1,3,7] :=
  source_excluded a [6,2,8,1,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2062 : Excluded a [6,2,8,1,3] :=
  branch_excluded a [6,2,8,1,3] (by decide)
    (fin9_cases _
      node_2063
      (invalid_excluded a [6,2,8,1,3,1] (by decide +kernel))
      (invalid_excluded a [6,2,8,1,3,2] (by decide +kernel))
      (invalid_excluded a [6,2,8,1,3,3] (by decide +kernel))
      node_2064
      (invalid_excluded a [6,2,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [6,2,8,1,3,6] (by decide +kernel))
      node_2065
      (invalid_excluded a [6,2,8,1,3,8] (by decide +kernel)))

theorem node_2067 : Excluded a [6,2,8,1,7,0] :=
  source_excluded a [6,2,8,1,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2069 : Excluded a [6,2,8,1,7,3,0] :=
  predecessor_excluded a [6,2,8,1,7,3,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2070 : Excluded a [6,2,8,1,7,3,4] :=
  source_excluded a [6,2,8,1,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2071 : Excluded a [6,2,8,1,7,3,5] :=
  source_excluded a [6,2,8,1,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_2068 : Excluded a [6,2,8,1,7,3] :=
  branch_excluded a [6,2,8,1,7,3] (by decide)
    (fin9_cases _
      node_2069
      (invalid_excluded a [6,2,8,1,7,3,1] (by decide +kernel))
      (invalid_excluded a [6,2,8,1,7,3,2] (by decide +kernel))
      (invalid_excluded a [6,2,8,1,7,3,3] (by decide +kernel))
      node_2070
      node_2071
      (invalid_excluded a [6,2,8,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,2,8,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,2,8,1,7,3,8] (by decide +kernel)))

theorem node_2072 : Excluded a [6,2,8,1,7,4] :=
  predecessor_excluded a [6,2,8,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2066 : Excluded a [6,2,8,1,7] :=
  branch_excluded a [6,2,8,1,7] (by decide)
    (fin9_cases _
      node_2067
      (invalid_excluded a [6,2,8,1,7,1] (by decide +kernel))
      (invalid_excluded a [6,2,8,1,7,2] (by decide +kernel))
      node_2068
      node_2072
      (invalid_excluded a [6,2,8,1,7,5] (by decide +kernel))
      (invalid_excluded a [6,2,8,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,2,8,1,7,7] (by decide +kernel))
      (invalid_excluded a [6,2,8,1,7,8] (by decide +kernel)))

theorem node_2060 : Excluded a [6,2,8,1] :=
  branch_excluded a [6,2,8,1] (by decide)
    (fin9_cases _
      node_2061
      (invalid_excluded a [6,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [6,2,8,1,2] (by decide +kernel))
      node_2062
      (invalid_excluded a [6,2,8,1,4] (by decide +kernel))
      (invalid_excluded a [6,2,8,1,5] (by decide +kernel))
      (invalid_excluded a [6,2,8,1,6] (by decide +kernel))
      node_2066
      (invalid_excluded a [6,2,8,1,8] (by decide +kernel)))

theorem node_2073 : Excluded a [6,2,8,5] :=
  source_excluded a [6,2,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2075 : Excluded a [6,2,8,7,0] :=
  predecessor_excluded a [6,2,8,7,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_2077 : Excluded a [6,2,8,7,1,0] :=
  source_excluded a [6,2,8,7,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2078 : Excluded a [6,2,8,7,1,3] :=
  predecessor_excluded a [6,2,8,7,1,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_2080 : Excluded a [6,2,8,7,1,4,0] :=
  predecessor_excluded a [6,2,8,7,1,4,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2081 : Excluded a [6,2,8,7,1,4,3] :=
  source_excluded a [6,2,8,7,1,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2082 : Excluded a [6,2,8,7,1,4,5] :=
  predecessor_excluded a [6,2,8,7,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2079 : Excluded a [6,2,8,7,1,4] :=
  branch_excluded a [6,2,8,7,1,4] (by decide)
    (fin9_cases _
      node_2080
      (invalid_excluded a [6,2,8,7,1,4,1] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,1,4,2] (by decide +kernel))
      node_2081
      (invalid_excluded a [6,2,8,7,1,4,4] (by decide +kernel))
      node_2082
      (invalid_excluded a [6,2,8,7,1,4,6] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,1,4,7] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,1,4,8] (by decide +kernel)))

theorem node_2076 : Excluded a [6,2,8,7,1] :=
  branch_excluded a [6,2,8,7,1] (by decide)
    (fin9_cases _
      node_2077
      (invalid_excluded a [6,2,8,7,1,1] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,1,2] (by decide +kernel))
      node_2078
      node_2079
      (invalid_excluded a [6,2,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,1,8] (by decide +kernel)))

theorem node_2084 : Excluded a [6,2,8,7,3,0] :=
  source_excluded a [6,2,8,7,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2085 : Excluded a [6,2,8,7,3,1] :=
  source_excluded a [6,2,8,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2086 : Excluded a [6,2,8,7,3,4] :=
  predecessor_excluded a [6,2,8,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2083 : Excluded a [6,2,8,7,3] :=
  branch_excluded a [6,2,8,7,3] (by decide)
    (fin9_cases _
      node_2084
      node_2085
      (invalid_excluded a [6,2,8,7,3,2] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,3,3] (by decide +kernel))
      node_2086
      (invalid_excluded a [6,2,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,3,8] (by decide +kernel)))

theorem node_2074 : Excluded a [6,2,8,7] :=
  branch_excluded a [6,2,8,7] (by decide)
    (fin9_cases _
      node_2075
      node_2076
      (invalid_excluded a [6,2,8,7,2] (by decide +kernel))
      node_2083
      (invalid_excluded a [6,2,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,2,8,7,8] (by decide +kernel)))

theorem node_2046 : Excluded a [6,2,8] :=
  branch_excluded a [6,2,8] (by decide)
    (fin9_cases _
      node_2047
      node_2060
      (invalid_excluded a [6,2,8,2] (by decide +kernel))
      (invalid_excluded a [6,2,8,3] (by decide +kernel))
      (invalid_excluded a [6,2,8,4] (by decide +kernel))
      node_2073
      (invalid_excluded a [6,2,8,6] (by decide +kernel))
      node_2074
      (invalid_excluded a [6,2,8,8] (by decide +kernel)))

theorem node_1939 : Excluded a [6,2] :=
  branch_excluded a [6,2] (by decide)
    (fin9_cases _
      node_1940
      node_1941
      (invalid_excluded a [6,2,2] (by decide +kernel))
      (invalid_excluded a [6,2,3] (by decide +kernel))
      node_1942
      node_1943
      (invalid_excluded a [6,2,6] (by decide +kernel))
      node_1995
      node_2046)

theorem node_2088 : Excluded a [6,3,0] :=
  source_excluded a [6,3,0] 1 2 2 (by decide) (by decide +kernel)

theorem node_2089 : Excluded a [6,3,1] :=
  source_excluded a [6,3,1] 2 0 1 (by decide) (by decide +kernel)

theorem node_2090 : Excluded a [6,3,4] :=
  source_excluded a [6,3,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_2092 : Excluded a [6,3,5,0] :=
  source_excluded a [6,3,5,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2093 : Excluded a [6,3,5,1] :=
  predecessor_excluded a [6,3,5,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_2094 : Excluded a [6,3,5,2] :=
  predecessor_excluded a [6,3,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_2096 : Excluded a [6,3,5,7,0] :=
  predecessor_excluded a [6,3,5,7,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_2098 : Excluded a [6,3,5,7,1,0] :=
  source_excluded a [6,3,5,7,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2100 : Excluded a [6,3,5,7,1,2,0] :=
  predecessor_excluded a [6,3,5,7,1,2,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2101 : Excluded a [6,3,5,7,1,2,4] :=
  source_excluded a [6,3,5,7,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2102 : Excluded a [6,3,5,7,1,2,8] :=
  source_excluded a [6,3,5,7,1,2,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_2099 : Excluded a [6,3,5,7,1,2] :=
  branch_excluded a [6,3,5,7,1,2] (by decide)
    (fin9_cases _
      node_2100
      (invalid_excluded a [6,3,5,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,1,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,1,2,3] (by decide +kernel))
      node_2101
      (invalid_excluded a [6,3,5,7,1,2,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,1,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,1,2,7] (by decide +kernel))
      node_2102)

theorem node_2103 : Excluded a [6,3,5,7,1,4] :=
  predecessor_excluded a [6,3,5,7,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2105 : Excluded a [6,3,5,7,1,8,0] :=
  predecessor_excluded a [6,3,5,7,1,8,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2106 : Excluded a [6,3,5,7,1,8,2] :=
  predecessor_excluded a [6,3,5,7,1,8,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2107 : Excluded a [6,3,5,7,1,8,4] :=
  source_excluded a [6,3,5,7,1,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2104 : Excluded a [6,3,5,7,1,8] :=
  branch_excluded a [6,3,5,7,1,8] (by decide)
    (fin9_cases _
      node_2105
      (invalid_excluded a [6,3,5,7,1,8,1] (by decide +kernel))
      node_2106
      (invalid_excluded a [6,3,5,7,1,8,3] (by decide +kernel))
      node_2107
      (invalid_excluded a [6,3,5,7,1,8,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,1,8,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,1,8,7] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,1,8,8] (by decide +kernel)))

theorem node_2097 : Excluded a [6,3,5,7,1] :=
  branch_excluded a [6,3,5,7,1] (by decide)
    (fin9_cases _
      node_2098
      (invalid_excluded a [6,3,5,7,1,1] (by decide +kernel))
      node_2099
      (invalid_excluded a [6,3,5,7,1,3] (by decide +kernel))
      node_2103
      (invalid_excluded a [6,3,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,1,7] (by decide +kernel))
      node_2104)

theorem node_2108 : Excluded a [6,3,5,7,2] :=
  source_excluded a [6,3,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2109 : Excluded a [6,3,5,7,8] :=
  predecessor_excluded a [6,3,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_2095 : Excluded a [6,3,5,7] :=
  branch_excluded a [6,3,5,7] (by decide)
    (fin9_cases _
      node_2096
      node_2097
      node_2108
      (invalid_excluded a [6,3,5,7,3] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,4] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,7,7] (by decide +kernel))
      node_2109)

theorem node_2111 : Excluded a [6,3,5,8,0] :=
  predecessor_excluded a [6,3,5,8,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_2113 : Excluded a [6,3,5,8,1,0] :=
  source_excluded a [6,3,5,8,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2115 : Excluded a [6,3,5,8,1,2,0] :=
  predecessor_excluded a [6,3,5,8,1,2,0] 2 0 0 6 (by decide) (by decide +kernel)

def b_2118 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 3
  | 2 => 5
  | 3 => 8
  | 4 => 1
  | 5 => 2
  | 6 => 4
  | 7 => 0
  | 8 => 7
  | _ => 0

def cert_2118 : LosingRegion (edgeOf a b_2118) 0 :=
  losingMask a b_2118 0 2116804251635848039891968
    (by decide +kernel) (by decide +kernel)

theorem node_2118 : Excluded a [6,3,5,8,1,2,4,0,7] :=
  losing_excluded a [6,3,5,8,1,2,4,0,7] (by decide) b_2118 (by decide +kernel) 2 0 0 cert_2118 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2118 2 0 ∧ 0 ≠ 2 ∧ maskRegion 2116804251635848039891968 2 0; decide +kernel)

theorem node_2117 : Excluded a [6,3,5,8,1,2,4,0] :=
  branch_excluded a [6,3,5,8,1,2,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,5,8,1,2,4,0,0] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,4,0,1] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,4,0,2] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,4,0,3] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,4,0,4] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,4,0,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,4,0,6] (by decide +kernel))
      node_2118
      (invalid_excluded a [6,3,5,8,1,2,4,0,8] (by decide +kernel)))

theorem node_2116 : Excluded a [6,3,5,8,1,2,4] :=
  branch_excluded a [6,3,5,8,1,2,4] (by decide)
    (fin9_cases _
      node_2117
      (invalid_excluded a [6,3,5,8,1,2,4,1] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,4,2] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,4,3] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,4,4] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,4,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,4,8] (by decide +kernel)))

theorem node_2114 : Excluded a [6,3,5,8,1,2] :=
  branch_excluded a [6,3,5,8,1,2] (by decide)
    (fin9_cases _
      node_2115
      (invalid_excluded a [6,3,5,8,1,2,1] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,3] (by decide +kernel))
      node_2116
      (invalid_excluded a [6,3,5,8,1,2,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,7] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,2,8] (by decide +kernel)))

theorem node_2119 : Excluded a [6,3,5,8,1,4] :=
  predecessor_excluded a [6,3,5,8,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2120 : Excluded a [6,3,5,8,1,7] :=
  source_excluded a [6,3,5,8,1,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2112 : Excluded a [6,3,5,8,1] :=
  branch_excluded a [6,3,5,8,1] (by decide)
    (fin9_cases _
      node_2113
      (invalid_excluded a [6,3,5,8,1,1] (by decide +kernel))
      node_2114
      (invalid_excluded a [6,3,5,8,1,3] (by decide +kernel))
      node_2119
      (invalid_excluded a [6,3,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,1,6] (by decide +kernel))
      node_2120
      (invalid_excluded a [6,3,5,8,1,8] (by decide +kernel)))

theorem node_2121 : Excluded a [6,3,5,8,2] :=
  source_excluded a [6,3,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2123 : Excluded a [6,3,5,8,7,0] :=
  source_excluded a [6,3,5,8,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2124 : Excluded a [6,3,5,8,7,1] :=
  source_excluded a [6,3,5,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2126 : Excluded a [6,3,5,8,7,2,0] :=
  predecessor_excluded a [6,3,5,8,7,2,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2127 : Excluded a [6,3,5,8,7,2,1] :=
  source_excluded a [6,3,5,8,7,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2128 : Excluded a [6,3,5,8,7,2,4] :=
  source_excluded a [6,3,5,8,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2125 : Excluded a [6,3,5,8,7,2] :=
  branch_excluded a [6,3,5,8,7,2] (by decide)
    (fin9_cases _
      node_2126
      node_2127
      (invalid_excluded a [6,3,5,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,2,3] (by decide +kernel))
      node_2128
      (invalid_excluded a [6,3,5,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,2,8] (by decide +kernel)))

theorem node_2129 : Excluded a [6,3,5,8,7,4] :=
  predecessor_excluded a [6,3,5,8,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2122 : Excluded a [6,3,5,8,7] :=
  branch_excluded a [6,3,5,8,7] (by decide)
    (fin9_cases _
      node_2123
      node_2124
      node_2125
      (invalid_excluded a [6,3,5,8,7,3] (by decide +kernel))
      node_2129
      (invalid_excluded a [6,3,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,7,8] (by decide +kernel)))

theorem node_2110 : Excluded a [6,3,5,8] :=
  branch_excluded a [6,3,5,8] (by decide)
    (fin9_cases _
      node_2111
      node_2112
      node_2121
      (invalid_excluded a [6,3,5,8,3] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,4] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,8,6] (by decide +kernel))
      node_2122
      (invalid_excluded a [6,3,5,8,8] (by decide +kernel)))

theorem node_2091 : Excluded a [6,3,5] :=
  branch_excluded a [6,3,5] (by decide)
    (fin9_cases _
      node_2092
      node_2093
      node_2094
      (invalid_excluded a [6,3,5,3] (by decide +kernel))
      (invalid_excluded a [6,3,5,4] (by decide +kernel))
      (invalid_excluded a [6,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,3,5,6] (by decide +kernel))
      node_2095
      node_2110)

theorem node_2131 : Excluded a [6,3,7,0] :=
  source_excluded a [6,3,7,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2132 : Excluded a [6,3,7,1] :=
  predecessor_excluded a [6,3,7,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_2134 : Excluded a [6,3,7,2,0] :=
  predecessor_excluded a [6,3,7,2,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_2136 : Excluded a [6,3,7,2,1,0] :=
  source_excluded a [6,3,7,2,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2138 : Excluded a [6,3,7,2,1,4,0] :=
  predecessor_excluded a [6,3,7,2,1,4,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2139 : Excluded a [6,3,7,2,1,4,5] :=
  predecessor_excluded a [6,3,7,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2140 : Excluded a [6,3,7,2,1,4,8] :=
  source_excluded a [6,3,7,2,1,4,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_2137 : Excluded a [6,3,7,2,1,4] :=
  branch_excluded a [6,3,7,2,1,4] (by decide)
    (fin9_cases _
      node_2138
      (invalid_excluded a [6,3,7,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,4,2] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,4,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,4,4] (by decide +kernel))
      node_2139
      (invalid_excluded a [6,3,7,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,4,7] (by decide +kernel))
      node_2140)

theorem node_2142 : Excluded a [6,3,7,2,1,8,0] :=
  predecessor_excluded a [6,3,7,2,1,8,0] 2 0 0 6 (by decide) (by decide +kernel)

def b_2145 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 3
  | 2 => 7
  | 3 => 2
  | 4 => 1
  | 5 => 8
  | 6 => 4
  | 7 => 0
  | 8 => 5
  | _ => 0

def cert_2145 : LosingRegion (edgeOf a b_2145) 0 :=
  losingMask a b_2145 0 2329310734498520229741568
    (by decide +kernel) (by decide +kernel)

theorem node_2145 : Excluded a [6,3,7,2,1,8,4,0,5] :=
  losing_excluded a [6,3,7,2,1,8,4,0,5] (by decide) b_2145 (by decide +kernel) 2 0 6 cert_2145 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2145 2 0 ∧ 6 ≠ 2 ∧ maskRegion 2329310734498520229741568 2 6; decide +kernel)

theorem node_2144 : Excluded a [6,3,7,2,1,8,4,0] :=
  branch_excluded a [6,3,7,2,1,8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,7,2,1,8,4,0,0] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,8,4,0,1] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,8,4,0,2] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,8,4,0,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,8,4,0,4] (by decide +kernel))
      node_2145
      (invalid_excluded a [6,3,7,2,1,8,4,0,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,8,4,0,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,8,4,0,8] (by decide +kernel)))

theorem node_2146 : Excluded a [6,3,7,2,1,8,4,5] :=
  source_excluded a [6,3,7,2,1,8,4,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_2143 : Excluded a [6,3,7,2,1,8,4] :=
  branch_excluded a [6,3,7,2,1,8,4] (by decide)
    (fin9_cases _
      node_2144
      (invalid_excluded a [6,3,7,2,1,8,4,1] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,8,4,2] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,8,4,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,8,4,4] (by decide +kernel))
      node_2146
      (invalid_excluded a [6,3,7,2,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,8,4,8] (by decide +kernel)))

theorem node_2147 : Excluded a [6,3,7,2,1,8,5] :=
  predecessor_excluded a [6,3,7,2,1,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_2141 : Excluded a [6,3,7,2,1,8] :=
  branch_excluded a [6,3,7,2,1,8] (by decide)
    (fin9_cases _
      node_2142
      (invalid_excluded a [6,3,7,2,1,8,1] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,8,2] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,8,3] (by decide +kernel))
      node_2143
      node_2147
      (invalid_excluded a [6,3,7,2,1,8,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,8,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,8,8] (by decide +kernel)))

theorem node_2135 : Excluded a [6,3,7,2,1] :=
  branch_excluded a [6,3,7,2,1] (by decide)
    (fin9_cases _
      node_2136
      (invalid_excluded a [6,3,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,2] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,3] (by decide +kernel))
      node_2137
      (invalid_excluded a [6,3,7,2,1,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,1,7] (by decide +kernel))
      node_2141)

theorem node_2149 : Excluded a [6,3,7,2,8,0] :=
  source_excluded a [6,3,7,2,8,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2150 : Excluded a [6,3,7,2,8,1] :=
  source_excluded a [6,3,7,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2152 : Excluded a [6,3,7,2,8,4,0] :=
  predecessor_excluded a [6,3,7,2,8,4,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2153 : Excluded a [6,3,7,2,8,4,1] :=
  source_excluded a [6,3,7,2,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2154 : Excluded a [6,3,7,2,8,4,5] :=
  predecessor_excluded a [6,3,7,2,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2151 : Excluded a [6,3,7,2,8,4] :=
  branch_excluded a [6,3,7,2,8,4] (by decide)
    (fin9_cases _
      node_2152
      node_2153
      (invalid_excluded a [6,3,7,2,8,4,2] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,8,4,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,8,4,4] (by decide +kernel))
      node_2154
      (invalid_excluded a [6,3,7,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,8,4,8] (by decide +kernel)))

theorem node_2148 : Excluded a [6,3,7,2,8] :=
  branch_excluded a [6,3,7,2,8] (by decide)
    (fin9_cases _
      node_2149
      node_2150
      (invalid_excluded a [6,3,7,2,8,2] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,8,3] (by decide +kernel))
      node_2151
      (invalid_excluded a [6,3,7,2,8,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,8,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,8,7] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,8,8] (by decide +kernel)))

theorem node_2133 : Excluded a [6,3,7,2] :=
  branch_excluded a [6,3,7,2] (by decide)
    (fin9_cases _
      node_2134
      node_2135
      (invalid_excluded a [6,3,7,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,4] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,2,7] (by decide +kernel))
      node_2148)

theorem node_2155 : Excluded a [6,3,7,5] :=
  source_excluded a [6,3,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2156 : Excluded a [6,3,7,8] :=
  predecessor_excluded a [6,3,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_2130 : Excluded a [6,3,7] :=
  branch_excluded a [6,3,7] (by decide)
    (fin9_cases _
      node_2131
      node_2132
      node_2133
      (invalid_excluded a [6,3,7,3] (by decide +kernel))
      (invalid_excluded a [6,3,7,4] (by decide +kernel))
      node_2155
      (invalid_excluded a [6,3,7,6] (by decide +kernel))
      (invalid_excluded a [6,3,7,7] (by decide +kernel))
      node_2156)

theorem node_2158 : Excluded a [6,3,8,0] :=
  source_excluded a [6,3,8,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2159 : Excluded a [6,3,8,1] :=
  predecessor_excluded a [6,3,8,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_2160 : Excluded a [6,3,8,2] :=
  predecessor_excluded a [6,3,8,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_2161 : Excluded a [6,3,8,5] :=
  source_excluded a [6,3,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2163 : Excluded a [6,3,8,7,0] :=
  predecessor_excluded a [6,3,8,7,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_2165 : Excluded a [6,3,8,7,1,0] :=
  source_excluded a [6,3,8,7,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2167 : Excluded a [6,3,8,7,1,2,0] :=
  predecessor_excluded a [6,3,8,7,1,2,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2168 : Excluded a [6,3,8,7,1,2,4] :=
  source_excluded a [6,3,8,7,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2171 : Excluded a [6,3,8,7,1,2,5,0,4] :=
  predecessor_excluded a [6,3,8,7,1,2,5,0,4] 0 4 2 8 (by decide) (by decide +kernel)

theorem node_2170 : Excluded a [6,3,8,7,1,2,5,0] :=
  branch_excluded a [6,3,8,7,1,2,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,3,8,7,1,2,5,0,0] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,2,5,0,1] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,2,5,0,2] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,2,5,0,3] (by decide +kernel))
      node_2171
      (invalid_excluded a [6,3,8,7,1,2,5,0,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,2,5,0,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,2,5,0,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,2,5,0,8] (by decide +kernel)))

theorem node_2172 : Excluded a [6,3,8,7,1,2,5,4] :=
  source_excluded a [6,3,8,7,1,2,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_2169 : Excluded a [6,3,8,7,1,2,5] :=
  branch_excluded a [6,3,8,7,1,2,5] (by decide)
    (fin9_cases _
      node_2170
      (invalid_excluded a [6,3,8,7,1,2,5,1] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,2,5,3] (by decide +kernel))
      node_2172
      (invalid_excluded a [6,3,8,7,1,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,2,5,8] (by decide +kernel)))

theorem node_2166 : Excluded a [6,3,8,7,1,2] :=
  branch_excluded a [6,3,8,7,1,2] (by decide)
    (fin9_cases _
      node_2167
      (invalid_excluded a [6,3,8,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,2,3] (by decide +kernel))
      node_2168
      node_2169
      (invalid_excluded a [6,3,8,7,1,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,2,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,2,8] (by decide +kernel)))

theorem node_2174 : Excluded a [6,3,8,7,1,4,0] :=
  predecessor_excluded a [6,3,8,7,1,4,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2175 : Excluded a [6,3,8,7,1,4,2] :=
  predecessor_excluded a [6,3,8,7,1,4,2] 0 8 6 2 (by decide) (by decide +kernel)

theorem node_2176 : Excluded a [6,3,8,7,1,4,5] :=
  predecessor_excluded a [6,3,8,7,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2173 : Excluded a [6,3,8,7,1,4] :=
  branch_excluded a [6,3,8,7,1,4] (by decide)
    (fin9_cases _
      node_2174
      (invalid_excluded a [6,3,8,7,1,4,1] (by decide +kernel))
      node_2175
      (invalid_excluded a [6,3,8,7,1,4,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,4,4] (by decide +kernel))
      node_2176
      (invalid_excluded a [6,3,8,7,1,4,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,4,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,4,8] (by decide +kernel)))

theorem node_2164 : Excluded a [6,3,8,7,1] :=
  branch_excluded a [6,3,8,7,1] (by decide)
    (fin9_cases _
      node_2165
      (invalid_excluded a [6,3,8,7,1,1] (by decide +kernel))
      node_2166
      (invalid_excluded a [6,3,8,7,1,3] (by decide +kernel))
      node_2173
      (invalid_excluded a [6,3,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,1,8] (by decide +kernel)))

theorem node_2178 : Excluded a [6,3,8,7,2,0] :=
  source_excluded a [6,3,8,7,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2179 : Excluded a [6,3,8,7,2,1] :=
  source_excluded a [6,3,8,7,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2181 : Excluded a [6,3,8,7,2,4,0] :=
  predecessor_excluded a [6,3,8,7,2,4,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2182 : Excluded a [6,3,8,7,2,4,1] :=
  source_excluded a [6,3,8,7,2,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2183 : Excluded a [6,3,8,7,2,4,5] :=
  predecessor_excluded a [6,3,8,7,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2180 : Excluded a [6,3,8,7,2,4] :=
  branch_excluded a [6,3,8,7,2,4] (by decide)
    (fin9_cases _
      node_2181
      node_2182
      (invalid_excluded a [6,3,8,7,2,4,2] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,4,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,4,4] (by decide +kernel))
      node_2183
      (invalid_excluded a [6,3,8,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,4,8] (by decide +kernel)))

theorem node_2177 : Excluded a [6,3,8,7,2] :=
  branch_excluded a [6,3,8,7,2] (by decide)
    (fin9_cases _
      node_2178
      node_2179
      (invalid_excluded a [6,3,8,7,2,2] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,3] (by decide +kernel))
      node_2180
      (invalid_excluded a [6,3,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,2,8] (by decide +kernel)))

theorem node_2162 : Excluded a [6,3,8,7] :=
  branch_excluded a [6,3,8,7] (by decide)
    (fin9_cases _
      node_2163
      node_2164
      node_2177
      (invalid_excluded a [6,3,8,7,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,3,8,7,8] (by decide +kernel)))

theorem node_2157 : Excluded a [6,3,8] :=
  branch_excluded a [6,3,8] (by decide)
    (fin9_cases _
      node_2158
      node_2159
      node_2160
      (invalid_excluded a [6,3,8,3] (by decide +kernel))
      (invalid_excluded a [6,3,8,4] (by decide +kernel))
      node_2161
      (invalid_excluded a [6,3,8,6] (by decide +kernel))
      node_2162
      (invalid_excluded a [6,3,8,8] (by decide +kernel)))

theorem node_2087 : Excluded a [6,3] :=
  branch_excluded a [6,3] (by decide)
    (fin9_cases _
      node_2088
      node_2089
      (invalid_excluded a [6,3,2] (by decide +kernel))
      (invalid_excluded a [6,3,3] (by decide +kernel))
      node_2090
      node_2091
      (invalid_excluded a [6,3,6] (by decide +kernel))
      node_2130
      node_2157)

theorem node_2186 : Excluded a [6,4,0,1] :=
  source_excluded a [6,4,0,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2188 : Excluded a [6,4,0,2,1] :=
  predecessor_excluded a [6,4,0,2,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2189 : Excluded a [6,4,0,2,3] :=
  predecessor_excluded a [6,4,0,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2191 : Excluded a [6,4,0,2,7,1] :=
  source_excluded a [6,4,0,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2193 : Excluded a [6,4,0,2,7,3,1] :=
  source_excluded a [6,4,0,2,7,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2194 : Excluded a [6,4,0,2,7,3,5] :=
  source_excluded a [6,4,0,2,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_2195 : Excluded a [6,4,0,2,7,3,8] :=
  source_excluded a [6,4,0,2,7,3,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_2192 : Excluded a [6,4,0,2,7,3] :=
  branch_excluded a [6,4,0,2,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,2,7,3,0] (by decide +kernel))
      node_2193
      (invalid_excluded a [6,4,0,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,7,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,7,3,4] (by decide +kernel))
      node_2194
      (invalid_excluded a [6,4,0,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,7,3,7] (by decide +kernel))
      node_2195)

theorem node_2196 : Excluded a [6,4,0,2,7,8] :=
  predecessor_excluded a [6,4,0,2,7,8] 0 8 4 5 (by decide) (by decide +kernel)

theorem node_2190 : Excluded a [6,4,0,2,7] :=
  branch_excluded a [6,4,0,2,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,2,7,0] (by decide +kernel))
      node_2191
      (invalid_excluded a [6,4,0,2,7,2] (by decide +kernel))
      node_2192
      (invalid_excluded a [6,4,0,2,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,7,7] (by decide +kernel))
      node_2196)

theorem node_2198 : Excluded a [6,4,0,2,8,1] :=
  source_excluded a [6,4,0,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2200 : Excluded a [6,4,0,2,8,3,1] :=
  source_excluded a [6,4,0,2,8,3,1] 0 2 6 (by decide) (by decide +kernel)

def b_2203 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 4
  | 2 => 0
  | 3 => 2
  | 4 => 8
  | 5 => 3
  | 6 => 5
  | 7 => 1
  | 8 => 7
  | _ => 0

def cert_2203 : LosingRegion (edgeOf a b_2203) 0 :=
  losingMask a b_2203 0 1210114496913050801538048
    (by decide +kernel) (by decide +kernel)

theorem node_2203 : Excluded a [6,4,0,2,8,3,5,1,7] :=
  losing_excluded a [6,4,0,2,8,3,5,1,7] (by decide) b_2203 (by decide +kernel) 3 0 8 cert_2203 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_2203 3 0 ∧ 8 ≠ 3 ∧ maskRegion 1210114496913050801538048 3 8; decide +kernel)

theorem node_2202 : Excluded a [6,4,0,2,8,3,5,1] :=
  branch_excluded a [6,4,0,2,8,3,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,2,8,3,5,1,0] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,3,5,1,1] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,3,5,1,2] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,3,5,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,3,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,3,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,3,5,1,6] (by decide +kernel))
      node_2203
      (invalid_excluded a [6,4,0,2,8,3,5,1,8] (by decide +kernel)))

theorem node_2201 : Excluded a [6,4,0,2,8,3,5] :=
  branch_excluded a [6,4,0,2,8,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,2,8,3,5,0] (by decide +kernel))
      node_2202
      (invalid_excluded a [6,4,0,2,8,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,3,5,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,3,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,3,5,8] (by decide +kernel)))

theorem node_2199 : Excluded a [6,4,0,2,8,3] :=
  branch_excluded a [6,4,0,2,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,2,8,3,0] (by decide +kernel))
      node_2200
      (invalid_excluded a [6,4,0,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,3,4] (by decide +kernel))
      node_2201
      (invalid_excluded a [6,4,0,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,3,8] (by decide +kernel)))

theorem node_2204 : Excluded a [6,4,0,2,8,7] :=
  source_excluded a [6,4,0,2,8,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2197 : Excluded a [6,4,0,2,8] :=
  branch_excluded a [6,4,0,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,2,8,0] (by decide +kernel))
      node_2198
      (invalid_excluded a [6,4,0,2,8,2] (by decide +kernel))
      node_2199
      (invalid_excluded a [6,4,0,2,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,8,6] (by decide +kernel))
      node_2204
      (invalid_excluded a [6,4,0,2,8,8] (by decide +kernel)))

theorem node_2187 : Excluded a [6,4,0,2] :=
  branch_excluded a [6,4,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,2,0] (by decide +kernel))
      node_2188
      (invalid_excluded a [6,4,0,2,2] (by decide +kernel))
      node_2189
      (invalid_excluded a [6,4,0,2,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,2,6] (by decide +kernel))
      node_2190
      node_2197)

theorem node_2205 : Excluded a [6,4,0,5] :=
  source_excluded a [6,4,0,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2207 : Excluded a [6,4,0,7,1] :=
  predecessor_excluded a [6,4,0,7,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2209 : Excluded a [6,4,0,7,2,1] :=
  source_excluded a [6,4,0,7,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2210 : Excluded a [6,4,0,7,2,3] :=
  predecessor_excluded a [6,4,0,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_2212 : Excluded a [6,4,0,7,2,8,1] :=
  source_excluded a [6,4,0,7,2,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2213 : Excluded a [6,4,0,7,2,8,3] :=
  source_excluded a [6,4,0,7,2,8,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2214 : Excluded a [6,4,0,7,2,8,5] :=
  predecessor_excluded a [6,4,0,7,2,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_2211 : Excluded a [6,4,0,7,2,8] :=
  branch_excluded a [6,4,0,7,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,7,2,8,0] (by decide +kernel))
      node_2212
      (invalid_excluded a [6,4,0,7,2,8,2] (by decide +kernel))
      node_2213
      (invalid_excluded a [6,4,0,7,2,8,4] (by decide +kernel))
      node_2214
      (invalid_excluded a [6,4,0,7,2,8,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,2,8,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,2,8,8] (by decide +kernel)))

theorem node_2208 : Excluded a [6,4,0,7,2] :=
  branch_excluded a [6,4,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,7,2,0] (by decide +kernel))
      node_2209
      (invalid_excluded a [6,4,0,7,2,2] (by decide +kernel))
      node_2210
      (invalid_excluded a [6,4,0,7,2,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,2,7] (by decide +kernel))
      node_2211)

theorem node_2216 : Excluded a [6,4,0,7,3,1] :=
  source_excluded a [6,4,0,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2218 : Excluded a [6,4,0,7,3,2,1] :=
  source_excluded a [6,4,0,7,3,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2220 : Excluded a [6,4,0,7,3,2,5,1] :=
  branch_excluded a [6,4,0,7,3,2,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,7,3,2,5,1,0] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,5,1,1] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,5,1,2] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,5,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,5,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,5,1,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,5,1,8] (by decide +kernel)))

theorem node_2219 : Excluded a [6,4,0,7,3,2,5] :=
  branch_excluded a [6,4,0,7,3,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,7,3,2,5,0] (by decide +kernel))
      node_2220
      (invalid_excluded a [6,4,0,7,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,5,8] (by decide +kernel)))

theorem node_2221 : Excluded a [6,4,0,7,3,2,8] :=
  source_excluded a [6,4,0,7,3,2,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_2217 : Excluded a [6,4,0,7,3,2] :=
  branch_excluded a [6,4,0,7,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,7,3,2,0] (by decide +kernel))
      node_2218
      (invalid_excluded a [6,4,0,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,4] (by decide +kernel))
      node_2219
      (invalid_excluded a [6,4,0,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,2,7] (by decide +kernel))
      node_2221)

theorem node_2223 : Excluded a [6,4,0,7,3,8,1] :=
  source_excluded a [6,4,0,7,3,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2224 : Excluded a [6,4,0,7,3,8,2] :=
  predecessor_excluded a [6,4,0,7,3,8,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2225 : Excluded a [6,4,0,7,3,8,5] :=
  predecessor_excluded a [6,4,0,7,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_2222 : Excluded a [6,4,0,7,3,8] :=
  branch_excluded a [6,4,0,7,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,7,3,8,0] (by decide +kernel))
      node_2223
      node_2224
      (invalid_excluded a [6,4,0,7,3,8,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,8,4] (by decide +kernel))
      node_2225
      (invalid_excluded a [6,4,0,7,3,8,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,8,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,8,8] (by decide +kernel)))

theorem node_2215 : Excluded a [6,4,0,7,3] :=
  branch_excluded a [6,4,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,7,3,0] (by decide +kernel))
      node_2216
      node_2217
      (invalid_excluded a [6,4,0,7,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,3,7] (by decide +kernel))
      node_2222)

theorem node_2226 : Excluded a [6,4,0,7,8] :=
  predecessor_excluded a [6,4,0,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_2206 : Excluded a [6,4,0,7] :=
  branch_excluded a [6,4,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,7,0] (by decide +kernel))
      node_2207
      node_2208
      node_2215
      (invalid_excluded a [6,4,0,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,7,7] (by decide +kernel))
      node_2226)

theorem node_2228 : Excluded a [6,4,0,8,1] :=
  predecessor_excluded a [6,4,0,8,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2229 : Excluded a [6,4,0,8,2] :=
  predecessor_excluded a [6,4,0,8,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_2231 : Excluded a [6,4,0,8,3,1] :=
  source_excluded a [6,4,0,8,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2233 : Excluded a [6,4,0,8,3,2,1] :=
  source_excluded a [6,4,0,8,3,2,1] 0 2 6 (by decide) (by decide +kernel)

def b_2236 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 4
  | 2 => 0
  | 3 => 8
  | 4 => 3
  | 5 => 2
  | 6 => 5
  | 7 => 1
  | 8 => 7
  | _ => 0

def cert_2236 : LosingRegion (edgeOf a b_2236) 0 :=
  losingMask a b_2236 0 1210114491851466202940416
    (by decide +kernel) (by decide +kernel)

theorem node_2236 : Excluded a [6,4,0,8,3,2,5,1,7] :=
  losing_excluded a [6,4,0,8,3,2,5,1,7] (by decide) b_2236 (by decide +kernel) 3 0 7 cert_2236 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_2236 3 0 ∧ 7 ≠ 3 ∧ maskRegion 1210114491851466202940416 3 7; decide +kernel)

theorem node_2235 : Excluded a [6,4,0,8,3,2,5,1] :=
  branch_excluded a [6,4,0,8,3,2,5,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,3,2,5,1,0] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,2,5,1,1] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,2,5,1,2] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,2,5,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,2,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,2,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,2,5,1,6] (by decide +kernel))
      node_2236
      (invalid_excluded a [6,4,0,8,3,2,5,1,8] (by decide +kernel)))

theorem node_2234 : Excluded a [6,4,0,8,3,2,5] :=
  branch_excluded a [6,4,0,8,3,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,3,2,5,0] (by decide +kernel))
      node_2235
      (invalid_excluded a [6,4,0,8,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,2,5,8] (by decide +kernel)))

theorem node_2232 : Excluded a [6,4,0,8,3,2] :=
  branch_excluded a [6,4,0,8,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,3,2,0] (by decide +kernel))
      node_2233
      (invalid_excluded a [6,4,0,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,2,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,2,4] (by decide +kernel))
      node_2234
      (invalid_excluded a [6,4,0,8,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,2,8] (by decide +kernel)))

theorem node_2237 : Excluded a [6,4,0,8,3,7] :=
  source_excluded a [6,4,0,8,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2230 : Excluded a [6,4,0,8,3] :=
  branch_excluded a [6,4,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,3,0] (by decide +kernel))
      node_2231
      node_2232
      (invalid_excluded a [6,4,0,8,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,3,6] (by decide +kernel))
      node_2237
      (invalid_excluded a [6,4,0,8,3,8] (by decide +kernel)))

theorem node_2239 : Excluded a [6,4,0,8,7,1] :=
  source_excluded a [6,4,0,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2241 : Excluded a [6,4,0,8,7,2,1] :=
  source_excluded a [6,4,0,8,7,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2242 : Excluded a [6,4,0,8,7,2,3] :=
  predecessor_excluded a [6,4,0,8,7,2,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_2243 : Excluded a [6,4,0,8,7,2,5] :=
  source_excluded a [6,4,0,8,7,2,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_2240 : Excluded a [6,4,0,8,7,2] :=
  branch_excluded a [6,4,0,8,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,7,2,0] (by decide +kernel))
      node_2241
      (invalid_excluded a [6,4,0,8,7,2,2] (by decide +kernel))
      node_2242
      (invalid_excluded a [6,4,0,8,7,2,4] (by decide +kernel))
      node_2243
      (invalid_excluded a [6,4,0,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,2,8] (by decide +kernel)))

theorem node_2245 : Excluded a [6,4,0,8,7,3,1] :=
  source_excluded a [6,4,0,8,7,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2248 : Excluded a [6,4,0,8,7,3,2,1,5] :=
  predecessor_excluded a [6,4,0,8,7,3,2,1,5] 0 3 8 5 (by decide) (by decide +kernel)

theorem node_2247 : Excluded a [6,4,0,8,7,3,2,1] :=
  branch_excluded a [6,4,0,8,7,3,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,7,3,2,1,0] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,2,1,1] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,2,1,2] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,2,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,2,1,4] (by decide +kernel))
      node_2248
      (invalid_excluded a [6,4,0,8,7,3,2,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,2,1,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,2,1,8] (by decide +kernel)))

theorem node_2249 : Excluded a [6,4,0,8,7,3,2,5] :=
  source_excluded a [6,4,0,8,7,3,2,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_2246 : Excluded a [6,4,0,8,7,3,2] :=
  branch_excluded a [6,4,0,8,7,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,7,3,2,0] (by decide +kernel))
      node_2247
      (invalid_excluded a [6,4,0,8,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,2,4] (by decide +kernel))
      node_2249
      (invalid_excluded a [6,4,0,8,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,2,8] (by decide +kernel)))

theorem node_2250 : Excluded a [6,4,0,8,7,3,5] :=
  source_excluded a [6,4,0,8,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_2244 : Excluded a [6,4,0,8,7,3] :=
  branch_excluded a [6,4,0,8,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,7,3,0] (by decide +kernel))
      node_2245
      node_2246
      (invalid_excluded a [6,4,0,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,4] (by decide +kernel))
      node_2250
      (invalid_excluded a [6,4,0,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,3,8] (by decide +kernel)))

theorem node_2238 : Excluded a [6,4,0,8,7] :=
  branch_excluded a [6,4,0,8,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,7,0] (by decide +kernel))
      node_2239
      node_2240
      node_2244
      (invalid_excluded a [6,4,0,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,7,8] (by decide +kernel)))

theorem node_2227 : Excluded a [6,4,0,8] :=
  branch_excluded a [6,4,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,8,0] (by decide +kernel))
      node_2228
      node_2229
      node_2230
      (invalid_excluded a [6,4,0,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,0,8,6] (by decide +kernel))
      node_2238
      (invalid_excluded a [6,4,0,8,8] (by decide +kernel)))

theorem node_2185 : Excluded a [6,4,0] :=
  branch_excluded a [6,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,0,0] (by decide +kernel))
      node_2186
      node_2187
      (invalid_excluded a [6,4,0,3] (by decide +kernel))
      (invalid_excluded a [6,4,0,4] (by decide +kernel))
      node_2205
      (invalid_excluded a [6,4,0,6] (by decide +kernel))
      node_2206
      node_2227)

theorem node_2251 : Excluded a [6,4,1] :=
  predecessor_excluded a [6,4,1] 0 4 2 1 (by decide) (by decide +kernel)

theorem node_2253 : Excluded a [6,4,5,0] :=
  source_excluded a [6,4,5,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2254 : Excluded a [6,4,5,1] :=
  source_excluded a [6,4,5,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2255 : Excluded a [6,4,5,2] :=
  predecessor_excluded a [6,4,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_2257 : Excluded a [6,4,5,7,0] :=
  source_excluded a [6,4,5,7,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2258 : Excluded a [6,4,5,7,1] :=
  predecessor_excluded a [6,4,5,7,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2259 : Excluded a [6,4,5,7,2] :=
  source_excluded a [6,4,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2260 : Excluded a [6,4,5,7,3] :=
  source_excluded a [6,4,5,7,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2261 : Excluded a [6,4,5,7,8] :=
  predecessor_excluded a [6,4,5,7,8] 0 8 3 4 (by decide) (by decide +kernel)

theorem node_2256 : Excluded a [6,4,5,7] :=
  branch_excluded a [6,4,5,7] (by decide)
    (fin9_cases _
      node_2257
      node_2258
      node_2259
      node_2260
      (invalid_excluded a [6,4,5,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,5,7,7] (by decide +kernel))
      node_2261)

theorem node_2263 : Excluded a [6,4,5,8,0] :=
  source_excluded a [6,4,5,8,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2264 : Excluded a [6,4,5,8,1] :=
  predecessor_excluded a [6,4,5,8,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2265 : Excluded a [6,4,5,8,2] :=
  source_excluded a [6,4,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2266 : Excluded a [6,4,5,8,3] :=
  source_excluded a [6,4,5,8,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2268 : Excluded a [6,4,5,8,7,0] :=
  source_excluded a [6,4,5,8,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2269 : Excluded a [6,4,5,8,7,1] :=
  source_excluded a [6,4,5,8,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2271 : Excluded a [6,4,5,8,7,2,0] :=
  predecessor_excluded a [6,4,5,8,7,2,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2272 : Excluded a [6,4,5,8,7,2,1] :=
  source_excluded a [6,4,5,8,7,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2273 : Excluded a [6,4,5,8,7,2,3] :=
  predecessor_excluded a [6,4,5,8,7,2,3] 0 8 6 3 (by decide) (by decide +kernel)

theorem node_2270 : Excluded a [6,4,5,8,7,2] :=
  branch_excluded a [6,4,5,8,7,2] (by decide)
    (fin9_cases _
      node_2271
      node_2272
      (invalid_excluded a [6,4,5,8,7,2,2] (by decide +kernel))
      node_2273
      (invalid_excluded a [6,4,5,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,7,2,8] (by decide +kernel)))

theorem node_2274 : Excluded a [6,4,5,8,7,3] :=
  source_excluded a [6,4,5,8,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2267 : Excluded a [6,4,5,8,7] :=
  branch_excluded a [6,4,5,8,7] (by decide)
    (fin9_cases _
      node_2268
      node_2269
      node_2270
      node_2274
      (invalid_excluded a [6,4,5,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,7,8] (by decide +kernel)))

theorem node_2262 : Excluded a [6,4,5,8] :=
  branch_excluded a [6,4,5,8] (by decide)
    (fin9_cases _
      node_2263
      node_2264
      node_2265
      node_2266
      (invalid_excluded a [6,4,5,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,5,8,6] (by decide +kernel))
      node_2267
      (invalid_excluded a [6,4,5,8,8] (by decide +kernel)))

theorem node_2252 : Excluded a [6,4,5] :=
  branch_excluded a [6,4,5] (by decide)
    (fin9_cases _
      node_2253
      node_2254
      node_2255
      (invalid_excluded a [6,4,5,3] (by decide +kernel))
      (invalid_excluded a [6,4,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,5,6] (by decide +kernel))
      node_2256
      node_2262)

theorem node_2276 : Excluded a [6,4,7,0] :=
  source_excluded a [6,4,7,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2277 : Excluded a [6,4,7,1] :=
  source_excluded a [6,4,7,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2279 : Excluded a [6,4,7,2,0] :=
  source_excluded a [6,4,7,2,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2280 : Excluded a [6,4,7,2,1] :=
  predecessor_excluded a [6,4,7,2,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2281 : Excluded a [6,4,7,2,3] :=
  predecessor_excluded a [6,4,7,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2283 : Excluded a [6,4,7,2,8,0] :=
  source_excluded a [6,4,7,2,8,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2284 : Excluded a [6,4,7,2,8,1] :=
  source_excluded a [6,4,7,2,8,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2286 : Excluded a [6,4,7,2,8,3,0] :=
  predecessor_excluded a [6,4,7,2,8,3,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2287 : Excluded a [6,4,7,2,8,3,1] :=
  source_excluded a [6,4,7,2,8,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2290 : Excluded a [6,4,7,2,8,3,5,0,1] :=
  predecessor_excluded a [6,4,7,2,8,3,5,0,1] 2 1 7 8 (by decide) (by decide +kernel)

theorem node_2289 : Excluded a [6,4,7,2,8,3,5,0] :=
  branch_excluded a [6,4,7,2,8,3,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,7,2,8,3,5,0,0] (by decide +kernel))
      node_2290
      (invalid_excluded a [6,4,7,2,8,3,5,0,2] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,0,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,0,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,0,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,0,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,0,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,0,8] (by decide +kernel)))

theorem node_2292 : Excluded a [6,4,7,2,8,3,5,1,0] :=
  predecessor_excluded a [6,4,7,2,8,3,5,1,0] 2 0 7 8 (by decide) (by decide +kernel)

theorem node_2291 : Excluded a [6,4,7,2,8,3,5,1] :=
  branch_excluded a [6,4,7,2,8,3,5,1] (by decide)
    (fin9_cases _
      node_2292
      (invalid_excluded a [6,4,7,2,8,3,5,1,1] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,1,2] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,1,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,1,8] (by decide +kernel)))

theorem node_2288 : Excluded a [6,4,7,2,8,3,5] :=
  branch_excluded a [6,4,7,2,8,3,5] (by decide)
    (fin9_cases _
      node_2289
      node_2291
      (invalid_excluded a [6,4,7,2,8,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,5,8] (by decide +kernel)))

theorem node_2285 : Excluded a [6,4,7,2,8,3] :=
  branch_excluded a [6,4,7,2,8,3] (by decide)
    (fin9_cases _
      node_2286
      node_2287
      (invalid_excluded a [6,4,7,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,4] (by decide +kernel))
      node_2288
      (invalid_excluded a [6,4,7,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,3,8] (by decide +kernel)))

theorem node_2282 : Excluded a [6,4,7,2,8] :=
  branch_excluded a [6,4,7,2,8] (by decide)
    (fin9_cases _
      node_2283
      node_2284
      (invalid_excluded a [6,4,7,2,8,2] (by decide +kernel))
      node_2285
      (invalid_excluded a [6,4,7,2,8,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,7] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,8,8] (by decide +kernel)))

theorem node_2278 : Excluded a [6,4,7,2] :=
  branch_excluded a [6,4,7,2] (by decide)
    (fin9_cases _
      node_2279
      node_2280
      (invalid_excluded a [6,4,7,2,2] (by decide +kernel))
      node_2281
      (invalid_excluded a [6,4,7,2,4] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,2,7] (by decide +kernel))
      node_2282)

theorem node_2293 : Excluded a [6,4,7,5] :=
  source_excluded a [6,4,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2294 : Excluded a [6,4,7,8] :=
  predecessor_excluded a [6,4,7,8] 0 8 2 3 (by decide) (by decide +kernel)

theorem node_2275 : Excluded a [6,4,7] :=
  branch_excluded a [6,4,7] (by decide)
    (fin9_cases _
      node_2276
      node_2277
      node_2278
      (invalid_excluded a [6,4,7,3] (by decide +kernel))
      (invalid_excluded a [6,4,7,4] (by decide +kernel))
      node_2293
      (invalid_excluded a [6,4,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,7,7] (by decide +kernel))
      node_2294)

theorem node_2296 : Excluded a [6,4,8,0] :=
  source_excluded a [6,4,8,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2297 : Excluded a [6,4,8,1] :=
  source_excluded a [6,4,8,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2298 : Excluded a [6,4,8,2] :=
  predecessor_excluded a [6,4,8,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_2299 : Excluded a [6,4,8,5] :=
  source_excluded a [6,4,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2301 : Excluded a [6,4,8,7,0] :=
  source_excluded a [6,4,8,7,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2302 : Excluded a [6,4,8,7,1] :=
  predecessor_excluded a [6,4,8,7,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2304 : Excluded a [6,4,8,7,2,0] :=
  source_excluded a [6,4,8,7,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2305 : Excluded a [6,4,8,7,2,1] :=
  source_excluded a [6,4,8,7,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2306 : Excluded a [6,4,8,7,2,3] :=
  predecessor_excluded a [6,4,8,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_2303 : Excluded a [6,4,8,7,2] :=
  branch_excluded a [6,4,8,7,2] (by decide)
    (fin9_cases _
      node_2304
      node_2305
      (invalid_excluded a [6,4,8,7,2,2] (by decide +kernel))
      node_2306
      (invalid_excluded a [6,4,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,2,8] (by decide +kernel)))

theorem node_2308 : Excluded a [6,4,8,7,3,0] :=
  source_excluded a [6,4,8,7,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2309 : Excluded a [6,4,8,7,3,1] :=
  source_excluded a [6,4,8,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2311 : Excluded a [6,4,8,7,3,2,0] :=
  predecessor_excluded a [6,4,8,7,3,2,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2312 : Excluded a [6,4,8,7,3,2,1] :=
  source_excluded a [6,4,8,7,3,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2315 : Excluded a [6,4,8,7,3,2,5,0,1] :=
  predecessor_excluded a [6,4,8,7,3,2,5,0,1] 2 1 7 8 (by decide) (by decide +kernel)

theorem node_2314 : Excluded a [6,4,8,7,3,2,5,0] :=
  branch_excluded a [6,4,8,7,3,2,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,4,8,7,3,2,5,0,0] (by decide +kernel))
      node_2315
      (invalid_excluded a [6,4,8,7,3,2,5,0,2] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,0,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,0,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,0,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,0,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,0,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,0,8] (by decide +kernel)))

theorem node_2317 : Excluded a [6,4,8,7,3,2,5,1,0] :=
  predecessor_excluded a [6,4,8,7,3,2,5,1,0] 2 0 7 8 (by decide) (by decide +kernel)

theorem node_2316 : Excluded a [6,4,8,7,3,2,5,1] :=
  branch_excluded a [6,4,8,7,3,2,5,1] (by decide)
    (fin9_cases _
      node_2317
      (invalid_excluded a [6,4,8,7,3,2,5,1,1] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,1,2] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,1,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,1,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,1,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,1,8] (by decide +kernel)))

theorem node_2313 : Excluded a [6,4,8,7,3,2,5] :=
  branch_excluded a [6,4,8,7,3,2,5] (by decide)
    (fin9_cases _
      node_2314
      node_2316
      (invalid_excluded a [6,4,8,7,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,5,8] (by decide +kernel)))

theorem node_2310 : Excluded a [6,4,8,7,3,2] :=
  branch_excluded a [6,4,8,7,3,2] (by decide)
    (fin9_cases _
      node_2311
      node_2312
      (invalid_excluded a [6,4,8,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,4] (by decide +kernel))
      node_2313
      (invalid_excluded a [6,4,8,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,2,8] (by decide +kernel)))

theorem node_2307 : Excluded a [6,4,8,7,3] :=
  branch_excluded a [6,4,8,7,3] (by decide)
    (fin9_cases _
      node_2308
      node_2309
      node_2310
      (invalid_excluded a [6,4,8,7,3,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,3,8] (by decide +kernel)))

theorem node_2300 : Excluded a [6,4,8,7] :=
  branch_excluded a [6,4,8,7] (by decide)
    (fin9_cases _
      node_2301
      node_2302
      node_2303
      node_2307
      (invalid_excluded a [6,4,8,7,4] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,5] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,4,8,7,8] (by decide +kernel)))

theorem node_2295 : Excluded a [6,4,8] :=
  branch_excluded a [6,4,8] (by decide)
    (fin9_cases _
      node_2296
      node_2297
      node_2298
      (invalid_excluded a [6,4,8,3] (by decide +kernel))
      (invalid_excluded a [6,4,8,4] (by decide +kernel))
      node_2299
      (invalid_excluded a [6,4,8,6] (by decide +kernel))
      node_2300
      (invalid_excluded a [6,4,8,8] (by decide +kernel)))

theorem node_2184 : Excluded a [6,4] :=
  branch_excluded a [6,4] (by decide)
    (fin9_cases _
      node_2185
      node_2251
      (invalid_excluded a [6,4,2] (by decide +kernel))
      (invalid_excluded a [6,4,3] (by decide +kernel))
      (invalid_excluded a [6,4,4] (by decide +kernel))
      node_2252
      (invalid_excluded a [6,4,6] (by decide +kernel))
      node_2275
      node_2295)

theorem node_2318 : Excluded a [6,5] :=
  predecessor_excluded a [6,5] 2 6 1 0 (by decide) (by decide +kernel)

theorem node_2319 : Excluded a [6,7] :=
  predecessor_excluded a [6,7] 2 7 0 1 (by decide) (by decide +kernel)

theorem node_2322 : Excluded a [6,8,0,1] :=
  predecessor_excluded a [6,8,0,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_2326 : Excluded a [6,8,0,2,1,3,4] :=
  predecessor_excluded a [6,8,0,2,1,3,4] 0 4 5 6 (by decide) (by decide +kernel)

def b_2329 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | 5 => 3
  | 6 => 5
  | 7 => 4
  | 8 => 7
  | _ => 0

def cert_2329 : LosingRegion (edgeOf a b_2329) 0 :=
  losingMask a b_2329 0 1266855154796347576550400
    (by decide +kernel) (by decide +kernel)

theorem node_2329 : Excluded a [6,8,0,2,1,3,5,4,7] :=
  losing_excluded a [6,8,0,2,1,3,5,4,7] (by decide) b_2329 (by decide +kernel) 5 0 2 cert_2329 (by change 5 ≠ 0 ∧ ¬ edgeOf a b_2329 5 0 ∧ 2 ≠ 5 ∧ maskRegion 1266855154796347576550400 5 2; decide +kernel)

theorem node_2328 : Excluded a [6,8,0,2,1,3,5,4] :=
  branch_excluded a [6,8,0,2,1,3,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,2,1,3,5,4,0] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,5,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,5,4,2] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,5,4,3] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,5,4,4] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,5,4,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,5,4,6] (by decide +kernel))
      node_2329
      (invalid_excluded a [6,8,0,2,1,3,5,4,8] (by decide +kernel)))

theorem node_2327 : Excluded a [6,8,0,2,1,3,5] :=
  branch_excluded a [6,8,0,2,1,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,2,1,3,5,0] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,5,3] (by decide +kernel))
      node_2328
      (invalid_excluded a [6,8,0,2,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,5,8] (by decide +kernel)))

theorem node_2325 : Excluded a [6,8,0,2,1,3] :=
  branch_excluded a [6,8,0,2,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,2,1,3,0] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,3] (by decide +kernel))
      node_2326
      node_2327
      (invalid_excluded a [6,8,0,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,3,8] (by decide +kernel)))

def b_2333 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 6
  | 1 => 8
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | 5 => 4
  | 6 => 3
  | 7 => 5
  | 8 => 7
  | _ => 0

def cert_2333 : LosingRegion (edgeOf a b_2333) 0 :=
  losingMask a b_2333 0 1269861397725369741607936
    (by decide +kernel) (by decide +kernel)

theorem node_2333 : Excluded a [6,8,0,2,1,4,3,5,7] :=
  losing_excluded a [6,8,0,2,1,4,3,5,7] (by decide) b_2333 (by decide +kernel) 3 0 2 cert_2333 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_2333 3 0 ∧ 2 ≠ 3 ∧ maskRegion 1269861397725369741607936 3 2; decide +kernel)

theorem node_2332 : Excluded a [6,8,0,2,1,4,3,5] :=
  branch_excluded a [6,8,0,2,1,4,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,2,1,4,3,5,0] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,4,3,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,4,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,4,3,5,3] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,4,3,5,4] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,4,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,4,3,5,6] (by decide +kernel))
      node_2333
      (invalid_excluded a [6,8,0,2,1,4,3,5,8] (by decide +kernel)))

theorem node_2331 : Excluded a [6,8,0,2,1,4,3] :=
  branch_excluded a [6,8,0,2,1,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,2,1,4,3,0] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,4,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,4,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,4,3,3] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,4,3,4] (by decide +kernel))
      node_2332
      (invalid_excluded a [6,8,0,2,1,4,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,4,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,4,3,8] (by decide +kernel)))

theorem node_2334 : Excluded a [6,8,0,2,1,4,5] :=
  predecessor_excluded a [6,8,0,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2330 : Excluded a [6,8,0,2,1,4] :=
  branch_excluded a [6,8,0,2,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,2,1,4,0] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,4,2] (by decide +kernel))
      node_2331
      (invalid_excluded a [6,8,0,2,1,4,4] (by decide +kernel))
      node_2334
      (invalid_excluded a [6,8,0,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,4,8] (by decide +kernel)))

theorem node_2335 : Excluded a [6,8,0,2,1,7] :=
  source_excluded a [6,8,0,2,1,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_2324 : Excluded a [6,8,0,2,1] :=
  branch_excluded a [6,8,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,2] (by decide +kernel))
      node_2325
      node_2330
      (invalid_excluded a [6,8,0,2,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,1,6] (by decide +kernel))
      node_2335
      (invalid_excluded a [6,8,0,2,1,8] (by decide +kernel)))

theorem node_2336 : Excluded a [6,8,0,2,3] :=
  predecessor_excluded a [6,8,0,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2338 : Excluded a [6,8,0,2,7,1] :=
  source_excluded a [6,8,0,2,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2340 : Excluded a [6,8,0,2,7,3,1] :=
  source_excluded a [6,8,0,2,7,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2341 : Excluded a [6,8,0,2,7,3,4] :=
  source_excluded a [6,8,0,2,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2342 : Excluded a [6,8,0,2,7,3,5] :=
  source_excluded a [6,8,0,2,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_2339 : Excluded a [6,8,0,2,7,3] :=
  branch_excluded a [6,8,0,2,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,2,7,3,0] (by decide +kernel))
      node_2340
      (invalid_excluded a [6,8,0,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,7,3,3] (by decide +kernel))
      node_2341
      node_2342
      (invalid_excluded a [6,8,0,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,7,3,8] (by decide +kernel)))

theorem node_2343 : Excluded a [6,8,0,2,7,4] :=
  predecessor_excluded a [6,8,0,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2337 : Excluded a [6,8,0,2,7] :=
  branch_excluded a [6,8,0,2,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,2,7,0] (by decide +kernel))
      node_2338
      (invalid_excluded a [6,8,0,2,7,2] (by decide +kernel))
      node_2339
      node_2343
      (invalid_excluded a [6,8,0,2,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,7,8] (by decide +kernel)))

theorem node_2323 : Excluded a [6,8,0,2] :=
  branch_excluded a [6,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,2,0] (by decide +kernel))
      node_2324
      (invalid_excluded a [6,8,0,2,2] (by decide +kernel))
      node_2336
      (invalid_excluded a [6,8,0,2,4] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,2,6] (by decide +kernel))
      node_2337
      (invalid_excluded a [6,8,0,2,8] (by decide +kernel)))

theorem node_2344 : Excluded a [6,8,0,5] :=
  source_excluded a [6,8,0,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2348 : Excluded a [6,8,0,7,1,2,3] :=
  source_excluded a [6,8,0,7,1,2,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2349 : Excluded a [6,8,0,7,1,2,4] :=
  source_excluded a [6,8,0,7,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2352 : Excluded a [6,8,0,7,1,2,5,3,4] :=
  predecessor_excluded a [6,8,0,7,1,2,5,3,4] 0 4 7 8 (by decide) (by decide +kernel)

theorem node_2351 : Excluded a [6,8,0,7,1,2,5,3] :=
  branch_excluded a [6,8,0,7,1,2,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,7,1,2,5,3,0] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,2,5,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,2,5,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,2,5,3,3] (by decide +kernel))
      node_2352
      (invalid_excluded a [6,8,0,7,1,2,5,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,2,5,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,2,5,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,2,5,3,8] (by decide +kernel)))

theorem node_2353 : Excluded a [6,8,0,7,1,2,5,4] :=
  source_excluded a [6,8,0,7,1,2,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_2350 : Excluded a [6,8,0,7,1,2,5] :=
  branch_excluded a [6,8,0,7,1,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,7,1,2,5,0] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,2,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,2,5,2] (by decide +kernel))
      node_2351
      node_2353
      (invalid_excluded a [6,8,0,7,1,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,2,5,8] (by decide +kernel)))

theorem node_2347 : Excluded a [6,8,0,7,1,2] :=
  branch_excluded a [6,8,0,7,1,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,7,1,2,0] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,2,2] (by decide +kernel))
      node_2348
      node_2349
      node_2350
      (invalid_excluded a [6,8,0,7,1,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,2,8] (by decide +kernel)))

theorem node_2354 : Excluded a [6,8,0,7,1,3] :=
  predecessor_excluded a [6,8,0,7,1,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_2357 : Excluded a [6,8,0,7,1,4,2,3] :=
  predecessor_excluded a [6,8,0,7,1,4,2,3] 0 3 6 7 (by decide) (by decide +kernel)

theorem node_2358 : Excluded a [6,8,0,7,1,4,2,5] :=
  predecessor_excluded a [6,8,0,7,1,4,2,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_2356 : Excluded a [6,8,0,7,1,4,2] :=
  branch_excluded a [6,8,0,7,1,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,7,1,4,2,0] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,4,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,4,2,2] (by decide +kernel))
      node_2357
      (invalid_excluded a [6,8,0,7,1,4,2,4] (by decide +kernel))
      node_2358
      (invalid_excluded a [6,8,0,7,1,4,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,4,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,4,2,8] (by decide +kernel)))

theorem node_2359 : Excluded a [6,8,0,7,1,4,3] :=
  source_excluded a [6,8,0,7,1,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2360 : Excluded a [6,8,0,7,1,4,5] :=
  predecessor_excluded a [6,8,0,7,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2355 : Excluded a [6,8,0,7,1,4] :=
  branch_excluded a [6,8,0,7,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,7,1,4,0] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,4,1] (by decide +kernel))
      node_2356
      node_2359
      (invalid_excluded a [6,8,0,7,1,4,4] (by decide +kernel))
      node_2360
      (invalid_excluded a [6,8,0,7,1,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,4,8] (by decide +kernel)))

theorem node_2346 : Excluded a [6,8,0,7,1] :=
  branch_excluded a [6,8,0,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,7,1,0] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,1] (by decide +kernel))
      node_2347
      node_2354
      node_2355
      (invalid_excluded a [6,8,0,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,1,8] (by decide +kernel)))

theorem node_2362 : Excluded a [6,8,0,7,2,1] :=
  source_excluded a [6,8,0,7,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2363 : Excluded a [6,8,0,7,2,3] :=
  predecessor_excluded a [6,8,0,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_2365 : Excluded a [6,8,0,7,2,4,1] :=
  source_excluded a [6,8,0,7,2,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2366 : Excluded a [6,8,0,7,2,4,3] :=
  source_excluded a [6,8,0,7,2,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2367 : Excluded a [6,8,0,7,2,4,5] :=
  predecessor_excluded a [6,8,0,7,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2364 : Excluded a [6,8,0,7,2,4] :=
  branch_excluded a [6,8,0,7,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,7,2,4,0] (by decide +kernel))
      node_2365
      (invalid_excluded a [6,8,0,7,2,4,2] (by decide +kernel))
      node_2366
      (invalid_excluded a [6,8,0,7,2,4,4] (by decide +kernel))
      node_2367
      (invalid_excluded a [6,8,0,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,2,4,8] (by decide +kernel)))

theorem node_2361 : Excluded a [6,8,0,7,2] :=
  branch_excluded a [6,8,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,7,2,0] (by decide +kernel))
      node_2362
      (invalid_excluded a [6,8,0,7,2,2] (by decide +kernel))
      node_2363
      node_2364
      (invalid_excluded a [6,8,0,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,2,8] (by decide +kernel)))

theorem node_2369 : Excluded a [6,8,0,7,3,1] :=
  source_excluded a [6,8,0,7,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2371 : Excluded a [6,8,0,7,3,2,1] :=
  source_excluded a [6,8,0,7,3,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2372 : Excluded a [6,8,0,7,3,2,4] :=
  source_excluded a [6,8,0,7,3,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2374 : Excluded a [6,8,0,7,3,2,5,1] :=
  source_excluded a [6,8,0,7,3,2,5,1] 7 0 1 (by decide) (by decide +kernel)

theorem node_2375 : Excluded a [6,8,0,7,3,2,5,4] :=
  source_excluded a [6,8,0,7,3,2,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_2373 : Excluded a [6,8,0,7,3,2,5] :=
  branch_excluded a [6,8,0,7,3,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,7,3,2,5,0] (by decide +kernel))
      node_2374
      (invalid_excluded a [6,8,0,7,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,3,2,5,3] (by decide +kernel))
      node_2375
      (invalid_excluded a [6,8,0,7,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,3,2,5,8] (by decide +kernel)))

theorem node_2370 : Excluded a [6,8,0,7,3,2] :=
  branch_excluded a [6,8,0,7,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,7,3,2,0] (by decide +kernel))
      node_2371
      (invalid_excluded a [6,8,0,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,3,2,3] (by decide +kernel))
      node_2372
      node_2373
      (invalid_excluded a [6,8,0,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,3,2,8] (by decide +kernel)))

theorem node_2376 : Excluded a [6,8,0,7,3,4] :=
  predecessor_excluded a [6,8,0,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2368 : Excluded a [6,8,0,7,3] :=
  branch_excluded a [6,8,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,7,3,0] (by decide +kernel))
      node_2369
      node_2370
      (invalid_excluded a [6,8,0,7,3,3] (by decide +kernel))
      node_2376
      (invalid_excluded a [6,8,0,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,3,8] (by decide +kernel)))

theorem node_2345 : Excluded a [6,8,0,7] :=
  branch_excluded a [6,8,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,7,0] (by decide +kernel))
      node_2346
      node_2361
      node_2368
      (invalid_excluded a [6,8,0,7,4] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,0,7,8] (by decide +kernel)))

theorem node_2321 : Excluded a [6,8,0] :=
  branch_excluded a [6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,0,0] (by decide +kernel))
      node_2322
      node_2323
      (invalid_excluded a [6,8,0,3] (by decide +kernel))
      (invalid_excluded a [6,8,0,4] (by decide +kernel))
      node_2344
      (invalid_excluded a [6,8,0,6] (by decide +kernel))
      node_2345
      (invalid_excluded a [6,8,0,8] (by decide +kernel)))

theorem node_2378 : Excluded a [6,8,1,0] :=
  predecessor_excluded a [6,8,1,0] 4 0 2 3 (by decide) (by decide +kernel)

theorem node_2380 : Excluded a [6,8,1,2,0] :=
  predecessor_excluded a [6,8,1,2,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_2381 : Excluded a [6,8,1,2,3] :=
  predecessor_excluded a [6,8,1,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2383 : Excluded a [6,8,1,2,7,0] :=
  source_excluded a [6,8,1,2,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2385 : Excluded a [6,8,1,2,7,3,0] :=
  predecessor_excluded a [6,8,1,2,7,3,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2386 : Excluded a [6,8,1,2,7,3,4] :=
  source_excluded a [6,8,1,2,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2387 : Excluded a [6,8,1,2,7,3,5] :=
  source_excluded a [6,8,1,2,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_2384 : Excluded a [6,8,1,2,7,3] :=
  branch_excluded a [6,8,1,2,7,3] (by decide)
    (fin9_cases _
      node_2385
      (invalid_excluded a [6,8,1,2,7,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,1,2,7,3,3] (by decide +kernel))
      node_2386
      node_2387
      (invalid_excluded a [6,8,1,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,2,7,3,8] (by decide +kernel)))

theorem node_2388 : Excluded a [6,8,1,2,7,4] :=
  predecessor_excluded a [6,8,1,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2382 : Excluded a [6,8,1,2,7] :=
  branch_excluded a [6,8,1,2,7] (by decide)
    (fin9_cases _
      node_2383
      (invalid_excluded a [6,8,1,2,7,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,2,7,2] (by decide +kernel))
      node_2384
      node_2388
      (invalid_excluded a [6,8,1,2,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,2,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,2,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,2,7,8] (by decide +kernel)))

theorem node_2379 : Excluded a [6,8,1,2] :=
  branch_excluded a [6,8,1,2] (by decide)
    (fin9_cases _
      node_2380
      (invalid_excluded a [6,8,1,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,2,2] (by decide +kernel))
      node_2381
      (invalid_excluded a [6,8,1,2,4] (by decide +kernel))
      (invalid_excluded a [6,8,1,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,2,6] (by decide +kernel))
      node_2382
      (invalid_excluded a [6,8,1,2,8] (by decide +kernel)))

theorem node_2389 : Excluded a [6,8,1,5] :=
  source_excluded a [6,8,1,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2391 : Excluded a [6,8,1,7,0] :=
  predecessor_excluded a [6,8,1,7,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_2393 : Excluded a [6,8,1,7,2,0] :=
  source_excluded a [6,8,1,7,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2394 : Excluded a [6,8,1,7,2,3] :=
  predecessor_excluded a [6,8,1,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_2396 : Excluded a [6,8,1,7,2,4,0] :=
  predecessor_excluded a [6,8,1,7,2,4,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2397 : Excluded a [6,8,1,7,2,4,3] :=
  source_excluded a [6,8,1,7,2,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2398 : Excluded a [6,8,1,7,2,4,5] :=
  predecessor_excluded a [6,8,1,7,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2395 : Excluded a [6,8,1,7,2,4] :=
  branch_excluded a [6,8,1,7,2,4] (by decide)
    (fin9_cases _
      node_2396
      (invalid_excluded a [6,8,1,7,2,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,4,2] (by decide +kernel))
      node_2397
      (invalid_excluded a [6,8,1,7,2,4,4] (by decide +kernel))
      node_2398
      (invalid_excluded a [6,8,1,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,4,8] (by decide +kernel)))

theorem node_2392 : Excluded a [6,8,1,7,2] :=
  branch_excluded a [6,8,1,7,2] (by decide)
    (fin9_cases _
      node_2393
      (invalid_excluded a [6,8,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,2] (by decide +kernel))
      node_2394
      node_2395
      (invalid_excluded a [6,8,1,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,2,8] (by decide +kernel)))

theorem node_2400 : Excluded a [6,8,1,7,3,0] :=
  source_excluded a [6,8,1,7,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2402 : Excluded a [6,8,1,7,3,2,0] :=
  predecessor_excluded a [6,8,1,7,3,2,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2403 : Excluded a [6,8,1,7,3,2,4] :=
  source_excluded a [6,8,1,7,3,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2405 : Excluded a [6,8,1,7,3,2,5,0] :=
  source_excluded a [6,8,1,7,3,2,5,0] 1 2 7 (by decide) (by decide +kernel)

theorem node_2406 : Excluded a [6,8,1,7,3,2,5,4] :=
  source_excluded a [6,8,1,7,3,2,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_2404 : Excluded a [6,8,1,7,3,2,5] :=
  branch_excluded a [6,8,1,7,3,2,5] (by decide)
    (fin9_cases _
      node_2405
      (invalid_excluded a [6,8,1,7,3,2,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,5,3] (by decide +kernel))
      node_2406
      (invalid_excluded a [6,8,1,7,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,5,8] (by decide +kernel)))

theorem node_2401 : Excluded a [6,8,1,7,3,2] :=
  branch_excluded a [6,8,1,7,3,2] (by decide)
    (fin9_cases _
      node_2402
      (invalid_excluded a [6,8,1,7,3,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,3] (by decide +kernel))
      node_2403
      node_2404
      (invalid_excluded a [6,8,1,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,2,8] (by decide +kernel)))

theorem node_2407 : Excluded a [6,8,1,7,3,4] :=
  predecessor_excluded a [6,8,1,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2399 : Excluded a [6,8,1,7,3] :=
  branch_excluded a [6,8,1,7,3] (by decide)
    (fin9_cases _
      node_2400
      (invalid_excluded a [6,8,1,7,3,1] (by decide +kernel))
      node_2401
      (invalid_excluded a [6,8,1,7,3,3] (by decide +kernel))
      node_2407
      (invalid_excluded a [6,8,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,3,8] (by decide +kernel)))

theorem node_2390 : Excluded a [6,8,1,7] :=
  branch_excluded a [6,8,1,7] (by decide)
    (fin9_cases _
      node_2391
      (invalid_excluded a [6,8,1,7,1] (by decide +kernel))
      node_2392
      node_2399
      (invalid_excluded a [6,8,1,7,4] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,1,7,8] (by decide +kernel)))

theorem node_2377 : Excluded a [6,8,1] :=
  branch_excluded a [6,8,1] (by decide)
    (fin9_cases _
      node_2378
      (invalid_excluded a [6,8,1,1] (by decide +kernel))
      node_2379
      (invalid_excluded a [6,8,1,3] (by decide +kernel))
      (invalid_excluded a [6,8,1,4] (by decide +kernel))
      node_2389
      (invalid_excluded a [6,8,1,6] (by decide +kernel))
      node_2390
      (invalid_excluded a [6,8,1,8] (by decide +kernel)))

theorem node_2408 : Excluded a [6,8,4] :=
  source_excluded a [6,8,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_2411 : Excluded a [6,8,5,0,1] :=
  predecessor_excluded a [6,8,5,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2412 : Excluded a [6,8,5,0,2] :=
  source_excluded a [6,8,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2413 : Excluded a [6,8,5,0,3] :=
  source_excluded a [6,8,5,0,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2415 : Excluded a [6,8,5,0,7,1] :=
  source_excluded a [6,8,5,0,7,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2417 : Excluded a [6,8,5,0,7,2,1] :=
  source_excluded a [6,8,5,0,7,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2418 : Excluded a [6,8,5,0,7,2,3] :=
  predecessor_excluded a [6,8,5,0,7,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_2419 : Excluded a [6,8,5,0,7,2,4] :=
  source_excluded a [6,8,5,0,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2416 : Excluded a [6,8,5,0,7,2] :=
  branch_excluded a [6,8,5,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,0,7,2,0] (by decide +kernel))
      node_2417
      (invalid_excluded a [6,8,5,0,7,2,2] (by decide +kernel))
      node_2418
      node_2419
      (invalid_excluded a [6,8,5,0,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,2,8] (by decide +kernel)))

theorem node_2420 : Excluded a [6,8,5,0,7,3] :=
  source_excluded a [6,8,5,0,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2421 : Excluded a [6,8,5,0,7,4] :=
  predecessor_excluded a [6,8,5,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2414 : Excluded a [6,8,5,0,7] :=
  branch_excluded a [6,8,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,0,7,0] (by decide +kernel))
      node_2415
      node_2416
      node_2420
      node_2421
      (invalid_excluded a [6,8,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,7,8] (by decide +kernel)))

theorem node_2410 : Excluded a [6,8,5,0] :=
  branch_excluded a [6,8,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,5,0,0] (by decide +kernel))
      node_2411
      node_2412
      node_2413
      (invalid_excluded a [6,8,5,0,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,0,6] (by decide +kernel))
      node_2414
      (invalid_excluded a [6,8,5,0,8] (by decide +kernel)))

theorem node_2423 : Excluded a [6,8,5,1,0] :=
  predecessor_excluded a [6,8,5,1,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_2424 : Excluded a [6,8,5,1,2] :=
  source_excluded a [6,8,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2425 : Excluded a [6,8,5,1,3] :=
  source_excluded a [6,8,5,1,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2427 : Excluded a [6,8,5,1,7,0] :=
  source_excluded a [6,8,5,1,7,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2429 : Excluded a [6,8,5,1,7,2,0] :=
  predecessor_excluded a [6,8,5,1,7,2,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2430 : Excluded a [6,8,5,1,7,2,3] :=
  predecessor_excluded a [6,8,5,1,7,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_2431 : Excluded a [6,8,5,1,7,2,4] :=
  source_excluded a [6,8,5,1,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_2428 : Excluded a [6,8,5,1,7,2] :=
  branch_excluded a [6,8,5,1,7,2] (by decide)
    (fin9_cases _
      node_2429
      (invalid_excluded a [6,8,5,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,2] (by decide +kernel))
      node_2430
      node_2431
      (invalid_excluded a [6,8,5,1,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,2,8] (by decide +kernel)))

theorem node_2432 : Excluded a [6,8,5,1,7,3] :=
  source_excluded a [6,8,5,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2433 : Excluded a [6,8,5,1,7,4] :=
  predecessor_excluded a [6,8,5,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_2426 : Excluded a [6,8,5,1,7] :=
  branch_excluded a [6,8,5,1,7] (by decide)
    (fin9_cases _
      node_2427
      (invalid_excluded a [6,8,5,1,7,1] (by decide +kernel))
      node_2428
      node_2432
      node_2433
      (invalid_excluded a [6,8,5,1,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,7,8] (by decide +kernel)))

theorem node_2422 : Excluded a [6,8,5,1] :=
  branch_excluded a [6,8,5,1] (by decide)
    (fin9_cases _
      node_2423
      (invalid_excluded a [6,8,5,1,1] (by decide +kernel))
      node_2424
      node_2425
      (invalid_excluded a [6,8,5,1,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,1,6] (by decide +kernel))
      node_2426
      (invalid_excluded a [6,8,5,1,8] (by decide +kernel)))

theorem node_2434 : Excluded a [6,8,5,2] :=
  predecessor_excluded a [6,8,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_2436 : Excluded a [6,8,5,7,0] :=
  predecessor_excluded a [6,8,5,7,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_2438 : Excluded a [6,8,5,7,1,0] :=
  source_excluded a [6,8,5,7,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2440 : Excluded a [6,8,5,7,1,2,0] :=
  predecessor_excluded a [6,8,5,7,1,2,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2441 : Excluded a [6,8,5,7,1,2,3] :=
  source_excluded a [6,8,5,7,1,2,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_2442 : Excluded a [6,8,5,7,1,2,4] :=
  source_excluded a [6,8,5,7,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2439 : Excluded a [6,8,5,7,1,2] :=
  branch_excluded a [6,8,5,7,1,2] (by decide)
    (fin9_cases _
      node_2440
      (invalid_excluded a [6,8,5,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,2,2] (by decide +kernel))
      node_2441
      node_2442
      (invalid_excluded a [6,8,5,7,1,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,2,8] (by decide +kernel)))

theorem node_2443 : Excluded a [6,8,5,7,1,3] :=
  source_excluded a [6,8,5,7,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2444 : Excluded a [6,8,5,7,1,4] :=
  predecessor_excluded a [6,8,5,7,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2437 : Excluded a [6,8,5,7,1] :=
  branch_excluded a [6,8,5,7,1] (by decide)
    (fin9_cases _
      node_2438
      (invalid_excluded a [6,8,5,7,1,1] (by decide +kernel))
      node_2439
      node_2443
      node_2444
      (invalid_excluded a [6,8,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,1,8] (by decide +kernel)))

theorem node_2445 : Excluded a [6,8,5,7,2] :=
  source_excluded a [6,8,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2446 : Excluded a [6,8,5,7,3] :=
  source_excluded a [6,8,5,7,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2435 : Excluded a [6,8,5,7] :=
  branch_excluded a [6,8,5,7] (by decide)
    (fin9_cases _
      node_2436
      node_2437
      node_2445
      node_2446
      (invalid_excluded a [6,8,5,7,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,5,7,8] (by decide +kernel)))

theorem node_2409 : Excluded a [6,8,5] :=
  branch_excluded a [6,8,5] (by decide)
    (fin9_cases _
      node_2410
      node_2422
      node_2434
      (invalid_excluded a [6,8,5,3] (by decide +kernel))
      (invalid_excluded a [6,8,5,4] (by decide +kernel))
      (invalid_excluded a [6,8,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,5,6] (by decide +kernel))
      node_2435
      (invalid_excluded a [6,8,5,8] (by decide +kernel)))

theorem node_2449 : Excluded a [6,8,7,0,1] :=
  predecessor_excluded a [6,8,7,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2451 : Excluded a [6,8,7,0,2,1] :=
  source_excluded a [6,8,7,0,2,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2452 : Excluded a [6,8,7,0,2,3] :=
  predecessor_excluded a [6,8,7,0,2,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_2454 : Excluded a [6,8,7,0,2,4,1] :=
  source_excluded a [6,8,7,0,2,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2455 : Excluded a [6,8,7,0,2,4,3] :=
  source_excluded a [6,8,7,0,2,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2456 : Excluded a [6,8,7,0,2,4,5] :=
  predecessor_excluded a [6,8,7,0,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2453 : Excluded a [6,8,7,0,2,4] :=
  branch_excluded a [6,8,7,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,4,0] (by decide +kernel))
      node_2454
      (invalid_excluded a [6,8,7,0,2,4,2] (by decide +kernel))
      node_2455
      (invalid_excluded a [6,8,7,0,2,4,4] (by decide +kernel))
      node_2456
      (invalid_excluded a [6,8,7,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,4,8] (by decide +kernel)))

theorem node_2450 : Excluded a [6,8,7,0,2] :=
  branch_excluded a [6,8,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,2,0] (by decide +kernel))
      node_2451
      (invalid_excluded a [6,8,7,0,2,2] (by decide +kernel))
      node_2452
      node_2453
      (invalid_excluded a [6,8,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,2,8] (by decide +kernel)))

theorem node_2458 : Excluded a [6,8,7,0,3,1] :=
  source_excluded a [6,8,7,0,3,1] 0 2 5 (by decide) (by decide +kernel)

theorem node_2459 : Excluded a [6,8,7,0,3,2] :=
  predecessor_excluded a [6,8,7,0,3,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_2460 : Excluded a [6,8,7,0,3,4] :=
  predecessor_excluded a [6,8,7,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2457 : Excluded a [6,8,7,0,3] :=
  branch_excluded a [6,8,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,3,0] (by decide +kernel))
      node_2458
      node_2459
      (invalid_excluded a [6,8,7,0,3,3] (by decide +kernel))
      node_2460
      (invalid_excluded a [6,8,7,0,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,3,8] (by decide +kernel)))

theorem node_2448 : Excluded a [6,8,7,0] :=
  branch_excluded a [6,8,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,8,7,0,0] (by decide +kernel))
      node_2449
      node_2450
      node_2457
      (invalid_excluded a [6,8,7,0,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,0,8] (by decide +kernel)))

theorem node_2462 : Excluded a [6,8,7,1,0] :=
  predecessor_excluded a [6,8,7,1,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_2464 : Excluded a [6,8,7,1,2,0] :=
  source_excluded a [6,8,7,1,2,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2465 : Excluded a [6,8,7,1,2,3] :=
  predecessor_excluded a [6,8,7,1,2,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_2467 : Excluded a [6,8,7,1,2,4,0] :=
  predecessor_excluded a [6,8,7,1,2,4,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2468 : Excluded a [6,8,7,1,2,4,3] :=
  source_excluded a [6,8,7,1,2,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2469 : Excluded a [6,8,7,1,2,4,5] :=
  predecessor_excluded a [6,8,7,1,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2466 : Excluded a [6,8,7,1,2,4] :=
  branch_excluded a [6,8,7,1,2,4] (by decide)
    (fin9_cases _
      node_2467
      (invalid_excluded a [6,8,7,1,2,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,2,4,2] (by decide +kernel))
      node_2468
      (invalid_excluded a [6,8,7,1,2,4,4] (by decide +kernel))
      node_2469
      (invalid_excluded a [6,8,7,1,2,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,2,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,2,4,8] (by decide +kernel)))

theorem node_2463 : Excluded a [6,8,7,1,2] :=
  branch_excluded a [6,8,7,1,2] (by decide)
    (fin9_cases _
      node_2464
      (invalid_excluded a [6,8,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,2,2] (by decide +kernel))
      node_2465
      node_2466
      (invalid_excluded a [6,8,7,1,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,2,8] (by decide +kernel)))

theorem node_2471 : Excluded a [6,8,7,1,3,0] :=
  source_excluded a [6,8,7,1,3,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2472 : Excluded a [6,8,7,1,3,2] :=
  predecessor_excluded a [6,8,7,1,3,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_2473 : Excluded a [6,8,7,1,3,4] :=
  predecessor_excluded a [6,8,7,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2470 : Excluded a [6,8,7,1,3] :=
  branch_excluded a [6,8,7,1,3] (by decide)
    (fin9_cases _
      node_2471
      (invalid_excluded a [6,8,7,1,3,1] (by decide +kernel))
      node_2472
      (invalid_excluded a [6,8,7,1,3,3] (by decide +kernel))
      node_2473
      (invalid_excluded a [6,8,7,1,3,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,3,8] (by decide +kernel)))

theorem node_2461 : Excluded a [6,8,7,1] :=
  branch_excluded a [6,8,7,1] (by decide)
    (fin9_cases _
      node_2462
      (invalid_excluded a [6,8,7,1,1] (by decide +kernel))
      node_2463
      node_2470
      (invalid_excluded a [6,8,7,1,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,1,8] (by decide +kernel)))

theorem node_2475 : Excluded a [6,8,7,2,0] :=
  predecessor_excluded a [6,8,7,2,0] 1 6 4 0 (by decide) (by decide +kernel)

theorem node_2477 : Excluded a [6,8,7,2,1,0] :=
  source_excluded a [6,8,7,2,1,0] 5 1 0 (by decide) (by decide +kernel)

theorem node_2479 : Excluded a [6,8,7,2,1,3,0] :=
  predecessor_excluded a [6,8,7,2,1,3,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2480 : Excluded a [6,8,7,2,1,3,4] :=
  predecessor_excluded a [6,8,7,2,1,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_2482 : Excluded a [6,8,7,2,1,3,5,0] :=
  source_excluded a [6,8,7,2,1,3,5,0] 1 2 7 (by decide) (by decide +kernel)

theorem node_2483 : Excluded a [6,8,7,2,1,3,5,4] :=
  predecessor_excluded a [6,8,7,2,1,3,5,4] 0 4 2 7 (by decide) (by decide +kernel)

theorem node_2481 : Excluded a [6,8,7,2,1,3,5] :=
  branch_excluded a [6,8,7,2,1,3,5] (by decide)
    (fin9_cases _
      node_2482
      (invalid_excluded a [6,8,7,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,3] (by decide +kernel))
      node_2483
      (invalid_excluded a [6,8,7,2,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,5,8] (by decide +kernel)))

theorem node_2478 : Excluded a [6,8,7,2,1,3] :=
  branch_excluded a [6,8,7,2,1,3] (by decide)
    (fin9_cases _
      node_2479
      (invalid_excluded a [6,8,7,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,3] (by decide +kernel))
      node_2480
      node_2481
      (invalid_excluded a [6,8,7,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,3,8] (by decide +kernel)))

theorem node_2485 : Excluded a [6,8,7,2,1,4,0] :=
  predecessor_excluded a [6,8,7,2,1,4,0] 2 0 0 6 (by decide) (by decide +kernel)

theorem node_2486 : Excluded a [6,8,7,2,1,4,3] :=
  source_excluded a [6,8,7,2,1,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2487 : Excluded a [6,8,7,2,1,4,5] :=
  predecessor_excluded a [6,8,7,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2484 : Excluded a [6,8,7,2,1,4] :=
  branch_excluded a [6,8,7,2,1,4] (by decide)
    (fin9_cases _
      node_2485
      (invalid_excluded a [6,8,7,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,2] (by decide +kernel))
      node_2486
      (invalid_excluded a [6,8,7,2,1,4,4] (by decide +kernel))
      node_2487
      (invalid_excluded a [6,8,7,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,4,8] (by decide +kernel)))

theorem node_2476 : Excluded a [6,8,7,2,1] :=
  branch_excluded a [6,8,7,2,1] (by decide)
    (fin9_cases _
      node_2477
      (invalid_excluded a [6,8,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,2] (by decide +kernel))
      node_2478
      node_2484
      (invalid_excluded a [6,8,7,2,1,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,1,8] (by decide +kernel)))

theorem node_2488 : Excluded a [6,8,7,2,3] :=
  predecessor_excluded a [6,8,7,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2474 : Excluded a [6,8,7,2] :=
  branch_excluded a [6,8,7,2] (by decide)
    (fin9_cases _
      node_2475
      node_2476
      (invalid_excluded a [6,8,7,2,2] (by decide +kernel))
      node_2488
      (invalid_excluded a [6,8,7,2,4] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,5] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,2,8] (by decide +kernel)))

theorem node_2489 : Excluded a [6,8,7,5] :=
  source_excluded a [6,8,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2447 : Excluded a [6,8,7] :=
  branch_excluded a [6,8,7] (by decide)
    (fin9_cases _
      node_2448
      node_2461
      node_2474
      (invalid_excluded a [6,8,7,3] (by decide +kernel))
      (invalid_excluded a [6,8,7,4] (by decide +kernel))
      node_2489
      (invalid_excluded a [6,8,7,6] (by decide +kernel))
      (invalid_excluded a [6,8,7,7] (by decide +kernel))
      (invalid_excluded a [6,8,7,8] (by decide +kernel)))

theorem node_2320 : Excluded a [6,8] :=
  branch_excluded a [6,8] (by decide)
    (fin9_cases _
      node_2321
      node_2377
      (invalid_excluded a [6,8,2] (by decide +kernel))
      (invalid_excluded a [6,8,3] (by decide +kernel))
      node_2408
      node_2409
      (invalid_excluded a [6,8,6] (by decide +kernel))
      node_2447
      (invalid_excluded a [6,8,8] (by decide +kernel)))

theorem node_1938 : Excluded a [6] :=
  branch_excluded a [6] (by decide)
    (fin9_cases _
      (invalid_excluded a [6,0] (by decide +kernel))
      (invalid_excluded a [6,1] (by decide +kernel))
      node_1939
      node_2087
      node_2184
      node_2318
      (invalid_excluded a [6,6] (by decide +kernel))
      node_2319
      node_2320)

theorem node_2492 : Excluded a [7,2,0] :=
  source_excluded a [7,2,0] 1 3 2 (by decide) (by decide +kernel)

theorem node_2493 : Excluded a [7,2,1] :=
  predecessor_excluded a [7,2,1] 3 1 1 2 (by decide) (by decide +kernel)

theorem node_2494 : Excluded a [7,2,4] :=
  source_excluded a [7,2,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_2497 : Excluded a [7,2,5,0,1] :=
  predecessor_excluded a [7,2,5,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2498 : Excluded a [7,2,5,0,3] :=
  source_excluded a [7,2,5,0,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2499 : Excluded a [7,2,5,0,6] :=
  source_excluded a [7,2,5,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2503 : Excluded a [7,2,5,0,8,1,3,4] :=
  source_excluded a [7,2,5,0,8,1,3,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_2505 : Excluded a [7,2,5,0,8,1,3,6,4] :=
  predecessor_excluded a [7,2,5,0,8,1,3,6,4] 0 5 8 2 (by decide) (by decide +kernel)

theorem node_2504 : Excluded a [7,2,5,0,8,1,3,6] :=
  branch_excluded a [7,2,5,0,8,1,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,5,0,8,1,3,6,0] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,1,3,6,1] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,1,3,6,2] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,1,3,6,3] (by decide +kernel))
      node_2505
      (invalid_excluded a [7,2,5,0,8,1,3,6,5] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,1,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,1,3,6,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,1,3,6,8] (by decide +kernel)))

theorem node_2502 : Excluded a [7,2,5,0,8,1,3] :=
  branch_excluded a [7,2,5,0,8,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,5,0,8,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,1,3,1] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,1,3,2] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,1,3,3] (by decide +kernel))
      node_2503
      (invalid_excluded a [7,2,5,0,8,1,3,5] (by decide +kernel))
      node_2504
      (invalid_excluded a [7,2,5,0,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,1,3,8] (by decide +kernel)))

theorem node_2506 : Excluded a [7,2,5,0,8,1,4] :=
  predecessor_excluded a [7,2,5,0,8,1,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_2501 : Excluded a [7,2,5,0,8,1] :=
  branch_excluded a [7,2,5,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,5,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,1,2] (by decide +kernel))
      node_2502
      node_2506
      (invalid_excluded a [7,2,5,0,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,1,8] (by decide +kernel)))

theorem node_2507 : Excluded a [7,2,5,0,8,3] :=
  source_excluded a [7,2,5,0,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2508 : Excluded a [7,2,5,0,8,4] :=
  predecessor_excluded a [7,2,5,0,8,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2500 : Excluded a [7,2,5,0,8] :=
  branch_excluded a [7,2,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,5,0,8,0] (by decide +kernel))
      node_2501
      (invalid_excluded a [7,2,5,0,8,2] (by decide +kernel))
      node_2507
      node_2508
      (invalid_excluded a [7,2,5,0,8,5] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,8,8] (by decide +kernel)))

theorem node_2496 : Excluded a [7,2,5,0] :=
  branch_excluded a [7,2,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,5,0,0] (by decide +kernel))
      node_2497
      (invalid_excluded a [7,2,5,0,2] (by decide +kernel))
      node_2498
      (invalid_excluded a [7,2,5,0,4] (by decide +kernel))
      (invalid_excluded a [7,2,5,0,5] (by decide +kernel))
      node_2499
      (invalid_excluded a [7,2,5,0,7] (by decide +kernel))
      node_2500)

theorem node_2510 : Excluded a [7,2,5,1,0] :=
  predecessor_excluded a [7,2,5,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_2511 : Excluded a [7,2,5,1,3] :=
  source_excluded a [7,2,5,1,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2512 : Excluded a [7,2,5,1,6] :=
  source_excluded a [7,2,5,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2514 : Excluded a [7,2,5,1,8,0] :=
  predecessor_excluded a [7,2,5,1,8,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2515 : Excluded a [7,2,5,1,8,3] :=
  source_excluded a [7,2,5,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2516 : Excluded a [7,2,5,1,8,4] :=
  predecessor_excluded a [7,2,5,1,8,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2513 : Excluded a [7,2,5,1,8] :=
  branch_excluded a [7,2,5,1,8] (by decide)
    (fin9_cases _
      node_2514
      (invalid_excluded a [7,2,5,1,8,1] (by decide +kernel))
      (invalid_excluded a [7,2,5,1,8,2] (by decide +kernel))
      node_2515
      node_2516
      (invalid_excluded a [7,2,5,1,8,5] (by decide +kernel))
      (invalid_excluded a [7,2,5,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,2,5,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,1,8,8] (by decide +kernel)))

theorem node_2509 : Excluded a [7,2,5,1] :=
  branch_excluded a [7,2,5,1] (by decide)
    (fin9_cases _
      node_2510
      (invalid_excluded a [7,2,5,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,5,1,2] (by decide +kernel))
      node_2511
      (invalid_excluded a [7,2,5,1,4] (by decide +kernel))
      (invalid_excluded a [7,2,5,1,5] (by decide +kernel))
      node_2512
      (invalid_excluded a [7,2,5,1,7] (by decide +kernel))
      node_2513)

theorem node_2517 : Excluded a [7,2,5,6] :=
  predecessor_excluded a [7,2,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_2520 : Excluded a [7,2,5,8,0,1] :=
  predecessor_excluded a [7,2,5,8,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_2521 : Excluded a [7,2,5,8,0,3] :=
  source_excluded a [7,2,5,8,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2522 : Excluded a [7,2,5,8,0,4] :=
  predecessor_excluded a [7,2,5,8,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2519 : Excluded a [7,2,5,8,0] :=
  branch_excluded a [7,2,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,5,8,0,0] (by decide +kernel))
      node_2520
      (invalid_excluded a [7,2,5,8,0,2] (by decide +kernel))
      node_2521
      node_2522
      (invalid_excluded a [7,2,5,8,0,5] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,0,6] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,0,8] (by decide +kernel)))

theorem node_2524 : Excluded a [7,2,5,8,1,0] :=
  predecessor_excluded a [7,2,5,8,1,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2525 : Excluded a [7,2,5,8,1,3] :=
  source_excluded a [7,2,5,8,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2526 : Excluded a [7,2,5,8,1,4] :=
  predecessor_excluded a [7,2,5,8,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2523 : Excluded a [7,2,5,8,1] :=
  branch_excluded a [7,2,5,8,1] (by decide)
    (fin9_cases _
      node_2524
      (invalid_excluded a [7,2,5,8,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,1,2] (by decide +kernel))
      node_2525
      node_2526
      (invalid_excluded a [7,2,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,1,8] (by decide +kernel)))

theorem node_2527 : Excluded a [7,2,5,8,3] :=
  source_excluded a [7,2,5,8,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2528 : Excluded a [7,2,5,8,6] :=
  source_excluded a [7,2,5,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2518 : Excluded a [7,2,5,8] :=
  branch_excluded a [7,2,5,8] (by decide)
    (fin9_cases _
      node_2519
      node_2523
      (invalid_excluded a [7,2,5,8,2] (by decide +kernel))
      node_2527
      (invalid_excluded a [7,2,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,5] (by decide +kernel))
      node_2528
      (invalid_excluded a [7,2,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,2,5,8,8] (by decide +kernel)))

theorem node_2495 : Excluded a [7,2,5] :=
  branch_excluded a [7,2,5] (by decide)
    (fin9_cases _
      node_2496
      node_2509
      (invalid_excluded a [7,2,5,2] (by decide +kernel))
      (invalid_excluded a [7,2,5,3] (by decide +kernel))
      (invalid_excluded a [7,2,5,4] (by decide +kernel))
      (invalid_excluded a [7,2,5,5] (by decide +kernel))
      node_2517
      (invalid_excluded a [7,2,5,7] (by decide +kernel))
      node_2518)

theorem node_2531 : Excluded a [7,2,6,0,1] :=
  predecessor_excluded a [7,2,6,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2534 : Excluded a [7,2,6,0,3,1,4] :=
  predecessor_excluded a [7,2,6,0,3,1,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_2536 : Excluded a [7,2,6,0,3,1,5,4] :=
  branch_excluded a [7,2,6,0,3,1,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,3,1,5,4,0] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,5,4,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,5,4,2] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,5,4,3] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,5,4,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,5,4,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,5,4,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,5,4,8] (by decide +kernel)))

theorem node_2535 : Excluded a [7,2,6,0,3,1,5] :=
  branch_excluded a [7,2,6,0,3,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,3,1,5,0] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,5,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,5,2] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,5,3] (by decide +kernel))
      node_2536
      (invalid_excluded a [7,2,6,0,3,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,5,8] (by decide +kernel)))

theorem node_2537 : Excluded a [7,2,6,0,3,1,8] :=
  source_excluded a [7,2,6,0,3,1,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_2533 : Excluded a [7,2,6,0,3,1] :=
  branch_excluded a [7,2,6,0,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,3,1,0] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,2] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,3] (by decide +kernel))
      node_2534
      node_2535
      (invalid_excluded a [7,2,6,0,3,1,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,1,7] (by decide +kernel))
      node_2537)

theorem node_2538 : Excluded a [7,2,6,0,3,4] :=
  predecessor_excluded a [7,2,6,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2540 : Excluded a [7,2,6,0,3,8,1] :=
  source_excluded a [7,2,6,0,3,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2541 : Excluded a [7,2,6,0,3,8,4] :=
  predecessor_excluded a [7,2,6,0,3,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_2542 : Excluded a [7,2,6,0,3,8,5] :=
  predecessor_excluded a [7,2,6,0,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_2539 : Excluded a [7,2,6,0,3,8] :=
  branch_excluded a [7,2,6,0,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,3,8,0] (by decide +kernel))
      node_2540
      (invalid_excluded a [7,2,6,0,3,8,2] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,8,3] (by decide +kernel))
      node_2541
      node_2542
      (invalid_excluded a [7,2,6,0,3,8,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,8,8] (by decide +kernel)))

theorem node_2532 : Excluded a [7,2,6,0,3] :=
  branch_excluded a [7,2,6,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,3,0] (by decide +kernel))
      node_2533
      (invalid_excluded a [7,2,6,0,3,2] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,3] (by decide +kernel))
      node_2538
      (invalid_excluded a [7,2,6,0,3,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,3,7] (by decide +kernel))
      node_2539)

theorem node_2545 : Excluded a [7,2,6,0,8,1,3] :=
  source_excluded a [7,2,6,0,8,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2546 : Excluded a [7,2,6,0,8,1,4] :=
  predecessor_excluded a [7,2,6,0,8,1,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_2549 : Excluded a [7,2,6,0,8,1,5,3,4] :=
  predecessor_excluded a [7,2,6,0,8,1,5,3,4] 0 4 7 8 (by decide) (by decide +kernel)

theorem node_2548 : Excluded a [7,2,6,0,8,1,5,3] :=
  branch_excluded a [7,2,6,0,8,1,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,8,1,5,3,0] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,3,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,3,2] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,3,3] (by decide +kernel))
      node_2549
      (invalid_excluded a [7,2,6,0,8,1,5,3,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,3,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,3,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,3,8] (by decide +kernel)))

theorem node_2550 : Excluded a [7,2,6,0,8,1,5,4] :=
  source_excluded a [7,2,6,0,8,1,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_2547 : Excluded a [7,2,6,0,8,1,5] :=
  branch_excluded a [7,2,6,0,8,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,8,1,5,0] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,2] (by decide +kernel))
      node_2548
      node_2550
      (invalid_excluded a [7,2,6,0,8,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,5,8] (by decide +kernel)))

theorem node_2544 : Excluded a [7,2,6,0,8,1] :=
  branch_excluded a [7,2,6,0,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,8,1,0] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,2] (by decide +kernel))
      node_2545
      node_2546
      node_2547
      (invalid_excluded a [7,2,6,0,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,1,8] (by decide +kernel)))

theorem node_2551 : Excluded a [7,2,6,0,8,3] :=
  source_excluded a [7,2,6,0,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2553 : Excluded a [7,2,6,0,8,4,1] :=
  source_excluded a [7,2,6,0,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2554 : Excluded a [7,2,6,0,8,4,3] :=
  source_excluded a [7,2,6,0,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2555 : Excluded a [7,2,6,0,8,4,5] :=
  predecessor_excluded a [7,2,6,0,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2552 : Excluded a [7,2,6,0,8,4] :=
  branch_excluded a [7,2,6,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,8,4,0] (by decide +kernel))
      node_2553
      (invalid_excluded a [7,2,6,0,8,4,2] (by decide +kernel))
      node_2554
      (invalid_excluded a [7,2,6,0,8,4,4] (by decide +kernel))
      node_2555
      (invalid_excluded a [7,2,6,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,4,8] (by decide +kernel)))

theorem node_2543 : Excluded a [7,2,6,0,8] :=
  branch_excluded a [7,2,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,8,0] (by decide +kernel))
      node_2544
      (invalid_excluded a [7,2,6,0,8,2] (by decide +kernel))
      node_2551
      node_2552
      (invalid_excluded a [7,2,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,8,8] (by decide +kernel)))

theorem node_2530 : Excluded a [7,2,6,0] :=
  branch_excluded a [7,2,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,0,0] (by decide +kernel))
      node_2531
      (invalid_excluded a [7,2,6,0,2] (by decide +kernel))
      node_2532
      (invalid_excluded a [7,2,6,0,4] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,0,7] (by decide +kernel))
      node_2543)

theorem node_2557 : Excluded a [7,2,6,1,0] :=
  predecessor_excluded a [7,2,6,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_2559 : Excluded a [7,2,6,1,3,0] :=
  predecessor_excluded a [7,2,6,1,3,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2560 : Excluded a [7,2,6,1,3,4] :=
  predecessor_excluded a [7,2,6,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2562 : Excluded a [7,2,6,1,3,8,0] :=
  source_excluded a [7,2,6,1,3,8,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2563 : Excluded a [7,2,6,1,3,8,4] :=
  predecessor_excluded a [7,2,6,1,3,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_2564 : Excluded a [7,2,6,1,3,8,5] :=
  predecessor_excluded a [7,2,6,1,3,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_2561 : Excluded a [7,2,6,1,3,8] :=
  branch_excluded a [7,2,6,1,3,8] (by decide)
    (fin9_cases _
      node_2562
      (invalid_excluded a [7,2,6,1,3,8,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,3,8,2] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,3,8,3] (by decide +kernel))
      node_2563
      node_2564
      (invalid_excluded a [7,2,6,1,3,8,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,3,8,8] (by decide +kernel)))

theorem node_2558 : Excluded a [7,2,6,1,3] :=
  branch_excluded a [7,2,6,1,3] (by decide)
    (fin9_cases _
      node_2559
      (invalid_excluded a [7,2,6,1,3,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,3,2] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,3,3] (by decide +kernel))
      node_2560
      (invalid_excluded a [7,2,6,1,3,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,3,7] (by decide +kernel))
      node_2561)

theorem node_2566 : Excluded a [7,2,6,1,8,0] :=
  predecessor_excluded a [7,2,6,1,8,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2567 : Excluded a [7,2,6,1,8,3] :=
  source_excluded a [7,2,6,1,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2569 : Excluded a [7,2,6,1,8,4,0] :=
  source_excluded a [7,2,6,1,8,4,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2570 : Excluded a [7,2,6,1,8,4,3] :=
  source_excluded a [7,2,6,1,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2571 : Excluded a [7,2,6,1,8,4,5] :=
  predecessor_excluded a [7,2,6,1,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2568 : Excluded a [7,2,6,1,8,4] :=
  branch_excluded a [7,2,6,1,8,4] (by decide)
    (fin9_cases _
      node_2569
      (invalid_excluded a [7,2,6,1,8,4,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,8,4,2] (by decide +kernel))
      node_2570
      (invalid_excluded a [7,2,6,1,8,4,4] (by decide +kernel))
      node_2571
      (invalid_excluded a [7,2,6,1,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,8,4,8] (by decide +kernel)))

theorem node_2565 : Excluded a [7,2,6,1,8] :=
  branch_excluded a [7,2,6,1,8] (by decide)
    (fin9_cases _
      node_2566
      (invalid_excluded a [7,2,6,1,8,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,8,2] (by decide +kernel))
      node_2567
      node_2568
      (invalid_excluded a [7,2,6,1,8,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,8,8] (by decide +kernel)))

theorem node_2556 : Excluded a [7,2,6,1] :=
  branch_excluded a [7,2,6,1] (by decide)
    (fin9_cases _
      node_2557
      (invalid_excluded a [7,2,6,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,2] (by decide +kernel))
      node_2558
      (invalid_excluded a [7,2,6,1,4] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,1,7] (by decide +kernel))
      node_2565)

theorem node_2572 : Excluded a [7,2,6,5] :=
  source_excluded a [7,2,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2575 : Excluded a [7,2,6,8,0,1] :=
  predecessor_excluded a [7,2,6,8,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_2576 : Excluded a [7,2,6,8,0,3] :=
  source_excluded a [7,2,6,8,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2578 : Excluded a [7,2,6,8,0,4,1] :=
  source_excluded a [7,2,6,8,0,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2579 : Excluded a [7,2,6,8,0,4,3] :=
  source_excluded a [7,2,6,8,0,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2580 : Excluded a [7,2,6,8,0,4,5] :=
  predecessor_excluded a [7,2,6,8,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2577 : Excluded a [7,2,6,8,0,4] :=
  branch_excluded a [7,2,6,8,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,8,0,4,0] (by decide +kernel))
      node_2578
      (invalid_excluded a [7,2,6,8,0,4,2] (by decide +kernel))
      node_2579
      (invalid_excluded a [7,2,6,8,0,4,4] (by decide +kernel))
      node_2580
      (invalid_excluded a [7,2,6,8,0,4,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,0,4,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,0,4,8] (by decide +kernel)))

theorem node_2574 : Excluded a [7,2,6,8,0] :=
  branch_excluded a [7,2,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,6,8,0,0] (by decide +kernel))
      node_2575
      (invalid_excluded a [7,2,6,8,0,2] (by decide +kernel))
      node_2576
      node_2577
      (invalid_excluded a [7,2,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,0,8] (by decide +kernel)))

theorem node_2582 : Excluded a [7,2,6,8,1,0] :=
  predecessor_excluded a [7,2,6,8,1,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2583 : Excluded a [7,2,6,8,1,3] :=
  source_excluded a [7,2,6,8,1,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2585 : Excluded a [7,2,6,8,1,4,0] :=
  source_excluded a [7,2,6,8,1,4,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2586 : Excluded a [7,2,6,8,1,4,3] :=
  source_excluded a [7,2,6,8,1,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2587 : Excluded a [7,2,6,8,1,4,5] :=
  predecessor_excluded a [7,2,6,8,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2584 : Excluded a [7,2,6,8,1,4] :=
  branch_excluded a [7,2,6,8,1,4] (by decide)
    (fin9_cases _
      node_2585
      (invalid_excluded a [7,2,6,8,1,4,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,1,4,2] (by decide +kernel))
      node_2586
      (invalid_excluded a [7,2,6,8,1,4,4] (by decide +kernel))
      node_2587
      (invalid_excluded a [7,2,6,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,1,4,8] (by decide +kernel)))

theorem node_2581 : Excluded a [7,2,6,8,1] :=
  branch_excluded a [7,2,6,8,1] (by decide)
    (fin9_cases _
      node_2582
      (invalid_excluded a [7,2,6,8,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,1,2] (by decide +kernel))
      node_2583
      node_2584
      (invalid_excluded a [7,2,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,1,8] (by decide +kernel)))

theorem node_2589 : Excluded a [7,2,6,8,3,0] :=
  predecessor_excluded a [7,2,6,8,3,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2591 : Excluded a [7,2,6,8,3,1,0] :=
  source_excluded a [7,2,6,8,3,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2592 : Excluded a [7,2,6,8,3,1,4] :=
  predecessor_excluded a [7,2,6,8,3,1,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_2594 : Excluded a [7,2,6,8,3,1,5,0] :=
  predecessor_excluded a [7,2,6,8,3,1,5,0] 2 0 0 7 (by decide) (by decide +kernel)

theorem node_2595 : Excluded a [7,2,6,8,3,1,5,4] :=
  source_excluded a [7,2,6,8,3,1,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_2593 : Excluded a [7,2,6,8,3,1,5] :=
  branch_excluded a [7,2,6,8,3,1,5] (by decide)
    (fin9_cases _
      node_2594
      (invalid_excluded a [7,2,6,8,3,1,5,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,3,1,5,2] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,3,1,5,3] (by decide +kernel))
      node_2595
      (invalid_excluded a [7,2,6,8,3,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,3,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,3,1,5,8] (by decide +kernel)))

theorem node_2590 : Excluded a [7,2,6,8,3,1] :=
  branch_excluded a [7,2,6,8,3,1] (by decide)
    (fin9_cases _
      node_2591
      (invalid_excluded a [7,2,6,8,3,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,3,1,2] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,3,1,3] (by decide +kernel))
      node_2592
      node_2593
      (invalid_excluded a [7,2,6,8,3,1,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,3,1,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,3,1,8] (by decide +kernel)))

theorem node_2596 : Excluded a [7,2,6,8,3,4] :=
  predecessor_excluded a [7,2,6,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2588 : Excluded a [7,2,6,8,3] :=
  branch_excluded a [7,2,6,8,3] (by decide)
    (fin9_cases _
      node_2589
      node_2590
      (invalid_excluded a [7,2,6,8,3,2] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,3,3] (by decide +kernel))
      node_2596
      (invalid_excluded a [7,2,6,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,3,8] (by decide +kernel)))

theorem node_2573 : Excluded a [7,2,6,8] :=
  branch_excluded a [7,2,6,8] (by decide)
    (fin9_cases _
      node_2574
      node_2581
      (invalid_excluded a [7,2,6,8,2] (by decide +kernel))
      node_2588
      (invalid_excluded a [7,2,6,8,4] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,2,6,8,8] (by decide +kernel)))

theorem node_2529 : Excluded a [7,2,6] :=
  branch_excluded a [7,2,6] (by decide)
    (fin9_cases _
      node_2530
      node_2556
      (invalid_excluded a [7,2,6,2] (by decide +kernel))
      (invalid_excluded a [7,2,6,3] (by decide +kernel))
      (invalid_excluded a [7,2,6,4] (by decide +kernel))
      node_2572
      (invalid_excluded a [7,2,6,6] (by decide +kernel))
      (invalid_excluded a [7,2,6,7] (by decide +kernel))
      node_2573)

theorem node_2599 : Excluded a [7,2,8,0,1] :=
  predecessor_excluded a [7,2,8,0,1] 2 1 3 4 (by decide) (by decide +kernel)

theorem node_2603 : Excluded a [7,2,8,0,3,1,4,5] :=
  predecessor_excluded a [7,2,8,0,3,1,4,5] 0 5 6 7 (by decide) (by decide +kernel)

def b_2605 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 2
  | 2 => 8
  | 3 => 0
  | 4 => 3
  | 5 => 1
  | 6 => 4
  | 7 => 6
  | 8 => 5
  | _ => 0

def cert_2605 : LosingRegion (edgeOf a b_2605) 0 :=
  losingMask a b_2605 0 1286514411582720882770944
    (by decide +kernel) (by decide +kernel)

theorem node_2605 : Excluded a [7,2,8,0,3,1,4,6,5] :=
  losing_excluded a [7,2,8,0,3,1,4,6,5] (by decide) b_2605 (by decide +kernel) 2 0 3 cert_2605 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2605 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1286514411582720882770944 2 3; decide +kernel)

theorem node_2604 : Excluded a [7,2,8,0,3,1,4,6] :=
  branch_excluded a [7,2,8,0,3,1,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,3,1,4,6,0] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,4,6,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,4,6,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,4,6,3] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,4,6,4] (by decide +kernel))
      node_2605
      (invalid_excluded a [7,2,8,0,3,1,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,4,6,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,4,6,8] (by decide +kernel)))

theorem node_2602 : Excluded a [7,2,8,0,3,1,4] :=
  branch_excluded a [7,2,8,0,3,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,3,1,4,0] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,4,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,4,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,4,3] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,4,4] (by decide +kernel))
      node_2603
      node_2604
      (invalid_excluded a [7,2,8,0,3,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,4,8] (by decide +kernel)))

def b_2608 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 2
  | 2 => 8
  | 3 => 0
  | 4 => 3
  | 5 => 1
  | 6 => 5
  | 7 => 4
  | 8 => 6
  | _ => 0

def cert_2608 : LosingRegion (edgeOf a b_2608) 0 :=
  losingMask a b_2608 0 1956500210489150197990400
    (by decide +kernel) (by decide +kernel)

theorem node_2608 : Excluded a [7,2,8,0,3,1,5,4,6] :=
  losing_excluded a [7,2,8,0,3,1,5,4,6] (by decide) b_2608 (by decide +kernel) 2 0 3 cert_2608 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2608 2 0 ∧ 3 ≠ 2 ∧ maskRegion 1956500210489150197990400 2 3; decide +kernel)

theorem node_2607 : Excluded a [7,2,8,0,3,1,5,4] :=
  branch_excluded a [7,2,8,0,3,1,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,3,1,5,4,0] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,5,4,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,5,4,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,5,4,3] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,5,4,4] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,5,4,5] (by decide +kernel))
      node_2608
      (invalid_excluded a [7,2,8,0,3,1,5,4,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,5,4,8] (by decide +kernel)))

theorem node_2609 : Excluded a [7,2,8,0,3,1,5,6] :=
  predecessor_excluded a [7,2,8,0,3,1,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_2606 : Excluded a [7,2,8,0,3,1,5] :=
  branch_excluded a [7,2,8,0,3,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,3,1,5,0] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,5,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,5,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,5,3] (by decide +kernel))
      node_2607
      (invalid_excluded a [7,2,8,0,3,1,5,5] (by decide +kernel))
      node_2609
      (invalid_excluded a [7,2,8,0,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,5,8] (by decide +kernel)))

theorem node_2601 : Excluded a [7,2,8,0,3,1] :=
  branch_excluded a [7,2,8,0,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,3,1,0] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,3] (by decide +kernel))
      node_2602
      node_2606
      (invalid_excluded a [7,2,8,0,3,1,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,1,8] (by decide +kernel)))

theorem node_2610 : Excluded a [7,2,8,0,3,4] :=
  predecessor_excluded a [7,2,8,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2600 : Excluded a [7,2,8,0,3] :=
  branch_excluded a [7,2,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,3,0] (by decide +kernel))
      node_2601
      (invalid_excluded a [7,2,8,0,3,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,3] (by decide +kernel))
      node_2610
      (invalid_excluded a [7,2,8,0,3,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,3,8] (by decide +kernel)))

theorem node_2611 : Excluded a [7,2,8,0,6] :=
  source_excluded a [7,2,8,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2598 : Excluded a [7,2,8,0] :=
  branch_excluded a [7,2,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,0,0] (by decide +kernel))
      node_2599
      (invalid_excluded a [7,2,8,0,2] (by decide +kernel))
      node_2600
      (invalid_excluded a [7,2,8,0,4] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,5] (by decide +kernel))
      node_2611
      (invalid_excluded a [7,2,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,0,8] (by decide +kernel)))

theorem node_2613 : Excluded a [7,2,8,1,0] :=
  predecessor_excluded a [7,2,8,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_2615 : Excluded a [7,2,8,1,3,0] :=
  predecessor_excluded a [7,2,8,1,3,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2616 : Excluded a [7,2,8,1,3,4] :=
  predecessor_excluded a [7,2,8,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2614 : Excluded a [7,2,8,1,3] :=
  branch_excluded a [7,2,8,1,3] (by decide)
    (fin9_cases _
      node_2615
      (invalid_excluded a [7,2,8,1,3,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,1,3,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,1,3,3] (by decide +kernel))
      node_2616
      (invalid_excluded a [7,2,8,1,3,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,1,3,8] (by decide +kernel)))

theorem node_2617 : Excluded a [7,2,8,1,6] :=
  source_excluded a [7,2,8,1,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2612 : Excluded a [7,2,8,1] :=
  branch_excluded a [7,2,8,1] (by decide)
    (fin9_cases _
      node_2613
      (invalid_excluded a [7,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,1,2] (by decide +kernel))
      node_2614
      (invalid_excluded a [7,2,8,1,4] (by decide +kernel))
      (invalid_excluded a [7,2,8,1,5] (by decide +kernel))
      node_2617
      (invalid_excluded a [7,2,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,1,8] (by decide +kernel)))

theorem node_2618 : Excluded a [7,2,8,5] :=
  source_excluded a [7,2,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2621 : Excluded a [7,2,8,6,0,1] :=
  predecessor_excluded a [7,2,8,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_2622 : Excluded a [7,2,8,6,0,3] :=
  source_excluded a [7,2,8,6,0,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2623 : Excluded a [7,2,8,6,0,4] :=
  source_excluded a [7,2,8,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2620 : Excluded a [7,2,8,6,0] :=
  branch_excluded a [7,2,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,2,8,6,0,0] (by decide +kernel))
      node_2621
      (invalid_excluded a [7,2,8,6,0,2] (by decide +kernel))
      node_2622
      node_2623
      (invalid_excluded a [7,2,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,0,8] (by decide +kernel)))

theorem node_2625 : Excluded a [7,2,8,6,1,0] :=
  predecessor_excluded a [7,2,8,6,1,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2626 : Excluded a [7,2,8,6,1,3] :=
  source_excluded a [7,2,8,6,1,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2627 : Excluded a [7,2,8,6,1,4] :=
  source_excluded a [7,2,8,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2624 : Excluded a [7,2,8,6,1] :=
  branch_excluded a [7,2,8,6,1] (by decide)
    (fin9_cases _
      node_2625
      (invalid_excluded a [7,2,8,6,1,1] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,1,2] (by decide +kernel))
      node_2626
      node_2627
      (invalid_excluded a [7,2,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,1,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,1,8] (by decide +kernel)))

theorem node_2628 : Excluded a [7,2,8,6,3] :=
  predecessor_excluded a [7,2,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2619 : Excluded a [7,2,8,6] :=
  branch_excluded a [7,2,8,6] (by decide)
    (fin9_cases _
      node_2620
      node_2624
      (invalid_excluded a [7,2,8,6,2] (by decide +kernel))
      node_2628
      (invalid_excluded a [7,2,8,6,4] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,6,8] (by decide +kernel)))

theorem node_2597 : Excluded a [7,2,8] :=
  branch_excluded a [7,2,8] (by decide)
    (fin9_cases _
      node_2598
      node_2612
      (invalid_excluded a [7,2,8,2] (by decide +kernel))
      (invalid_excluded a [7,2,8,3] (by decide +kernel))
      (invalid_excluded a [7,2,8,4] (by decide +kernel))
      node_2618
      node_2619
      (invalid_excluded a [7,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,2,8,8] (by decide +kernel)))

theorem node_2491 : Excluded a [7,2] :=
  branch_excluded a [7,2] (by decide)
    (fin9_cases _
      node_2492
      node_2493
      (invalid_excluded a [7,2,2] (by decide +kernel))
      (invalid_excluded a [7,2,3] (by decide +kernel))
      node_2494
      node_2495
      node_2529
      (invalid_excluded a [7,2,7] (by decide +kernel))
      node_2597)

theorem node_2630 : Excluded a [7,3,0] :=
  source_excluded a [7,3,0] 1 2 2 (by decide) (by decide +kernel)

theorem node_2631 : Excluded a [7,3,1] :=
  source_excluded a [7,3,1] 2 0 1 (by decide) (by decide +kernel)

theorem node_2632 : Excluded a [7,3,4] :=
  source_excluded a [7,3,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_2634 : Excluded a [7,3,5,0] :=
  source_excluded a [7,3,5,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2635 : Excluded a [7,3,5,1] :=
  predecessor_excluded a [7,3,5,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_2636 : Excluded a [7,3,5,2] :=
  predecessor_excluded a [7,3,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_2637 : Excluded a [7,3,5,6] :=
  predecessor_excluded a [7,3,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_2640 : Excluded a [7,3,5,8,0,1] :=
  predecessor_excluded a [7,3,5,8,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_2642 : Excluded a [7,3,5,8,0,2,1] :=
  source_excluded a [7,3,5,8,0,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2644 : Excluded a [7,3,5,8,0,2,4,1] :=
  source_excluded a [7,3,5,8,0,2,4,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2646 : Excluded a [7,3,5,8,0,2,4,6,1] :=
  predecessor_excluded a [7,3,5,8,0,2,4,6,1] 0 3 8 1 (by decide) (by decide +kernel)

theorem node_2645 : Excluded a [7,3,5,8,0,2,4,6] :=
  branch_excluded a [7,3,5,8,0,2,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,5,8,0,2,4,6,0] (by decide +kernel))
      node_2646
      (invalid_excluded a [7,3,5,8,0,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,6,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,6,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,6,8] (by decide +kernel)))

theorem node_2643 : Excluded a [7,3,5,8,0,2,4] :=
  branch_excluded a [7,3,5,8,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,5,8,0,2,4,0] (by decide +kernel))
      node_2644
      (invalid_excluded a [7,3,5,8,0,2,4,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,5] (by decide +kernel))
      node_2645
      (invalid_excluded a [7,3,5,8,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,4,8] (by decide +kernel)))

theorem node_2641 : Excluded a [7,3,5,8,0,2] :=
  branch_excluded a [7,3,5,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,5,8,0,2,0] (by decide +kernel))
      node_2642
      (invalid_excluded a [7,3,5,8,0,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,3] (by decide +kernel))
      node_2643
      (invalid_excluded a [7,3,5,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,2,8] (by decide +kernel)))

theorem node_2647 : Excluded a [7,3,5,8,0,4] :=
  predecessor_excluded a [7,3,5,8,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2639 : Excluded a [7,3,5,8,0] :=
  branch_excluded a [7,3,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,5,8,0,0] (by decide +kernel))
      node_2640
      node_2641
      (invalid_excluded a [7,3,5,8,0,3] (by decide +kernel))
      node_2647
      (invalid_excluded a [7,3,5,8,0,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,0,8] (by decide +kernel)))

theorem node_2649 : Excluded a [7,3,5,8,1,0] :=
  predecessor_excluded a [7,3,5,8,1,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2651 : Excluded a [7,3,5,8,1,2,0] :=
  source_excluded a [7,3,5,8,1,2,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2653 : Excluded a [7,3,5,8,1,2,4,0] :=
  predecessor_excluded a [7,3,5,8,1,2,4,0] 2 0 0 7 (by decide) (by decide +kernel)

def b_2655 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 3
  | 2 => 5
  | 3 => 8
  | 4 => 1
  | 5 => 2
  | 6 => 4
  | 7 => 6
  | 8 => 0
  | _ => 0

def cert_2655 : LosingRegion (edgeOf a b_2655) 0 :=
  losingMask a b_2655 0 1212547362199538230625280
    (by decide +kernel) (by decide +kernel)

theorem node_2655 : Excluded a [7,3,5,8,1,2,4,6,0] :=
  losing_excluded a [7,3,5,8,1,2,4,6,0] (by decide) b_2655 (by decide +kernel) 2 0 1 cert_2655 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2655 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1212547362199538230625280 2 1; decide +kernel)

theorem node_2654 : Excluded a [7,3,5,8,1,2,4,6] :=
  branch_excluded a [7,3,5,8,1,2,4,6] (by decide)
    (fin9_cases _
      node_2655
      (invalid_excluded a [7,3,5,8,1,2,4,6,1] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,4,6,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,4,6,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,4,6,8] (by decide +kernel)))

theorem node_2652 : Excluded a [7,3,5,8,1,2,4] :=
  branch_excluded a [7,3,5,8,1,2,4] (by decide)
    (fin9_cases _
      node_2653
      (invalid_excluded a [7,3,5,8,1,2,4,1] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,4,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,4,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,4,5] (by decide +kernel))
      node_2654
      (invalid_excluded a [7,3,5,8,1,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,4,8] (by decide +kernel)))

theorem node_2650 : Excluded a [7,3,5,8,1,2] :=
  branch_excluded a [7,3,5,8,1,2] (by decide)
    (fin9_cases _
      node_2651
      (invalid_excluded a [7,3,5,8,1,2,1] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,3] (by decide +kernel))
      node_2652
      (invalid_excluded a [7,3,5,8,1,2,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,2,8] (by decide +kernel)))

theorem node_2656 : Excluded a [7,3,5,8,1,4] :=
  predecessor_excluded a [7,3,5,8,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_2648 : Excluded a [7,3,5,8,1] :=
  branch_excluded a [7,3,5,8,1] (by decide)
    (fin9_cases _
      node_2649
      (invalid_excluded a [7,3,5,8,1,1] (by decide +kernel))
      node_2650
      (invalid_excluded a [7,3,5,8,1,3] (by decide +kernel))
      node_2656
      (invalid_excluded a [7,3,5,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,1,8] (by decide +kernel)))

theorem node_2657 : Excluded a [7,3,5,8,2] :=
  source_excluded a [7,3,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2658 : Excluded a [7,3,5,8,6] :=
  source_excluded a [7,3,5,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2638 : Excluded a [7,3,5,8] :=
  branch_excluded a [7,3,5,8] (by decide)
    (fin9_cases _
      node_2639
      node_2648
      node_2657
      (invalid_excluded a [7,3,5,8,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,5] (by decide +kernel))
      node_2658
      (invalid_excluded a [7,3,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,5,8,8] (by decide +kernel)))

theorem node_2633 : Excluded a [7,3,5] :=
  branch_excluded a [7,3,5] (by decide)
    (fin9_cases _
      node_2634
      node_2635
      node_2636
      (invalid_excluded a [7,3,5,3] (by decide +kernel))
      (invalid_excluded a [7,3,5,4] (by decide +kernel))
      (invalid_excluded a [7,3,5,5] (by decide +kernel))
      node_2637
      (invalid_excluded a [7,3,5,7] (by decide +kernel))
      node_2638)

theorem node_2660 : Excluded a [7,3,6,0] :=
  source_excluded a [7,3,6,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2661 : Excluded a [7,3,6,1] :=
  predecessor_excluded a [7,3,6,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_2664 : Excluded a [7,3,6,2,0,1] :=
  predecessor_excluded a [7,3,6,2,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_2666 : Excluded a [7,3,6,2,0,4,1] :=
  source_excluded a [7,3,6,2,0,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2667 : Excluded a [7,3,6,2,0,4,5] :=
  predecessor_excluded a [7,3,6,2,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2668 : Excluded a [7,3,6,2,0,4,8] :=
  source_excluded a [7,3,6,2,0,4,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_2665 : Excluded a [7,3,6,2,0,4] :=
  branch_excluded a [7,3,6,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,2,0,4,0] (by decide +kernel))
      node_2666
      (invalid_excluded a [7,3,6,2,0,4,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,0,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,0,4,4] (by decide +kernel))
      node_2667
      (invalid_excluded a [7,3,6,2,0,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,0,4,7] (by decide +kernel))
      node_2668)

theorem node_2670 : Excluded a [7,3,6,2,0,8,1] :=
  source_excluded a [7,3,6,2,0,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2671 : Excluded a [7,3,6,2,0,8,4] :=
  predecessor_excluded a [7,3,6,2,0,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_2672 : Excluded a [7,3,6,2,0,8,5] :=
  predecessor_excluded a [7,3,6,2,0,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_2669 : Excluded a [7,3,6,2,0,8] :=
  branch_excluded a [7,3,6,2,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,2,0,8,0] (by decide +kernel))
      node_2670
      (invalid_excluded a [7,3,6,2,0,8,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,0,8,3] (by decide +kernel))
      node_2671
      node_2672
      (invalid_excluded a [7,3,6,2,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,0,8,8] (by decide +kernel)))

theorem node_2663 : Excluded a [7,3,6,2,0] :=
  branch_excluded a [7,3,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,2,0,0] (by decide +kernel))
      node_2664
      (invalid_excluded a [7,3,6,2,0,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,0,3] (by decide +kernel))
      node_2665
      (invalid_excluded a [7,3,6,2,0,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,0,7] (by decide +kernel))
      node_2669)

theorem node_2674 : Excluded a [7,3,6,2,1,0] :=
  predecessor_excluded a [7,3,6,2,1,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2676 : Excluded a [7,3,6,2,1,4,0] :=
  source_excluded a [7,3,6,2,1,4,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2677 : Excluded a [7,3,6,2,1,4,5] :=
  predecessor_excluded a [7,3,6,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2678 : Excluded a [7,3,6,2,1,4,8] :=
  source_excluded a [7,3,6,2,1,4,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_2675 : Excluded a [7,3,6,2,1,4] :=
  branch_excluded a [7,3,6,2,1,4] (by decide)
    (fin9_cases _
      node_2676
      (invalid_excluded a [7,3,6,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,1,4,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,1,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,1,4,4] (by decide +kernel))
      node_2677
      (invalid_excluded a [7,3,6,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,1,4,7] (by decide +kernel))
      node_2678)

theorem node_2680 : Excluded a [7,3,6,2,1,8,0] :=
  source_excluded a [7,3,6,2,1,8,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2681 : Excluded a [7,3,6,2,1,8,4] :=
  predecessor_excluded a [7,3,6,2,1,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_2682 : Excluded a [7,3,6,2,1,8,5] :=
  predecessor_excluded a [7,3,6,2,1,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_2679 : Excluded a [7,3,6,2,1,8] :=
  branch_excluded a [7,3,6,2,1,8] (by decide)
    (fin9_cases _
      node_2680
      (invalid_excluded a [7,3,6,2,1,8,1] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,1,8,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,1,8,3] (by decide +kernel))
      node_2681
      node_2682
      (invalid_excluded a [7,3,6,2,1,8,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,1,8,8] (by decide +kernel)))

theorem node_2673 : Excluded a [7,3,6,2,1] :=
  branch_excluded a [7,3,6,2,1] (by decide)
    (fin9_cases _
      node_2674
      (invalid_excluded a [7,3,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,1,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,1,3] (by decide +kernel))
      node_2675
      (invalid_excluded a [7,3,6,2,1,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,1,7] (by decide +kernel))
      node_2679)

theorem node_2684 : Excluded a [7,3,6,2,8,0] :=
  predecessor_excluded a [7,3,6,2,8,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2686 : Excluded a [7,3,6,2,8,1,0] :=
  source_excluded a [7,3,6,2,8,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2687 : Excluded a [7,3,6,2,8,1,4] :=
  predecessor_excluded a [7,3,6,2,8,1,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_2689 : Excluded a [7,3,6,2,8,1,5,0] :=
  predecessor_excluded a [7,3,6,2,8,1,5,0] 2 0 0 7 (by decide) (by decide +kernel)

theorem node_2690 : Excluded a [7,3,6,2,8,1,5,4] :=
  source_excluded a [7,3,6,2,8,1,5,4] 7 0 4 (by decide) (by decide +kernel)

theorem node_2688 : Excluded a [7,3,6,2,8,1,5] :=
  branch_excluded a [7,3,6,2,8,1,5] (by decide)
    (fin9_cases _
      node_2689
      (invalid_excluded a [7,3,6,2,8,1,5,1] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,1,5,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,1,5,3] (by decide +kernel))
      node_2690
      (invalid_excluded a [7,3,6,2,8,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,1,5,8] (by decide +kernel)))

theorem node_2685 : Excluded a [7,3,6,2,8,1] :=
  branch_excluded a [7,3,6,2,8,1] (by decide)
    (fin9_cases _
      node_2686
      (invalid_excluded a [7,3,6,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,1,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,1,3] (by decide +kernel))
      node_2687
      node_2688
      (invalid_excluded a [7,3,6,2,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,1,8] (by decide +kernel)))

theorem node_2692 : Excluded a [7,3,6,2,8,4,0] :=
  source_excluded a [7,3,6,2,8,4,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2693 : Excluded a [7,3,6,2,8,4,1] :=
  source_excluded a [7,3,6,2,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2694 : Excluded a [7,3,6,2,8,4,5] :=
  predecessor_excluded a [7,3,6,2,8,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2691 : Excluded a [7,3,6,2,8,4] :=
  branch_excluded a [7,3,6,2,8,4] (by decide)
    (fin9_cases _
      node_2692
      node_2693
      (invalid_excluded a [7,3,6,2,8,4,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,4,4] (by decide +kernel))
      node_2694
      (invalid_excluded a [7,3,6,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,4,8] (by decide +kernel)))

theorem node_2683 : Excluded a [7,3,6,2,8] :=
  branch_excluded a [7,3,6,2,8] (by decide)
    (fin9_cases _
      node_2684
      node_2685
      (invalid_excluded a [7,3,6,2,8,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,3] (by decide +kernel))
      node_2691
      (invalid_excluded a [7,3,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,8,8] (by decide +kernel)))

theorem node_2662 : Excluded a [7,3,6,2] :=
  branch_excluded a [7,3,6,2] (by decide)
    (fin9_cases _
      node_2663
      node_2673
      (invalid_excluded a [7,3,6,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,4] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,2,7] (by decide +kernel))
      node_2683)

theorem node_2695 : Excluded a [7,3,6,5] :=
  source_excluded a [7,3,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2698 : Excluded a [7,3,6,8,0,1] :=
  predecessor_excluded a [7,3,6,8,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_2699 : Excluded a [7,3,6,8,0,2] :=
  source_excluded a [7,3,6,8,0,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2701 : Excluded a [7,3,6,8,0,4,1] :=
  source_excluded a [7,3,6,8,0,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2703 : Excluded a [7,3,6,8,0,4,2,1] :=
  source_excluded a [7,3,6,8,0,4,2,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2705 : Excluded a [7,3,6,8,0,4,2,5,1] :=
  predecessor_excluded a [7,3,6,8,0,4,2,5,1] 0 3 8 1 (by decide) (by decide +kernel)

theorem node_2704 : Excluded a [7,3,6,8,0,4,2,5] :=
  branch_excluded a [7,3,6,8,0,4,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,8,0,4,2,5,0] (by decide +kernel))
      node_2705
      (invalid_excluded a [7,3,6,8,0,4,2,5,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,2,5,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,2,5,4] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,2,5,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,2,5,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,2,5,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,2,5,8] (by decide +kernel)))

theorem node_2702 : Excluded a [7,3,6,8,0,4,2] :=
  branch_excluded a [7,3,6,8,0,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,8,0,4,2,0] (by decide +kernel))
      node_2703
      (invalid_excluded a [7,3,6,8,0,4,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,2,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,2,4] (by decide +kernel))
      node_2704
      (invalid_excluded a [7,3,6,8,0,4,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,2,8] (by decide +kernel)))

theorem node_2706 : Excluded a [7,3,6,8,0,4,5] :=
  predecessor_excluded a [7,3,6,8,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2700 : Excluded a [7,3,6,8,0,4] :=
  branch_excluded a [7,3,6,8,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,8,0,4,0] (by decide +kernel))
      node_2701
      node_2702
      (invalid_excluded a [7,3,6,8,0,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,4] (by decide +kernel))
      node_2706
      (invalid_excluded a [7,3,6,8,0,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,4,8] (by decide +kernel)))

theorem node_2697 : Excluded a [7,3,6,8,0] :=
  branch_excluded a [7,3,6,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,6,8,0,0] (by decide +kernel))
      node_2698
      node_2699
      (invalid_excluded a [7,3,6,8,0,3] (by decide +kernel))
      node_2700
      (invalid_excluded a [7,3,6,8,0,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,0,8] (by decide +kernel)))

theorem node_2708 : Excluded a [7,3,6,8,1,0] :=
  predecessor_excluded a [7,3,6,8,1,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2709 : Excluded a [7,3,6,8,1,2] :=
  source_excluded a [7,3,6,8,1,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2711 : Excluded a [7,3,6,8,1,4,0] :=
  source_excluded a [7,3,6,8,1,4,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2713 : Excluded a [7,3,6,8,1,4,2,0] :=
  predecessor_excluded a [7,3,6,8,1,4,2,0] 2 0 0 7 (by decide) (by decide +kernel)

def b_2715 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 3
  | 2 => 6
  | 3 => 8
  | 4 => 1
  | 5 => 4
  | 6 => 2
  | 7 => 5
  | 8 => 0
  | _ => 0

def cert_2715 : LosingRegion (edgeOf a b_2715) 0 :=
  losingMask a b_2715 0 1212549733204004552836096
    (by decide +kernel) (by decide +kernel)

theorem node_2715 : Excluded a [7,3,6,8,1,4,2,5,0] :=
  losing_excluded a [7,3,6,8,1,4,2,5,0] (by decide) b_2715 (by decide +kernel) 2 0 1 cert_2715 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2715 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1212549733204004552836096 2 1; decide +kernel)

theorem node_2714 : Excluded a [7,3,6,8,1,4,2,5] :=
  branch_excluded a [7,3,6,8,1,4,2,5] (by decide)
    (fin9_cases _
      node_2715
      (invalid_excluded a [7,3,6,8,1,4,2,5,1] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,4,2,5,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,4,2,5,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,4,2,5,4] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,4,2,5,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,4,2,5,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,4,2,5,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,4,2,5,8] (by decide +kernel)))

theorem node_2712 : Excluded a [7,3,6,8,1,4,2] :=
  branch_excluded a [7,3,6,8,1,4,2] (by decide)
    (fin9_cases _
      node_2713
      (invalid_excluded a [7,3,6,8,1,4,2,1] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,4,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,4,2,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,4,2,4] (by decide +kernel))
      node_2714
      (invalid_excluded a [7,3,6,8,1,4,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,4,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,4,2,8] (by decide +kernel)))

theorem node_2716 : Excluded a [7,3,6,8,1,4,5] :=
  predecessor_excluded a [7,3,6,8,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_2710 : Excluded a [7,3,6,8,1,4] :=
  branch_excluded a [7,3,6,8,1,4] (by decide)
    (fin9_cases _
      node_2711
      (invalid_excluded a [7,3,6,8,1,4,1] (by decide +kernel))
      node_2712
      (invalid_excluded a [7,3,6,8,1,4,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,4,4] (by decide +kernel))
      node_2716
      (invalid_excluded a [7,3,6,8,1,4,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,4,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,4,8] (by decide +kernel)))

theorem node_2707 : Excluded a [7,3,6,8,1] :=
  branch_excluded a [7,3,6,8,1] (by decide)
    (fin9_cases _
      node_2708
      (invalid_excluded a [7,3,6,8,1,1] (by decide +kernel))
      node_2709
      (invalid_excluded a [7,3,6,8,1,3] (by decide +kernel))
      node_2710
      (invalid_excluded a [7,3,6,8,1,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,1,8] (by decide +kernel)))

theorem node_2717 : Excluded a [7,3,6,8,2] :=
  predecessor_excluded a [7,3,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_2696 : Excluded a [7,3,6,8] :=
  branch_excluded a [7,3,6,8] (by decide)
    (fin9_cases _
      node_2697
      node_2707
      node_2717
      (invalid_excluded a [7,3,6,8,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,4] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,6,8,8] (by decide +kernel)))

theorem node_2659 : Excluded a [7,3,6] :=
  branch_excluded a [7,3,6] (by decide)
    (fin9_cases _
      node_2660
      node_2661
      node_2662
      (invalid_excluded a [7,3,6,3] (by decide +kernel))
      (invalid_excluded a [7,3,6,4] (by decide +kernel))
      node_2695
      (invalid_excluded a [7,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,6,7] (by decide +kernel))
      node_2696)

theorem node_2719 : Excluded a [7,3,8,0] :=
  source_excluded a [7,3,8,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2720 : Excluded a [7,3,8,1] :=
  predecessor_excluded a [7,3,8,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_2721 : Excluded a [7,3,8,2] :=
  predecessor_excluded a [7,3,8,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_2722 : Excluded a [7,3,8,5] :=
  source_excluded a [7,3,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2725 : Excluded a [7,3,8,6,0,1] :=
  predecessor_excluded a [7,3,8,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_2727 : Excluded a [7,3,8,6,0,2,1] :=
  source_excluded a [7,3,8,6,0,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2728 : Excluded a [7,3,8,6,0,2,4] :=
  source_excluded a [7,3,8,6,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2729 : Excluded a [7,3,8,6,0,2,5] :=
  predecessor_excluded a [7,3,8,6,0,2,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2726 : Excluded a [7,3,8,6,0,2] :=
  branch_excluded a [7,3,8,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,6,0,2,0] (by decide +kernel))
      node_2727
      (invalid_excluded a [7,3,8,6,0,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,3] (by decide +kernel))
      node_2728
      node_2729
      (invalid_excluded a [7,3,8,6,0,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,2,8] (by decide +kernel)))

theorem node_2730 : Excluded a [7,3,8,6,0,4] :=
  source_excluded a [7,3,8,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2724 : Excluded a [7,3,8,6,0] :=
  branch_excluded a [7,3,8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,3,8,6,0,0] (by decide +kernel))
      node_2725
      node_2726
      (invalid_excluded a [7,3,8,6,0,3] (by decide +kernel))
      node_2730
      (invalid_excluded a [7,3,8,6,0,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,0,8] (by decide +kernel)))

theorem node_2732 : Excluded a [7,3,8,6,1,0] :=
  predecessor_excluded a [7,3,8,6,1,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2734 : Excluded a [7,3,8,6,1,2,0] :=
  source_excluded a [7,3,8,6,1,2,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2735 : Excluded a [7,3,8,6,1,2,4] :=
  source_excluded a [7,3,8,6,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2736 : Excluded a [7,3,8,6,1,2,5] :=
  predecessor_excluded a [7,3,8,6,1,2,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2733 : Excluded a [7,3,8,6,1,2] :=
  branch_excluded a [7,3,8,6,1,2] (by decide)
    (fin9_cases _
      node_2734
      (invalid_excluded a [7,3,8,6,1,2,1] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,1,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,1,2,3] (by decide +kernel))
      node_2735
      node_2736
      (invalid_excluded a [7,3,8,6,1,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,1,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,1,2,8] (by decide +kernel)))

theorem node_2737 : Excluded a [7,3,8,6,1,4] :=
  source_excluded a [7,3,8,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2731 : Excluded a [7,3,8,6,1] :=
  branch_excluded a [7,3,8,6,1] (by decide)
    (fin9_cases _
      node_2732
      (invalid_excluded a [7,3,8,6,1,1] (by decide +kernel))
      node_2733
      (invalid_excluded a [7,3,8,6,1,3] (by decide +kernel))
      node_2737
      (invalid_excluded a [7,3,8,6,1,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,1,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,1,8] (by decide +kernel)))

theorem node_2739 : Excluded a [7,3,8,6,2,0] :=
  predecessor_excluded a [7,3,8,6,2,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2741 : Excluded a [7,3,8,6,2,1,0] :=
  source_excluded a [7,3,8,6,2,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2742 : Excluded a [7,3,8,6,2,1,4] :=
  source_excluded a [7,3,8,6,2,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2743 : Excluded a [7,3,8,6,2,1,5] :=
  predecessor_excluded a [7,3,8,6,2,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2740 : Excluded a [7,3,8,6,2,1] :=
  branch_excluded a [7,3,8,6,2,1] (by decide)
    (fin9_cases _
      node_2741
      (invalid_excluded a [7,3,8,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,1,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,1,3] (by decide +kernel))
      node_2742
      node_2743
      (invalid_excluded a [7,3,8,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,1,8] (by decide +kernel)))

theorem node_2744 : Excluded a [7,3,8,6,2,4] :=
  source_excluded a [7,3,8,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2738 : Excluded a [7,3,8,6,2] :=
  branch_excluded a [7,3,8,6,2] (by decide)
    (fin9_cases _
      node_2739
      node_2740
      (invalid_excluded a [7,3,8,6,2,2] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,3] (by decide +kernel))
      node_2744
      (invalid_excluded a [7,3,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,2,8] (by decide +kernel)))

theorem node_2723 : Excluded a [7,3,8,6] :=
  branch_excluded a [7,3,8,6] (by decide)
    (fin9_cases _
      node_2724
      node_2731
      node_2738
      (invalid_excluded a [7,3,8,6,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,4] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,6,8] (by decide +kernel)))

theorem node_2718 : Excluded a [7,3,8] :=
  branch_excluded a [7,3,8] (by decide)
    (fin9_cases _
      node_2719
      node_2720
      node_2721
      (invalid_excluded a [7,3,8,3] (by decide +kernel))
      (invalid_excluded a [7,3,8,4] (by decide +kernel))
      node_2722
      node_2723
      (invalid_excluded a [7,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,3,8,8] (by decide +kernel)))

theorem node_2629 : Excluded a [7,3] :=
  branch_excluded a [7,3] (by decide)
    (fin9_cases _
      node_2630
      node_2631
      (invalid_excluded a [7,3,2] (by decide +kernel))
      (invalid_excluded a [7,3,3] (by decide +kernel))
      node_2632
      node_2633
      node_2659
      (invalid_excluded a [7,3,7] (by decide +kernel))
      node_2718)

theorem node_2747 : Excluded a [7,4,0,1] :=
  source_excluded a [7,4,0,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2749 : Excluded a [7,4,0,2,1] :=
  predecessor_excluded a [7,4,0,2,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2750 : Excluded a [7,4,0,2,3] :=
  predecessor_excluded a [7,4,0,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2751 : Excluded a [7,4,0,2,6] :=
  source_excluded a [7,4,0,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2755 : Excluded a [7,4,0,2,8,1,3,5] :=
  source_excluded a [7,4,0,2,8,1,3,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_2757 : Excluded a [7,4,0,2,8,1,3,6,5] :=
  source_excluded a [7,4,0,2,8,1,3,6,5] 4 0 8 (by decide) (by decide +kernel)

theorem node_2756 : Excluded a [7,4,0,2,8,1,3,6] :=
  branch_excluded a [7,4,0,2,8,1,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,2,8,1,3,6,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,3,6,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,3,6,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,3,6,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,3,6,4] (by decide +kernel))
      node_2757
      (invalid_excluded a [7,4,0,2,8,1,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,3,6,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,3,6,8] (by decide +kernel)))

theorem node_2754 : Excluded a [7,4,0,2,8,1,3] :=
  branch_excluded a [7,4,0,2,8,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,2,8,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,3,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,3,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,3,4] (by decide +kernel))
      node_2755
      node_2756
      (invalid_excluded a [7,4,0,2,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,3,8] (by decide +kernel)))

theorem node_2759 : Excluded a [7,4,0,2,8,1,5,3] :=
  predecessor_excluded a [7,4,0,2,8,1,5,3] 0 2 7 3 (by decide) (by decide +kernel)

theorem node_2760 : Excluded a [7,4,0,2,8,1,5,6] :=
  predecessor_excluded a [7,4,0,2,8,1,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_2758 : Excluded a [7,4,0,2,8,1,5] :=
  branch_excluded a [7,4,0,2,8,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,2,8,1,5,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,5,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,5,2] (by decide +kernel))
      node_2759
      (invalid_excluded a [7,4,0,2,8,1,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,5,5] (by decide +kernel))
      node_2760
      (invalid_excluded a [7,4,0,2,8,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,5,8] (by decide +kernel)))

theorem node_2753 : Excluded a [7,4,0,2,8,1] :=
  branch_excluded a [7,4,0,2,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,2,8,1,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,2] (by decide +kernel))
      node_2754
      (invalid_excluded a [7,4,0,2,8,1,4] (by decide +kernel))
      node_2758
      (invalid_excluded a [7,4,0,2,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,1,8] (by decide +kernel)))

theorem node_2762 : Excluded a [7,4,0,2,8,3,1] :=
  source_excluded a [7,4,0,2,8,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2764 : Excluded a [7,4,0,2,8,3,5,1] :=
  source_excluded a [7,4,0,2,8,3,5,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2765 : Excluded a [7,4,0,2,8,3,5,6] :=
  predecessor_excluded a [7,4,0,2,8,3,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_2763 : Excluded a [7,4,0,2,8,3,5] :=
  branch_excluded a [7,4,0,2,8,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,2,8,3,5,0] (by decide +kernel))
      node_2764
      (invalid_excluded a [7,4,0,2,8,3,5,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,3,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,3,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,3,5,5] (by decide +kernel))
      node_2765
      (invalid_excluded a [7,4,0,2,8,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,3,5,8] (by decide +kernel)))

theorem node_2761 : Excluded a [7,4,0,2,8,3] :=
  branch_excluded a [7,4,0,2,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,2,8,3,0] (by decide +kernel))
      node_2762
      (invalid_excluded a [7,4,0,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,3,4] (by decide +kernel))
      node_2763
      (invalid_excluded a [7,4,0,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,3,8] (by decide +kernel)))

theorem node_2752 : Excluded a [7,4,0,2,8] :=
  branch_excluded a [7,4,0,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,2,8,0] (by decide +kernel))
      node_2753
      (invalid_excluded a [7,4,0,2,8,2] (by decide +kernel))
      node_2761
      (invalid_excluded a [7,4,0,2,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,8,8] (by decide +kernel)))

theorem node_2748 : Excluded a [7,4,0,2] :=
  branch_excluded a [7,4,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,2,0] (by decide +kernel))
      node_2749
      (invalid_excluded a [7,4,0,2,2] (by decide +kernel))
      node_2750
      (invalid_excluded a [7,4,0,2,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,2,5] (by decide +kernel))
      node_2751
      (invalid_excluded a [7,4,0,2,7] (by decide +kernel))
      node_2752)

theorem node_2766 : Excluded a [7,4,0,5] :=
  source_excluded a [7,4,0,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2768 : Excluded a [7,4,0,6,1] :=
  predecessor_excluded a [7,4,0,6,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2772 : Excluded a [7,4,0,6,2,1,3,5] :=
  branch_excluded a [7,4,0,6,2,1,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,2,1,3,5,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,3,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,3,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,3,5,8] (by decide +kernel)))

theorem node_2771 : Excluded a [7,4,0,6,2,1,3] :=
  branch_excluded a [7,4,0,6,2,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,2,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,3,4] (by decide +kernel))
      node_2772
      (invalid_excluded a [7,4,0,6,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,3,8] (by decide +kernel)))

theorem node_2773 : Excluded a [7,4,0,6,2,1,5] :=
  predecessor_excluded a [7,4,0,6,2,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2774 : Excluded a [7,4,0,6,2,1,8] :=
  source_excluded a [7,4,0,6,2,1,8] 6 0 7 (by decide) (by decide +kernel)

theorem node_2770 : Excluded a [7,4,0,6,2,1] :=
  branch_excluded a [7,4,0,6,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,2,1,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,2] (by decide +kernel))
      node_2771
      (invalid_excluded a [7,4,0,6,2,1,4] (by decide +kernel))
      node_2773
      (invalid_excluded a [7,4,0,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,1,7] (by decide +kernel))
      node_2774)

theorem node_2775 : Excluded a [7,4,0,6,2,3] :=
  source_excluded a [7,4,0,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2777 : Excluded a [7,4,0,6,2,8,1] :=
  source_excluded a [7,4,0,6,2,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2779 : Excluded a [7,4,0,6,2,8,3,1] :=
  source_excluded a [7,4,0,6,2,8,3,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2780 : Excluded a [7,4,0,6,2,8,3,5] :=
  source_excluded a [7,4,0,6,2,8,3,5] 7 0 5 (by decide) (by decide +kernel)

theorem node_2778 : Excluded a [7,4,0,6,2,8,3] :=
  branch_excluded a [7,4,0,6,2,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,2,8,3,0] (by decide +kernel))
      node_2779
      (invalid_excluded a [7,4,0,6,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,8,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,8,3,4] (by decide +kernel))
      node_2780
      (invalid_excluded a [7,4,0,6,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,8,3,8] (by decide +kernel)))

theorem node_2781 : Excluded a [7,4,0,6,2,8,5] :=
  predecessor_excluded a [7,4,0,6,2,8,5] 0 8 6 5 (by decide) (by decide +kernel)

theorem node_2776 : Excluded a [7,4,0,6,2,8] :=
  branch_excluded a [7,4,0,6,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,2,8,0] (by decide +kernel))
      node_2777
      (invalid_excluded a [7,4,0,6,2,8,2] (by decide +kernel))
      node_2778
      (invalid_excluded a [7,4,0,6,2,8,4] (by decide +kernel))
      node_2781
      (invalid_excluded a [7,4,0,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,8,8] (by decide +kernel)))

theorem node_2769 : Excluded a [7,4,0,6,2] :=
  branch_excluded a [7,4,0,6,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,2,0] (by decide +kernel))
      node_2770
      (invalid_excluded a [7,4,0,6,2,2] (by decide +kernel))
      node_2775
      (invalid_excluded a [7,4,0,6,2,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,2,7] (by decide +kernel))
      node_2776)

theorem node_2782 : Excluded a [7,4,0,6,3] :=
  predecessor_excluded a [7,4,0,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2786 : Excluded a [7,4,0,6,8,1,2,3] :=
  predecessor_excluded a [7,4,0,6,8,1,2,3] 0 3 6 7 (by decide) (by decide +kernel)

theorem node_2787 : Excluded a [7,4,0,6,8,1,2,5] :=
  source_excluded a [7,4,0,6,8,1,2,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_2785 : Excluded a [7,4,0,6,8,1,2] :=
  branch_excluded a [7,4,0,6,8,1,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,8,1,2,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,2,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,2,2] (by decide +kernel))
      node_2786
      (invalid_excluded a [7,4,0,6,8,1,2,4] (by decide +kernel))
      node_2787
      (invalid_excluded a [7,4,0,6,8,1,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,2,8] (by decide +kernel)))

theorem node_2789 : Excluded a [7,4,0,6,8,1,3,2] :=
  source_excluded a [7,4,0,6,8,1,3,2] 7 0 8 (by decide) (by decide +kernel)

theorem node_2790 : Excluded a [7,4,0,6,8,1,3,5] :=
  source_excluded a [7,4,0,6,8,1,3,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_2788 : Excluded a [7,4,0,6,8,1,3] :=
  branch_excluded a [7,4,0,6,8,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,8,1,3,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,3,1] (by decide +kernel))
      node_2789
      (invalid_excluded a [7,4,0,6,8,1,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,3,4] (by decide +kernel))
      node_2790
      (invalid_excluded a [7,4,0,6,8,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,3,8] (by decide +kernel)))

theorem node_2791 : Excluded a [7,4,0,6,8,1,5] :=
  predecessor_excluded a [7,4,0,6,8,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2784 : Excluded a [7,4,0,6,8,1] :=
  branch_excluded a [7,4,0,6,8,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,8,1,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,1] (by decide +kernel))
      node_2785
      node_2788
      (invalid_excluded a [7,4,0,6,8,1,4] (by decide +kernel))
      node_2791
      (invalid_excluded a [7,4,0,6,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,1,8] (by decide +kernel)))

theorem node_2792 : Excluded a [7,4,0,6,8,2] :=
  predecessor_excluded a [7,4,0,6,8,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_2793 : Excluded a [7,4,0,6,8,3] :=
  source_excluded a [7,4,0,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2783 : Excluded a [7,4,0,6,8] :=
  branch_excluded a [7,4,0,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,8,0] (by decide +kernel))
      node_2784
      node_2792
      node_2793
      (invalid_excluded a [7,4,0,6,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,8,8] (by decide +kernel)))

theorem node_2767 : Excluded a [7,4,0,6] :=
  branch_excluded a [7,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,6,0] (by decide +kernel))
      node_2768
      node_2769
      node_2782
      (invalid_excluded a [7,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,6,7] (by decide +kernel))
      node_2783)

theorem node_2795 : Excluded a [7,4,0,8,1] :=
  predecessor_excluded a [7,4,0,8,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2796 : Excluded a [7,4,0,8,2] :=
  predecessor_excluded a [7,4,0,8,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_2801 : Excluded a [7,4,0,8,3,1,2,5,6] :=
  source_excluded a [7,4,0,8,3,1,2,5,6] 8 0 6 (by decide) (by decide +kernel)

theorem node_2800 : Excluded a [7,4,0,8,3,1,2,5] :=
  branch_excluded a [7,4,0,8,3,1,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,3,1,2,5,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,2,5,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,2,5,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,2,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,2,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,2,5,5] (by decide +kernel))
      node_2801
      (invalid_excluded a [7,4,0,8,3,1,2,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,2,5,8] (by decide +kernel)))

theorem node_2802 : Excluded a [7,4,0,8,3,1,2,6] :=
  predecessor_excluded a [7,4,0,8,3,1,2,6] 0 2 7 6 (by decide) (by decide +kernel)

theorem node_2799 : Excluded a [7,4,0,8,3,1,2] :=
  branch_excluded a [7,4,0,8,3,1,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,3,1,2,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,2,1] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,2,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,2,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,2,4] (by decide +kernel))
      node_2800
      node_2802
      (invalid_excluded a [7,4,0,8,3,1,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,2,8] (by decide +kernel)))

theorem node_2804 : Excluded a [7,4,0,8,3,1,5,2] :=
  source_excluded a [7,4,0,8,3,1,5,2] 7 0 8 (by decide) (by decide +kernel)

theorem node_2805 : Excluded a [7,4,0,8,3,1,5,6] :=
  predecessor_excluded a [7,4,0,8,3,1,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_2803 : Excluded a [7,4,0,8,3,1,5] :=
  branch_excluded a [7,4,0,8,3,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,3,1,5,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,5,1] (by decide +kernel))
      node_2804
      (invalid_excluded a [7,4,0,8,3,1,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,5,5] (by decide +kernel))
      node_2805
      (invalid_excluded a [7,4,0,8,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,5,8] (by decide +kernel)))

theorem node_2798 : Excluded a [7,4,0,8,3,1] :=
  branch_excluded a [7,4,0,8,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,3,1,0] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,1] (by decide +kernel))
      node_2799
      (invalid_excluded a [7,4,0,8,3,1,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,4] (by decide +kernel))
      node_2803
      (invalid_excluded a [7,4,0,8,3,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,1,8] (by decide +kernel)))

theorem node_2807 : Excluded a [7,4,0,8,3,2,1] :=
  source_excluded a [7,4,0,8,3,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2809 : Excluded a [7,4,0,8,3,2,5,1] :=
  source_excluded a [7,4,0,8,3,2,5,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2810 : Excluded a [7,4,0,8,3,2,5,6] :=
  predecessor_excluded a [7,4,0,8,3,2,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_2808 : Excluded a [7,4,0,8,3,2,5] :=
  branch_excluded a [7,4,0,8,3,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,3,2,5,0] (by decide +kernel))
      node_2809
      (invalid_excluded a [7,4,0,8,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,2,5,5] (by decide +kernel))
      node_2810
      (invalid_excluded a [7,4,0,8,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,2,5,8] (by decide +kernel)))

theorem node_2806 : Excluded a [7,4,0,8,3,2] :=
  branch_excluded a [7,4,0,8,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,3,2,0] (by decide +kernel))
      node_2807
      (invalid_excluded a [7,4,0,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,2,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,2,4] (by decide +kernel))
      node_2808
      (invalid_excluded a [7,4,0,8,3,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,2,8] (by decide +kernel)))

theorem node_2797 : Excluded a [7,4,0,8,3] :=
  branch_excluded a [7,4,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,3,0] (by decide +kernel))
      node_2798
      node_2806
      (invalid_excluded a [7,4,0,8,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,3,8] (by decide +kernel)))

theorem node_2811 : Excluded a [7,4,0,8,6] :=
  source_excluded a [7,4,0,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2794 : Excluded a [7,4,0,8] :=
  branch_excluded a [7,4,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,8,0] (by decide +kernel))
      node_2795
      node_2796
      node_2797
      (invalid_excluded a [7,4,0,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,5] (by decide +kernel))
      node_2811
      (invalid_excluded a [7,4,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,0,8,8] (by decide +kernel)))

theorem node_2746 : Excluded a [7,4,0] :=
  branch_excluded a [7,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,4,0,0] (by decide +kernel))
      node_2747
      node_2748
      (invalid_excluded a [7,4,0,3] (by decide +kernel))
      (invalid_excluded a [7,4,0,4] (by decide +kernel))
      node_2766
      node_2767
      (invalid_excluded a [7,4,0,7] (by decide +kernel))
      node_2794)

theorem node_2812 : Excluded a [7,4,1] :=
  predecessor_excluded a [7,4,1] 0 4 2 1 (by decide) (by decide +kernel)

theorem node_2814 : Excluded a [7,4,5,0] :=
  source_excluded a [7,4,5,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2815 : Excluded a [7,4,5,1] :=
  source_excluded a [7,4,5,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2816 : Excluded a [7,4,5,2] :=
  predecessor_excluded a [7,4,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_2817 : Excluded a [7,4,5,6] :=
  predecessor_excluded a [7,4,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_2819 : Excluded a [7,4,5,8,0] :=
  source_excluded a [7,4,5,8,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2820 : Excluded a [7,4,5,8,1] :=
  predecessor_excluded a [7,4,5,8,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2821 : Excluded a [7,4,5,8,2] :=
  source_excluded a [7,4,5,8,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_2822 : Excluded a [7,4,5,8,3] :=
  source_excluded a [7,4,5,8,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_2823 : Excluded a [7,4,5,8,6] :=
  source_excluded a [7,4,5,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2818 : Excluded a [7,4,5,8] :=
  branch_excluded a [7,4,5,8] (by decide)
    (fin9_cases _
      node_2819
      node_2820
      node_2821
      node_2822
      (invalid_excluded a [7,4,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,5,8,5] (by decide +kernel))
      node_2823
      (invalid_excluded a [7,4,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,5,8,8] (by decide +kernel)))

theorem node_2813 : Excluded a [7,4,5] :=
  branch_excluded a [7,4,5] (by decide)
    (fin9_cases _
      node_2814
      node_2815
      node_2816
      (invalid_excluded a [7,4,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,5,5] (by decide +kernel))
      node_2817
      (invalid_excluded a [7,4,5,7] (by decide +kernel))
      node_2818)

theorem node_2825 : Excluded a [7,4,6,0] :=
  source_excluded a [7,4,6,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2826 : Excluded a [7,4,6,1] :=
  source_excluded a [7,4,6,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2828 : Excluded a [7,4,6,2,0] :=
  source_excluded a [7,4,6,2,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2829 : Excluded a [7,4,6,2,1] :=
  predecessor_excluded a [7,4,6,2,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2830 : Excluded a [7,4,6,2,3] :=
  predecessor_excluded a [7,4,6,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2832 : Excluded a [7,4,6,2,8,0] :=
  predecessor_excluded a [7,4,6,2,8,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2834 : Excluded a [7,4,6,2,8,1,0] :=
  source_excluded a [7,4,6,2,8,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2835 : Excluded a [7,4,6,2,8,1,3] :=
  source_excluded a [7,4,6,2,8,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2837 : Excluded a [7,4,6,2,8,1,5,0] :=
  predecessor_excluded a [7,4,6,2,8,1,5,0] 2 0 0 7 (by decide) (by decide +kernel)

theorem node_2838 : Excluded a [7,4,6,2,8,1,5,3] :=
  predecessor_excluded a [7,4,6,2,8,1,5,3] 0 2 7 3 (by decide) (by decide +kernel)

theorem node_2836 : Excluded a [7,4,6,2,8,1,5] :=
  branch_excluded a [7,4,6,2,8,1,5] (by decide)
    (fin9_cases _
      node_2837
      (invalid_excluded a [7,4,6,2,8,1,5,1] (by decide +kernel))
      (invalid_excluded a [7,4,6,2,8,1,5,2] (by decide +kernel))
      node_2838
      (invalid_excluded a [7,4,6,2,8,1,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,6,2,8,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,4,6,2,8,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,2,8,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,2,8,1,5,8] (by decide +kernel)))

theorem node_2833 : Excluded a [7,4,6,2,8,1] :=
  branch_excluded a [7,4,6,2,8,1] (by decide)
    (fin9_cases _
      node_2834
      (invalid_excluded a [7,4,6,2,8,1,1] (by decide +kernel))
      (invalid_excluded a [7,4,6,2,8,1,2] (by decide +kernel))
      node_2835
      (invalid_excluded a [7,4,6,2,8,1,4] (by decide +kernel))
      node_2836
      (invalid_excluded a [7,4,6,2,8,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,2,8,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,2,8,1,8] (by decide +kernel)))

theorem node_2839 : Excluded a [7,4,6,2,8,3] :=
  source_excluded a [7,4,6,2,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2831 : Excluded a [7,4,6,2,8] :=
  branch_excluded a [7,4,6,2,8] (by decide)
    (fin9_cases _
      node_2832
      node_2833
      (invalid_excluded a [7,4,6,2,8,2] (by decide +kernel))
      node_2839
      (invalid_excluded a [7,4,6,2,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [7,4,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,2,8,8] (by decide +kernel)))

theorem node_2827 : Excluded a [7,4,6,2] :=
  branch_excluded a [7,4,6,2] (by decide)
    (fin9_cases _
      node_2828
      node_2829
      (invalid_excluded a [7,4,6,2,2] (by decide +kernel))
      node_2830
      (invalid_excluded a [7,4,6,2,4] (by decide +kernel))
      (invalid_excluded a [7,4,6,2,5] (by decide +kernel))
      (invalid_excluded a [7,4,6,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,2,7] (by decide +kernel))
      node_2831)

theorem node_2840 : Excluded a [7,4,6,5] :=
  source_excluded a [7,4,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2842 : Excluded a [7,4,6,8,0] :=
  source_excluded a [7,4,6,8,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2843 : Excluded a [7,4,6,8,1] :=
  predecessor_excluded a [7,4,6,8,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2844 : Excluded a [7,4,6,8,2] :=
  predecessor_excluded a [7,4,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_2846 : Excluded a [7,4,6,8,3,0] :=
  predecessor_excluded a [7,4,6,8,3,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2848 : Excluded a [7,4,6,8,3,1,0] :=
  source_excluded a [7,4,6,8,3,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2850 : Excluded a [7,4,6,8,3,1,2,0] :=
  predecessor_excluded a [7,4,6,8,3,1,2,0] 2 0 0 7 (by decide) (by decide +kernel)

def b_2852 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 4
  | 2 => 6
  | 3 => 8
  | 4 => 3
  | 5 => 1
  | 6 => 2
  | 7 => 5
  | 8 => 0
  | _ => 0

def cert_2852 : LosingRegion (edgeOf a b_2852) 0 :=
  losingMask a b_2852 0 1212475828315962513556480
    (by decide +kernel) (by decide +kernel)

theorem node_2852 : Excluded a [7,4,6,8,3,1,2,5,0] :=
  losing_excluded a [7,4,6,8,3,1,2,5,0] (by decide) b_2852 (by decide +kernel) 2 0 0 cert_2852 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2852 2 0 ∧ 0 ≠ 2 ∧ maskRegion 1212475828315962513556480 2 0; decide +kernel)

theorem node_2851 : Excluded a [7,4,6,8,3,1,2,5] :=
  branch_excluded a [7,4,6,8,3,1,2,5] (by decide)
    (fin9_cases _
      node_2852
      (invalid_excluded a [7,4,6,8,3,1,2,5,1] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,2,5,2] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,2,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,2,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,2,5,5] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,2,5,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,2,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,2,5,8] (by decide +kernel)))

theorem node_2849 : Excluded a [7,4,6,8,3,1,2] :=
  branch_excluded a [7,4,6,8,3,1,2] (by decide)
    (fin9_cases _
      node_2850
      (invalid_excluded a [7,4,6,8,3,1,2,1] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,2,2] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,2,3] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,2,4] (by decide +kernel))
      node_2851
      (invalid_excluded a [7,4,6,8,3,1,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,2,8] (by decide +kernel)))

theorem node_2854 : Excluded a [7,4,6,8,3,1,5,0] :=
  predecessor_excluded a [7,4,6,8,3,1,5,0] 2 0 0 7 (by decide) (by decide +kernel)

theorem node_2855 : Excluded a [7,4,6,8,3,1,5,2] :=
  source_excluded a [7,4,6,8,3,1,5,2] 7 0 8 (by decide) (by decide +kernel)

theorem node_2853 : Excluded a [7,4,6,8,3,1,5] :=
  branch_excluded a [7,4,6,8,3,1,5] (by decide)
    (fin9_cases _
      node_2854
      (invalid_excluded a [7,4,6,8,3,1,5,1] (by decide +kernel))
      node_2855
      (invalid_excluded a [7,4,6,8,3,1,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,5,5] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,5,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,5,8] (by decide +kernel)))

theorem node_2847 : Excluded a [7,4,6,8,3,1] :=
  branch_excluded a [7,4,6,8,3,1] (by decide)
    (fin9_cases _
      node_2848
      (invalid_excluded a [7,4,6,8,3,1,1] (by decide +kernel))
      node_2849
      (invalid_excluded a [7,4,6,8,3,1,3] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,4] (by decide +kernel))
      node_2853
      (invalid_excluded a [7,4,6,8,3,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,1,8] (by decide +kernel)))

theorem node_2856 : Excluded a [7,4,6,8,3,2] :=
  source_excluded a [7,4,6,8,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2845 : Excluded a [7,4,6,8,3] :=
  branch_excluded a [7,4,6,8,3] (by decide)
    (fin9_cases _
      node_2846
      node_2847
      node_2856
      (invalid_excluded a [7,4,6,8,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,4] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,3,8] (by decide +kernel)))

theorem node_2841 : Excluded a [7,4,6,8] :=
  branch_excluded a [7,4,6,8] (by decide)
    (fin9_cases _
      node_2842
      node_2843
      node_2844
      node_2845
      (invalid_excluded a [7,4,6,8,4] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,6,8,8] (by decide +kernel)))

theorem node_2824 : Excluded a [7,4,6] :=
  branch_excluded a [7,4,6] (by decide)
    (fin9_cases _
      node_2825
      node_2826
      node_2827
      (invalid_excluded a [7,4,6,3] (by decide +kernel))
      (invalid_excluded a [7,4,6,4] (by decide +kernel))
      node_2840
      (invalid_excluded a [7,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,6,7] (by decide +kernel))
      node_2841)

theorem node_2858 : Excluded a [7,4,8,0] :=
  source_excluded a [7,4,8,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_2859 : Excluded a [7,4,8,1] :=
  source_excluded a [7,4,8,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_2860 : Excluded a [7,4,8,2] :=
  predecessor_excluded a [7,4,8,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_2861 : Excluded a [7,4,8,5] :=
  source_excluded a [7,4,8,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_2863 : Excluded a [7,4,8,6,0] :=
  source_excluded a [7,4,8,6,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2864 : Excluded a [7,4,8,6,1] :=
  predecessor_excluded a [7,4,8,6,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_2866 : Excluded a [7,4,8,6,2,0] :=
  predecessor_excluded a [7,4,8,6,2,0] 1 7 5 0 (by decide) (by decide +kernel)

theorem node_2868 : Excluded a [7,4,8,6,2,1,0] :=
  source_excluded a [7,4,8,6,2,1,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2870 : Excluded a [7,4,8,6,2,1,3,0] :=
  predecessor_excluded a [7,4,8,6,2,1,3,0] 2 0 0 7 (by decide) (by decide +kernel)

def b_2872 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 4
  | 2 => 8
  | 3 => 6
  | 4 => 2
  | 5 => 1
  | 6 => 3
  | 7 => 5
  | 8 => 0
  | _ => 0

def cert_2872 : LosingRegion (edgeOf a b_2872) 0 :=
  losingMask a b_2872 0 1212475756258380129240064
    (by decide +kernel) (by decide +kernel)

theorem node_2872 : Excluded a [7,4,8,6,2,1,3,5,0] :=
  losing_excluded a [7,4,8,6,2,1,3,5,0] (by decide) b_2872 (by decide +kernel) 2 0 7 cert_2872 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_2872 2 0 ∧ 7 ≠ 2 ∧ maskRegion 1212475756258380129240064 2 7; decide +kernel)

theorem node_2871 : Excluded a [7,4,8,6,2,1,3,5] :=
  branch_excluded a [7,4,8,6,2,1,3,5] (by decide)
    (fin9_cases _
      node_2872
      (invalid_excluded a [7,4,8,6,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,1,3,5,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,1,3,5,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,1,3,5,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,1,3,5,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,1,3,5,8] (by decide +kernel)))

theorem node_2869 : Excluded a [7,4,8,6,2,1,3] :=
  branch_excluded a [7,4,8,6,2,1,3] (by decide)
    (fin9_cases _
      node_2870
      (invalid_excluded a [7,4,8,6,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,1,3,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,1,3,4] (by decide +kernel))
      node_2871
      (invalid_excluded a [7,4,8,6,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,1,3,8] (by decide +kernel)))

theorem node_2873 : Excluded a [7,4,8,6,2,1,5] :=
  predecessor_excluded a [7,4,8,6,2,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_2867 : Excluded a [7,4,8,6,2,1] :=
  branch_excluded a [7,4,8,6,2,1] (by decide)
    (fin9_cases _
      node_2868
      (invalid_excluded a [7,4,8,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,1,2] (by decide +kernel))
      node_2869
      (invalid_excluded a [7,4,8,6,2,1,4] (by decide +kernel))
      node_2873
      (invalid_excluded a [7,4,8,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,1,8] (by decide +kernel)))

theorem node_2874 : Excluded a [7,4,8,6,2,3] :=
  source_excluded a [7,4,8,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2865 : Excluded a [7,4,8,6,2] :=
  branch_excluded a [7,4,8,6,2] (by decide)
    (fin9_cases _
      node_2866
      node_2867
      (invalid_excluded a [7,4,8,6,2,2] (by decide +kernel))
      node_2874
      (invalid_excluded a [7,4,8,6,2,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,2,8] (by decide +kernel)))

theorem node_2875 : Excluded a [7,4,8,6,3] :=
  predecessor_excluded a [7,4,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2862 : Excluded a [7,4,8,6] :=
  branch_excluded a [7,4,8,6] (by decide)
    (fin9_cases _
      node_2863
      node_2864
      node_2865
      node_2875
      (invalid_excluded a [7,4,8,6,4] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,6,8] (by decide +kernel)))

theorem node_2857 : Excluded a [7,4,8] :=
  branch_excluded a [7,4,8] (by decide)
    (fin9_cases _
      node_2858
      node_2859
      node_2860
      (invalid_excluded a [7,4,8,3] (by decide +kernel))
      (invalid_excluded a [7,4,8,4] (by decide +kernel))
      node_2861
      node_2862
      (invalid_excluded a [7,4,8,7] (by decide +kernel))
      (invalid_excluded a [7,4,8,8] (by decide +kernel)))

theorem node_2745 : Excluded a [7,4] :=
  branch_excluded a [7,4] (by decide)
    (fin9_cases _
      node_2746
      node_2812
      (invalid_excluded a [7,4,2] (by decide +kernel))
      (invalid_excluded a [7,4,3] (by decide +kernel))
      (invalid_excluded a [7,4,4] (by decide +kernel))
      node_2813
      node_2824
      (invalid_excluded a [7,4,7] (by decide +kernel))
      node_2857)

theorem node_2878 : Excluded a [7,5,0,1] :=
  predecessor_excluded a [7,5,0,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_2880 : Excluded a [7,5,0,2,1] :=
  source_excluded a [7,5,0,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2881 : Excluded a [7,5,0,2,3] :=
  predecessor_excluded a [7,5,0,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2882 : Excluded a [7,5,0,2,6] :=
  source_excluded a [7,5,0,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2884 : Excluded a [7,5,0,2,8,1] :=
  predecessor_excluded a [7,5,0,2,8,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_2886 : Excluded a [7,5,0,2,8,3,1] :=
  source_excluded a [7,5,0,2,8,3,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2887 : Excluded a [7,5,0,2,8,3,4] :=
  predecessor_excluded a [7,5,0,2,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_2885 : Excluded a [7,5,0,2,8,3] :=
  branch_excluded a [7,5,0,2,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,2,8,3,0] (by decide +kernel))
      node_2886
      (invalid_excluded a [7,5,0,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,3,3] (by decide +kernel))
      node_2887
      (invalid_excluded a [7,5,0,2,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,3,8] (by decide +kernel)))

theorem node_2889 : Excluded a [7,5,0,2,8,4,1] :=
  source_excluded a [7,5,0,2,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2891 : Excluded a [7,5,0,2,8,4,3,1] :=
  source_excluded a [7,5,0,2,8,4,3,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2893 : Excluded a [7,5,0,2,8,4,3,6,1] :=
  predecessor_excluded a [7,5,0,2,8,4,3,6,1] 3 0 8 2 (by decide) (by decide +kernel)

theorem node_2892 : Excluded a [7,5,0,2,8,4,3,6] :=
  branch_excluded a [7,5,0,2,8,4,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,2,8,4,3,6,0] (by decide +kernel))
      node_2893
      (invalid_excluded a [7,5,0,2,8,4,3,6,2] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,6,8] (by decide +kernel)))

theorem node_2890 : Excluded a [7,5,0,2,8,4,3] :=
  branch_excluded a [7,5,0,2,8,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,2,8,4,3,0] (by decide +kernel))
      node_2891
      (invalid_excluded a [7,5,0,2,8,4,3,2] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,5] (by decide +kernel))
      node_2892
      (invalid_excluded a [7,5,0,2,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,3,8] (by decide +kernel)))

theorem node_2888 : Excluded a [7,5,0,2,8,4] :=
  branch_excluded a [7,5,0,2,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,2,8,4,0] (by decide +kernel))
      node_2889
      (invalid_excluded a [7,5,0,2,8,4,2] (by decide +kernel))
      node_2890
      (invalid_excluded a [7,5,0,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,4,8] (by decide +kernel)))

theorem node_2883 : Excluded a [7,5,0,2,8] :=
  branch_excluded a [7,5,0,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,2,8,0] (by decide +kernel))
      node_2884
      (invalid_excluded a [7,5,0,2,8,2] (by decide +kernel))
      node_2885
      node_2888
      (invalid_excluded a [7,5,0,2,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,8,8] (by decide +kernel)))

theorem node_2879 : Excluded a [7,5,0,2] :=
  branch_excluded a [7,5,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,2,0] (by decide +kernel))
      node_2880
      (invalid_excluded a [7,5,0,2,2] (by decide +kernel))
      node_2881
      (invalid_excluded a [7,5,0,2,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,2,5] (by decide +kernel))
      node_2882
      (invalid_excluded a [7,5,0,2,7] (by decide +kernel))
      node_2883)

theorem node_2895 : Excluded a [7,5,0,6,1] :=
  source_excluded a [7,5,0,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2897 : Excluded a [7,5,0,6,2,1] :=
  predecessor_excluded a [7,5,0,6,2,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_2898 : Excluded a [7,5,0,6,2,3] :=
  source_excluded a [7,5,0,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2899 : Excluded a [7,5,0,6,2,4] :=
  source_excluded a [7,5,0,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2901 : Excluded a [7,5,0,6,2,8,1] :=
  source_excluded a [7,5,0,6,2,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2903 : Excluded a [7,5,0,6,2,8,3,1] :=
  source_excluded a [7,5,0,6,2,8,3,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2904 : Excluded a [7,5,0,6,2,8,3,4] :=
  predecessor_excluded a [7,5,0,6,2,8,3,4] 0 2 7 4 (by decide) (by decide +kernel)

theorem node_2902 : Excluded a [7,5,0,6,2,8,3] :=
  branch_excluded a [7,5,0,6,2,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,6,2,8,3,0] (by decide +kernel))
      node_2903
      (invalid_excluded a [7,5,0,6,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,2,8,3,3] (by decide +kernel))
      node_2904
      (invalid_excluded a [7,5,0,6,2,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,2,8,3,8] (by decide +kernel)))

theorem node_2905 : Excluded a [7,5,0,6,2,8,4] :=
  source_excluded a [7,5,0,6,2,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2900 : Excluded a [7,5,0,6,2,8] :=
  branch_excluded a [7,5,0,6,2,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,6,2,8,0] (by decide +kernel))
      node_2901
      (invalid_excluded a [7,5,0,6,2,8,2] (by decide +kernel))
      node_2902
      node_2905
      (invalid_excluded a [7,5,0,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,2,8,8] (by decide +kernel)))

theorem node_2896 : Excluded a [7,5,0,6,2] :=
  branch_excluded a [7,5,0,6,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,6,2,0] (by decide +kernel))
      node_2897
      (invalid_excluded a [7,5,0,6,2,2] (by decide +kernel))
      node_2898
      node_2899
      (invalid_excluded a [7,5,0,6,2,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,2,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,2,7] (by decide +kernel))
      node_2900)

theorem node_2906 : Excluded a [7,5,0,6,3] :=
  predecessor_excluded a [7,5,0,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2908 : Excluded a [7,5,0,6,8,1] :=
  predecessor_excluded a [7,5,0,6,8,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_2909 : Excluded a [7,5,0,6,8,2] :=
  predecessor_excluded a [7,5,0,6,8,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_2910 : Excluded a [7,5,0,6,8,3] :=
  source_excluded a [7,5,0,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2911 : Excluded a [7,5,0,6,8,4] :=
  source_excluded a [7,5,0,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2907 : Excluded a [7,5,0,6,8] :=
  branch_excluded a [7,5,0,6,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,6,8,0] (by decide +kernel))
      node_2908
      node_2909
      node_2910
      node_2911
      (invalid_excluded a [7,5,0,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,8,8] (by decide +kernel)))

theorem node_2894 : Excluded a [7,5,0,6] :=
  branch_excluded a [7,5,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,6,0] (by decide +kernel))
      node_2895
      node_2896
      node_2906
      (invalid_excluded a [7,5,0,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,6,7] (by decide +kernel))
      node_2907)

theorem node_2913 : Excluded a [7,5,0,8,1] :=
  source_excluded a [7,5,0,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2914 : Excluded a [7,5,0,8,2] :=
  predecessor_excluded a [7,5,0,8,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_2916 : Excluded a [7,5,0,8,3,1] :=
  predecessor_excluded a [7,5,0,8,3,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_2918 : Excluded a [7,5,0,8,3,2,1] :=
  source_excluded a [7,5,0,8,3,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2920 : Excluded a [7,5,0,8,3,2,4,1] :=
  source_excluded a [7,5,0,8,3,2,4,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2922 : Excluded a [7,5,0,8,3,2,4,6,1] :=
  predecessor_excluded a [7,5,0,8,3,2,4,6,1] 3 0 8 2 (by decide) (by decide +kernel)

theorem node_2921 : Excluded a [7,5,0,8,3,2,4,6] :=
  branch_excluded a [7,5,0,8,3,2,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,8,3,2,4,6,0] (by decide +kernel))
      node_2922
      (invalid_excluded a [7,5,0,8,3,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,2,4,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,2,4,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,2,4,6,8] (by decide +kernel)))

theorem node_2919 : Excluded a [7,5,0,8,3,2,4] :=
  branch_excluded a [7,5,0,8,3,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,8,3,2,4,0] (by decide +kernel))
      node_2920
      (invalid_excluded a [7,5,0,8,3,2,4,2] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,2,4,3] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,2,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,2,4,5] (by decide +kernel))
      node_2921
      (invalid_excluded a [7,5,0,8,3,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,2,4,8] (by decide +kernel)))

theorem node_2917 : Excluded a [7,5,0,8,3,2] :=
  branch_excluded a [7,5,0,8,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,8,3,2,0] (by decide +kernel))
      node_2918
      (invalid_excluded a [7,5,0,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,2,3] (by decide +kernel))
      node_2919
      (invalid_excluded a [7,5,0,8,3,2,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,2,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,2,8] (by decide +kernel)))

theorem node_2923 : Excluded a [7,5,0,8,3,4] :=
  predecessor_excluded a [7,5,0,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2915 : Excluded a [7,5,0,8,3] :=
  branch_excluded a [7,5,0,8,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,8,3,0] (by decide +kernel))
      node_2916
      node_2917
      (invalid_excluded a [7,5,0,8,3,3] (by decide +kernel))
      node_2923
      (invalid_excluded a [7,5,0,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,3,8] (by decide +kernel)))

theorem node_2924 : Excluded a [7,5,0,8,6] :=
  source_excluded a [7,5,0,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2912 : Excluded a [7,5,0,8] :=
  branch_excluded a [7,5,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,8,0] (by decide +kernel))
      node_2913
      node_2914
      node_2915
      (invalid_excluded a [7,5,0,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,5] (by decide +kernel))
      node_2924
      (invalid_excluded a [7,5,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,0,8,8] (by decide +kernel)))

theorem node_2877 : Excluded a [7,5,0] :=
  branch_excluded a [7,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,0,0] (by decide +kernel))
      node_2878
      node_2879
      (invalid_excluded a [7,5,0,3] (by decide +kernel))
      (invalid_excluded a [7,5,0,4] (by decide +kernel))
      (invalid_excluded a [7,5,0,5] (by decide +kernel))
      node_2894
      (invalid_excluded a [7,5,0,7] (by decide +kernel))
      node_2912)

theorem node_2926 : Excluded a [7,5,1,0] :=
  predecessor_excluded a [7,5,1,0] 4 0 2 3 (by decide) (by decide +kernel)

theorem node_2928 : Excluded a [7,5,1,2,0] :=
  source_excluded a [7,5,1,2,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2929 : Excluded a [7,5,1,2,3] :=
  predecessor_excluded a [7,5,1,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_2930 : Excluded a [7,5,1,2,6] :=
  source_excluded a [7,5,1,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2932 : Excluded a [7,5,1,2,8,0] :=
  source_excluded a [7,5,1,2,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_2934 : Excluded a [7,5,1,2,8,3,0] :=
  source_excluded a [7,5,1,2,8,3,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2935 : Excluded a [7,5,1,2,8,3,4] :=
  predecessor_excluded a [7,5,1,2,8,3,4] 0 8 6 4 (by decide) (by decide +kernel)

theorem node_2933 : Excluded a [7,5,1,2,8,3] :=
  branch_excluded a [7,5,1,2,8,3] (by decide)
    (fin9_cases _
      node_2934
      (invalid_excluded a [7,5,1,2,8,3,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,3,3] (by decide +kernel))
      node_2935
      (invalid_excluded a [7,5,1,2,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,3,8] (by decide +kernel)))

theorem node_2937 : Excluded a [7,5,1,2,8,4,0] :=
  source_excluded a [7,5,1,2,8,4,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2939 : Excluded a [7,5,1,2,8,4,3,0] :=
  predecessor_excluded a [7,5,1,2,8,4,3,0] 2 0 0 7 (by decide) (by decide +kernel)

theorem node_2941 : Excluded a [7,5,1,2,8,4,3,6,0] :=
  predecessor_excluded a [7,5,1,2,8,4,3,6,0] 3 1 8 2 (by decide) (by decide +kernel)

theorem node_2940 : Excluded a [7,5,1,2,8,4,3,6] :=
  branch_excluded a [7,5,1,2,8,4,3,6] (by decide)
    (fin9_cases _
      node_2941
      (invalid_excluded a [7,5,1,2,8,4,3,6,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,3,6,2] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,3,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,3,6,8] (by decide +kernel)))

theorem node_2938 : Excluded a [7,5,1,2,8,4,3] :=
  branch_excluded a [7,5,1,2,8,4,3] (by decide)
    (fin9_cases _
      node_2939
      (invalid_excluded a [7,5,1,2,8,4,3,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,3,2] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,3,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,3,5] (by decide +kernel))
      node_2940
      (invalid_excluded a [7,5,1,2,8,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,3,8] (by decide +kernel)))

theorem node_2936 : Excluded a [7,5,1,2,8,4] :=
  branch_excluded a [7,5,1,2,8,4] (by decide)
    (fin9_cases _
      node_2937
      (invalid_excluded a [7,5,1,2,8,4,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,2] (by decide +kernel))
      node_2938
      (invalid_excluded a [7,5,1,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,4,8] (by decide +kernel)))

theorem node_2931 : Excluded a [7,5,1,2,8] :=
  branch_excluded a [7,5,1,2,8] (by decide)
    (fin9_cases _
      node_2932
      (invalid_excluded a [7,5,1,2,8,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,2] (by decide +kernel))
      node_2933
      node_2936
      (invalid_excluded a [7,5,1,2,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,8,8] (by decide +kernel)))

theorem node_2927 : Excluded a [7,5,1,2] :=
  branch_excluded a [7,5,1,2] (by decide)
    (fin9_cases _
      node_2928
      (invalid_excluded a [7,5,1,2,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,2] (by decide +kernel))
      node_2929
      (invalid_excluded a [7,5,1,2,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,2,5] (by decide +kernel))
      node_2930
      (invalid_excluded a [7,5,1,2,7] (by decide +kernel))
      node_2931)

theorem node_2943 : Excluded a [7,5,1,6,0] :=
  source_excluded a [7,5,1,6,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2945 : Excluded a [7,5,1,6,2,0] :=
  source_excluded a [7,5,1,6,2,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_2946 : Excluded a [7,5,1,6,2,3] :=
  source_excluded a [7,5,1,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2947 : Excluded a [7,5,1,6,2,4] :=
  source_excluded a [7,5,1,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2949 : Excluded a [7,5,1,6,2,8,0] :=
  source_excluded a [7,5,1,6,2,8,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2951 : Excluded a [7,5,1,6,2,8,3,0] :=
  predecessor_excluded a [7,5,1,6,2,8,3,0] 2 0 0 7 (by decide) (by decide +kernel)

theorem node_2952 : Excluded a [7,5,1,6,2,8,3,4] :=
  predecessor_excluded a [7,5,1,6,2,8,3,4] 0 2 7 4 (by decide) (by decide +kernel)

theorem node_2950 : Excluded a [7,5,1,6,2,8,3] :=
  branch_excluded a [7,5,1,6,2,8,3] (by decide)
    (fin9_cases _
      node_2951
      (invalid_excluded a [7,5,1,6,2,8,3,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,2,8,3,2] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,2,8,3,3] (by decide +kernel))
      node_2952
      (invalid_excluded a [7,5,1,6,2,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,2,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,2,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,2,8,3,8] (by decide +kernel)))

theorem node_2953 : Excluded a [7,5,1,6,2,8,4] :=
  source_excluded a [7,5,1,6,2,8,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_2948 : Excluded a [7,5,1,6,2,8] :=
  branch_excluded a [7,5,1,6,2,8] (by decide)
    (fin9_cases _
      node_2949
      (invalid_excluded a [7,5,1,6,2,8,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,2,8,2] (by decide +kernel))
      node_2950
      node_2953
      (invalid_excluded a [7,5,1,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,2,8,8] (by decide +kernel)))

theorem node_2944 : Excluded a [7,5,1,6,2] :=
  branch_excluded a [7,5,1,6,2] (by decide)
    (fin9_cases _
      node_2945
      (invalid_excluded a [7,5,1,6,2,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,2,2] (by decide +kernel))
      node_2946
      node_2947
      (invalid_excluded a [7,5,1,6,2,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,2,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,2,7] (by decide +kernel))
      node_2948)

theorem node_2954 : Excluded a [7,5,1,6,3] :=
  predecessor_excluded a [7,5,1,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_2956 : Excluded a [7,5,1,6,8,0] :=
  source_excluded a [7,5,1,6,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_2957 : Excluded a [7,5,1,6,8,2] :=
  predecessor_excluded a [7,5,1,6,8,2] 0 2 4 5 (by decide) (by decide +kernel)

theorem node_2958 : Excluded a [7,5,1,6,8,3] :=
  source_excluded a [7,5,1,6,8,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_2959 : Excluded a [7,5,1,6,8,4] :=
  source_excluded a [7,5,1,6,8,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_2955 : Excluded a [7,5,1,6,8] :=
  branch_excluded a [7,5,1,6,8] (by decide)
    (fin9_cases _
      node_2956
      (invalid_excluded a [7,5,1,6,8,1] (by decide +kernel))
      node_2957
      node_2958
      node_2959
      (invalid_excluded a [7,5,1,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,8,8] (by decide +kernel)))

theorem node_2942 : Excluded a [7,5,1,6] :=
  branch_excluded a [7,5,1,6] (by decide)
    (fin9_cases _
      node_2943
      (invalid_excluded a [7,5,1,6,1] (by decide +kernel))
      node_2944
      node_2954
      (invalid_excluded a [7,5,1,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,6,7] (by decide +kernel))
      node_2955)

theorem node_2961 : Excluded a [7,5,1,8,0] :=
  source_excluded a [7,5,1,8,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2962 : Excluded a [7,5,1,8,2] :=
  predecessor_excluded a [7,5,1,8,2] 0 2 3 4 (by decide) (by decide +kernel)

theorem node_2964 : Excluded a [7,5,1,8,3,0] :=
  source_excluded a [7,5,1,8,3,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_2966 : Excluded a [7,5,1,8,3,2,0] :=
  source_excluded a [7,5,1,8,3,2,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_2968 : Excluded a [7,5,1,8,3,2,4,0] :=
  predecessor_excluded a [7,5,1,8,3,2,4,0] 2 0 0 7 (by decide) (by decide +kernel)

theorem node_2970 : Excluded a [7,5,1,8,3,2,4,6,0] :=
  predecessor_excluded a [7,5,1,8,3,2,4,6,0] 3 1 8 2 (by decide) (by decide +kernel)

theorem node_2969 : Excluded a [7,5,1,8,3,2,4,6] :=
  branch_excluded a [7,5,1,8,3,2,4,6] (by decide)
    (fin9_cases _
      node_2970
      (invalid_excluded a [7,5,1,8,3,2,4,6,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,4,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,4,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,4,6,8] (by decide +kernel)))

theorem node_2967 : Excluded a [7,5,1,8,3,2,4] :=
  branch_excluded a [7,5,1,8,3,2,4] (by decide)
    (fin9_cases _
      node_2968
      (invalid_excluded a [7,5,1,8,3,2,4,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,4,2] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,4,3] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,4,5] (by decide +kernel))
      node_2969
      (invalid_excluded a [7,5,1,8,3,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,4,8] (by decide +kernel)))

theorem node_2965 : Excluded a [7,5,1,8,3,2] :=
  branch_excluded a [7,5,1,8,3,2] (by decide)
    (fin9_cases _
      node_2966
      (invalid_excluded a [7,5,1,8,3,2,1] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,2] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,3] (by decide +kernel))
      node_2967
      (invalid_excluded a [7,5,1,8,3,2,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,2,8] (by decide +kernel)))

theorem node_2971 : Excluded a [7,5,1,8,3,4] :=
  predecessor_excluded a [7,5,1,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2963 : Excluded a [7,5,1,8,3] :=
  branch_excluded a [7,5,1,8,3] (by decide)
    (fin9_cases _
      node_2964
      (invalid_excluded a [7,5,1,8,3,1] (by decide +kernel))
      node_2965
      (invalid_excluded a [7,5,1,8,3,3] (by decide +kernel))
      node_2971
      (invalid_excluded a [7,5,1,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,3,8] (by decide +kernel)))

theorem node_2972 : Excluded a [7,5,1,8,6] :=
  source_excluded a [7,5,1,8,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_2960 : Excluded a [7,5,1,8] :=
  branch_excluded a [7,5,1,8] (by decide)
    (fin9_cases _
      node_2961
      (invalid_excluded a [7,5,1,8,1] (by decide +kernel))
      node_2962
      node_2963
      (invalid_excluded a [7,5,1,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,5] (by decide +kernel))
      node_2972
      (invalid_excluded a [7,5,1,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,1,8,8] (by decide +kernel)))

theorem node_2925 : Excluded a [7,5,1] :=
  branch_excluded a [7,5,1] (by decide)
    (fin9_cases _
      node_2926
      (invalid_excluded a [7,5,1,1] (by decide +kernel))
      node_2927
      (invalid_excluded a [7,5,1,3] (by decide +kernel))
      (invalid_excluded a [7,5,1,4] (by decide +kernel))
      (invalid_excluded a [7,5,1,5] (by decide +kernel))
      node_2942
      (invalid_excluded a [7,5,1,7] (by decide +kernel))
      node_2960)

theorem node_2973 : Excluded a [7,5,4] :=
  source_excluded a [7,5,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_2976 : Excluded a [7,5,6,0,1] :=
  source_excluded a [7,5,6,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_2977 : Excluded a [7,5,6,0,2] :=
  predecessor_excluded a [7,5,6,0,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_2979 : Excluded a [7,5,6,0,3,1] :=
  predecessor_excluded a [7,5,6,0,3,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_2980 : Excluded a [7,5,6,0,3,2] :=
  source_excluded a [7,5,6,0,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2981 : Excluded a [7,5,6,0,3,4] :=
  predecessor_excluded a [7,5,6,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_2983 : Excluded a [7,5,6,0,3,8,1] :=
  source_excluded a [7,5,6,0,3,8,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2984 : Excluded a [7,5,6,0,3,8,2] :=
  predecessor_excluded a [7,5,6,0,3,8,2] 0 2 5 6 (by decide) (by decide +kernel)

theorem node_2985 : Excluded a [7,5,6,0,3,8,4] :=
  predecessor_excluded a [7,5,6,0,3,8,4] 0 4 2 6 (by decide) (by decide +kernel)

theorem node_2982 : Excluded a [7,5,6,0,3,8] :=
  branch_excluded a [7,5,6,0,3,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,6,0,3,8,0] (by decide +kernel))
      node_2983
      node_2984
      (invalid_excluded a [7,5,6,0,3,8,3] (by decide +kernel))
      node_2985
      (invalid_excluded a [7,5,6,0,3,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,3,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,3,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,3,8,8] (by decide +kernel)))

theorem node_2978 : Excluded a [7,5,6,0,3] :=
  branch_excluded a [7,5,6,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,6,0,3,0] (by decide +kernel))
      node_2979
      node_2980
      (invalid_excluded a [7,5,6,0,3,3] (by decide +kernel))
      node_2981
      (invalid_excluded a [7,5,6,0,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,3,7] (by decide +kernel))
      node_2982)

theorem node_2987 : Excluded a [7,5,6,0,8,1] :=
  predecessor_excluded a [7,5,6,0,8,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_2988 : Excluded a [7,5,6,0,8,2] :=
  source_excluded a [7,5,6,0,8,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_2989 : Excluded a [7,5,6,0,8,3] :=
  source_excluded a [7,5,6,0,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_2991 : Excluded a [7,5,6,0,8,4,1] :=
  source_excluded a [7,5,6,0,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_2993 : Excluded a [7,5,6,0,8,4,2,1] :=
  source_excluded a [7,5,6,0,8,4,2,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_2994 : Excluded a [7,5,6,0,8,4,2,3] :=
  predecessor_excluded a [7,5,6,0,8,4,2,3] 0 3 6 7 (by decide) (by decide +kernel)

theorem node_2992 : Excluded a [7,5,6,0,8,4,2] :=
  branch_excluded a [7,5,6,0,8,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,6,0,8,4,2,0] (by decide +kernel))
      node_2993
      (invalid_excluded a [7,5,6,0,8,4,2,2] (by decide +kernel))
      node_2994
      (invalid_excluded a [7,5,6,0,8,4,2,4] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,4,2,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,4,2,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,4,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,4,2,8] (by decide +kernel)))

theorem node_2995 : Excluded a [7,5,6,0,8,4,3] :=
  source_excluded a [7,5,6,0,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_2990 : Excluded a [7,5,6,0,8,4] :=
  branch_excluded a [7,5,6,0,8,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,6,0,8,4,0] (by decide +kernel))
      node_2991
      node_2992
      node_2995
      (invalid_excluded a [7,5,6,0,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,4,8] (by decide +kernel)))

theorem node_2986 : Excluded a [7,5,6,0,8] :=
  branch_excluded a [7,5,6,0,8] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,6,0,8,0] (by decide +kernel))
      node_2987
      node_2988
      node_2989
      node_2990
      (invalid_excluded a [7,5,6,0,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,8,8] (by decide +kernel)))

theorem node_2975 : Excluded a [7,5,6,0] :=
  branch_excluded a [7,5,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,6,0,0] (by decide +kernel))
      node_2976
      node_2977
      node_2978
      (invalid_excluded a [7,5,6,0,4] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,0,7] (by decide +kernel))
      node_2986)

theorem node_2996 : Excluded a [7,5,6,1] :=
  predecessor_excluded a [7,5,6,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_2998 : Excluded a [7,5,6,2,0] :=
  source_excluded a [7,5,6,2,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_2999 : Excluded a [7,5,6,2,1] :=
  source_excluded a [7,5,6,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_3000 : Excluded a [7,5,6,2,3] :=
  predecessor_excluded a [7,5,6,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_3002 : Excluded a [7,5,6,2,8,0] :=
  source_excluded a [7,5,6,2,8,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3003 : Excluded a [7,5,6,2,8,1] :=
  predecessor_excluded a [7,5,6,2,8,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_3004 : Excluded a [7,5,6,2,8,3] :=
  source_excluded a [7,5,6,2,8,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_3006 : Excluded a [7,5,6,2,8,4,0] :=
  source_excluded a [7,5,6,2,8,4,0] 6 1 0 (by decide) (by decide +kernel)

theorem node_3007 : Excluded a [7,5,6,2,8,4,1] :=
  source_excluded a [7,5,6,2,8,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_3008 : Excluded a [7,5,6,2,8,4,3] :=
  source_excluded a [7,5,6,2,8,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_3005 : Excluded a [7,5,6,2,8,4] :=
  branch_excluded a [7,5,6,2,8,4] (by decide)
    (fin9_cases _
      node_3006
      node_3007
      (invalid_excluded a [7,5,6,2,8,4,2] (by decide +kernel))
      node_3008
      (invalid_excluded a [7,5,6,2,8,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,6,2,8,4,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,2,8,4,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,2,8,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,2,8,4,8] (by decide +kernel)))

theorem node_3001 : Excluded a [7,5,6,2,8] :=
  branch_excluded a [7,5,6,2,8] (by decide)
    (fin9_cases _
      node_3002
      node_3003
      (invalid_excluded a [7,5,6,2,8,2] (by decide +kernel))
      node_3004
      node_3005
      (invalid_excluded a [7,5,6,2,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,2,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,2,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,2,8,8] (by decide +kernel)))

theorem node_2997 : Excluded a [7,5,6,2] :=
  branch_excluded a [7,5,6,2] (by decide)
    (fin9_cases _
      node_2998
      node_2999
      (invalid_excluded a [7,5,6,2,2] (by decide +kernel))
      node_3000
      (invalid_excluded a [7,5,6,2,4] (by decide +kernel))
      (invalid_excluded a [7,5,6,2,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,2,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,2,7] (by decide +kernel))
      node_3001)

theorem node_3010 : Excluded a [7,5,6,8,0] :=
  source_excluded a [7,5,6,8,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_3011 : Excluded a [7,5,6,8,1] :=
  source_excluded a [7,5,6,8,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_3012 : Excluded a [7,5,6,8,2] :=
  predecessor_excluded a [7,5,6,8,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_3014 : Excluded a [7,5,6,8,3,0] :=
  source_excluded a [7,5,6,8,3,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3015 : Excluded a [7,5,6,8,3,1] :=
  predecessor_excluded a [7,5,6,8,3,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_3016 : Excluded a [7,5,6,8,3,2] :=
  source_excluded a [7,5,6,8,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_3017 : Excluded a [7,5,6,8,3,4] :=
  predecessor_excluded a [7,5,6,8,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_3013 : Excluded a [7,5,6,8,3] :=
  branch_excluded a [7,5,6,8,3] (by decide)
    (fin9_cases _
      node_3014
      node_3015
      node_3016
      (invalid_excluded a [7,5,6,8,3,3] (by decide +kernel))
      node_3017
      (invalid_excluded a [7,5,6,8,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,3,8] (by decide +kernel)))

theorem node_3009 : Excluded a [7,5,6,8] :=
  branch_excluded a [7,5,6,8] (by decide)
    (fin9_cases _
      node_3010
      node_3011
      node_3012
      node_3013
      (invalid_excluded a [7,5,6,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,6,8,8] (by decide +kernel)))

theorem node_2974 : Excluded a [7,5,6] :=
  branch_excluded a [7,5,6] (by decide)
    (fin9_cases _
      node_2975
      node_2996
      node_2997
      (invalid_excluded a [7,5,6,3] (by decide +kernel))
      (invalid_excluded a [7,5,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,6,7] (by decide +kernel))
      node_3009)

theorem node_3020 : Excluded a [7,5,8,0,1] :=
  source_excluded a [7,5,8,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_3022 : Excluded a [7,5,8,0,2,1] :=
  predecessor_excluded a [7,5,8,0,2,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_3023 : Excluded a [7,5,8,0,2,3] :=
  predecessor_excluded a [7,5,8,0,2,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_3025 : Excluded a [7,5,8,0,2,4,1] :=
  source_excluded a [7,5,8,0,2,4,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_3027 : Excluded a [7,5,8,0,2,4,3,1] :=
  source_excluded a [7,5,8,0,2,4,3,1] 0 2 7 (by decide) (by decide +kernel)

def b_3029 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 5
  | 2 => 8
  | 3 => 0
  | 4 => 2
  | 5 => 4
  | 6 => 3
  | 7 => 6
  | 8 => 1
  | _ => 0

def cert_3029 : LosingRegion (edgeOf a b_3029) 0 :=
  losingMask a b_3029 0 1212505728303381353595904
    (by decide +kernel) (by decide +kernel)

theorem node_3029 : Excluded a [7,5,8,0,2,4,3,6,1] :=
  losing_excluded a [7,5,8,0,2,4,3,6,1] (by decide) b_3029 (by decide +kernel) 4 0 2 cert_3029 (by change 4 ≠ 0 ∧ ¬ edgeOf a b_3029 4 0 ∧ 2 ≠ 4 ∧ maskRegion 1212505728303381353595904 4 2; decide +kernel)

theorem node_3028 : Excluded a [7,5,8,0,2,4,3,6] :=
  branch_excluded a [7,5,8,0,2,4,3,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,2,4,3,6,0] (by decide +kernel))
      node_3029
      (invalid_excluded a [7,5,8,0,2,4,3,6,2] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,4,3,6,3] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,4,3,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,4,3,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,4,3,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,4,3,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,4,3,6,8] (by decide +kernel)))

theorem node_3026 : Excluded a [7,5,8,0,2,4,3] :=
  branch_excluded a [7,5,8,0,2,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,2,4,3,0] (by decide +kernel))
      node_3027
      (invalid_excluded a [7,5,8,0,2,4,3,2] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,4,3,3] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,4,3,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,4,3,5] (by decide +kernel))
      node_3028
      (invalid_excluded a [7,5,8,0,2,4,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,4,3,8] (by decide +kernel)))

theorem node_3024 : Excluded a [7,5,8,0,2,4] :=
  branch_excluded a [7,5,8,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,2,4,0] (by decide +kernel))
      node_3025
      (invalid_excluded a [7,5,8,0,2,4,2] (by decide +kernel))
      node_3026
      (invalid_excluded a [7,5,8,0,2,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,4,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,4,8] (by decide +kernel)))

theorem node_3021 : Excluded a [7,5,8,0,2] :=
  branch_excluded a [7,5,8,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,2,0] (by decide +kernel))
      node_3022
      (invalid_excluded a [7,5,8,0,2,2] (by decide +kernel))
      node_3023
      node_3024
      (invalid_excluded a [7,5,8,0,2,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,2,8] (by decide +kernel)))

theorem node_3031 : Excluded a [7,5,8,0,3,1] :=
  predecessor_excluded a [7,5,8,0,3,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_3033 : Excluded a [7,5,8,0,3,2,1] :=
  source_excluded a [7,5,8,0,3,2,1] 0 2 6 (by decide) (by decide +kernel)

theorem node_3035 : Excluded a [7,5,8,0,3,2,4,1] :=
  source_excluded a [7,5,8,0,3,2,4,1] 0 2 7 (by decide) (by decide +kernel)

def b_3037 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 7
  | 1 => 5
  | 2 => 8
  | 3 => 0
  | 4 => 3
  | 5 => 2
  | 6 => 4
  | 7 => 6
  | 8 => 1
  | _ => 0

def cert_3037 : LosingRegion (edgeOf a b_3037) 0 :=
  losingMask a b_3037 0 1212510911366010317571072
    (by decide +kernel) (by decide +kernel)

theorem node_3037 : Excluded a [7,5,8,0,3,2,4,6,1] :=
  losing_excluded a [7,5,8,0,3,2,4,6,1] (by decide) b_3037 (by decide +kernel) 4 0 2 cert_3037 (by change 4 ≠ 0 ∧ ¬ edgeOf a b_3037 4 0 ∧ 2 ≠ 4 ∧ maskRegion 1212510911366010317571072 4 2; decide +kernel)

theorem node_3036 : Excluded a [7,5,8,0,3,2,4,6] :=
  branch_excluded a [7,5,8,0,3,2,4,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,3,2,4,6,0] (by decide +kernel))
      node_3037
      (invalid_excluded a [7,5,8,0,3,2,4,6,2] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,2,4,6,3] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,2,4,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,2,4,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,2,4,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,2,4,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,2,4,6,8] (by decide +kernel)))

theorem node_3034 : Excluded a [7,5,8,0,3,2,4] :=
  branch_excluded a [7,5,8,0,3,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,3,2,4,0] (by decide +kernel))
      node_3035
      (invalid_excluded a [7,5,8,0,3,2,4,2] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,2,4,3] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,2,4,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,2,4,5] (by decide +kernel))
      node_3036
      (invalid_excluded a [7,5,8,0,3,2,4,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,2,4,8] (by decide +kernel)))

theorem node_3032 : Excluded a [7,5,8,0,3,2] :=
  branch_excluded a [7,5,8,0,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,3,2,0] (by decide +kernel))
      node_3033
      (invalid_excluded a [7,5,8,0,3,2,2] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,2,3] (by decide +kernel))
      node_3034
      (invalid_excluded a [7,5,8,0,3,2,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,2,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,2,8] (by decide +kernel)))

theorem node_3038 : Excluded a [7,5,8,0,3,4] :=
  predecessor_excluded a [7,5,8,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_3030 : Excluded a [7,5,8,0,3] :=
  branch_excluded a [7,5,8,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,3,0] (by decide +kernel))
      node_3031
      node_3032
      (invalid_excluded a [7,5,8,0,3,3] (by decide +kernel))
      node_3038
      (invalid_excluded a [7,5,8,0,3,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,3,8] (by decide +kernel)))

theorem node_3039 : Excluded a [7,5,8,0,6] :=
  source_excluded a [7,5,8,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_3019 : Excluded a [7,5,8,0] :=
  branch_excluded a [7,5,8,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,5,8,0,0] (by decide +kernel))
      node_3020
      node_3021
      node_3030
      (invalid_excluded a [7,5,8,0,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,5] (by decide +kernel))
      node_3039
      (invalid_excluded a [7,5,8,0,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,0,8] (by decide +kernel)))

theorem node_3040 : Excluded a [7,5,8,1] :=
  predecessor_excluded a [7,5,8,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_3041 : Excluded a [7,5,8,2] :=
  predecessor_excluded a [7,5,8,2] 0 2 2 3 (by decide) (by decide +kernel)

theorem node_3043 : Excluded a [7,5,8,6,0] :=
  source_excluded a [7,5,8,6,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_3044 : Excluded a [7,5,8,6,1] :=
  source_excluded a [7,5,8,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_3046 : Excluded a [7,5,8,6,2,0] :=
  source_excluded a [7,5,8,6,2,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3047 : Excluded a [7,5,8,6,2,1] :=
  predecessor_excluded a [7,5,8,6,2,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_3048 : Excluded a [7,5,8,6,2,3] :=
  source_excluded a [7,5,8,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_3049 : Excluded a [7,5,8,6,2,4] :=
  source_excluded a [7,5,8,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_3045 : Excluded a [7,5,8,6,2] :=
  branch_excluded a [7,5,8,6,2] (by decide)
    (fin9_cases _
      node_3046
      node_3047
      (invalid_excluded a [7,5,8,6,2,2] (by decide +kernel))
      node_3048
      node_3049
      (invalid_excluded a [7,5,8,6,2,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,2,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,2,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,2,8] (by decide +kernel)))

theorem node_3050 : Excluded a [7,5,8,6,3] :=
  predecessor_excluded a [7,5,8,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_3042 : Excluded a [7,5,8,6] :=
  branch_excluded a [7,5,8,6] (by decide)
    (fin9_cases _
      node_3043
      node_3044
      node_3045
      node_3050
      (invalid_excluded a [7,5,8,6,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,5] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,6] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,6,8] (by decide +kernel)))

theorem node_3018 : Excluded a [7,5,8] :=
  branch_excluded a [7,5,8] (by decide)
    (fin9_cases _
      node_3019
      node_3040
      node_3041
      (invalid_excluded a [7,5,8,3] (by decide +kernel))
      (invalid_excluded a [7,5,8,4] (by decide +kernel))
      (invalid_excluded a [7,5,8,5] (by decide +kernel))
      node_3042
      (invalid_excluded a [7,5,8,7] (by decide +kernel))
      (invalid_excluded a [7,5,8,8] (by decide +kernel)))

theorem node_2876 : Excluded a [7,5] :=
  branch_excluded a [7,5] (by decide)
    (fin9_cases _
      node_2877
      node_2925
      (invalid_excluded a [7,5,2] (by decide +kernel))
      (invalid_excluded a [7,5,3] (by decide +kernel))
      node_2973
      (invalid_excluded a [7,5,5] (by decide +kernel))
      node_2974
      (invalid_excluded a [7,5,7] (by decide +kernel))
      node_3018)

theorem node_3051 : Excluded a [7,6] :=
  predecessor_excluded a [7,6] 2 7 1 0 (by decide) (by decide +kernel)

theorem node_3052 : Excluded a [7,8] :=
  predecessor_excluded a [7,8] 2 8 0 1 (by decide) (by decide +kernel)

theorem node_2490 : Excluded a [7] :=
  branch_excluded a [7] (by decide)
    (fin9_cases _
      (invalid_excluded a [7,0] (by decide +kernel))
      (invalid_excluded a [7,1] (by decide +kernel))
      node_2491
      node_2629
      node_2745
      node_2876
      node_3051
      (invalid_excluded a [7,7] (by decide +kernel))
      node_3052)

theorem node_3054 : Excluded a [8,2] :=
  predecessor_excluded a [8,2] 3 2 0 1 (by decide) (by decide +kernel)

theorem node_3056 : Excluded a [8,3,0] :=
  source_excluded a [8,3,0] 1 2 2 (by decide) (by decide +kernel)

theorem node_3057 : Excluded a [8,3,1] :=
  source_excluded a [8,3,1] 2 0 1 (by decide) (by decide +kernel)

theorem node_3058 : Excluded a [8,3,4] :=
  source_excluded a [8,3,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_3060 : Excluded a [8,3,5,0] :=
  source_excluded a [8,3,5,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_3061 : Excluded a [8,3,5,1] :=
  predecessor_excluded a [8,3,5,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_3062 : Excluded a [8,3,5,2] :=
  predecessor_excluded a [8,3,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_3063 : Excluded a [8,3,5,6] :=
  predecessor_excluded a [8,3,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_3066 : Excluded a [8,3,5,7,0,1] :=
  predecessor_excluded a [8,3,5,7,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_3069 : Excluded a [8,3,5,7,0,2,1,4] :=
  source_excluded a [8,3,5,7,0,2,1,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_3071 : Excluded a [8,3,5,7,0,2,1,6,4] :=
  predecessor_excluded a [8,3,5,7,0,2,1,6,4] 0 5 8 2 (by decide) (by decide +kernel)

theorem node_3070 : Excluded a [8,3,5,7,0,2,1,6] :=
  branch_excluded a [8,3,5,7,0,2,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,5,7,0,2,1,6,0] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,6,1] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,6,2] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,6,3] (by decide +kernel))
      node_3071
      (invalid_excluded a [8,3,5,7,0,2,1,6,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,6,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,6,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,6,8] (by decide +kernel)))

theorem node_3068 : Excluded a [8,3,5,7,0,2,1] :=
  branch_excluded a [8,3,5,7,0,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,5,7,0,2,1,0] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,2] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,3] (by decide +kernel))
      node_3069
      (invalid_excluded a [8,3,5,7,0,2,1,5] (by decide +kernel))
      node_3070
      (invalid_excluded a [8,3,5,7,0,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,1,8] (by decide +kernel)))

theorem node_3072 : Excluded a [8,3,5,7,0,2,4] :=
  source_excluded a [8,3,5,7,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_3067 : Excluded a [8,3,5,7,0,2] :=
  branch_excluded a [8,3,5,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,5,7,0,2,0] (by decide +kernel))
      node_3068
      (invalid_excluded a [8,3,5,7,0,2,2] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,3] (by decide +kernel))
      node_3072
      (invalid_excluded a [8,3,5,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,2,8] (by decide +kernel)))

theorem node_3073 : Excluded a [8,3,5,7,0,4] :=
  predecessor_excluded a [8,3,5,7,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_3065 : Excluded a [8,3,5,7,0] :=
  branch_excluded a [8,3,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,5,7,0,0] (by decide +kernel))
      node_3066
      node_3067
      (invalid_excluded a [8,3,5,7,0,3] (by decide +kernel))
      node_3073
      (invalid_excluded a [8,3,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,0,8] (by decide +kernel)))

theorem node_3075 : Excluded a [8,3,5,7,1,0] :=
  predecessor_excluded a [8,3,5,7,1,0] 2 0 4 5 (by decide) (by decide +kernel)

theorem node_3077 : Excluded a [8,3,5,7,1,2,0] :=
  predecessor_excluded a [8,3,5,7,1,2,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_3078 : Excluded a [8,3,5,7,1,2,4] :=
  source_excluded a [8,3,5,7,1,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_3076 : Excluded a [8,3,5,7,1,2] :=
  branch_excluded a [8,3,5,7,1,2] (by decide)
    (fin9_cases _
      node_3077
      (invalid_excluded a [8,3,5,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,1,2,2] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,1,2,3] (by decide +kernel))
      node_3078
      (invalid_excluded a [8,3,5,7,1,2,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,1,2,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,1,2,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,1,2,8] (by decide +kernel)))

theorem node_3079 : Excluded a [8,3,5,7,1,4] :=
  predecessor_excluded a [8,3,5,7,1,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_3074 : Excluded a [8,3,5,7,1] :=
  branch_excluded a [8,3,5,7,1] (by decide)
    (fin9_cases _
      node_3075
      (invalid_excluded a [8,3,5,7,1,1] (by decide +kernel))
      node_3076
      (invalid_excluded a [8,3,5,7,1,3] (by decide +kernel))
      node_3079
      (invalid_excluded a [8,3,5,7,1,5] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,1,8] (by decide +kernel)))

theorem node_3080 : Excluded a [8,3,5,7,2] :=
  source_excluded a [8,3,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_3081 : Excluded a [8,3,5,7,6] :=
  source_excluded a [8,3,5,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_3064 : Excluded a [8,3,5,7] :=
  branch_excluded a [8,3,5,7] (by decide)
    (fin9_cases _
      node_3065
      node_3074
      node_3080
      (invalid_excluded a [8,3,5,7,3] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,4] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,5] (by decide +kernel))
      node_3081
      (invalid_excluded a [8,3,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,3,5,7,8] (by decide +kernel)))

theorem node_3059 : Excluded a [8,3,5] :=
  branch_excluded a [8,3,5] (by decide)
    (fin9_cases _
      node_3060
      node_3061
      node_3062
      (invalid_excluded a [8,3,5,3] (by decide +kernel))
      (invalid_excluded a [8,3,5,4] (by decide +kernel))
      (invalid_excluded a [8,3,5,5] (by decide +kernel))
      node_3063
      node_3064
      (invalid_excluded a [8,3,5,8] (by decide +kernel)))

theorem node_3083 : Excluded a [8,3,6,0] :=
  source_excluded a [8,3,6,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_3084 : Excluded a [8,3,6,1] :=
  predecessor_excluded a [8,3,6,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_3087 : Excluded a [8,3,6,2,0,1] :=
  predecessor_excluded a [8,3,6,2,0,1] 2 1 4 5 (by decide) (by decide +kernel)

def b_3091 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 3
  | 2 => 6
  | 3 => 2
  | 4 => 0
  | 5 => 4
  | 6 => 1
  | 7 => 5
  | 8 => 7
  | _ => 0

def cert_3091 : LosingRegion (edgeOf a b_3091) 0 :=
  losingMask a b_3091 0 2079465719989641885516800
    (by decide +kernel) (by decide +kernel)

theorem node_3091 : Excluded a [8,3,6,2,0,4,1,5,7] :=
  losing_excluded a [8,3,6,2,0,4,1,5,7] (by decide) b_3091 (by decide +kernel) 2 0 5 cert_3091 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_3091 2 0 ∧ 5 ≠ 2 ∧ maskRegion 2079465719989641885516800 2 5; decide +kernel)

theorem node_3090 : Excluded a [8,3,6,2,0,4,1,5] :=
  branch_excluded a [8,3,6,2,0,4,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,6,2,0,4,1,5,0] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,4,1,5,1] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,4,1,5,2] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,4,1,5,3] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,4,1,5,4] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,4,1,5,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,4,1,5,6] (by decide +kernel))
      node_3091
      (invalid_excluded a [8,3,6,2,0,4,1,5,8] (by decide +kernel)))

theorem node_3089 : Excluded a [8,3,6,2,0,4,1] :=
  branch_excluded a [8,3,6,2,0,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,6,2,0,4,1,0] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,4,1,1] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,4,1,2] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,4,1,3] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,4,1,4] (by decide +kernel))
      node_3090
      (invalid_excluded a [8,3,6,2,0,4,1,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,4,1,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,4,1,8] (by decide +kernel)))

theorem node_3092 : Excluded a [8,3,6,2,0,4,5] :=
  predecessor_excluded a [8,3,6,2,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_3088 : Excluded a [8,3,6,2,0,4] :=
  branch_excluded a [8,3,6,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,6,2,0,4,0] (by decide +kernel))
      node_3089
      (invalid_excluded a [8,3,6,2,0,4,2] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,4,3] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,4,4] (by decide +kernel))
      node_3092
      (invalid_excluded a [8,3,6,2,0,4,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,4,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,4,8] (by decide +kernel)))

theorem node_3093 : Excluded a [8,3,6,2,0,7] :=
  source_excluded a [8,3,6,2,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_3086 : Excluded a [8,3,6,2,0] :=
  branch_excluded a [8,3,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,6,2,0,0] (by decide +kernel))
      node_3087
      (invalid_excluded a [8,3,6,2,0,2] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,3] (by decide +kernel))
      node_3088
      (invalid_excluded a [8,3,6,2,0,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,0,6] (by decide +kernel))
      node_3093
      (invalid_excluded a [8,3,6,2,0,8] (by decide +kernel)))

theorem node_3095 : Excluded a [8,3,6,2,1,0] :=
  predecessor_excluded a [8,3,6,2,1,0] 2 0 4 5 (by decide) (by decide +kernel)

theorem node_3097 : Excluded a [8,3,6,2,1,4,0] :=
  predecessor_excluded a [8,3,6,2,1,4,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_3098 : Excluded a [8,3,6,2,1,4,5] :=
  predecessor_excluded a [8,3,6,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_3096 : Excluded a [8,3,6,2,1,4] :=
  branch_excluded a [8,3,6,2,1,4] (by decide)
    (fin9_cases _
      node_3097
      (invalid_excluded a [8,3,6,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,1,4,2] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,1,4,3] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,1,4,4] (by decide +kernel))
      node_3098
      (invalid_excluded a [8,3,6,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,1,4,8] (by decide +kernel)))

theorem node_3099 : Excluded a [8,3,6,2,1,7] :=
  source_excluded a [8,3,6,2,1,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_3094 : Excluded a [8,3,6,2,1] :=
  branch_excluded a [8,3,6,2,1] (by decide)
    (fin9_cases _
      node_3095
      (invalid_excluded a [8,3,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,1,2] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,1,3] (by decide +kernel))
      node_3096
      (invalid_excluded a [8,3,6,2,1,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,1,6] (by decide +kernel))
      node_3099
      (invalid_excluded a [8,3,6,2,1,8] (by decide +kernel)))

theorem node_3102 : Excluded a [8,3,6,2,7,0,1] :=
  predecessor_excluded a [8,3,6,2,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_3103 : Excluded a [8,3,6,2,7,0,4] :=
  source_excluded a [8,3,6,2,7,0,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_3104 : Excluded a [8,3,6,2,7,0,5] :=
  source_excluded a [8,3,6,2,7,0,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_3101 : Excluded a [8,3,6,2,7,0] :=
  branch_excluded a [8,3,6,2,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,6,2,7,0,0] (by decide +kernel))
      node_3102
      (invalid_excluded a [8,3,6,2,7,0,2] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,7,0,3] (by decide +kernel))
      node_3103
      node_3104
      (invalid_excluded a [8,3,6,2,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,7,0,8] (by decide +kernel)))

theorem node_3106 : Excluded a [8,3,6,2,7,1,0] :=
  predecessor_excluded a [8,3,6,2,7,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_3107 : Excluded a [8,3,6,2,7,1,4] :=
  source_excluded a [8,3,6,2,7,1,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_3108 : Excluded a [8,3,6,2,7,1,5] :=
  source_excluded a [8,3,6,2,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_3105 : Excluded a [8,3,6,2,7,1] :=
  branch_excluded a [8,3,6,2,7,1] (by decide)
    (fin9_cases _
      node_3106
      (invalid_excluded a [8,3,6,2,7,1,1] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,7,1,2] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,7,1,3] (by decide +kernel))
      node_3107
      node_3108
      (invalid_excluded a [8,3,6,2,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,7,1,8] (by decide +kernel)))

theorem node_3109 : Excluded a [8,3,6,2,7,4] :=
  predecessor_excluded a [8,3,6,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_3100 : Excluded a [8,3,6,2,7] :=
  branch_excluded a [8,3,6,2,7] (by decide)
    (fin9_cases _
      node_3101
      node_3105
      (invalid_excluded a [8,3,6,2,7,2] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,7,3] (by decide +kernel))
      node_3109
      (invalid_excluded a [8,3,6,2,7,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,7,6] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,7,7] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,7,8] (by decide +kernel)))

theorem node_3085 : Excluded a [8,3,6,2] :=
  branch_excluded a [8,3,6,2] (by decide)
    (fin9_cases _
      node_3086
      node_3094
      (invalid_excluded a [8,3,6,2,2] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,3] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,4] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,3,6,2,6] (by decide +kernel))
      node_3100
      (invalid_excluded a [8,3,6,2,8] (by decide +kernel)))

theorem node_3110 : Excluded a [8,3,6,5] :=
  source_excluded a [8,3,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_3111 : Excluded a [8,3,6,7] :=
  predecessor_excluded a [8,3,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_3082 : Excluded a [8,3,6] :=
  branch_excluded a [8,3,6] (by decide)
    (fin9_cases _
      node_3083
      node_3084
      node_3085
      (invalid_excluded a [8,3,6,3] (by decide +kernel))
      (invalid_excluded a [8,3,6,4] (by decide +kernel))
      node_3110
      (invalid_excluded a [8,3,6,6] (by decide +kernel))
      node_3111
      (invalid_excluded a [8,3,6,8] (by decide +kernel)))

theorem node_3113 : Excluded a [8,3,7,0] :=
  source_excluded a [8,3,7,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_3114 : Excluded a [8,3,7,1] :=
  predecessor_excluded a [8,3,7,1] 2 1 1 3 (by decide) (by decide +kernel)

theorem node_3117 : Excluded a [8,3,7,2,0,1] :=
  predecessor_excluded a [8,3,7,2,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_3121 : Excluded a [8,3,7,2,0,4,1,5,6] :=
  predecessor_excluded a [8,3,7,2,0,4,1,5,6] 0 7 8 2 (by decide) (by decide +kernel)

theorem node_3120 : Excluded a [8,3,7,2,0,4,1,5] :=
  branch_excluded a [8,3,7,2,0,4,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,7,2,0,4,1,5,0] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,5,1] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,5,2] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,5,3] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,5,4] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,5,5] (by decide +kernel))
      node_3121
      (invalid_excluded a [8,3,7,2,0,4,1,5,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,5,8] (by decide +kernel)))

def b_3123 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 3
  | 2 => 7
  | 3 => 2
  | 4 => 0
  | 5 => 4
  | 6 => 1
  | 7 => 6
  | 8 => 5
  | _ => 0

def cert_3123 : LosingRegion (edgeOf a b_3123) 0 :=
  losingMask a b_3123 0 1475030534904583418283008
    (by decide +kernel) (by decide +kernel)

theorem node_3123 : Excluded a [8,3,7,2,0,4,1,6,5] :=
  losing_excluded a [8,3,7,2,0,4,1,6,5] (by decide) b_3123 (by decide +kernel) 2 0 1 cert_3123 (by change 2 ≠ 0 ∧ ¬ edgeOf a b_3123 2 0 ∧ 1 ≠ 2 ∧ maskRegion 1475030534904583418283008 2 1; decide +kernel)

theorem node_3122 : Excluded a [8,3,7,2,0,4,1,6] :=
  branch_excluded a [8,3,7,2,0,4,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,7,2,0,4,1,6,0] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,6,1] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,6,2] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,6,3] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,6,4] (by decide +kernel))
      node_3123
      (invalid_excluded a [8,3,7,2,0,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,6,8] (by decide +kernel)))

theorem node_3119 : Excluded a [8,3,7,2,0,4,1] :=
  branch_excluded a [8,3,7,2,0,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,7,2,0,4,1,0] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,1] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,2] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,3] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,4] (by decide +kernel))
      node_3120
      node_3122
      (invalid_excluded a [8,3,7,2,0,4,1,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,1,8] (by decide +kernel)))

theorem node_3124 : Excluded a [8,3,7,2,0,4,5] :=
  predecessor_excluded a [8,3,7,2,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_3118 : Excluded a [8,3,7,2,0,4] :=
  branch_excluded a [8,3,7,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,7,2,0,4,0] (by decide +kernel))
      node_3119
      (invalid_excluded a [8,3,7,2,0,4,2] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,3] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,4] (by decide +kernel))
      node_3124
      (invalid_excluded a [8,3,7,2,0,4,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,4,8] (by decide +kernel)))

theorem node_3116 : Excluded a [8,3,7,2,0] :=
  branch_excluded a [8,3,7,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,7,2,0,0] (by decide +kernel))
      node_3117
      (invalid_excluded a [8,3,7,2,0,2] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,3] (by decide +kernel))
      node_3118
      (invalid_excluded a [8,3,7,2,0,5] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,0,8] (by decide +kernel)))

theorem node_3126 : Excluded a [8,3,7,2,1,0] :=
  predecessor_excluded a [8,3,7,2,1,0] 2 0 4 5 (by decide) (by decide +kernel)

theorem node_3128 : Excluded a [8,3,7,2,1,4,0] :=
  predecessor_excluded a [8,3,7,2,1,4,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_3129 : Excluded a [8,3,7,2,1,4,5] :=
  predecessor_excluded a [8,3,7,2,1,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_3127 : Excluded a [8,3,7,2,1,4] :=
  branch_excluded a [8,3,7,2,1,4] (by decide)
    (fin9_cases _
      node_3128
      (invalid_excluded a [8,3,7,2,1,4,1] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,1,4,2] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,1,4,3] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,1,4,4] (by decide +kernel))
      node_3129
      (invalid_excluded a [8,3,7,2,1,4,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,1,4,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,1,4,8] (by decide +kernel)))

theorem node_3125 : Excluded a [8,3,7,2,1] :=
  branch_excluded a [8,3,7,2,1] (by decide)
    (fin9_cases _
      node_3126
      (invalid_excluded a [8,3,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,1,2] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,1,3] (by decide +kernel))
      node_3127
      (invalid_excluded a [8,3,7,2,1,5] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,1,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,1,8] (by decide +kernel)))

theorem node_3130 : Excluded a [8,3,7,2,6] :=
  source_excluded a [8,3,7,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_3115 : Excluded a [8,3,7,2] :=
  branch_excluded a [8,3,7,2] (by decide)
    (fin9_cases _
      node_3116
      node_3125
      (invalid_excluded a [8,3,7,2,2] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,3] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,4] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,5] (by decide +kernel))
      node_3130
      (invalid_excluded a [8,3,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,2,8] (by decide +kernel)))

theorem node_3131 : Excluded a [8,3,7,5] :=
  source_excluded a [8,3,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_3134 : Excluded a [8,3,7,6,0,1] :=
  predecessor_excluded a [8,3,7,6,0,1] 2 1 4 5 (by decide) (by decide +kernel)

theorem node_3135 : Excluded a [8,3,7,6,0,2] :=
  predecessor_excluded a [8,3,7,6,0,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_3136 : Excluded a [8,3,7,6,0,4] :=
  source_excluded a [8,3,7,6,0,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_3133 : Excluded a [8,3,7,6,0] :=
  branch_excluded a [8,3,7,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,7,6,0,0] (by decide +kernel))
      node_3134
      node_3135
      (invalid_excluded a [8,3,7,6,0,3] (by decide +kernel))
      node_3136
      (invalid_excluded a [8,3,7,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,0,8] (by decide +kernel)))

theorem node_3138 : Excluded a [8,3,7,6,1,0] :=
  predecessor_excluded a [8,3,7,6,1,0] 2 0 4 5 (by decide) (by decide +kernel)

theorem node_3139 : Excluded a [8,3,7,6,1,2] :=
  predecessor_excluded a [8,3,7,6,1,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_3140 : Excluded a [8,3,7,6,1,4] :=
  source_excluded a [8,3,7,6,1,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_3137 : Excluded a [8,3,7,6,1] :=
  branch_excluded a [8,3,7,6,1] (by decide)
    (fin9_cases _
      node_3138
      (invalid_excluded a [8,3,7,6,1,1] (by decide +kernel))
      node_3139
      (invalid_excluded a [8,3,7,6,1,3] (by decide +kernel))
      node_3140
      (invalid_excluded a [8,3,7,6,1,5] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,1,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,1,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,1,8] (by decide +kernel)))

theorem node_3143 : Excluded a [8,3,7,6,2,0,1] :=
  predecessor_excluded a [8,3,7,6,2,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_3144 : Excluded a [8,3,7,6,2,0,4] :=
  source_excluded a [8,3,7,6,2,0,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_3145 : Excluded a [8,3,7,6,2,0,5] :=
  predecessor_excluded a [8,3,7,6,2,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_3142 : Excluded a [8,3,7,6,2,0] :=
  branch_excluded a [8,3,7,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,3,7,6,2,0,0] (by decide +kernel))
      node_3143
      (invalid_excluded a [8,3,7,6,2,0,2] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,2,0,3] (by decide +kernel))
      node_3144
      node_3145
      (invalid_excluded a [8,3,7,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,2,0,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,2,0,8] (by decide +kernel)))

theorem node_3147 : Excluded a [8,3,7,6,2,1,0] :=
  predecessor_excluded a [8,3,7,6,2,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_3148 : Excluded a [8,3,7,6,2,1,4] :=
  source_excluded a [8,3,7,6,2,1,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_3149 : Excluded a [8,3,7,6,2,1,5] :=
  predecessor_excluded a [8,3,7,6,2,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_3146 : Excluded a [8,3,7,6,2,1] :=
  branch_excluded a [8,3,7,6,2,1] (by decide)
    (fin9_cases _
      node_3147
      (invalid_excluded a [8,3,7,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,2,1,2] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,2,1,3] (by decide +kernel))
      node_3148
      node_3149
      (invalid_excluded a [8,3,7,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,2,1,8] (by decide +kernel)))

theorem node_3150 : Excluded a [8,3,7,6,2,4] :=
  source_excluded a [8,3,7,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_3141 : Excluded a [8,3,7,6,2] :=
  branch_excluded a [8,3,7,6,2] (by decide)
    (fin9_cases _
      node_3142
      node_3146
      (invalid_excluded a [8,3,7,6,2,2] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,2,3] (by decide +kernel))
      node_3150
      (invalid_excluded a [8,3,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,2,8] (by decide +kernel)))

theorem node_3132 : Excluded a [8,3,7,6] :=
  branch_excluded a [8,3,7,6] (by decide)
    (fin9_cases _
      node_3133
      node_3137
      node_3141
      (invalid_excluded a [8,3,7,6,3] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,4] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,5] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,6,8] (by decide +kernel)))

theorem node_3112 : Excluded a [8,3,7] :=
  branch_excluded a [8,3,7] (by decide)
    (fin9_cases _
      node_3113
      node_3114
      node_3115
      (invalid_excluded a [8,3,7,3] (by decide +kernel))
      (invalid_excluded a [8,3,7,4] (by decide +kernel))
      node_3131
      node_3132
      (invalid_excluded a [8,3,7,7] (by decide +kernel))
      (invalid_excluded a [8,3,7,8] (by decide +kernel)))

theorem node_3055 : Excluded a [8,3] :=
  branch_excluded a [8,3] (by decide)
    (fin9_cases _
      node_3056
      node_3057
      (invalid_excluded a [8,3,2] (by decide +kernel))
      (invalid_excluded a [8,3,3] (by decide +kernel))
      node_3058
      node_3059
      node_3082
      node_3112
      (invalid_excluded a [8,3,8] (by decide +kernel)))

theorem node_3153 : Excluded a [8,4,0,1] :=
  source_excluded a [8,4,0,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_3155 : Excluded a [8,4,0,2,1] :=
  predecessor_excluded a [8,4,0,2,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_3156 : Excluded a [8,4,0,2,3] :=
  predecessor_excluded a [8,4,0,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_3157 : Excluded a [8,4,0,2,6] :=
  source_excluded a [8,4,0,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_3161 : Excluded a [8,4,0,2,7,1,3,5] :=
  source_excluded a [8,4,0,2,7,1,3,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_3162 : Excluded a [8,4,0,2,7,1,3,6] :=
  predecessor_excluded a [8,4,0,2,7,1,3,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_3160 : Excluded a [8,4,0,2,7,1,3] :=
  branch_excluded a [8,4,0,2,7,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,2,7,1,3,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,1,3,1] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,1,3,2] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,1,3,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,1,3,4] (by decide +kernel))
      node_3161
      node_3162
      (invalid_excluded a [8,4,0,2,7,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,1,3,8] (by decide +kernel)))

theorem node_3163 : Excluded a [8,4,0,2,7,1,5] :=
  source_excluded a [8,4,0,2,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_3159 : Excluded a [8,4,0,2,7,1] :=
  branch_excluded a [8,4,0,2,7,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,2,7,1,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,1,1] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,1,2] (by decide +kernel))
      node_3160
      (invalid_excluded a [8,4,0,2,7,1,4] (by decide +kernel))
      node_3163
      (invalid_excluded a [8,4,0,2,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,1,8] (by decide +kernel)))

theorem node_3166 : Excluded a [8,4,0,2,7,3,1,5] :=
  source_excluded a [8,4,0,2,7,3,1,5] 4 0 7 (by decide) (by decide +kernel)

theorem node_3167 : Excluded a [8,4,0,2,7,3,1,6] :=
  predecessor_excluded a [8,4,0,2,7,3,1,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_3165 : Excluded a [8,4,0,2,7,3,1] :=
  branch_excluded a [8,4,0,2,7,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,2,7,3,1,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,3,1,1] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,3,1,2] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,3,1,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,3,1,4] (by decide +kernel))
      node_3166
      node_3167
      (invalid_excluded a [8,4,0,2,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,3,1,8] (by decide +kernel)))

theorem node_3168 : Excluded a [8,4,0,2,7,3,5] :=
  source_excluded a [8,4,0,2,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_3164 : Excluded a [8,4,0,2,7,3] :=
  branch_excluded a [8,4,0,2,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,2,7,3,0] (by decide +kernel))
      node_3165
      (invalid_excluded a [8,4,0,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,3,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,3,4] (by decide +kernel))
      node_3168
      (invalid_excluded a [8,4,0,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,3,8] (by decide +kernel)))

theorem node_3158 : Excluded a [8,4,0,2,7] :=
  branch_excluded a [8,4,0,2,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,2,7,0] (by decide +kernel))
      node_3159
      (invalid_excluded a [8,4,0,2,7,2] (by decide +kernel))
      node_3164
      (invalid_excluded a [8,4,0,2,7,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,7,8] (by decide +kernel)))

theorem node_3154 : Excluded a [8,4,0,2] :=
  branch_excluded a [8,4,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,2,0] (by decide +kernel))
      node_3155
      (invalid_excluded a [8,4,0,2,2] (by decide +kernel))
      node_3156
      (invalid_excluded a [8,4,0,2,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,2,5] (by decide +kernel))
      node_3157
      node_3158
      (invalid_excluded a [8,4,0,2,8] (by decide +kernel)))

theorem node_3169 : Excluded a [8,4,0,5] :=
  source_excluded a [8,4,0,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_3171 : Excluded a [8,4,0,6,1] :=
  predecessor_excluded a [8,4,0,6,1] 2 1 1 4 (by decide) (by decide +kernel)

def b_3176 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 4
  | 2 => 0
  | 3 => 6
  | 4 => 2
  | 5 => 1
  | 6 => 3
  | 7 => 5
  | 8 => 7
  | _ => 0

def cert_3176 : LosingRegion (edgeOf a b_3176) 0 :=
  losingMask a b_3176 0 1304775085040091295384576
    (by decide +kernel) (by decide +kernel)

theorem node_3176 : Excluded a [8,4,0,6,2,1,3,5,7] :=
  losing_excluded a [8,4,0,6,2,1,3,5,7] (by decide) b_3176 (by decide +kernel) 3 0 1 cert_3176 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_3176 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1304775085040091295384576 3 1; decide +kernel)

theorem node_3175 : Excluded a [8,4,0,6,2,1,3,5] :=
  branch_excluded a [8,4,0,6,2,1,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,6,2,1,3,5,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,1,3,5,1] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,1,3,5,2] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,1,3,5,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,1,3,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,1,3,5,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,1,3,5,6] (by decide +kernel))
      node_3176
      (invalid_excluded a [8,4,0,6,2,1,3,5,8] (by decide +kernel)))

theorem node_3174 : Excluded a [8,4,0,6,2,1,3] :=
  branch_excluded a [8,4,0,6,2,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,6,2,1,3,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,1,3,1] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,1,3,2] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,1,3,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,1,3,4] (by decide +kernel))
      node_3175
      (invalid_excluded a [8,4,0,6,2,1,3,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,1,3,8] (by decide +kernel)))

theorem node_3177 : Excluded a [8,4,0,6,2,1,5] :=
  predecessor_excluded a [8,4,0,6,2,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_3173 : Excluded a [8,4,0,6,2,1] :=
  branch_excluded a [8,4,0,6,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,6,2,1,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,1,2] (by decide +kernel))
      node_3174
      (invalid_excluded a [8,4,0,6,2,1,4] (by decide +kernel))
      node_3177
      (invalid_excluded a [8,4,0,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,1,8] (by decide +kernel)))

theorem node_3178 : Excluded a [8,4,0,6,2,3] :=
  source_excluded a [8,4,0,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_3179 : Excluded a [8,4,0,6,2,7] :=
  source_excluded a [8,4,0,6,2,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_3172 : Excluded a [8,4,0,6,2] :=
  branch_excluded a [8,4,0,6,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,6,2,0] (by decide +kernel))
      node_3173
      (invalid_excluded a [8,4,0,6,2,2] (by decide +kernel))
      node_3178
      (invalid_excluded a [8,4,0,6,2,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,2,6] (by decide +kernel))
      node_3179
      (invalid_excluded a [8,4,0,6,2,8] (by decide +kernel)))

theorem node_3180 : Excluded a [8,4,0,6,3] :=
  predecessor_excluded a [8,4,0,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_3181 : Excluded a [8,4,0,6,7] :=
  predecessor_excluded a [8,4,0,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_3170 : Excluded a [8,4,0,6] :=
  branch_excluded a [8,4,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,6,0] (by decide +kernel))
      node_3171
      node_3172
      node_3180
      (invalid_excluded a [8,4,0,6,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,6,6] (by decide +kernel))
      node_3181
      (invalid_excluded a [8,4,0,6,8] (by decide +kernel)))

theorem node_3183 : Excluded a [8,4,0,7,1] :=
  predecessor_excluded a [8,4,0,7,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_3186 : Excluded a [8,4,0,7,2,1,3] :=
  source_excluded a [8,4,0,7,2,1,3] 6 0 3 (by decide) (by decide +kernel)

def b_3189 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 4
  | 2 => 0
  | 3 => 7
  | 4 => 2
  | 5 => 1
  | 6 => 5
  | 7 => 3
  | 8 => 6
  | _ => 0

def cert_3189 : LosingRegion (edgeOf a b_3189) 0 :=
  losingMask a b_3189 0 1307202993613605239260160
    (by decide +kernel) (by decide +kernel)

theorem node_3189 : Excluded a [8,4,0,7,2,1,5,3,6] :=
  losing_excluded a [8,4,0,7,2,1,5,3,6] (by decide) b_3189 (by decide +kernel) 3 0 1 cert_3189 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_3189 3 0 ∧ 1 ≠ 3 ∧ maskRegion 1307202993613605239260160 3 1; decide +kernel)

theorem node_3188 : Excluded a [8,4,0,7,2,1,5,3] :=
  branch_excluded a [8,4,0,7,2,1,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,2,1,5,3,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,1,5,3,1] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,1,5,3,2] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,1,5,3,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,1,5,3,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,1,5,3,5] (by decide +kernel))
      node_3189
      (invalid_excluded a [8,4,0,7,2,1,5,3,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,1,5,3,8] (by decide +kernel)))

theorem node_3190 : Excluded a [8,4,0,7,2,1,5,6] :=
  predecessor_excluded a [8,4,0,7,2,1,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_3187 : Excluded a [8,4,0,7,2,1,5] :=
  branch_excluded a [8,4,0,7,2,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,2,1,5,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,1,5,1] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,1,5,2] (by decide +kernel))
      node_3188
      (invalid_excluded a [8,4,0,7,2,1,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,1,5,5] (by decide +kernel))
      node_3190
      (invalid_excluded a [8,4,0,7,2,1,5,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,1,5,8] (by decide +kernel)))

theorem node_3185 : Excluded a [8,4,0,7,2,1] :=
  branch_excluded a [8,4,0,7,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,2,1,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,1,2] (by decide +kernel))
      node_3186
      (invalid_excluded a [8,4,0,7,2,1,4] (by decide +kernel))
      node_3187
      (invalid_excluded a [8,4,0,7,2,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,1,8] (by decide +kernel)))

theorem node_3191 : Excluded a [8,4,0,7,2,3] :=
  predecessor_excluded a [8,4,0,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_3184 : Excluded a [8,4,0,7,2] :=
  branch_excluded a [8,4,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,2,0] (by decide +kernel))
      node_3185
      (invalid_excluded a [8,4,0,7,2,2] (by decide +kernel))
      node_3191
      (invalid_excluded a [8,4,0,7,2,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,2,8] (by decide +kernel)))

theorem node_3195 : Excluded a [8,4,0,7,3,1,2,5] :=
  predecessor_excluded a [8,4,0,7,3,1,2,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_3196 : Excluded a [8,4,0,7,3,1,2,6] :=
  predecessor_excluded a [8,4,0,7,3,1,2,6] 0 2 7 6 (by decide) (by decide +kernel)

theorem node_3194 : Excluded a [8,4,0,7,3,1,2] :=
  branch_excluded a [8,4,0,7,3,1,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,3,1,2,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,1,2,1] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,1,2,2] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,1,2,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,1,2,4] (by decide +kernel))
      node_3195
      node_3196
      (invalid_excluded a [8,4,0,7,3,1,2,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,1,2,8] (by decide +kernel)))

theorem node_3198 : Excluded a [8,4,0,7,3,1,5,2] :=
  source_excluded a [8,4,0,7,3,1,5,2] 7 0 8 (by decide) (by decide +kernel)

theorem node_3199 : Excluded a [8,4,0,7,3,1,5,6] :=
  predecessor_excluded a [8,4,0,7,3,1,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_3197 : Excluded a [8,4,0,7,3,1,5] :=
  branch_excluded a [8,4,0,7,3,1,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,3,1,5,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,1,5,1] (by decide +kernel))
      node_3198
      (invalid_excluded a [8,4,0,7,3,1,5,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,1,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,1,5,5] (by decide +kernel))
      node_3199
      (invalid_excluded a [8,4,0,7,3,1,5,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,1,5,8] (by decide +kernel)))

theorem node_3193 : Excluded a [8,4,0,7,3,1] :=
  branch_excluded a [8,4,0,7,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,3,1,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,1,1] (by decide +kernel))
      node_3194
      (invalid_excluded a [8,4,0,7,3,1,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,1,4] (by decide +kernel))
      node_3197
      (invalid_excluded a [8,4,0,7,3,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,1,8] (by decide +kernel)))

theorem node_3202 : Excluded a [8,4,0,7,3,2,1,5] :=
  predecessor_excluded a [8,4,0,7,3,2,1,5] 0 2 7 5 (by decide) (by decide +kernel)

theorem node_3204 : Excluded a [8,4,0,7,3,2,1,6,5] :=
  source_excluded a [8,4,0,7,3,2,1,6,5] 8 0 5 (by decide) (by decide +kernel)

theorem node_3203 : Excluded a [8,4,0,7,3,2,1,6] :=
  branch_excluded a [8,4,0,7,3,2,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,3,2,1,6,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,1,6,1] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,1,6,2] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,1,6,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,1,6,4] (by decide +kernel))
      node_3204
      (invalid_excluded a [8,4,0,7,3,2,1,6,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,1,6,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,1,6,8] (by decide +kernel)))

theorem node_3201 : Excluded a [8,4,0,7,3,2,1] :=
  branch_excluded a [8,4,0,7,3,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,3,2,1,0] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,1,2] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,1,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,1,4] (by decide +kernel))
      node_3202
      node_3203
      (invalid_excluded a [8,4,0,7,3,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,1,8] (by decide +kernel)))

theorem node_3206 : Excluded a [8,4,0,7,3,2,5,1] :=
  source_excluded a [8,4,0,7,3,2,5,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_3207 : Excluded a [8,4,0,7,3,2,5,6] :=
  predecessor_excluded a [8,4,0,7,3,2,5,6] 0 6 6 7 (by decide) (by decide +kernel)

theorem node_3205 : Excluded a [8,4,0,7,3,2,5] :=
  branch_excluded a [8,4,0,7,3,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,3,2,5,0] (by decide +kernel))
      node_3206
      (invalid_excluded a [8,4,0,7,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,5,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,5,5] (by decide +kernel))
      node_3207
      (invalid_excluded a [8,4,0,7,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,5,8] (by decide +kernel)))

theorem node_3200 : Excluded a [8,4,0,7,3,2] :=
  branch_excluded a [8,4,0,7,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,3,2,0] (by decide +kernel))
      node_3201
      (invalid_excluded a [8,4,0,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,4] (by decide +kernel))
      node_3205
      (invalid_excluded a [8,4,0,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,2,8] (by decide +kernel)))

theorem node_3192 : Excluded a [8,4,0,7,3] :=
  branch_excluded a [8,4,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,3,0] (by decide +kernel))
      node_3193
      node_3200
      (invalid_excluded a [8,4,0,7,3,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,3,8] (by decide +kernel)))

theorem node_3208 : Excluded a [8,4,0,7,6] :=
  source_excluded a [8,4,0,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_3182 : Excluded a [8,4,0,7] :=
  branch_excluded a [8,4,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,7,0] (by decide +kernel))
      node_3183
      node_3184
      node_3192
      (invalid_excluded a [8,4,0,7,4] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,5] (by decide +kernel))
      node_3208
      (invalid_excluded a [8,4,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,0,7,8] (by decide +kernel)))

theorem node_3152 : Excluded a [8,4,0] :=
  branch_excluded a [8,4,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,0,0] (by decide +kernel))
      node_3153
      node_3154
      (invalid_excluded a [8,4,0,3] (by decide +kernel))
      (invalid_excluded a [8,4,0,4] (by decide +kernel))
      node_3169
      node_3170
      node_3182
      (invalid_excluded a [8,4,0,8] (by decide +kernel)))

theorem node_3209 : Excluded a [8,4,1] :=
  predecessor_excluded a [8,4,1] 0 4 2 1 (by decide) (by decide +kernel)

theorem node_3211 : Excluded a [8,4,5,0] :=
  source_excluded a [8,4,5,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_3212 : Excluded a [8,4,5,1] :=
  source_excluded a [8,4,5,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_3213 : Excluded a [8,4,5,2] :=
  predecessor_excluded a [8,4,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_3214 : Excluded a [8,4,5,6] :=
  predecessor_excluded a [8,4,5,6] 0 6 2 3 (by decide) (by decide +kernel)

theorem node_3216 : Excluded a [8,4,5,7,0] :=
  source_excluded a [8,4,5,7,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_3217 : Excluded a [8,4,5,7,1] :=
  predecessor_excluded a [8,4,5,7,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_3218 : Excluded a [8,4,5,7,2] :=
  source_excluded a [8,4,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_3219 : Excluded a [8,4,5,7,3] :=
  source_excluded a [8,4,5,7,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_3220 : Excluded a [8,4,5,7,6] :=
  source_excluded a [8,4,5,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_3215 : Excluded a [8,4,5,7] :=
  branch_excluded a [8,4,5,7] (by decide)
    (fin9_cases _
      node_3216
      node_3217
      node_3218
      node_3219
      (invalid_excluded a [8,4,5,7,4] (by decide +kernel))
      (invalid_excluded a [8,4,5,7,5] (by decide +kernel))
      node_3220
      (invalid_excluded a [8,4,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,5,7,8] (by decide +kernel)))

theorem node_3210 : Excluded a [8,4,5] :=
  branch_excluded a [8,4,5] (by decide)
    (fin9_cases _
      node_3211
      node_3212
      node_3213
      (invalid_excluded a [8,4,5,3] (by decide +kernel))
      (invalid_excluded a [8,4,5,4] (by decide +kernel))
      (invalid_excluded a [8,4,5,5] (by decide +kernel))
      node_3214
      node_3215
      (invalid_excluded a [8,4,5,8] (by decide +kernel)))

theorem node_3222 : Excluded a [8,4,6,0] :=
  source_excluded a [8,4,6,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_3223 : Excluded a [8,4,6,1] :=
  source_excluded a [8,4,6,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_3225 : Excluded a [8,4,6,2,0] :=
  source_excluded a [8,4,6,2,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_3226 : Excluded a [8,4,6,2,1] :=
  predecessor_excluded a [8,4,6,2,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_3227 : Excluded a [8,4,6,2,3] :=
  predecessor_excluded a [8,4,6,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_3230 : Excluded a [8,4,6,2,7,0,1] :=
  predecessor_excluded a [8,4,6,2,7,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_3231 : Excluded a [8,4,6,2,7,0,3] :=
  source_excluded a [8,4,6,2,7,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_3232 : Excluded a [8,4,6,2,7,0,5] :=
  source_excluded a [8,4,6,2,7,0,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_3229 : Excluded a [8,4,6,2,7,0] :=
  branch_excluded a [8,4,6,2,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,6,2,7,0,0] (by decide +kernel))
      node_3230
      (invalid_excluded a [8,4,6,2,7,0,2] (by decide +kernel))
      node_3231
      (invalid_excluded a [8,4,6,2,7,0,4] (by decide +kernel))
      node_3232
      (invalid_excluded a [8,4,6,2,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,2,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,2,7,0,8] (by decide +kernel)))

theorem node_3234 : Excluded a [8,4,6,2,7,1,0] :=
  predecessor_excluded a [8,4,6,2,7,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_3235 : Excluded a [8,4,6,2,7,1,3] :=
  source_excluded a [8,4,6,2,7,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_3236 : Excluded a [8,4,6,2,7,1,5] :=
  source_excluded a [8,4,6,2,7,1,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_3233 : Excluded a [8,4,6,2,7,1] :=
  branch_excluded a [8,4,6,2,7,1] (by decide)
    (fin9_cases _
      node_3234
      (invalid_excluded a [8,4,6,2,7,1,1] (by decide +kernel))
      (invalid_excluded a [8,4,6,2,7,1,2] (by decide +kernel))
      node_3235
      (invalid_excluded a [8,4,6,2,7,1,4] (by decide +kernel))
      node_3236
      (invalid_excluded a [8,4,6,2,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,2,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,2,7,1,8] (by decide +kernel)))

theorem node_3237 : Excluded a [8,4,6,2,7,3] :=
  source_excluded a [8,4,6,2,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_3228 : Excluded a [8,4,6,2,7] :=
  branch_excluded a [8,4,6,2,7] (by decide)
    (fin9_cases _
      node_3229
      node_3233
      (invalid_excluded a [8,4,6,2,7,2] (by decide +kernel))
      node_3237
      (invalid_excluded a [8,4,6,2,7,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,2,7,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,2,7,6] (by decide +kernel))
      (invalid_excluded a [8,4,6,2,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,6,2,7,8] (by decide +kernel)))

theorem node_3224 : Excluded a [8,4,6,2] :=
  branch_excluded a [8,4,6,2] (by decide)
    (fin9_cases _
      node_3225
      node_3226
      (invalid_excluded a [8,4,6,2,2] (by decide +kernel))
      node_3227
      (invalid_excluded a [8,4,6,2,4] (by decide +kernel))
      (invalid_excluded a [8,4,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,4,6,2,6] (by decide +kernel))
      node_3228
      (invalid_excluded a [8,4,6,2,8] (by decide +kernel)))

theorem node_3238 : Excluded a [8,4,6,5] :=
  source_excluded a [8,4,6,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_3239 : Excluded a [8,4,6,7] :=
  predecessor_excluded a [8,4,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_3221 : Excluded a [8,4,6] :=
  branch_excluded a [8,4,6] (by decide)
    (fin9_cases _
      node_3222
      node_3223
      node_3224
      (invalid_excluded a [8,4,6,3] (by decide +kernel))
      (invalid_excluded a [8,4,6,4] (by decide +kernel))
      node_3238
      (invalid_excluded a [8,4,6,6] (by decide +kernel))
      node_3239
      (invalid_excluded a [8,4,6,8] (by decide +kernel)))

theorem node_3241 : Excluded a [8,4,7,0] :=
  source_excluded a [8,4,7,0] 1 2 3 (by decide) (by decide +kernel)

theorem node_3242 : Excluded a [8,4,7,1] :=
  source_excluded a [8,4,7,1] 3 0 1 (by decide) (by decide +kernel)

theorem node_3244 : Excluded a [8,4,7,2,0] :=
  source_excluded a [8,4,7,2,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_3245 : Excluded a [8,4,7,2,1] :=
  predecessor_excluded a [8,4,7,2,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_3246 : Excluded a [8,4,7,2,3] :=
  predecessor_excluded a [8,4,7,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_3247 : Excluded a [8,4,7,2,6] :=
  source_excluded a [8,4,7,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_3243 : Excluded a [8,4,7,2] :=
  branch_excluded a [8,4,7,2] (by decide)
    (fin9_cases _
      node_3244
      node_3245
      (invalid_excluded a [8,4,7,2,2] (by decide +kernel))
      node_3246
      (invalid_excluded a [8,4,7,2,4] (by decide +kernel))
      (invalid_excluded a [8,4,7,2,5] (by decide +kernel))
      node_3247
      (invalid_excluded a [8,4,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,2,8] (by decide +kernel)))

theorem node_3248 : Excluded a [8,4,7,5] :=
  source_excluded a [8,4,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_3250 : Excluded a [8,4,7,6,0] :=
  source_excluded a [8,4,7,6,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_3251 : Excluded a [8,4,7,6,1] :=
  predecessor_excluded a [8,4,7,6,1] 2 1 1 4 (by decide) (by decide +kernel)

theorem node_3254 : Excluded a [8,4,7,6,2,0,1] :=
  predecessor_excluded a [8,4,7,6,2,0,1] 2 1 5 6 (by decide) (by decide +kernel)

theorem node_3255 : Excluded a [8,4,7,6,2,0,3] :=
  source_excluded a [8,4,7,6,2,0,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_3256 : Excluded a [8,4,7,6,2,0,5] :=
  predecessor_excluded a [8,4,7,6,2,0,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_3253 : Excluded a [8,4,7,6,2,0] :=
  branch_excluded a [8,4,7,6,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,4,7,6,2,0,0] (by decide +kernel))
      node_3254
      (invalid_excluded a [8,4,7,6,2,0,2] (by decide +kernel))
      node_3255
      (invalid_excluded a [8,4,7,6,2,0,4] (by decide +kernel))
      node_3256
      (invalid_excluded a [8,4,7,6,2,0,6] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,2,0,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,2,0,8] (by decide +kernel)))

theorem node_3258 : Excluded a [8,4,7,6,2,1,0] :=
  predecessor_excluded a [8,4,7,6,2,1,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_3259 : Excluded a [8,4,7,6,2,1,3] :=
  source_excluded a [8,4,7,6,2,1,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_3260 : Excluded a [8,4,7,6,2,1,5] :=
  predecessor_excluded a [8,4,7,6,2,1,5] 0 5 3 6 (by decide) (by decide +kernel)

theorem node_3257 : Excluded a [8,4,7,6,2,1] :=
  branch_excluded a [8,4,7,6,2,1] (by decide)
    (fin9_cases _
      node_3258
      (invalid_excluded a [8,4,7,6,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,2,1,2] (by decide +kernel))
      node_3259
      (invalid_excluded a [8,4,7,6,2,1,4] (by decide +kernel))
      node_3260
      (invalid_excluded a [8,4,7,6,2,1,6] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,2,1,8] (by decide +kernel)))

theorem node_3261 : Excluded a [8,4,7,6,2,3] :=
  source_excluded a [8,4,7,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_3252 : Excluded a [8,4,7,6,2] :=
  branch_excluded a [8,4,7,6,2] (by decide)
    (fin9_cases _
      node_3253
      node_3257
      (invalid_excluded a [8,4,7,6,2,2] (by decide +kernel))
      node_3261
      (invalid_excluded a [8,4,7,6,2,4] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,2,8] (by decide +kernel)))

theorem node_3262 : Excluded a [8,4,7,6,3] :=
  predecessor_excluded a [8,4,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_3249 : Excluded a [8,4,7,6] :=
  branch_excluded a [8,4,7,6] (by decide)
    (fin9_cases _
      node_3250
      node_3251
      node_3252
      node_3262
      (invalid_excluded a [8,4,7,6,4] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,5] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,6,8] (by decide +kernel)))

theorem node_3240 : Excluded a [8,4,7] :=
  branch_excluded a [8,4,7] (by decide)
    (fin9_cases _
      node_3241
      node_3242
      node_3243
      (invalid_excluded a [8,4,7,3] (by decide +kernel))
      (invalid_excluded a [8,4,7,4] (by decide +kernel))
      node_3248
      node_3249
      (invalid_excluded a [8,4,7,7] (by decide +kernel))
      (invalid_excluded a [8,4,7,8] (by decide +kernel)))

theorem node_3151 : Excluded a [8,4] :=
  branch_excluded a [8,4] (by decide)
    (fin9_cases _
      node_3152
      node_3209
      (invalid_excluded a [8,4,2] (by decide +kernel))
      (invalid_excluded a [8,4,3] (by decide +kernel))
      (invalid_excluded a [8,4,4] (by decide +kernel))
      node_3210
      node_3221
      node_3240
      (invalid_excluded a [8,4,8] (by decide +kernel)))

theorem node_3265 : Excluded a [8,5,0,1] :=
  predecessor_excluded a [8,5,0,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_3267 : Excluded a [8,5,0,2,1] :=
  source_excluded a [8,5,0,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_3268 : Excluded a [8,5,0,2,3] :=
  predecessor_excluded a [8,5,0,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_3269 : Excluded a [8,5,0,2,6] :=
  source_excluded a [8,5,0,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_3271 : Excluded a [8,5,0,2,7,1] :=
  predecessor_excluded a [8,5,0,2,7,1] 2 1 1 5 (by decide) (by decide +kernel)

def b_3275 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 5
  | 2 => 0
  | 3 => 2
  | 4 => 7
  | 5 => 3
  | 6 => 1
  | 7 => 4
  | 8 => 6
  | _ => 0

def cert_3275 : LosingRegion (edgeOf a b_3275) 0 :=
  losingMask a b_3275 0 1231478181549213836379136
    (by decide +kernel) (by decide +kernel)

theorem node_3275 : Excluded a [8,5,0,2,7,3,1,4,6] :=
  losing_excluded a [8,5,0,2,7,3,1,4,6] (by decide) b_3275 (by decide +kernel) 3 0 2 cert_3275 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_3275 3 0 ∧ 2 ≠ 3 ∧ maskRegion 1231478181549213836379136 3 2; decide +kernel)

theorem node_3274 : Excluded a [8,5,0,2,7,3,1,4] :=
  branch_excluded a [8,5,0,2,7,3,1,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,2,7,3,1,4,0] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,3,1,4,1] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,3,1,4,2] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,3,1,4,3] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,3,1,4,4] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,3,1,4,5] (by decide +kernel))
      node_3275
      (invalid_excluded a [8,5,0,2,7,3,1,4,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,3,1,4,8] (by decide +kernel)))

theorem node_3276 : Excluded a [8,5,0,2,7,3,1,6] :=
  predecessor_excluded a [8,5,0,2,7,3,1,6] 0 6 4 7 (by decide) (by decide +kernel)

theorem node_3273 : Excluded a [8,5,0,2,7,3,1] :=
  branch_excluded a [8,5,0,2,7,3,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,2,7,3,1,0] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,3,1,1] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,3,1,2] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,3,1,3] (by decide +kernel))
      node_3274
      (invalid_excluded a [8,5,0,2,7,3,1,5] (by decide +kernel))
      node_3276
      (invalid_excluded a [8,5,0,2,7,3,1,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,3,1,8] (by decide +kernel)))

theorem node_3277 : Excluded a [8,5,0,2,7,3,4] :=
  source_excluded a [8,5,0,2,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_3272 : Excluded a [8,5,0,2,7,3] :=
  branch_excluded a [8,5,0,2,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,2,7,3,0] (by decide +kernel))
      node_3273
      (invalid_excluded a [8,5,0,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,3,3] (by decide +kernel))
      node_3277
      (invalid_excluded a [8,5,0,2,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,3,8] (by decide +kernel)))

theorem node_3278 : Excluded a [8,5,0,2,7,4] :=
  predecessor_excluded a [8,5,0,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_3270 : Excluded a [8,5,0,2,7] :=
  branch_excluded a [8,5,0,2,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,2,7,0] (by decide +kernel))
      node_3271
      (invalid_excluded a [8,5,0,2,7,2] (by decide +kernel))
      node_3272
      node_3278
      (invalid_excluded a [8,5,0,2,7,5] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,6] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,7,8] (by decide +kernel)))

theorem node_3266 : Excluded a [8,5,0,2] :=
  branch_excluded a [8,5,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,2,0] (by decide +kernel))
      node_3267
      (invalid_excluded a [8,5,0,2,2] (by decide +kernel))
      node_3268
      (invalid_excluded a [8,5,0,2,4] (by decide +kernel))
      (invalid_excluded a [8,5,0,2,5] (by decide +kernel))
      node_3269
      node_3270
      (invalid_excluded a [8,5,0,2,8] (by decide +kernel)))

theorem node_3280 : Excluded a [8,5,0,6,1] :=
  source_excluded a [8,5,0,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_3282 : Excluded a [8,5,0,6,2,1] :=
  predecessor_excluded a [8,5,0,6,2,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_3283 : Excluded a [8,5,0,6,2,3] :=
  source_excluded a [8,5,0,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_3284 : Excluded a [8,5,0,6,2,4] :=
  source_excluded a [8,5,0,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_3285 : Excluded a [8,5,0,6,2,7] :=
  source_excluded a [8,5,0,6,2,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_3281 : Excluded a [8,5,0,6,2] :=
  branch_excluded a [8,5,0,6,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,6,2,0] (by decide +kernel))
      node_3282
      (invalid_excluded a [8,5,0,6,2,2] (by decide +kernel))
      node_3283
      node_3284
      (invalid_excluded a [8,5,0,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,5,0,6,2,6] (by decide +kernel))
      node_3285
      (invalid_excluded a [8,5,0,6,2,8] (by decide +kernel)))

theorem node_3286 : Excluded a [8,5,0,6,3] :=
  predecessor_excluded a [8,5,0,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_3287 : Excluded a [8,5,0,6,7] :=
  predecessor_excluded a [8,5,0,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_3279 : Excluded a [8,5,0,6] :=
  branch_excluded a [8,5,0,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,6,0] (by decide +kernel))
      node_3280
      node_3281
      node_3286
      (invalid_excluded a [8,5,0,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,0,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,0,6,6] (by decide +kernel))
      node_3287
      (invalid_excluded a [8,5,0,6,8] (by decide +kernel)))

theorem node_3289 : Excluded a [8,5,0,7,1] :=
  source_excluded a [8,5,0,7,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_3291 : Excluded a [8,5,0,7,2,1] :=
  predecessor_excluded a [8,5,0,7,2,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_3292 : Excluded a [8,5,0,7,2,3] :=
  predecessor_excluded a [8,5,0,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

def b_3296 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 5
  | 2 => 0
  | 3 => 7
  | 4 => 2
  | 5 => 4
  | 6 => 1
  | 7 => 3
  | 8 => 6
  | _ => 0

def cert_3296 : LosingRegion (edgeOf a b_3296) 0 :=
  losingMask a b_3296 0 1231551968513781400601600
    (by decide +kernel) (by decide +kernel)

theorem node_3296 : Excluded a [8,5,0,7,2,4,1,3,6] :=
  losing_excluded a [8,5,0,7,2,4,1,3,6] (by decide) b_3296 (by decide +kernel) 3 0 0 cert_3296 (by change 3 ≠ 0 ∧ ¬ edgeOf a b_3296 3 0 ∧ 0 ≠ 3 ∧ maskRegion 1231551968513781400601600 3 0; decide +kernel)

theorem node_3295 : Excluded a [8,5,0,7,2,4,1,3] :=
  branch_excluded a [8,5,0,7,2,4,1,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,7,2,4,1,3,0] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,1,3,1] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,1,3,2] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,1,3,3] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,1,3,4] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,1,3,5] (by decide +kernel))
      node_3296
      (invalid_excluded a [8,5,0,7,2,4,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,1,3,8] (by decide +kernel)))

theorem node_3298 : Excluded a [8,5,0,7,2,4,1,6,3] :=
  source_excluded a [8,5,0,7,2,4,1,6,3] 8 0 2 (by decide) (by decide +kernel)

theorem node_3297 : Excluded a [8,5,0,7,2,4,1,6] :=
  branch_excluded a [8,5,0,7,2,4,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,7,2,4,1,6,0] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,1,6,1] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,1,6,2] (by decide +kernel))
      node_3298
      (invalid_excluded a [8,5,0,7,2,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,1,6,8] (by decide +kernel)))

theorem node_3294 : Excluded a [8,5,0,7,2,4,1] :=
  branch_excluded a [8,5,0,7,2,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,7,2,4,1,0] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,1,1] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,1,2] (by decide +kernel))
      node_3295
      (invalid_excluded a [8,5,0,7,2,4,1,4] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,1,5] (by decide +kernel))
      node_3297
      (invalid_excluded a [8,5,0,7,2,4,1,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,1,8] (by decide +kernel)))

theorem node_3299 : Excluded a [8,5,0,7,2,4,3] :=
  source_excluded a [8,5,0,7,2,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_3293 : Excluded a [8,5,0,7,2,4] :=
  branch_excluded a [8,5,0,7,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,7,2,4,0] (by decide +kernel))
      node_3294
      (invalid_excluded a [8,5,0,7,2,4,2] (by decide +kernel))
      node_3299
      (invalid_excluded a [8,5,0,7,2,4,4] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,5] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,4,8] (by decide +kernel)))

theorem node_3290 : Excluded a [8,5,0,7,2] :=
  branch_excluded a [8,5,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,7,2,0] (by decide +kernel))
      node_3291
      (invalid_excluded a [8,5,0,7,2,2] (by decide +kernel))
      node_3292
      node_3293
      (invalid_excluded a [8,5,0,7,2,5] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,2,8] (by decide +kernel)))

theorem node_3301 : Excluded a [8,5,0,7,3,1] :=
  predecessor_excluded a [8,5,0,7,3,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_3304 : Excluded a [8,5,0,7,3,2,1,4] :=
  source_excluded a [8,5,0,7,3,2,1,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_3306 : Excluded a [8,5,0,7,3,2,1,6,4] :=
  predecessor_excluded a [8,5,0,7,3,2,1,6,4] 0 3 8 4 (by decide) (by decide +kernel)

theorem node_3305 : Excluded a [8,5,0,7,3,2,1,6] :=
  branch_excluded a [8,5,0,7,3,2,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,7,3,2,1,6,0] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,2,1,6,1] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,2,1,6,2] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,2,1,6,3] (by decide +kernel))
      node_3306
      (invalid_excluded a [8,5,0,7,3,2,1,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,2,1,6,6] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,2,1,6,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,2,1,6,8] (by decide +kernel)))

theorem node_3303 : Excluded a [8,5,0,7,3,2,1] :=
  branch_excluded a [8,5,0,7,3,2,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,7,3,2,1,0] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,2,1,1] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,2,1,2] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,2,1,3] (by decide +kernel))
      node_3304
      (invalid_excluded a [8,5,0,7,3,2,1,5] (by decide +kernel))
      node_3305
      (invalid_excluded a [8,5,0,7,3,2,1,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,2,1,8] (by decide +kernel)))

theorem node_3307 : Excluded a [8,5,0,7,3,2,4] :=
  source_excluded a [8,5,0,7,3,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_3302 : Excluded a [8,5,0,7,3,2] :=
  branch_excluded a [8,5,0,7,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,7,3,2,0] (by decide +kernel))
      node_3303
      (invalid_excluded a [8,5,0,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,2,3] (by decide +kernel))
      node_3307
      (invalid_excluded a [8,5,0,7,3,2,5] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,2,8] (by decide +kernel)))

theorem node_3308 : Excluded a [8,5,0,7,3,4] :=
  predecessor_excluded a [8,5,0,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_3300 : Excluded a [8,5,0,7,3] :=
  branch_excluded a [8,5,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,7,3,0] (by decide +kernel))
      node_3301
      node_3302
      (invalid_excluded a [8,5,0,7,3,3] (by decide +kernel))
      node_3308
      (invalid_excluded a [8,5,0,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,3,8] (by decide +kernel)))

theorem node_3309 : Excluded a [8,5,0,7,6] :=
  source_excluded a [8,5,0,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_3288 : Excluded a [8,5,0,7] :=
  branch_excluded a [8,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,7,0] (by decide +kernel))
      node_3289
      node_3290
      node_3300
      (invalid_excluded a [8,5,0,7,4] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,5] (by decide +kernel))
      node_3309
      (invalid_excluded a [8,5,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,0,7,8] (by decide +kernel)))

theorem node_3264 : Excluded a [8,5,0] :=
  branch_excluded a [8,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,0,0] (by decide +kernel))
      node_3265
      node_3266
      (invalid_excluded a [8,5,0,3] (by decide +kernel))
      (invalid_excluded a [8,5,0,4] (by decide +kernel))
      (invalid_excluded a [8,5,0,5] (by decide +kernel))
      node_3279
      node_3288
      (invalid_excluded a [8,5,0,8] (by decide +kernel)))

theorem node_3311 : Excluded a [8,5,1,0] :=
  predecessor_excluded a [8,5,1,0] 4 0 2 3 (by decide) (by decide +kernel)

theorem node_3313 : Excluded a [8,5,1,2,0] :=
  source_excluded a [8,5,1,2,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_3314 : Excluded a [8,5,1,2,3] :=
  predecessor_excluded a [8,5,1,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_3315 : Excluded a [8,5,1,2,6] :=
  source_excluded a [8,5,1,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_3317 : Excluded a [8,5,1,2,7,0] :=
  source_excluded a [8,5,1,2,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3319 : Excluded a [8,5,1,2,7,3,0] :=
  predecessor_excluded a [8,5,1,2,7,3,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_3320 : Excluded a [8,5,1,2,7,3,4] :=
  source_excluded a [8,5,1,2,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_3318 : Excluded a [8,5,1,2,7,3] :=
  branch_excluded a [8,5,1,2,7,3] (by decide)
    (fin9_cases _
      node_3319
      (invalid_excluded a [8,5,1,2,7,3,1] (by decide +kernel))
      (invalid_excluded a [8,5,1,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [8,5,1,2,7,3,3] (by decide +kernel))
      node_3320
      (invalid_excluded a [8,5,1,2,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,5,1,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,2,7,3,8] (by decide +kernel)))

theorem node_3321 : Excluded a [8,5,1,2,7,4] :=
  predecessor_excluded a [8,5,1,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_3316 : Excluded a [8,5,1,2,7] :=
  branch_excluded a [8,5,1,2,7] (by decide)
    (fin9_cases _
      node_3317
      (invalid_excluded a [8,5,1,2,7,1] (by decide +kernel))
      (invalid_excluded a [8,5,1,2,7,2] (by decide +kernel))
      node_3318
      node_3321
      (invalid_excluded a [8,5,1,2,7,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,2,7,6] (by decide +kernel))
      (invalid_excluded a [8,5,1,2,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,2,7,8] (by decide +kernel)))

theorem node_3312 : Excluded a [8,5,1,2] :=
  branch_excluded a [8,5,1,2] (by decide)
    (fin9_cases _
      node_3313
      (invalid_excluded a [8,5,1,2,1] (by decide +kernel))
      (invalid_excluded a [8,5,1,2,2] (by decide +kernel))
      node_3314
      (invalid_excluded a [8,5,1,2,4] (by decide +kernel))
      (invalid_excluded a [8,5,1,2,5] (by decide +kernel))
      node_3315
      node_3316
      (invalid_excluded a [8,5,1,2,8] (by decide +kernel)))

theorem node_3323 : Excluded a [8,5,1,6,0] :=
  source_excluded a [8,5,1,6,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_3325 : Excluded a [8,5,1,6,2,0] :=
  source_excluded a [8,5,1,6,2,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3326 : Excluded a [8,5,1,6,2,3] :=
  source_excluded a [8,5,1,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_3327 : Excluded a [8,5,1,6,2,4] :=
  source_excluded a [8,5,1,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_3328 : Excluded a [8,5,1,6,2,7] :=
  source_excluded a [8,5,1,6,2,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_3324 : Excluded a [8,5,1,6,2] :=
  branch_excluded a [8,5,1,6,2] (by decide)
    (fin9_cases _
      node_3325
      (invalid_excluded a [8,5,1,6,2,1] (by decide +kernel))
      (invalid_excluded a [8,5,1,6,2,2] (by decide +kernel))
      node_3326
      node_3327
      (invalid_excluded a [8,5,1,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,6,2,6] (by decide +kernel))
      node_3328
      (invalid_excluded a [8,5,1,6,2,8] (by decide +kernel)))

theorem node_3329 : Excluded a [8,5,1,6,3] :=
  predecessor_excluded a [8,5,1,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_3330 : Excluded a [8,5,1,6,7] :=
  predecessor_excluded a [8,5,1,6,7] 0 7 3 4 (by decide) (by decide +kernel)

theorem node_3322 : Excluded a [8,5,1,6] :=
  branch_excluded a [8,5,1,6] (by decide)
    (fin9_cases _
      node_3323
      (invalid_excluded a [8,5,1,6,1] (by decide +kernel))
      node_3324
      node_3329
      (invalid_excluded a [8,5,1,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,1,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,6,6] (by decide +kernel))
      node_3330
      (invalid_excluded a [8,5,1,6,8] (by decide +kernel)))

theorem node_3332 : Excluded a [8,5,1,7,0] :=
  source_excluded a [8,5,1,7,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_3334 : Excluded a [8,5,1,7,2,0] :=
  source_excluded a [8,5,1,7,2,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3335 : Excluded a [8,5,1,7,2,3] :=
  predecessor_excluded a [8,5,1,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_3337 : Excluded a [8,5,1,7,2,4,0] :=
  predecessor_excluded a [8,5,1,7,2,4,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_3338 : Excluded a [8,5,1,7,2,4,3] :=
  source_excluded a [8,5,1,7,2,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_3336 : Excluded a [8,5,1,7,2,4] :=
  branch_excluded a [8,5,1,7,2,4] (by decide)
    (fin9_cases _
      node_3337
      (invalid_excluded a [8,5,1,7,2,4,1] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,2,4,2] (by decide +kernel))
      node_3338
      (invalid_excluded a [8,5,1,7,2,4,4] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,2,4,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,2,4,8] (by decide +kernel)))

theorem node_3333 : Excluded a [8,5,1,7,2] :=
  branch_excluded a [8,5,1,7,2] (by decide)
    (fin9_cases _
      node_3334
      (invalid_excluded a [8,5,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,2,2] (by decide +kernel))
      node_3335
      node_3336
      (invalid_excluded a [8,5,1,7,2,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,2,8] (by decide +kernel)))

theorem node_3340 : Excluded a [8,5,1,7,3,0] :=
  source_excluded a [8,5,1,7,3,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3342 : Excluded a [8,5,1,7,3,2,0] :=
  predecessor_excluded a [8,5,1,7,3,2,0] 1 8 6 0 (by decide) (by decide +kernel)

theorem node_3343 : Excluded a [8,5,1,7,3,2,4] :=
  source_excluded a [8,5,1,7,3,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_3341 : Excluded a [8,5,1,7,3,2] :=
  branch_excluded a [8,5,1,7,3,2] (by decide)
    (fin9_cases _
      node_3342
      (invalid_excluded a [8,5,1,7,3,2,1] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,2,3] (by decide +kernel))
      node_3343
      (invalid_excluded a [8,5,1,7,3,2,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,2,8] (by decide +kernel)))

theorem node_3344 : Excluded a [8,5,1,7,3,4] :=
  predecessor_excluded a [8,5,1,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_3339 : Excluded a [8,5,1,7,3] :=
  branch_excluded a [8,5,1,7,3] (by decide)
    (fin9_cases _
      node_3340
      (invalid_excluded a [8,5,1,7,3,1] (by decide +kernel))
      node_3341
      (invalid_excluded a [8,5,1,7,3,3] (by decide +kernel))
      node_3344
      (invalid_excluded a [8,5,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,3,8] (by decide +kernel)))

theorem node_3345 : Excluded a [8,5,1,7,6] :=
  source_excluded a [8,5,1,7,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_3331 : Excluded a [8,5,1,7] :=
  branch_excluded a [8,5,1,7] (by decide)
    (fin9_cases _
      node_3332
      (invalid_excluded a [8,5,1,7,1] (by decide +kernel))
      node_3333
      node_3339
      (invalid_excluded a [8,5,1,7,4] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,5] (by decide +kernel))
      node_3345
      (invalid_excluded a [8,5,1,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,1,7,8] (by decide +kernel)))

theorem node_3310 : Excluded a [8,5,1] :=
  branch_excluded a [8,5,1] (by decide)
    (fin9_cases _
      node_3311
      (invalid_excluded a [8,5,1,1] (by decide +kernel))
      node_3312
      (invalid_excluded a [8,5,1,3] (by decide +kernel))
      (invalid_excluded a [8,5,1,4] (by decide +kernel))
      (invalid_excluded a [8,5,1,5] (by decide +kernel))
      node_3322
      node_3331
      (invalid_excluded a [8,5,1,8] (by decide +kernel)))

theorem node_3346 : Excluded a [8,5,4] :=
  source_excluded a [8,5,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_3349 : Excluded a [8,5,6,0,1] :=
  source_excluded a [8,5,6,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_3350 : Excluded a [8,5,6,0,2] :=
  predecessor_excluded a [8,5,6,0,2] 0 6 4 2 (by decide) (by decide +kernel)

theorem node_3352 : Excluded a [8,5,6,0,3,1] :=
  predecessor_excluded a [8,5,6,0,3,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_3353 : Excluded a [8,5,6,0,3,2] :=
  source_excluded a [8,5,6,0,3,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_3354 : Excluded a [8,5,6,0,3,4] :=
  predecessor_excluded a [8,5,6,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_3355 : Excluded a [8,5,6,0,3,7] :=
  source_excluded a [8,5,6,0,3,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_3351 : Excluded a [8,5,6,0,3] :=
  branch_excluded a [8,5,6,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,6,0,3,0] (by decide +kernel))
      node_3352
      node_3353
      (invalid_excluded a [8,5,6,0,3,3] (by decide +kernel))
      node_3354
      (invalid_excluded a [8,5,6,0,3,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,3,6] (by decide +kernel))
      node_3355
      (invalid_excluded a [8,5,6,0,3,8] (by decide +kernel)))

theorem node_3357 : Excluded a [8,5,6,0,7,1] :=
  predecessor_excluded a [8,5,6,0,7,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_3358 : Excluded a [8,5,6,0,7,2] :=
  source_excluded a [8,5,6,0,7,2] 5 0 2 (by decide) (by decide +kernel)

theorem node_3359 : Excluded a [8,5,6,0,7,3] :=
  source_excluded a [8,5,6,0,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_3360 : Excluded a [8,5,6,0,7,4] :=
  predecessor_excluded a [8,5,6,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_3356 : Excluded a [8,5,6,0,7] :=
  branch_excluded a [8,5,6,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,6,0,7,0] (by decide +kernel))
      node_3357
      node_3358
      node_3359
      node_3360
      (invalid_excluded a [8,5,6,0,7,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,7,8] (by decide +kernel)))

theorem node_3348 : Excluded a [8,5,6,0] :=
  branch_excluded a [8,5,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,6,0,0] (by decide +kernel))
      node_3349
      node_3350
      node_3351
      (invalid_excluded a [8,5,6,0,4] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,0,6] (by decide +kernel))
      node_3356
      (invalid_excluded a [8,5,6,0,8] (by decide +kernel)))

theorem node_3361 : Excluded a [8,5,6,1] :=
  predecessor_excluded a [8,5,6,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_3363 : Excluded a [8,5,6,2,0] :=
  source_excluded a [8,5,6,2,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_3364 : Excluded a [8,5,6,2,1] :=
  source_excluded a [8,5,6,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_3365 : Excluded a [8,5,6,2,3] :=
  predecessor_excluded a [8,5,6,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_3367 : Excluded a [8,5,6,2,7,0] :=
  source_excluded a [8,5,6,2,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3368 : Excluded a [8,5,6,2,7,1] :=
  predecessor_excluded a [8,5,6,2,7,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_3369 : Excluded a [8,5,6,2,7,3] :=
  source_excluded a [8,5,6,2,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_3370 : Excluded a [8,5,6,2,7,4] :=
  predecessor_excluded a [8,5,6,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_3366 : Excluded a [8,5,6,2,7] :=
  branch_excluded a [8,5,6,2,7] (by decide)
    (fin9_cases _
      node_3367
      node_3368
      (invalid_excluded a [8,5,6,2,7,2] (by decide +kernel))
      node_3369
      node_3370
      (invalid_excluded a [8,5,6,2,7,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,2,7,6] (by decide +kernel))
      (invalid_excluded a [8,5,6,2,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,6,2,7,8] (by decide +kernel)))

theorem node_3362 : Excluded a [8,5,6,2] :=
  branch_excluded a [8,5,6,2] (by decide)
    (fin9_cases _
      node_3363
      node_3364
      (invalid_excluded a [8,5,6,2,2] (by decide +kernel))
      node_3365
      (invalid_excluded a [8,5,6,2,4] (by decide +kernel))
      (invalid_excluded a [8,5,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,2,6] (by decide +kernel))
      node_3366
      (invalid_excluded a [8,5,6,2,8] (by decide +kernel)))

theorem node_3371 : Excluded a [8,5,6,7] :=
  predecessor_excluded a [8,5,6,7] 0 7 2 3 (by decide) (by decide +kernel)

theorem node_3347 : Excluded a [8,5,6] :=
  branch_excluded a [8,5,6] (by decide)
    (fin9_cases _
      node_3348
      node_3361
      node_3362
      (invalid_excluded a [8,5,6,3] (by decide +kernel))
      (invalid_excluded a [8,5,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,6,6] (by decide +kernel))
      node_3371
      (invalid_excluded a [8,5,6,8] (by decide +kernel)))

theorem node_3374 : Excluded a [8,5,7,0,1] :=
  source_excluded a [8,5,7,0,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_3376 : Excluded a [8,5,7,0,2,1] :=
  predecessor_excluded a [8,5,7,0,2,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_3377 : Excluded a [8,5,7,0,2,3] :=
  predecessor_excluded a [8,5,7,0,2,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_3380 : Excluded a [8,5,7,0,2,4,1,3] :=
  source_excluded a [8,5,7,0,2,4,1,3] 2 0 7 (by decide) (by decide +kernel)

theorem node_3382 : Excluded a [8,5,7,0,2,4,1,6,3] :=
  source_excluded a [8,5,7,0,2,4,1,6,3] 8 0 2 (by decide) (by decide +kernel)

theorem node_3381 : Excluded a [8,5,7,0,2,4,1,6] :=
  branch_excluded a [8,5,7,0,2,4,1,6] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,0,2,4,1,6,0] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,4,1,6,1] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,4,1,6,2] (by decide +kernel))
      node_3382
      (invalid_excluded a [8,5,7,0,2,4,1,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,4,1,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,4,1,6,6] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,4,1,6,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,4,1,6,8] (by decide +kernel)))

theorem node_3379 : Excluded a [8,5,7,0,2,4,1] :=
  branch_excluded a [8,5,7,0,2,4,1] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,0,2,4,1,0] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,4,1,1] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,4,1,2] (by decide +kernel))
      node_3380
      (invalid_excluded a [8,5,7,0,2,4,1,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,4,1,5] (by decide +kernel))
      node_3381
      (invalid_excluded a [8,5,7,0,2,4,1,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,4,1,8] (by decide +kernel)))

theorem node_3383 : Excluded a [8,5,7,0,2,4,3] :=
  source_excluded a [8,5,7,0,2,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_3378 : Excluded a [8,5,7,0,2,4] :=
  branch_excluded a [8,5,7,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,0,2,4,0] (by decide +kernel))
      node_3379
      (invalid_excluded a [8,5,7,0,2,4,2] (by decide +kernel))
      node_3383
      (invalid_excluded a [8,5,7,0,2,4,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,4,5] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,4,8] (by decide +kernel)))

theorem node_3375 : Excluded a [8,5,7,0,2] :=
  branch_excluded a [8,5,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,0,2,0] (by decide +kernel))
      node_3376
      (invalid_excluded a [8,5,7,0,2,2] (by decide +kernel))
      node_3377
      node_3378
      (invalid_excluded a [8,5,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,2,8] (by decide +kernel)))

theorem node_3385 : Excluded a [8,5,7,0,3,1] :=
  predecessor_excluded a [8,5,7,0,3,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_3386 : Excluded a [8,5,7,0,3,2] :=
  predecessor_excluded a [8,5,7,0,3,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_3387 : Excluded a [8,5,7,0,3,4] :=
  predecessor_excluded a [8,5,7,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_3384 : Excluded a [8,5,7,0,3] :=
  branch_excluded a [8,5,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,0,3,0] (by decide +kernel))
      node_3385
      node_3386
      (invalid_excluded a [8,5,7,0,3,3] (by decide +kernel))
      node_3387
      (invalid_excluded a [8,5,7,0,3,5] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,6] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,3,8] (by decide +kernel)))

theorem node_3388 : Excluded a [8,5,7,0,6] :=
  source_excluded a [8,5,7,0,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_3373 : Excluded a [8,5,7,0] :=
  branch_excluded a [8,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,5,7,0,0] (by decide +kernel))
      node_3374
      node_3375
      node_3384
      (invalid_excluded a [8,5,7,0,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,5] (by decide +kernel))
      node_3388
      (invalid_excluded a [8,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,0,8] (by decide +kernel)))

theorem node_3389 : Excluded a [8,5,7,1] :=
  predecessor_excluded a [8,5,7,1] 0 5 3 1 (by decide) (by decide +kernel)

theorem node_3391 : Excluded a [8,5,7,2,0] :=
  source_excluded a [8,5,7,2,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_3392 : Excluded a [8,5,7,2,1] :=
  source_excluded a [8,5,7,2,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_3393 : Excluded a [8,5,7,2,3] :=
  predecessor_excluded a [8,5,7,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_3394 : Excluded a [8,5,7,2,6] :=
  source_excluded a [8,5,7,2,6] 4 0 5 (by decide) (by decide +kernel)

theorem node_3390 : Excluded a [8,5,7,2] :=
  branch_excluded a [8,5,7,2] (by decide)
    (fin9_cases _
      node_3391
      node_3392
      (invalid_excluded a [8,5,7,2,2] (by decide +kernel))
      node_3393
      (invalid_excluded a [8,5,7,2,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,5] (by decide +kernel))
      node_3394
      (invalid_excluded a [8,5,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,2,8] (by decide +kernel)))

theorem node_3396 : Excluded a [8,5,7,6,0] :=
  source_excluded a [8,5,7,6,0] 1 2 4 (by decide) (by decide +kernel)

theorem node_3397 : Excluded a [8,5,7,6,1] :=
  source_excluded a [8,5,7,6,1] 4 0 1 (by decide) (by decide +kernel)

theorem node_3399 : Excluded a [8,5,7,6,2,0] :=
  source_excluded a [8,5,7,6,2,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3400 : Excluded a [8,5,7,6,2,1] :=
  predecessor_excluded a [8,5,7,6,2,1] 2 1 1 5 (by decide) (by decide +kernel)

theorem node_3401 : Excluded a [8,5,7,6,2,3] :=
  source_excluded a [8,5,7,6,2,3] 5 0 3 (by decide) (by decide +kernel)

theorem node_3402 : Excluded a [8,5,7,6,2,4] :=
  source_excluded a [8,5,7,6,2,4] 3 0 5 (by decide) (by decide +kernel)

theorem node_3398 : Excluded a [8,5,7,6,2] :=
  branch_excluded a [8,5,7,6,2] (by decide)
    (fin9_cases _
      node_3399
      node_3400
      (invalid_excluded a [8,5,7,6,2,2] (by decide +kernel))
      node_3401
      node_3402
      (invalid_excluded a [8,5,7,6,2,5] (by decide +kernel))
      (invalid_excluded a [8,5,7,6,2,6] (by decide +kernel))
      (invalid_excluded a [8,5,7,6,2,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,6,2,8] (by decide +kernel)))

theorem node_3403 : Excluded a [8,5,7,6,3] :=
  predecessor_excluded a [8,5,7,6,3] 0 6 4 3 (by decide) (by decide +kernel)

theorem node_3395 : Excluded a [8,5,7,6] :=
  branch_excluded a [8,5,7,6] (by decide)
    (fin9_cases _
      node_3396
      node_3397
      node_3398
      node_3403
      (invalid_excluded a [8,5,7,6,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,6,5] (by decide +kernel))
      (invalid_excluded a [8,5,7,6,6] (by decide +kernel))
      (invalid_excluded a [8,5,7,6,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,6,8] (by decide +kernel)))

theorem node_3372 : Excluded a [8,5,7] :=
  branch_excluded a [8,5,7] (by decide)
    (fin9_cases _
      node_3373
      node_3389
      node_3390
      (invalid_excluded a [8,5,7,3] (by decide +kernel))
      (invalid_excluded a [8,5,7,4] (by decide +kernel))
      (invalid_excluded a [8,5,7,5] (by decide +kernel))
      node_3395
      (invalid_excluded a [8,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,5,7,8] (by decide +kernel)))

theorem node_3263 : Excluded a [8,5] :=
  branch_excluded a [8,5] (by decide)
    (fin9_cases _
      node_3264
      node_3310
      (invalid_excluded a [8,5,2] (by decide +kernel))
      (invalid_excluded a [8,5,3] (by decide +kernel))
      node_3346
      (invalid_excluded a [8,5,5] (by decide +kernel))
      node_3347
      node_3372
      (invalid_excluded a [8,5,8] (by decide +kernel)))

theorem node_3406 : Excluded a [8,6,0,1] :=
  predecessor_excluded a [8,6,0,1] 4 1 2 3 (by decide) (by decide +kernel)

theorem node_3408 : Excluded a [8,6,0,2,1] :=
  predecessor_excluded a [8,6,0,2,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_3409 : Excluded a [8,6,0,2,3] :=
  predecessor_excluded a [8,6,0,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_3411 : Excluded a [8,6,0,2,7,1] :=
  source_excluded a [8,6,0,2,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_3413 : Excluded a [8,6,0,2,7,3,1] :=
  predecessor_excluded a [8,6,0,2,7,3,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_3414 : Excluded a [8,6,0,2,7,3,4] :=
  source_excluded a [8,6,0,2,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_3415 : Excluded a [8,6,0,2,7,3,5] :=
  source_excluded a [8,6,0,2,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_3412 : Excluded a [8,6,0,2,7,3] :=
  branch_excluded a [8,6,0,2,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,2,7,3,0] (by decide +kernel))
      node_3413
      (invalid_excluded a [8,6,0,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,3] (by decide +kernel))
      node_3414
      node_3415
      (invalid_excluded a [8,6,0,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,3,8] (by decide +kernel)))

theorem node_3416 : Excluded a [8,6,0,2,7,4] :=
  predecessor_excluded a [8,6,0,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_3410 : Excluded a [8,6,0,2,7] :=
  branch_excluded a [8,6,0,2,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,2,7,0] (by decide +kernel))
      node_3411
      (invalid_excluded a [8,6,0,2,7,2] (by decide +kernel))
      node_3412
      node_3416
      (invalid_excluded a [8,6,0,2,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,7,8] (by decide +kernel)))

theorem node_3407 : Excluded a [8,6,0,2] :=
  branch_excluded a [8,6,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,2,0] (by decide +kernel))
      node_3408
      (invalid_excluded a [8,6,0,2,2] (by decide +kernel))
      node_3409
      (invalid_excluded a [8,6,0,2,4] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,0,2,6] (by decide +kernel))
      node_3410
      (invalid_excluded a [8,6,0,2,8] (by decide +kernel)))

theorem node_3417 : Excluded a [8,6,0,5] :=
  source_excluded a [8,6,0,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_3419 : Excluded a [8,6,0,7,1] :=
  predecessor_excluded a [8,6,0,7,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_3421 : Excluded a [8,6,0,7,2,1] :=
  source_excluded a [8,6,0,7,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_3422 : Excluded a [8,6,0,7,2,3] :=
  predecessor_excluded a [8,6,0,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_3424 : Excluded a [8,6,0,7,2,4,1] :=
  predecessor_excluded a [8,6,0,7,2,4,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_3425 : Excluded a [8,6,0,7,2,4,3] :=
  source_excluded a [8,6,0,7,2,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_3426 : Excluded a [8,6,0,7,2,4,5] :=
  predecessor_excluded a [8,6,0,7,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_3423 : Excluded a [8,6,0,7,2,4] :=
  branch_excluded a [8,6,0,7,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,7,2,4,0] (by decide +kernel))
      node_3424
      (invalid_excluded a [8,6,0,7,2,4,2] (by decide +kernel))
      node_3425
      (invalid_excluded a [8,6,0,7,2,4,4] (by decide +kernel))
      node_3426
      (invalid_excluded a [8,6,0,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,4,8] (by decide +kernel)))

theorem node_3420 : Excluded a [8,6,0,7,2] :=
  branch_excluded a [8,6,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,7,2,0] (by decide +kernel))
      node_3421
      (invalid_excluded a [8,6,0,7,2,2] (by decide +kernel))
      node_3422
      node_3423
      (invalid_excluded a [8,6,0,7,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,2,8] (by decide +kernel)))

theorem node_3428 : Excluded a [8,6,0,7,3,1] :=
  source_excluded a [8,6,0,7,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_3430 : Excluded a [8,6,0,7,3,2,1] :=
  predecessor_excluded a [8,6,0,7,3,2,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_3431 : Excluded a [8,6,0,7,3,2,4] :=
  source_excluded a [8,6,0,7,3,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_3433 : Excluded a [8,6,0,7,3,2,5,1] :=
  source_excluded a [8,6,0,7,3,2,5,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_3434 : Excluded a [8,6,0,7,3,2,5,4] :=
  source_excluded a [8,6,0,7,3,2,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_3432 : Excluded a [8,6,0,7,3,2,5] :=
  branch_excluded a [8,6,0,7,3,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,7,3,2,5,0] (by decide +kernel))
      node_3433
      (invalid_excluded a [8,6,0,7,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,3,2,5,3] (by decide +kernel))
      node_3434
      (invalid_excluded a [8,6,0,7,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,3,2,5,8] (by decide +kernel)))

theorem node_3429 : Excluded a [8,6,0,7,3,2] :=
  branch_excluded a [8,6,0,7,3,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,7,3,2,0] (by decide +kernel))
      node_3430
      (invalid_excluded a [8,6,0,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,3,2,3] (by decide +kernel))
      node_3431
      node_3432
      (invalid_excluded a [8,6,0,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,3,2,8] (by decide +kernel)))

theorem node_3435 : Excluded a [8,6,0,7,3,4] :=
  predecessor_excluded a [8,6,0,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_3427 : Excluded a [8,6,0,7,3] :=
  branch_excluded a [8,6,0,7,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,7,3,0] (by decide +kernel))
      node_3428
      node_3429
      (invalid_excluded a [8,6,0,7,3,3] (by decide +kernel))
      node_3435
      (invalid_excluded a [8,6,0,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,3,8] (by decide +kernel)))

theorem node_3418 : Excluded a [8,6,0,7] :=
  branch_excluded a [8,6,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,7,0] (by decide +kernel))
      node_3419
      node_3420
      node_3427
      (invalid_excluded a [8,6,0,7,4] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,0,7,8] (by decide +kernel)))

theorem node_3405 : Excluded a [8,6,0] :=
  branch_excluded a [8,6,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,0,0] (by decide +kernel))
      node_3406
      node_3407
      (invalid_excluded a [8,6,0,3] (by decide +kernel))
      (invalid_excluded a [8,6,0,4] (by decide +kernel))
      node_3417
      (invalid_excluded a [8,6,0,6] (by decide +kernel))
      node_3418
      (invalid_excluded a [8,6,0,8] (by decide +kernel)))

theorem node_3437 : Excluded a [8,6,1,0] :=
  predecessor_excluded a [8,6,1,0] 4 0 2 3 (by decide) (by decide +kernel)

theorem node_3441 : Excluded a [8,6,1,2,0,3,4] :=
  predecessor_excluded a [8,6,1,2,0,3,4] 0 4 5 6 (by decide) (by decide +kernel)

def b_3444 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 6
  | 2 => 1
  | 3 => 2
  | 4 => 0
  | 5 => 3
  | 6 => 5
  | 7 => 4
  | 8 => 7
  | _ => 0

def cert_3444 : LosingRegion (edgeOf a b_3444) 0 :=
  losingMask a b_3444 0 1266855154796347576550400
    (by decide +kernel) (by decide +kernel)

theorem node_3444 : Excluded a [8,6,1,2,0,3,5,4,7] :=
  losing_excluded a [8,6,1,2,0,3,5,4,7] (by decide) b_3444 (by decide +kernel) 5 0 2 cert_3444 (by change 5 ≠ 0 ∧ ¬ edgeOf a b_3444 5 0 ∧ 2 ≠ 5 ∧ maskRegion 1266855154796347576550400 5 2; decide +kernel)

theorem node_3443 : Excluded a [8,6,1,2,0,3,5,4] :=
  branch_excluded a [8,6,1,2,0,3,5,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,2,0,3,5,4,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,5,4,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,5,4,2] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,5,4,3] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,5,4,4] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,5,4,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,5,4,6] (by decide +kernel))
      node_3444
      (invalid_excluded a [8,6,1,2,0,3,5,4,8] (by decide +kernel)))

theorem node_3442 : Excluded a [8,6,1,2,0,3,5] :=
  branch_excluded a [8,6,1,2,0,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,2,0,3,5,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,5,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,5,2] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,5,3] (by decide +kernel))
      node_3443
      (invalid_excluded a [8,6,1,2,0,3,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,5,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,5,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,5,8] (by decide +kernel)))

theorem node_3440 : Excluded a [8,6,1,2,0,3] :=
  branch_excluded a [8,6,1,2,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,2,0,3,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,2] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,3] (by decide +kernel))
      node_3441
      node_3442
      (invalid_excluded a [8,6,1,2,0,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,3,8] (by decide +kernel)))

def b_3448 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 8
  | 1 => 6
  | 2 => 1
  | 3 => 2
  | 4 => 0
  | 5 => 4
  | 6 => 3
  | 7 => 5
  | 8 => 7
  | _ => 0

def cert_3448 : LosingRegion (edgeOf a b_3448) 0 :=
  losingMask a b_3448 0 1267477155807345482138624
    (by decide +kernel) (by decide +kernel)

theorem node_3448 : Excluded a [8,6,1,2,0,4,3,5,7] :=
  losing_excluded a [8,6,1,2,0,4,3,5,7] (by decide) b_3448 (by decide +kernel) 5 0 3 cert_3448 (by change 5 ≠ 0 ∧ ¬ edgeOf a b_3448 5 0 ∧ 3 ≠ 5 ∧ maskRegion 1267477155807345482138624 5 3; decide +kernel)

theorem node_3447 : Excluded a [8,6,1,2,0,4,3,5] :=
  branch_excluded a [8,6,1,2,0,4,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,2,0,4,3,5,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,4,3,5,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,4,3,5,2] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,4,3,5,3] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,4,3,5,4] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,4,3,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,4,3,5,6] (by decide +kernel))
      node_3448
      (invalid_excluded a [8,6,1,2,0,4,3,5,8] (by decide +kernel)))

theorem node_3446 : Excluded a [8,6,1,2,0,4,3] :=
  branch_excluded a [8,6,1,2,0,4,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,2,0,4,3,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,4,3,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,4,3,2] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,4,3,3] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,4,3,4] (by decide +kernel))
      node_3447
      (invalid_excluded a [8,6,1,2,0,4,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,4,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,4,3,8] (by decide +kernel)))

theorem node_3449 : Excluded a [8,6,1,2,0,4,5] :=
  predecessor_excluded a [8,6,1,2,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_3445 : Excluded a [8,6,1,2,0,4] :=
  branch_excluded a [8,6,1,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,2,0,4,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,4,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,4,2] (by decide +kernel))
      node_3446
      (invalid_excluded a [8,6,1,2,0,4,4] (by decide +kernel))
      node_3449
      (invalid_excluded a [8,6,1,2,0,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,4,8] (by decide +kernel)))

theorem node_3450 : Excluded a [8,6,1,2,0,7] :=
  source_excluded a [8,6,1,2,0,7] 5 0 6 (by decide) (by decide +kernel)

theorem node_3439 : Excluded a [8,6,1,2,0] :=
  branch_excluded a [8,6,1,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,2,0,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,2] (by decide +kernel))
      node_3440
      node_3445
      (invalid_excluded a [8,6,1,2,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,0,6] (by decide +kernel))
      node_3450
      (invalid_excluded a [8,6,1,2,0,8] (by decide +kernel)))

theorem node_3451 : Excluded a [8,6,1,2,3] :=
  predecessor_excluded a [8,6,1,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_3453 : Excluded a [8,6,1,2,7,0] :=
  source_excluded a [8,6,1,2,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3455 : Excluded a [8,6,1,2,7,3,0] :=
  source_excluded a [8,6,1,2,7,3,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_3456 : Excluded a [8,6,1,2,7,3,4] :=
  source_excluded a [8,6,1,2,7,3,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_3457 : Excluded a [8,6,1,2,7,3,5] :=
  source_excluded a [8,6,1,2,7,3,5] 4 0 6 (by decide) (by decide +kernel)

theorem node_3454 : Excluded a [8,6,1,2,7,3] :=
  branch_excluded a [8,6,1,2,7,3] (by decide)
    (fin9_cases _
      node_3455
      (invalid_excluded a [8,6,1,2,7,3,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,7,3,2] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,7,3,3] (by decide +kernel))
      node_3456
      node_3457
      (invalid_excluded a [8,6,1,2,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,7,3,8] (by decide +kernel)))

theorem node_3458 : Excluded a [8,6,1,2,7,4] :=
  predecessor_excluded a [8,6,1,2,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_3452 : Excluded a [8,6,1,2,7] :=
  branch_excluded a [8,6,1,2,7] (by decide)
    (fin9_cases _
      node_3453
      (invalid_excluded a [8,6,1,2,7,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,7,2] (by decide +kernel))
      node_3454
      node_3458
      (invalid_excluded a [8,6,1,2,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,7,8] (by decide +kernel)))

theorem node_3438 : Excluded a [8,6,1,2] :=
  branch_excluded a [8,6,1,2] (by decide)
    (fin9_cases _
      node_3439
      (invalid_excluded a [8,6,1,2,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,2] (by decide +kernel))
      node_3451
      (invalid_excluded a [8,6,1,2,4] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,2,6] (by decide +kernel))
      node_3452
      (invalid_excluded a [8,6,1,2,8] (by decide +kernel)))

theorem node_3459 : Excluded a [8,6,1,5] :=
  source_excluded a [8,6,1,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_3463 : Excluded a [8,6,1,7,0,2,3] :=
  source_excluded a [8,6,1,7,0,2,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_3464 : Excluded a [8,6,1,7,0,2,4] :=
  source_excluded a [8,6,1,7,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_3467 : Excluded a [8,6,1,7,0,2,5,3,4] :=
  predecessor_excluded a [8,6,1,7,0,2,5,3,4] 0 4 7 8 (by decide) (by decide +kernel)

theorem node_3466 : Excluded a [8,6,1,7,0,2,5,3] :=
  branch_excluded a [8,6,1,7,0,2,5,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,7,0,2,5,3,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,2,5,3,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,2,5,3,2] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,2,5,3,3] (by decide +kernel))
      node_3467
      (invalid_excluded a [8,6,1,7,0,2,5,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,2,5,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,2,5,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,2,5,3,8] (by decide +kernel)))

theorem node_3468 : Excluded a [8,6,1,7,0,2,5,4] :=
  source_excluded a [8,6,1,7,0,2,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_3465 : Excluded a [8,6,1,7,0,2,5] :=
  branch_excluded a [8,6,1,7,0,2,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,7,0,2,5,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,2,5,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,2,5,2] (by decide +kernel))
      node_3466
      node_3468
      (invalid_excluded a [8,6,1,7,0,2,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,2,5,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,2,5,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,2,5,8] (by decide +kernel)))

theorem node_3462 : Excluded a [8,6,1,7,0,2] :=
  branch_excluded a [8,6,1,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,7,0,2,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,2,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,2,2] (by decide +kernel))
      node_3463
      node_3464
      node_3465
      (invalid_excluded a [8,6,1,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,2,8] (by decide +kernel)))

theorem node_3469 : Excluded a [8,6,1,7,0,3] :=
  predecessor_excluded a [8,6,1,7,0,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_3472 : Excluded a [8,6,1,7,0,4,2,3] :=
  predecessor_excluded a [8,6,1,7,0,4,2,3] 0 3 6 7 (by decide) (by decide +kernel)

theorem node_3473 : Excluded a [8,6,1,7,0,4,2,5] :=
  predecessor_excluded a [8,6,1,7,0,4,2,5] 0 5 3 7 (by decide) (by decide +kernel)

theorem node_3471 : Excluded a [8,6,1,7,0,4,2] :=
  branch_excluded a [8,6,1,7,0,4,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,7,0,4,2,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,4,2,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,4,2,2] (by decide +kernel))
      node_3472
      (invalid_excluded a [8,6,1,7,0,4,2,4] (by decide +kernel))
      node_3473
      (invalid_excluded a [8,6,1,7,0,4,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,4,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,4,2,8] (by decide +kernel)))

theorem node_3474 : Excluded a [8,6,1,7,0,4,3] :=
  source_excluded a [8,6,1,7,0,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_3475 : Excluded a [8,6,1,7,0,4,5] :=
  predecessor_excluded a [8,6,1,7,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_3470 : Excluded a [8,6,1,7,0,4] :=
  branch_excluded a [8,6,1,7,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,7,0,4,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,4,1] (by decide +kernel))
      node_3471
      node_3474
      (invalid_excluded a [8,6,1,7,0,4,4] (by decide +kernel))
      node_3475
      (invalid_excluded a [8,6,1,7,0,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,4,8] (by decide +kernel)))

theorem node_3461 : Excluded a [8,6,1,7,0] :=
  branch_excluded a [8,6,1,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,1,7,0,0] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,1] (by decide +kernel))
      node_3462
      node_3469
      node_3470
      (invalid_excluded a [8,6,1,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,0,8] (by decide +kernel)))

theorem node_3477 : Excluded a [8,6,1,7,2,0] :=
  source_excluded a [8,6,1,7,2,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3478 : Excluded a [8,6,1,7,2,3] :=
  predecessor_excluded a [8,6,1,7,2,3] 0 7 5 3 (by decide) (by decide +kernel)

theorem node_3480 : Excluded a [8,6,1,7,2,4,0] :=
  source_excluded a [8,6,1,7,2,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_3481 : Excluded a [8,6,1,7,2,4,3] :=
  source_excluded a [8,6,1,7,2,4,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_3482 : Excluded a [8,6,1,7,2,4,5] :=
  predecessor_excluded a [8,6,1,7,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_3479 : Excluded a [8,6,1,7,2,4] :=
  branch_excluded a [8,6,1,7,2,4] (by decide)
    (fin9_cases _
      node_3480
      (invalid_excluded a [8,6,1,7,2,4,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,4,2] (by decide +kernel))
      node_3481
      (invalid_excluded a [8,6,1,7,2,4,4] (by decide +kernel))
      node_3482
      (invalid_excluded a [8,6,1,7,2,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,4,8] (by decide +kernel)))

theorem node_3476 : Excluded a [8,6,1,7,2] :=
  branch_excluded a [8,6,1,7,2] (by decide)
    (fin9_cases _
      node_3477
      (invalid_excluded a [8,6,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,2] (by decide +kernel))
      node_3478
      node_3479
      (invalid_excluded a [8,6,1,7,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,2,8] (by decide +kernel)))

theorem node_3484 : Excluded a [8,6,1,7,3,0] :=
  source_excluded a [8,6,1,7,3,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3486 : Excluded a [8,6,1,7,3,2,0] :=
  source_excluded a [8,6,1,7,3,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_3487 : Excluded a [8,6,1,7,3,2,4] :=
  source_excluded a [8,6,1,7,3,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_3489 : Excluded a [8,6,1,7,3,2,5,0] :=
  source_excluded a [8,6,1,7,3,2,5,0] 7 1 0 (by decide) (by decide +kernel)

theorem node_3490 : Excluded a [8,6,1,7,3,2,5,4] :=
  source_excluded a [8,6,1,7,3,2,5,4] 3 0 7 (by decide) (by decide +kernel)

theorem node_3488 : Excluded a [8,6,1,7,3,2,5] :=
  branch_excluded a [8,6,1,7,3,2,5] (by decide)
    (fin9_cases _
      node_3489
      (invalid_excluded a [8,6,1,7,3,2,5,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,2,5,2] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,2,5,3] (by decide +kernel))
      node_3490
      (invalid_excluded a [8,6,1,7,3,2,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,2,5,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,2,5,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,2,5,8] (by decide +kernel)))

theorem node_3485 : Excluded a [8,6,1,7,3,2] :=
  branch_excluded a [8,6,1,7,3,2] (by decide)
    (fin9_cases _
      node_3486
      (invalid_excluded a [8,6,1,7,3,2,1] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,2,2] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,2,3] (by decide +kernel))
      node_3487
      node_3488
      (invalid_excluded a [8,6,1,7,3,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,2,8] (by decide +kernel)))

theorem node_3491 : Excluded a [8,6,1,7,3,4] :=
  predecessor_excluded a [8,6,1,7,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_3483 : Excluded a [8,6,1,7,3] :=
  branch_excluded a [8,6,1,7,3] (by decide)
    (fin9_cases _
      node_3484
      (invalid_excluded a [8,6,1,7,3,1] (by decide +kernel))
      node_3485
      (invalid_excluded a [8,6,1,7,3,3] (by decide +kernel))
      node_3491
      (invalid_excluded a [8,6,1,7,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,3,8] (by decide +kernel)))

theorem node_3460 : Excluded a [8,6,1,7] :=
  branch_excluded a [8,6,1,7] (by decide)
    (fin9_cases _
      node_3461
      (invalid_excluded a [8,6,1,7,1] (by decide +kernel))
      node_3476
      node_3483
      (invalid_excluded a [8,6,1,7,4] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,1,7,8] (by decide +kernel)))

theorem node_3436 : Excluded a [8,6,1] :=
  branch_excluded a [8,6,1] (by decide)
    (fin9_cases _
      node_3437
      (invalid_excluded a [8,6,1,1] (by decide +kernel))
      node_3438
      (invalid_excluded a [8,6,1,3] (by decide +kernel))
      (invalid_excluded a [8,6,1,4] (by decide +kernel))
      node_3459
      (invalid_excluded a [8,6,1,6] (by decide +kernel))
      node_3460
      (invalid_excluded a [8,6,1,8] (by decide +kernel)))

theorem node_3492 : Excluded a [8,6,4] :=
  source_excluded a [8,6,4] 2 0 3 (by decide) (by decide +kernel)

theorem node_3495 : Excluded a [8,6,5,0,1] :=
  predecessor_excluded a [8,6,5,0,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_3496 : Excluded a [8,6,5,0,2] :=
  source_excluded a [8,6,5,0,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_3497 : Excluded a [8,6,5,0,3] :=
  source_excluded a [8,6,5,0,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_3499 : Excluded a [8,6,5,0,7,1] :=
  source_excluded a [8,6,5,0,7,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_3501 : Excluded a [8,6,5,0,7,2,1] :=
  predecessor_excluded a [8,6,5,0,7,2,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_3502 : Excluded a [8,6,5,0,7,2,3] :=
  predecessor_excluded a [8,6,5,0,7,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_3503 : Excluded a [8,6,5,0,7,2,4] :=
  source_excluded a [8,6,5,0,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_3500 : Excluded a [8,6,5,0,7,2] :=
  branch_excluded a [8,6,5,0,7,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,0,7,2,0] (by decide +kernel))
      node_3501
      (invalid_excluded a [8,6,5,0,7,2,2] (by decide +kernel))
      node_3502
      node_3503
      (invalid_excluded a [8,6,5,0,7,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,2,8] (by decide +kernel)))

theorem node_3504 : Excluded a [8,6,5,0,7,3] :=
  source_excluded a [8,6,5,0,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_3505 : Excluded a [8,6,5,0,7,4] :=
  predecessor_excluded a [8,6,5,0,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_3498 : Excluded a [8,6,5,0,7] :=
  branch_excluded a [8,6,5,0,7] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,0,7,0] (by decide +kernel))
      node_3499
      node_3500
      node_3504
      node_3505
      (invalid_excluded a [8,6,5,0,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,7,8] (by decide +kernel)))

theorem node_3494 : Excluded a [8,6,5,0] :=
  branch_excluded a [8,6,5,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,0,0] (by decide +kernel))
      node_3495
      node_3496
      node_3497
      (invalid_excluded a [8,6,5,0,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,0,6] (by decide +kernel))
      node_3498
      (invalid_excluded a [8,6,5,0,8] (by decide +kernel)))

theorem node_3507 : Excluded a [8,6,5,1,0] :=
  predecessor_excluded a [8,6,5,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_3508 : Excluded a [8,6,5,1,2] :=
  source_excluded a [8,6,5,1,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_3509 : Excluded a [8,6,5,1,3] :=
  source_excluded a [8,6,5,1,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_3511 : Excluded a [8,6,5,1,7,0] :=
  source_excluded a [8,6,5,1,7,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3513 : Excluded a [8,6,5,1,7,2,0] :=
  source_excluded a [8,6,5,1,7,2,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_3514 : Excluded a [8,6,5,1,7,2,3] :=
  predecessor_excluded a [8,6,5,1,7,2,3] 0 3 5 6 (by decide) (by decide +kernel)

theorem node_3515 : Excluded a [8,6,5,1,7,2,4] :=
  source_excluded a [8,6,5,1,7,2,4] 6 0 4 (by decide) (by decide +kernel)

theorem node_3512 : Excluded a [8,6,5,1,7,2] :=
  branch_excluded a [8,6,5,1,7,2] (by decide)
    (fin9_cases _
      node_3513
      (invalid_excluded a [8,6,5,1,7,2,1] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,2,2] (by decide +kernel))
      node_3514
      node_3515
      (invalid_excluded a [8,6,5,1,7,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,2,8] (by decide +kernel)))

theorem node_3516 : Excluded a [8,6,5,1,7,3] :=
  source_excluded a [8,6,5,1,7,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_3517 : Excluded a [8,6,5,1,7,4] :=
  predecessor_excluded a [8,6,5,1,7,4] 0 7 5 4 (by decide) (by decide +kernel)

theorem node_3510 : Excluded a [8,6,5,1,7] :=
  branch_excluded a [8,6,5,1,7] (by decide)
    (fin9_cases _
      node_3511
      (invalid_excluded a [8,6,5,1,7,1] (by decide +kernel))
      node_3512
      node_3516
      node_3517
      (invalid_excluded a [8,6,5,1,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,7,8] (by decide +kernel)))

theorem node_3506 : Excluded a [8,6,5,1] :=
  branch_excluded a [8,6,5,1] (by decide)
    (fin9_cases _
      node_3507
      (invalid_excluded a [8,6,5,1,1] (by decide +kernel))
      node_3508
      node_3509
      (invalid_excluded a [8,6,5,1,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,1,6] (by decide +kernel))
      node_3510
      (invalid_excluded a [8,6,5,1,8] (by decide +kernel)))

theorem node_3518 : Excluded a [8,6,5,2] :=
  predecessor_excluded a [8,6,5,2] 0 5 3 2 (by decide) (by decide +kernel)

theorem node_3521 : Excluded a [8,6,5,7,0,1] :=
  source_excluded a [8,6,5,7,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_3523 : Excluded a [8,6,5,7,0,2,1] :=
  predecessor_excluded a [8,6,5,7,0,2,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_3524 : Excluded a [8,6,5,7,0,2,3] :=
  source_excluded a [8,6,5,7,0,2,3] 6 0 3 (by decide) (by decide +kernel)

theorem node_3525 : Excluded a [8,6,5,7,0,2,4] :=
  source_excluded a [8,6,5,7,0,2,4] 3 0 6 (by decide) (by decide +kernel)

theorem node_3522 : Excluded a [8,6,5,7,0,2] :=
  branch_excluded a [8,6,5,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,7,0,2,0] (by decide +kernel))
      node_3523
      (invalid_excluded a [8,6,5,7,0,2,2] (by decide +kernel))
      node_3524
      node_3525
      (invalid_excluded a [8,6,5,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,0,2,8] (by decide +kernel)))

theorem node_3526 : Excluded a [8,6,5,7,0,3] :=
  source_excluded a [8,6,5,7,0,3] 2 0 5 (by decide) (by decide +kernel)

theorem node_3527 : Excluded a [8,6,5,7,0,4] :=
  predecessor_excluded a [8,6,5,7,0,4] 0 4 2 5 (by decide) (by decide +kernel)

theorem node_3520 : Excluded a [8,6,5,7,0] :=
  branch_excluded a [8,6,5,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,5,7,0,0] (by decide +kernel))
      node_3521
      node_3522
      node_3526
      node_3527
      (invalid_excluded a [8,6,5,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,0,8] (by decide +kernel)))

theorem node_3528 : Excluded a [8,6,5,7,1] :=
  predecessor_excluded a [8,6,5,7,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_3529 : Excluded a [8,6,5,7,2] :=
  source_excluded a [8,6,5,7,2] 4 0 2 (by decide) (by decide +kernel)

theorem node_3530 : Excluded a [8,6,5,7,3] :=
  source_excluded a [8,6,5,7,3] 2 0 4 (by decide) (by decide +kernel)

theorem node_3519 : Excluded a [8,6,5,7] :=
  branch_excluded a [8,6,5,7] (by decide)
    (fin9_cases _
      node_3520
      node_3528
      node_3529
      node_3530
      (invalid_excluded a [8,6,5,7,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,5,7,8] (by decide +kernel)))

theorem node_3493 : Excluded a [8,6,5] :=
  branch_excluded a [8,6,5] (by decide)
    (fin9_cases _
      node_3494
      node_3506
      node_3518
      (invalid_excluded a [8,6,5,3] (by decide +kernel))
      (invalid_excluded a [8,6,5,4] (by decide +kernel))
      (invalid_excluded a [8,6,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,5,6] (by decide +kernel))
      node_3519
      (invalid_excluded a [8,6,5,8] (by decide +kernel)))

theorem node_3533 : Excluded a [8,6,7,0,1] :=
  predecessor_excluded a [8,6,7,0,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_3535 : Excluded a [8,6,7,0,2,1] :=
  source_excluded a [8,6,7,0,2,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_3536 : Excluded a [8,6,7,0,2,3] :=
  predecessor_excluded a [8,6,7,0,2,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_3538 : Excluded a [8,6,7,0,2,4,1] :=
  predecessor_excluded a [8,6,7,0,2,4,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_3539 : Excluded a [8,6,7,0,2,4,3] :=
  source_excluded a [8,6,7,0,2,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_3540 : Excluded a [8,6,7,0,2,4,5] :=
  predecessor_excluded a [8,6,7,0,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_3537 : Excluded a [8,6,7,0,2,4] :=
  branch_excluded a [8,6,7,0,2,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,7,0,2,4,0] (by decide +kernel))
      node_3538
      (invalid_excluded a [8,6,7,0,2,4,2] (by decide +kernel))
      node_3539
      (invalid_excluded a [8,6,7,0,2,4,4] (by decide +kernel))
      node_3540
      (invalid_excluded a [8,6,7,0,2,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,2,4,8] (by decide +kernel)))

theorem node_3534 : Excluded a [8,6,7,0,2] :=
  branch_excluded a [8,6,7,0,2] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,7,0,2,0] (by decide +kernel))
      node_3535
      (invalid_excluded a [8,6,7,0,2,2] (by decide +kernel))
      node_3536
      node_3537
      (invalid_excluded a [8,6,7,0,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,2,8] (by decide +kernel)))

theorem node_3542 : Excluded a [8,6,7,0,3,1] :=
  source_excluded a [8,6,7,0,3,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_3543 : Excluded a [8,6,7,0,3,2] :=
  predecessor_excluded a [8,6,7,0,3,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_3544 : Excluded a [8,6,7,0,3,4] :=
  predecessor_excluded a [8,6,7,0,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_3541 : Excluded a [8,6,7,0,3] :=
  branch_excluded a [8,6,7,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,7,0,3,0] (by decide +kernel))
      node_3542
      node_3543
      (invalid_excluded a [8,6,7,0,3,3] (by decide +kernel))
      node_3544
      (invalid_excluded a [8,6,7,0,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,3,8] (by decide +kernel)))

theorem node_3532 : Excluded a [8,6,7,0] :=
  branch_excluded a [8,6,7,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,7,0,0] (by decide +kernel))
      node_3533
      node_3534
      node_3541
      (invalid_excluded a [8,6,7,0,4] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,0,8] (by decide +kernel)))

theorem node_3546 : Excluded a [8,6,7,1,0] :=
  predecessor_excluded a [8,6,7,1,0] 2 0 3 4 (by decide) (by decide +kernel)

theorem node_3548 : Excluded a [8,6,7,1,2,0] :=
  source_excluded a [8,6,7,1,2,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3549 : Excluded a [8,6,7,1,2,3] :=
  predecessor_excluded a [8,6,7,1,2,3] 0 3 4 5 (by decide) (by decide +kernel)

theorem node_3551 : Excluded a [8,6,7,1,2,4,0] :=
  source_excluded a [8,6,7,1,2,4,0] 1 2 6 (by decide) (by decide +kernel)

theorem node_3552 : Excluded a [8,6,7,1,2,4,3] :=
  source_excluded a [8,6,7,1,2,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_3553 : Excluded a [8,6,7,1,2,4,5] :=
  predecessor_excluded a [8,6,7,1,2,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_3550 : Excluded a [8,6,7,1,2,4] :=
  branch_excluded a [8,6,7,1,2,4] (by decide)
    (fin9_cases _
      node_3551
      (invalid_excluded a [8,6,7,1,2,4,1] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,2,4,2] (by decide +kernel))
      node_3552
      (invalid_excluded a [8,6,7,1,2,4,4] (by decide +kernel))
      node_3553
      (invalid_excluded a [8,6,7,1,2,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,2,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,2,4,8] (by decide +kernel)))

theorem node_3547 : Excluded a [8,6,7,1,2] :=
  branch_excluded a [8,6,7,1,2] (by decide)
    (fin9_cases _
      node_3548
      (invalid_excluded a [8,6,7,1,2,1] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,2,2] (by decide +kernel))
      node_3549
      node_3550
      (invalid_excluded a [8,6,7,1,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,2,8] (by decide +kernel)))

theorem node_3555 : Excluded a [8,6,7,1,3,0] :=
  source_excluded a [8,6,7,1,3,0] 1 2 5 (by decide) (by decide +kernel)

theorem node_3556 : Excluded a [8,6,7,1,3,2] :=
  predecessor_excluded a [8,6,7,1,3,2] 0 7 5 2 (by decide) (by decide +kernel)

theorem node_3557 : Excluded a [8,6,7,1,3,4] :=
  predecessor_excluded a [8,6,7,1,3,4] 0 4 4 5 (by decide) (by decide +kernel)

theorem node_3554 : Excluded a [8,6,7,1,3] :=
  branch_excluded a [8,6,7,1,3] (by decide)
    (fin9_cases _
      node_3555
      (invalid_excluded a [8,6,7,1,3,1] (by decide +kernel))
      node_3556
      (invalid_excluded a [8,6,7,1,3,3] (by decide +kernel))
      node_3557
      (invalid_excluded a [8,6,7,1,3,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,3,8] (by decide +kernel)))

theorem node_3545 : Excluded a [8,6,7,1] :=
  branch_excluded a [8,6,7,1] (by decide)
    (fin9_cases _
      node_3546
      (invalid_excluded a [8,6,7,1,1] (by decide +kernel))
      node_3547
      node_3554
      (invalid_excluded a [8,6,7,1,4] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,1,8] (by decide +kernel)))

theorem node_3560 : Excluded a [8,6,7,2,0,1] :=
  source_excluded a [8,6,7,2,0,1] 5 0 1 (by decide) (by decide +kernel)

theorem node_3562 : Excluded a [8,6,7,2,0,3,1] :=
  predecessor_excluded a [8,6,7,2,0,3,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_3563 : Excluded a [8,6,7,2,0,3,4] :=
  predecessor_excluded a [8,6,7,2,0,3,4] 0 4 5 6 (by decide) (by decide +kernel)

theorem node_3565 : Excluded a [8,6,7,2,0,3,5,1] :=
  source_excluded a [8,6,7,2,0,3,5,1] 0 2 7 (by decide) (by decide +kernel)

theorem node_3566 : Excluded a [8,6,7,2,0,3,5,4] :=
  predecessor_excluded a [8,6,7,2,0,3,5,4] 0 4 2 7 (by decide) (by decide +kernel)

theorem node_3564 : Excluded a [8,6,7,2,0,3,5] :=
  branch_excluded a [8,6,7,2,0,3,5] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,7,2,0,3,5,0] (by decide +kernel))
      node_3565
      (invalid_excluded a [8,6,7,2,0,3,5,2] (by decide +kernel))
      (invalid_excluded a [8,6,7,2,0,3,5,3] (by decide +kernel))
      node_3566
      (invalid_excluded a [8,6,7,2,0,3,5,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,2,0,3,5,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,2,0,3,5,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,2,0,3,5,8] (by decide +kernel)))

theorem node_3561 : Excluded a [8,6,7,2,0,3] :=
  branch_excluded a [8,6,7,2,0,3] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,7,2,0,3,0] (by decide +kernel))
      node_3562
      (invalid_excluded a [8,6,7,2,0,3,2] (by decide +kernel))
      (invalid_excluded a [8,6,7,2,0,3,3] (by decide +kernel))
      node_3563
      node_3564
      (invalid_excluded a [8,6,7,2,0,3,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,2,0,3,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,2,0,3,8] (by decide +kernel)))

theorem node_3568 : Excluded a [8,6,7,2,0,4,1] :=
  predecessor_excluded a [8,6,7,2,0,4,1] 2 1 1 6 (by decide) (by decide +kernel)

theorem node_3569 : Excluded a [8,6,7,2,0,4,3] :=
  source_excluded a [8,6,7,2,0,4,3] 2 0 6 (by decide) (by decide +kernel)

theorem node_3570 : Excluded a [8,6,7,2,0,4,5] :=
  predecessor_excluded a [8,6,7,2,0,4,5] 0 5 5 6 (by decide) (by decide +kernel)

theorem node_3567 : Excluded a [8,6,7,2,0,4] :=
  branch_excluded a [8,6,7,2,0,4] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,7,2,0,4,0] (by decide +kernel))
      node_3568
      (invalid_excluded a [8,6,7,2,0,4,2] (by decide +kernel))
      node_3569
      (invalid_excluded a [8,6,7,2,0,4,4] (by decide +kernel))
      node_3570
      (invalid_excluded a [8,6,7,2,0,4,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,2,0,4,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,2,0,4,8] (by decide +kernel)))

theorem node_3559 : Excluded a [8,6,7,2,0] :=
  branch_excluded a [8,6,7,2,0] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,6,7,2,0,0] (by decide +kernel))
      node_3560
      (invalid_excluded a [8,6,7,2,0,2] (by decide +kernel))
      node_3561
      node_3567
      (invalid_excluded a [8,6,7,2,0,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,2,0,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,2,0,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,2,0,8] (by decide +kernel)))

theorem node_3571 : Excluded a [8,6,7,2,1] :=
  predecessor_excluded a [8,6,7,2,1] 0 6 4 1 (by decide) (by decide +kernel)

theorem node_3572 : Excluded a [8,6,7,2,3] :=
  predecessor_excluded a [8,6,7,2,3] 0 3 3 4 (by decide) (by decide +kernel)

theorem node_3558 : Excluded a [8,6,7,2] :=
  branch_excluded a [8,6,7,2] (by decide)
    (fin9_cases _
      node_3559
      node_3571
      (invalid_excluded a [8,6,7,2,2] (by decide +kernel))
      node_3572
      (invalid_excluded a [8,6,7,2,4] (by decide +kernel))
      (invalid_excluded a [8,6,7,2,5] (by decide +kernel))
      (invalid_excluded a [8,6,7,2,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,2,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,2,8] (by decide +kernel)))

theorem node_3573 : Excluded a [8,6,7,5] :=
  source_excluded a [8,6,7,5] 3 0 4 (by decide) (by decide +kernel)

theorem node_3531 : Excluded a [8,6,7] :=
  branch_excluded a [8,6,7] (by decide)
    (fin9_cases _
      node_3532
      node_3545
      node_3558
      (invalid_excluded a [8,6,7,3] (by decide +kernel))
      (invalid_excluded a [8,6,7,4] (by decide +kernel))
      node_3573
      (invalid_excluded a [8,6,7,6] (by decide +kernel))
      (invalid_excluded a [8,6,7,7] (by decide +kernel))
      (invalid_excluded a [8,6,7,8] (by decide +kernel)))

theorem node_3404 : Excluded a [8,6] :=
  branch_excluded a [8,6] (by decide)
    (fin9_cases _
      node_3405
      node_3436
      (invalid_excluded a [8,6,2] (by decide +kernel))
      (invalid_excluded a [8,6,3] (by decide +kernel))
      node_3492
      node_3493
      (invalid_excluded a [8,6,6] (by decide +kernel))
      node_3531
      (invalid_excluded a [8,6,8] (by decide +kernel)))

theorem node_3574 : Excluded a [8,7] :=
  predecessor_excluded a [8,7] 2 8 1 0 (by decide) (by decide +kernel)

theorem node_3053 : Excluded a [8] :=
  branch_excluded a [8] (by decide)
    (fin9_cases _
      (invalid_excluded a [8,0] (by decide +kernel))
      (invalid_excluded a [8,1] (by decide +kernel))
      node_3054
      node_3055
      node_3151
      node_3263
      node_3404
      node_3574
      (invalid_excluded a [8,8] (by decide +kernel)))

theorem node_1 : Excluded a [] :=
  branch_excluded a [] (by decide)
    (fin9_cases _
      (invalid_excluded a [0] (by decide +kernel))
      (invalid_excluded a [1] (by decide +kernel))
      node_2
      node_506
      node_921
      node_1400
      node_1938
      node_2490
      node_3053)

theorem every_second_factor_blocked (b : Assignment 9) (valid : Valid a b) : Blocked a b :=
  node_1 b valid (by intro i h; simp at h)

theorem primary_loopless : ∀ i : Fin 9, a i ≠ i := by decide +kernel

#print axioms every_second_factor_blocked
end Delivery.FiniteExclusion.Cycle2x7
